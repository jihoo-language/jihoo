import Jihoo.NativeLoanResourceReplay
import Jihoo.NativeControlScope
import Jihoo.NativeEnvironmentCaseQuantity

/-! Actual dependent-Lend resource guards. Reader and continuation controls
come from the native specialized source expressions in their exact loan
stacks. The returned owner aliases the original owner before demand checking;
the first result remains a distinct fresh slot with its actual resolved mode. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes ResourceReplay
variable {control : Control}

def dependentControl (owner : Nat) (mode : BinderMode) (reader rest : Control) : Option Control :=
  if reader.demand owner == some 0 && (Control.scope mode rest).demand owner == some 1
  then some (.seq reader (.scope mode rest)) else none

theorem dependentControl_origin (checked : dependentControl owner mode reader rest = some control) :
    control = .seq reader (.scope mode rest) ∧ reader.demand owner = some 0 ∧
      (Control.scope mode rest).demand owner = some 1 := by
  unfold dependentControl at checked
  split at checked
  · rename_i accepted
    obtain ⟨readZero,restoreOne⟩ := Bool.and_eq_true_iff.mp accepted
    cases checked
    exact ⟨rfl,beq_iff_eq.mp readZero,beq_iff_eq.mp restoreOne⟩
  · contradiction

theorem dependentControl_demand (checked : dependentControl owner mode reader rest = some control) :
    control.demand owner = some 1 := by
  obtain ⟨rfl,readZero,restoreOne⟩ := dependentControl_origin checked
  simp only [Control.demand,readZero,restoreOne,Bind.bind,Option.bind,Nat.zero_add]
  rfl

theorem dependent_reader_finished (checked : dependentControl owner mode reader rest = some control)
    (run : Finishes reader events) : events.count owner = 0 :=
  run.count_eq (dependentControl_origin checked).2.1

theorem dependent_reader_prefix (checked : dependentControl owner mode reader rest = some control)
    (run : Prefix reader events) : events.count owner = 0 := by
  have bound := run.count_le (dependentControl_origin checked).2.1
  omega

theorem dependent_finished (checked : dependentControl owner mode reader rest = some control)
    (run : Finishes control events) : events.count owner = 1 := run.count_eq (dependentControl_demand checked)

theorem dependent_prefix (checked : dependentControl owner mode reader rest = some control)
    (run : Prefix control events) : events.count owner ≤ 1 := run.count_le (dependentControl_demand checked)

theorem dependent_first_linear_finished
    (checked : dependentControl owner .linear reader rest = some control)
    (run : Finishes rest events) : events.count 0 = 1 :=
  Jihoo.Quantity.bound_finished (dependentControl_origin checked).2.2 run

theorem dependent_first_linear_prefix
    (checked : dependentControl owner .linear reader rest = some control)
    (run : Prefix rest events) : events.count 0 ≤ 1 :=
  Jihoo.Quantity.bound_prefix (dependentControl_origin checked).2.2 run

/-- This is an exact source identity, not a code typing substitution theorem.
Both the returned owner and original owner now name the same actual slot. -/
theorem restore_body_is_alias (body : Term) (owner : Nat) :
    body.subst (single ((Term.var owner).rename Nat.succ)) =
      body.rename (Jihoo.Quantity.openOwner (owner+1)) := by
  have mapping : single ((Term.var owner).rename Nat.succ) =
      (fun index => Term.var (Jihoo.Quantity.openOwner (owner+1) index)) := by
    funext index
    cases index <;> simp only [single,Term.rename,Jihoo.Quantity.openOwner]
  rw [mapping,Environment.variable_subst_eq_rename]

theorem restored_returned_owner :
    (Term.var 0).subst (single ((Term.var owner).rename Nat.succ)) = .var (owner+1) := by
  simp only [Term.subst,single,Term.rename]

theorem restored_original_owner :
    (Term.var (owner+2)).subst (single ((Term.var owner).rename Nat.succ)) = .var (owner+1) := by
  simp only [Term.subst,single]

theorem restored_first_result :
    (Term.var 1).subst (single ((Term.var owner).rename Nat.succ)) = .var 0 := by
  simp only [Term.subst,single]

def firstOwned (fuel : Nat) (env : Environment) (first : Term) : Bool :=
  (Conversion.normalize? env fuel first).any (ResourceReplay.linearDomain env)

theorem linearDomain_head (owned : ResourceReplay.linearDomain env normal = true) :
    ContextModes.head env normal = some .linear := by
  fun_cases ResourceReplay.linearDomain env normal
  · simp [ContextModes.head,NativeQuantity.binderMode]
  · simp only [ResourceReplay.linearDomain] at owned
    fun_cases Checker.ownedHead env normal
    · simp [ContextModes.head,NativeQuantity.binderMode]
    · rename_i family count indices excluded
      cases found : env.families[family]? with
      | none => simp [Checker.ownedHead,found] at owned
      | some entry =>
          simp only [Checker.ownedHead,found,Option.any_some] at owned
          simp only [ContextModes.head,found,Option.map_some,owned,↓reduceIte]
    · simp only [Checker.ownedHead] at owned
      contradiction

/-- Runtime ownership is classified from the actual same normalized first
annotation, without an output-safety certificate or normalizer completeness. -/
theorem firstOwned_resolve_linear (owned : firstOwned fuel env first = true)
    (resolved : resolve fuel env loans ctx false first = some mode) : mode = .linear := by
  cases normalized : Conversion.normalize? env fuel first with
  | none => simp [firstOwned,normalized] at owned
  | some normal =>
      have known : ResourceReplay.linearDomain env normal = true := by simpa only [firstOwned,normalized,Option.any_some] using owned
      have linear : resolve fuel env loans ctx false first = some .linear := by
        simp only [resolve,Bool.false_eq_true,↓reduceIte,normalized,Bind.bind,Option.bind,linearDomain_head known]
      exact Option.some.inj (resolved.symm.trans linear)

/-- Every recursive callback is the smaller-fuel complete projection. The
whole Lend check and source scope check are executed here, without evidence
inputs. Computed generic callbacks retain their source-expression boundary. -/
def projectLend (visit : Loans.Stack → Context → Term → Option Control)
    (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (owner reader continuation : Term) : Option Control := do
  if !NativeKernel.scopeCheck ctx.length (.lend owner reader continuation) then none else
  let _ ← Checker.infer fuel env loans ctx false (.lend owner reader continuation)
  let ownerType ← Checker.expose fuel env (Checker.infer fuel env loans ctx false owner)
  if !Checker.ownedHead env ownerType then none else
  match owner,reader,continuation with
  | .var index,.lam false _ readerBody,.lam false first (.lam false _ body) => do
      let entered := Loans.enter ctx.length index loans
      let read := Lending.read (.var index) readerBody
      let restored := body.subst (single ((Term.var index).rename Nat.succ))
      if !NativeKernel.scopeCheck ctx.length read || !NativeKernel.scopeCheck (ctx.length+1) restored then none else
      let readControl ← visit entered ctx read
      let mode ← resolve fuel env loans ctx false first
      let restControl ← visit loans (⟨first,false⟩ :: ctx) restored
      dependentControl index mode readControl restControl
  | _,_,_ => do
      let ownerControl ← visit loans ctx owner
      let readControl ← visit loans ctx reader
      let restControl ← visit loans ctx continuation
      pure (.seq ownerControl (.seq (.once (caseBody 1 readControl)) (.once (caseBody 2 restControl))))

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
