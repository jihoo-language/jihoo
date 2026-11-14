import Jihoo.NativeLendSyntax
import Jihoo.NativeEnvironmentContextualPreservation

/-! The native pure Lend expansion and its dependent specialization have the
same genuine forward beta contractum. Neither callback is assumed typable at
arbitrary arguments. This is not an active-loan CODE typing or heap theorem. -/
namespace Jihoo.NativeKernel.Environment.Lending

def desugar (owner reader continuation : Term) : Term :=
  .app (.app continuation (.app reader (.borrow owner))) owner

def finish (owner body value : Term) : Term :=
  (body.subst (single (owner.rename Nat.succ))).subst (single value)

theorem returned_owner_substitutions (owner body value : Term) :
    (body.subst (liftSubOne (single value))).subst (single owner) = finish owner body value := by
  simp only [finish,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [liftSubOne,single,Term.subst]
  | succ index =>
    cases index with
    | zero => simp [liftSubOne,single,Term.subst,Term.shift_subst_single]
    | succ index => simp [liftSubOne,single,Term.subst,Term.rename]

private theorem app_left (step : EnvironmentDelta.Forward env first second) :
    EnvironmentDelta.Forward env (.app first argument) (.app second argument) :=
  .node .app (.cons step (.cons .refl .nil))

private theorem app_right (step : EnvironmentDelta.Forward env first second) :
    EnvironmentDelta.Forward env (.app function first) (.app function second) :=
  .node .app (.cons .refl (.cons step .nil))

theorem continuation_forward (owner first again body value : Term) :
    EnvironmentDelta.Forward env
      (.app (.app (.lam false first (.lam false again body)) value) owner)
      (finish owner body value) := by
  have outer : EnvironmentDelta.Forward env
      (.app (.app (.lam false first (.lam false again body)) value) owner)
      (.app ((Term.lam false again body).subst (single value)) owner) :=
    app_left (.acu (.compute (.beta false first (.lam false again body) value)))
  have inner : EnvironmentDelta.Forward env
      (.app ((Term.lam false again body).subst (single value)) owner)
      ((body.subst (liftSubOne (single value))).subst (single owner)) := by
    simpa only [Term.lam,Term.subst,substArgs,Op.binders,liftSub] using
      (EnvironmentDelta.Forward.acu (env := env)
        (.compute (.beta false (again.subst (single value))
          (body.subst (liftSubOne (single value))) owner)))
  simpa only [returned_owner_substitutions] using outer.trans inner

theorem desugar_forward (owner domain readerBody first again body : Term) :
    EnvironmentDelta.Forward env
      (desugar owner (.lam false domain readerBody) (.lam false first (.lam false again body)))
      (finish owner body (read owner readerBody)) := by
  have readerStep : EnvironmentDelta.Forward env
      (.app (.lam false domain readerBody) (.borrow owner)) (read owner readerBody) :=
    .acu (.compute (.beta false domain readerBody (.borrow owner)))
  exact .trans (app_left (app_right readerStep))
    (continuation_forward owner first again body (read owner readerBody))

theorem specialized_forward (owner first body value : Term) :
    EnvironmentDelta.Forward env (.app (restore owner first body) value) (finish owner body value) :=
  .acu (.compute (.beta false first (body.subst (single (owner.rename Nat.succ))) value))

/-- This uses the specialized continuation actually checked by dependent_lend,
not a hypothetical universally typable two-argument continuation. The original
application type is retained, including independently converted representatives. -/
theorem finish_preserves
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode (.app (restore owner first body) value) type) :
    HasType env ctx true (finish owner body value) type :=
  typed.ghostBeta wf

theorem finish_from_specialized_checks
    (wf : UnifiedProgram.EnvWellFormed env)
    (continuation : HasType env ctx mode (restore owner first body) (.pi false actualDomain result))
    (reader : HasType env ctx true value actualDomain) :
    HasType env ctx true (finish owner body value) (result.subst (single value)) :=
  finish_preserves wf (.app continuation.ghost reader (Or.inl rfl))

/-- The two body checks used by the actual dependent path construct a typed
forward contractum of the pure expansion, even when callback specialization
uses facts about the original owner. -/
theorem dependent_checks_preserve
    (wf : UnifiedProgram.EnvWellFormed env)
    (accepted : dependent? owner reader continuation = some expansion)
    (readTyped : HasType env ctx true expansion.read domain)
    (continuationTyped : HasType env ctx mode expansion.continuation (.pi false domain result)) :
    ∃ output, EnvironmentDelta.Forward env (desugar owner reader continuation) output ∧
      HasType env ctx true output (result.subst (single expansion.read)) := by
  fun_cases dependent? owner reader continuation <;> simp only [dependent?] at accepted
  · cases accepted
    exact ⟨_,desugar_forward _ _ _ _ _ _,
      finish_from_specialized_checks wf continuationTyped readTyped⟩
  · contradiction

/-- Exact partial scope removal used by Core.dependent_lend's result. This
retains the inferred result representative without assuming type regularity. -/
theorem result_outside
    (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conversion.Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside) :
    Conversion.Conv env (result.subst (single value)) outside := by
  have reweakens := Checker.branch_type_reweakens removed
  have substituted := converted.substitution (single value) wf.closed
  simpa only [← reweakens,Term.shift_subst_single] using substituted

theorem dependent_original_type
    (wf : UnifiedProgram.EnvWellFormed env)
    (accepted : dependent? owner reader continuation = some expansion)
    (readTyped : HasType env ctx true expansion.read domain)
    (continuationTyped : HasType env ctx mode expansion.continuation (.pi false domain result))
    (converted : Conversion.Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside) :
    ∃ output, EnvironmentDelta.Forward env (desugar owner reader continuation) output ∧
      HasType env ctx true output outside := by
  obtain ⟨output,forward,typed⟩ := dependent_checks_preserve wf accepted readTyped continuationTyped
  exact ⟨output,forward,typed.convert (result_outside wf converted removed)⟩

end Jihoo.NativeKernel.Environment.Lending
