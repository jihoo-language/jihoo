import Jihoo.NativeCoreCodeUses
import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeLoanPolicies

/-! The specialized native Lend checks the resumed owner's demand after
inferring the restored callback, and normalizes the result once more
after lowering it out of the callback's binder. -/
namespace Jihoo.NativeKernel.NativeCoreCodeLendGates

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Visit)
open EnvironmentDelta (expand)

private def reject (state : State) (root : Nat) : Outcome Unit :=
  ⟨state,.error (.outsideFragment root)⟩

def ownerOnce (limit depth slot : Nat) (state : State) (continuation : Nat) : Outcome Unit :=
  let (selected,body) := match state.arena[continuation]? with
    | some (.node (.lam _) [_,body]) => (slot+1,body)
    | _ => (slot,continuation)
  (NativeCoreCodeUses.run limit selected depth state body).next fun after count =>
    if count = 1 then ⟨after,.ok ()⟩ else reject after continuation

theorem ownerOnce_progress :
    Progress limit state (ownerOnce limit depth slot state continuation) := by
  unfold ownerOnce
  split <;> exact (NativeCoreCodeUses.run_progress _ _ _ _ _).next
    (fun _ => by split <;> exact Progress.atState _ _)

/-- The actual one-binder visit preserves the graph and counts precisely
the lifted slot of the original returned owner. -/
theorem openedOwnerOnce_refines (bodyRep : Represents state.arena body written)
    (read : state.arena[continuation]? = some (.node (.lam erased) [domain,body]))
    (success : (ownerOnce limit depth slot state continuation).result = .ok ()) :
    (ownerOnce limit depth slot state continuation).state.arena = state.arena ∧
      ∃ control, NativeCoreCodeUses.Projects written control ∧ control.demand (slot+1) = some 1 := by
  simp only [ownerOnce,read] at success ⊢
  obtain ⟨count,counted,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  split at success
  · rename_i one
    rw [ite_eq_left one]
    subst count
    exact NativeCoreCodeUses.run_refines bodyRep counted
  · cases success

private def isProduct (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node (.pi _) _) => true
  | _ => false

def checkResult (normal : Visit) (state : State) (result continuation : Nat) : Outcome Unit :=
  (normal state result).next fun exposed root =>
    if isProduct exposed.arena root then reject exposed continuation else ⟨exposed,.ok ()⟩

theorem checkResult_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkResult normal state result continuation) := by
  unfold checkResult
  exact (normalProgress _ _).next fun _ => by split <;> exact Progress.atState _ _

/-- Acceptance exposes the exact root read by the native continuation
gate, with the original lowered result connected to it by conversion. -/
theorem checkResult_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (original : Represents state.arena result T)
    (success : (checkResult normal state result continuation).result = .ok ()) :
    let after := (checkResult normal state result continuation).state
    Prefix state.arena after.arena ∧ (Backward state.arena → Backward after.arena) ∧
      ∃ selected term, (normal state result).result = .ok selected ∧
        Represents after.arena selected term ∧ RawLend.Conv env (expand env T) (expand env term) ∧
        ∀ erased domain body, term ≠ Term.pi erased domain body := by
  unfold checkResult at success ⊢
  obtain ⟨selected,selectedOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,term,represented,converted⟩ := normalSound onBase original selectedOk
  by_cases rejected : isProduct (normal state result).state.arena selected = true
  · rw [ite_eq_left rejected] at success
    cases success
  · rw [ite_eq_right rejected]
    refine ⟨kept,backward,selected,term,selectedOk,represented,converted.converted,?_⟩
    intro erased domain body product
    subst term
    cases represented with
    | node read _ _ =>
      exact rejected (by simp only [isProduct,read])

private def canonicalHead (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.var _) => true
  | some (.node op _) => RawLend.nonFunctionOp op
  | none => false

private theorem canonicalHead_expanded (source : Represents arena root term)
    (known : canonicalHead arena root = true) :
    RawLend.nonFunctionHead (expand env term) = true := by
  cases source with
  | var read => simp only [expand,RawLend.nonFunctionHead]
  | @node _ op refs terms read width children =>
    have accepted : RawLend.nonFunctionOp op = true := by
      simpa only [canonicalHead,read] using known
    cases op <;> simp_all only [RawLend.nonFunctionOp,RawLend.nonFunctionHead,expand,Bool.false_eq_true]

private theorem canonicalHead_nonProduct (known : canonicalHead arena root = true) :
    isProduct arena root = false := by
  unfold canonicalHead isProduct at *
  split at known
  · simp_all
  · rename_i op refs read
    rw [read]
    cases op <;> simp_all only [RawLend.nonFunctionOp,Bool.false_eq_true]
  · contradiction

/-- The positive source policy applies when the native head is a retained
variable or a rigid nonfunction constructor. The check visits the same
normalization once and remembers the original lowered annotation. -/
def checkCanonical (normal : Visit) (state : State) (result continuation : Nat) : Outcome Unit :=
  (normal state result).next fun exposed root =>
    if canonicalHead exposed.arena root then ⟨exposed,.ok ()⟩ else reject exposed continuation

theorem checkCanonical_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkCanonical normal state result continuation) := by
  unfold checkCanonical
  exact (normalProgress _ _).next fun _ => by split <;> exact Progress.atState _ _

/-- An accepted canonical visit has the same native result and graph. -/
theorem checkCanonical_native
    (success : (checkCanonical normal state result continuation).result = .ok ()) :
    checkCanonical normal state result continuation = checkResult normal state result continuation := by
  unfold checkCanonical at success ⊢
  unfold checkResult
  obtain ⟨selected,selectedOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  simp only [Outcome.next,selectedOk]
  by_cases known : canonicalHead (normal state result).state.arena selected = true
  · simp only [known,canonicalHead_nonProduct known,Bool.false_eq_true,ite_false,ite_true]
  · rw [ite_eq_right known] at success
    cases success

theorem checkCanonical_policy
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (original : Represents state.arena result T)
    (success : (checkCanonical normal state result continuation).result = .ok ()) :
    let after := (checkCanonical normal state result continuation).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.continuationAllowed env false (expand env T) := by
  unfold checkCanonical at success ⊢
  obtain ⟨selected,selectedOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,term,represented,converted⟩ := normalSound onBase original selectedOk
  by_cases known : canonicalHead (normal state result).state.arena selected = true
  · rw [ite_eq_left known]
    exact ⟨kept,backward,.inr ⟨expand env term,converted.converted,canonicalHead_expanded represented known⟩⟩
  · rw [ite_eq_right known] at success
    cases success

end Jihoo.NativeKernel.NativeCoreCodeLendGates
