import Jihoo.NativeCoreCodeLeaseLookup
import Jihoo.NativeCoreGhostReferenceTypes
import Jihoo.NativeLoanCodeRenaming

/-! Code borrowing retains the written owner type. Its lease check executes
before the owner's ghost inference and the native owned-head check. -/
namespace Jihoo.NativeKernel.NativeCoreCodeBorrow

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred RetainedComparisons next_progress)
open NativeCoreGhostReferenceTypes (BoxedFamilies requireOwned requireOwned_progress requireOwned_refines)
open NativeCoreCodeLeaseLookup (Snapshot FramesRep)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

def run (isBoxed : Nat → Bool) (infer : Infer) (normal : Visit) (limit depth current : Nat)
    (state : State) (snapshots : List Snapshot) (source owner : Nat) : Outcome Inferred :=
  (NativeCoreCodeLeaseLookup.run limit depth current state snapshots owner).next fun permitted active =>
    if active then
      (infer permitted owner).next fun inferred result =>
        (requireOwned normal isBoxed inferred result.typeRoot owner).next fun owned _ =>
          (append owned .ref [result.typeRoot]).next fun after reference =>
            ⟨after,.ok ⟨reference,result.compared⟩⟩
    else ⟨permitted,.error (.outsideFragment source)⟩

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run isBoxed infer normal limit depth current state snapshots source owner) := by
  unfold run
  apply next_progress (NativeCoreCodeLeaseLookup.run_progress room) room
  intro active _ within
  cases active
  · exact Progress.atState _ _
  · simp only [ite_true]
    apply next_progress (childProgress _ _ within) within
    intro _ _ _
    exact (requireOwned_progress normalProgress).next
      (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))

/-- The actual reader snapshots supply permission at the use site. The
owner is checked as ghost syntax while the resulting borrow is code. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env) (metadata : BoxedFamilies env isBoxed)
    (frames : FramesRep state.arena snapshots loans)
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena owner (.var index))
    (success : (run isBoxed infer normal limit depth ctx.length state snapshots source owner).result = .ok answer)
    (ambient : Prefix (run isBoxed infer normal limit depth ctx.length state snapshots source owner).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (run isBoxed infer normal limit depth ctx.length state snapshots source owner).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot (.ref type) ∧
        LoanTyping.HasType env loans ctx false (.borrow (.var index)) (.ref (expand env type)) := by
  unfold run at success ambient ⊢
  obtain ⟨authorized,authorizedOk,authorizedNext⟩ := Outcome.next_success success
  rw [authorizedNext] at success ambient ⊢
  cases authorized with
  | false => cases success
  | true =>
    simp only [ite_true] at success ambient ⊢
    obtain ⟨ownerResult,ownerOk,ownerNext⟩ := Outcome.next_success success
    rw [ownerNext] at success ambient ⊢
    obtain ⟨_,ownedOk,ownedNext⟩ := Outcome.next_success success
    rw [ownedNext] at success ambient ⊢
    obtain ⟨reference,refOk,refNext⟩ := Outcome.next_success success
    rw [refNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let authorized := NativeCoreCodeLeaseLookup.run limit depth ctx.length state snapshots owner
    let inferred := infer authorized.state owner
    let owned := requireOwned normal isBoxed inferred.state ownerResult.typeRoot owner
    have allowed : Loans.active ctx.length loans index = true :=
      (NativeCoreCodeLeaseLookup.run_refines frames ownerRep authorizedOk).symm
    have authorization := NativeCoreCodeLeaseLookup.run_progress (depth := depth) (current := ctx.length)
      (snapshots := snapshots) (owner := owner) room
    have childRoom := authorization.accepted room true authorizedOk
    have retainCheck := (append_progress (limit := limit) owned.state .ref [ownerResult.typeRoot]).kept.trans ambient
    have policy := requireOwned_progress (state := inferred.state) (root := ownerResult.typeRoot)
      (rejected := owner) (isBoxed := isBoxed) normalProgress
    obtain ⟨childKept,childBack,type,typeRep,typed⟩ := inferSound (onBase.trans authorization.kept)
      childRoom (ownerRep.frame authorization.kept) ownerOk (policy.kept.trans retainCheck) retained
    obtain ⟨ownedKept,ownedBack,ownerType⟩ := requireOwned_refines metadata normalSound
      (onBase.trans (authorization.kept.trans childKept)) typeRep ownedOk
    obtain ⟨appendKept,appendBack,rootRep⟩ := append_refines (.cons (typeRep.frame ownedKept) .nil) rfl refOk
    have renamed : LoanTyping.CodeRenaming [] ctx loans ctx id := by
      refine ⟨?_,?_,?_⟩
      · intro i binding found
        simpa only [Term.rename_id,id_eq] using found
      · intro frame member
        cases member
      · intro selected impossible
        cases impossible
    have restored := typed.codeRenaming wf renamed
    have ownerTyped : LoanTyping.HasType env loans ctx true (.var index) (expand env type) := by
      simpa only [expand,Term.rename_id] using restored
    refine ⟨authorization.kept.trans (childKept.trans (ownedKept.trans appendKept)),?_,type,rootRep,
      .codeBorrowOwned ownerTyped ownerType allowed⟩
    intro backward
    exact appendBack (ownedBack (childBack (NativeCoreCodeLeaseLookup.run_backward frames ownerRep authorizedOk backward)))

end Jihoo.NativeKernel.NativeCoreCodeBorrow
