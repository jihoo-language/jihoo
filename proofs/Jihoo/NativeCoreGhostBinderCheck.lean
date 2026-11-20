import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreGhostSort

/-! A binder check infers its written domain in ghost mode, exposes the
sort and tests the admissible erasure before entering the binder. -/
namespace Jihoo.NativeKernel.NativeCoreGhostBinderCheck

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained next_progress)
open NativeCoreGhostSort (DataFamilies)
open EnvironmentDelta (expand)

structure InferredBinder where
  sort : SortTag
  compared : List (Nat × Nat)

def inferBinder (infer : Infer) (normal : Visit) (isData : Nat → Bool)
    (state : State) (domain : Nat) (erased : Bool) : Outcome InferredBinder :=
  (infer state domain).next fun afterDomain domainType =>
    (NativeCoreGhostSort.sort normal afterDomain domainType.typeRoot).next fun afterSort selected =>
      (NativeCoreGhostSort.policy normal isData afterSort domain erased selected).next fun after _ =>
        ⟨after, .ok ⟨selected, domainType.compared⟩⟩

theorem inferBinder_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferBinder infer normal isData state domain erased) := by
  apply next_progress (infers _ _ room) room
  intro inferred _ _
  exact (NativeCoreGhostSort.sort_progress normalizes).next (fun _ =>
    (NativeCoreGhostSort.policy_progress normalizes).next (fun _ => Progress.atState _ _))

theorem inferBinder_refines
    (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (domainRep : Represents state.arena domain term)
    (success : (inferBinder infer normal isData state domain erased).result = .ok answer)
    (ambient : Prefix (inferBinder infer normal isData state domain erased).state.arena final)
    (retained : ∀ pair ∈ answer.compared, PairRetained final pair) :
    let after := (inferBinder infer normal isData state domain erased).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Binder env [] ctx erased (expand env term) answer.sort := by
  unfold inferBinder at success ambient ⊢
  obtain ⟨inferred, inferenceOk, inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨selected, sortOk, sortNext⟩ := Outcome.next_success success
  rw [sortNext] at success ambient ⊢
  obtain ⟨⟨⟩, policyOk, policyNext⟩ := Outcome.next_success success
  rw [policyNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have inferProgress := childProgress state domain room
  let sorted := NativeCoreGhostSort.sort normal (infer state domain).state inferred.typeRoot
  have sortProgress := NativeCoreGhostSort.sort_progress (state := (infer state domain).state)
    (typeRoot := inferred.typeRoot) normalProgress
  have policyProgress := NativeCoreGhostSort.policy_progress (state := sorted.state) (isData := isData)
    (domain := domain) (selected := selected) (erased := erased) normalProgress
  have afterSort := policyProgress.kept.trans ambient
  obtain ⟨_, inferBack, _, inferredRep, domainTyped⟩ := childSound onBase room domainRep inferenceOk
    (sortProgress.kept.trans afterSort) retained
  obtain ⟨sortedKept, sortedBack, exposed⟩ := NativeCoreGhostSort.sort_refines normalSound
    (onBase.trans inferProgress.kept) inferredRep sortOk
  have throughSort := inferProgress.kept.trans sortedKept
  obtain ⟨policyKept, policyBack, allowed⟩ := NativeCoreGhostSort.policy_refines normalSound metadata
    (onBase.trans throughSort) (domainRep.frame throughSort) policyOk
  exact ⟨throughSort.trans policyKept, policyBack ∘ sortedBack ∘ inferBack,
    .intro (domainTyped.convert exposed) allowed⟩

end Jihoo.NativeKernel.NativeCoreGhostBinderCheck
