import Jihoo.NativeCoreGhostDeclarationAnnotations

/-! The evidence branch of native declaration checking derives its mode
from the actual annotation, then checks the original body against that
annotation. Its graph and meter are shared across the entire check. -/
namespace Jihoo.NativeKernel.NativeCoreGhostDefinitionChecking

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained requireTypes requireTypes_progress
  requireTypes_refines next_progress)
open EnvironmentDelta (expand)

def run (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (annotation body : Nat) : Outcome (List (Nat × Nat)) :=
  (NativeCoreGhostDeclarationAnnotations.run infer normal state annotation).next fun formed written =>
    if written.sort = .prop then
      (infer formed body).next fun inferred answer =>
        (requireTypes normal limit depth inferred answer.typeRoot annotation body).next fun checked pair =>
          ⟨checked,.ok (written.compared ++ (answer.compared ++ [pair]))⟩
    else ⟨formed,.error (.outsideFragment body)⟩

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth state annotation body) := by
  unfold run
  apply next_progress (NativeCoreGhostDeclarationAnnotations.run_progress infers normalizes room) room
  intro written _ annotationRoom
  split
  · apply next_progress (infers _ _ annotationRoom) annotationRoom
    intro answer _ bodyRoom
    exact (requireTypes_progress (fun after root _ => normalizes after root) bodyRoom).next
      (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

/-- Both source judgments use the original annotation. The accepted identity
comparison of the two live normalized type roots converts the checked body
to that annotation. Its expected type is never replaced by the result root. -/
theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base [] limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena annotation type) (source : Represents state.arena body term)
    (success : (run infer normal limit depth state annotation body).result = .ok compared)
    (ambient : Prefix (run infer normal limit depth state annotation body).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (run infer normal limit depth state annotation body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] [] true (expand env type) .prop ∧
      LoanTyping.HasType env [] [] true (expand env term) (expand env type) := by
  unfold run at success ambient ⊢
  obtain ⟨formed,formedOk,formedNext⟩ := Outcome.next_success success
  rw [formedNext] at success ambient ⊢
  split at success
  · rename_i ghost
    simp only [ite_eq_left ghost] at ambient ⊢
    obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
    rw [inferredNext] at success ambient ⊢
    obtain ⟨pair,pairOk,pairNext⟩ := Outcome.next_success success
    rw [pairNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst compared
    let formedType := NativeCoreGhostDeclarationAnnotations.run infer normal state annotation
    let bodyType := infer formedType.state body
    have formation := NativeCoreGhostDeclarationAnnotations.run_progress (state := state) (typeRoot := annotation)
      inferProgress normalProgress room
    have formedRoom := formation.accepted room formed formedOk
    have bodyProgress := inferProgress formedType.state body formedRoom
    have bodyRoom := bodyProgress.accepted formedRoom inferred inferredOk
    have comparedProgress := requireTypes_progress (state := bodyType.state) (depth := depth)
      (actual := inferred.typeRoot) (expected := annotation) (argument := body)
      (fun after root _ => normalProgress after root) bodyRoom
    have bodyFinal := comparedProgress.kept.trans ambient
    obtain ⟨formedKept,formedBack,validType⟩ := NativeCoreGhostDeclarationAnnotations.run_refines
      normalSound normalProgress inferSound onBase room written formedOk (bodyProgress.kept.trans bodyFinal)
      (fun entry member => retained entry (List.mem_append_left _ member))
    obtain ⟨bodyKept,bodyBack,_,typeRep,typed⟩ := inferSound (onBase.trans formedKept) formedRoom
      (source.frame formedKept) inferredOk bodyFinal
      (fun entry member => retained entry (List.mem_append_right _ (List.mem_append_left _ member)))
    have throughBody := formedKept.trans bodyKept
    obtain ⟨comparedKept,comparedBack,compatible⟩ := requireTypes_refines normalSound (onBase.trans throughBody)
      typeRep (written.frame throughBody) pairOk ambient (retained pair (by simp))
    exact ⟨throughBody.trans comparedKept,comparedBack ∘ bodyBack ∘ formedBack,
      by simpa only [ghost,SortTag.term] using validType,typed.convert compatible⟩
  · cases success

private def equalitySnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1,2⟩]
  families := []
  arena := #[.node (.natural 0) [],.node .eq [0,0],.node .refl [0]]

private def proofVisit (limit : Nat) : Outcome (List (Nat × Nat)) :=
  run (NativeCoreGhostSpineInference.run equalitySnapshot.definitions 0 limit 128 [])
    (NativeCoreGhostLiteralAddition.run equalitySnapshot.definitions 0 limit 128)
    limit 128 ⟨equalitySnapshot.arena,0⟩ 1 2

/-- The original annotation and proof consume a single budget. Requiring
one fewer step retains the graph but cannot complete its final identity. -/
theorem admitted_proof_body_uses_shared_meter :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot equalitySnapshot) = true ∧
    (let checked := proofVisit 24
     checked.state.steps = 24 ∧ checked.result.map List.length = .ok 4) ∧
    (let rejected := proofVisit 23
     rejected.state.steps = 24 ∧ rejected.state.arena = (proofVisit 24).state.arena ∧
       ∃ root, rejected.result = .error (.tick (.stepLimit root))) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  refine ⟨by cbv,by cbv,?_⟩
  exact ⟨by cbv,by cbv,⟨0,by cbv⟩⟩

end Jihoo.NativeKernel.NativeCoreGhostDefinitionChecking
