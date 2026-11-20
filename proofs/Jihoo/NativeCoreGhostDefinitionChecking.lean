import Jihoo.NativeCoreGhostDeclarationAnnotations
import Jihoo.NativeCoreCodeHeadInference

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

/-- A native declaration may use a deliberately bounded operative checker
for the body. Soundness is stated separately at the mode selected by the
annotation, with all comparisons retained in the same final arena. -/
def BodySound (env : Environment) (base : Arena) (limit : Nat) (infer : Bool → Infer) : Prop :=
  ∀ mode {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (infer mode state root).result = .ok answer → Prefix (infer mode state root).state.arena final →
    (∀ pair ∈ answer.compared, PairRetained final pair) →
    let after := (infer mode state root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env [] [] mode (expand env term) (expand env type)

def runWithModes (infer : Infer) (bodyInfer : Bool → Infer) (normal : Visit) (limit depth : Nat)
    (state : State) (annotation body : Nat) : Outcome (List (Nat × Nat)) :=
  (NativeCoreGhostDeclarationAnnotations.run infer normal state annotation).next fun formed written =>
    (bodyInfer (Definitions.bodyMode written.sort) formed body).next fun inferred answer =>
      (requireTypes normal limit depth inferred answer.typeRoot annotation body).next fun checked pair =>
        ⟨checked,.ok (written.compared ++ (answer.compared ++ [pair]))⟩

theorem runWithModes_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (bodies : ∀ mode state root, state.steps ≤ limit → Progress limit state (bodyInfer mode state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithModes infer bodyInfer normal limit depth state annotation body) := by
  unfold runWithModes
  apply next_progress (NativeCoreGhostDeclarationAnnotations.run_progress infers normalizes room) room
  intro _ _ annotationRoom
  apply next_progress (bodies _ _ _ annotationRoom) annotationRoom
  intro _ _ bodyRoom
  exact (requireTypes_progress (fun after root _ => normalizes after root) bodyRoom).next
    (fun _ => Progress.atState _ _)

/-- Formation and both body modes check the original roots. Any accepted
identity comparison converts the inferred body to the original annotation. -/
theorem runWithModes_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base [] limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (bodySound : BodySound env base limit bodyInfer)
    (bodyProgress : ∀ mode state root, state.steps ≤ limit → Progress limit state (bodyInfer mode state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena annotation type) (source : Represents state.arena body term)
    (success : (runWithModes infer bodyInfer normal limit depth state annotation body).result = .ok compared)
    (ambient : Prefix (runWithModes infer bodyInfer normal limit depth state annotation body).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (runWithModes infer bodyInfer normal limit depth state annotation body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ selected, (NativeCoreGhostDeclarationAnnotations.run infer normal state annotation).result = .ok selected ∧
        LoanTyping.HasType env [] [] true (expand env type) selected.sort.term ∧
        LoanTyping.HasType env [] [] (Definitions.bodyMode selected.sort) (expand env term) (expand env type) := by
  unfold runWithModes at success ambient ⊢
  obtain ⟨formed,formedOk,formedNext⟩ := Outcome.next_success success
  rw [formedNext] at success ambient ⊢
  obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨pair,pairOk,pairNext⟩ := Outcome.next_success success
  rw [pairNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst compared
  let formedType := NativeCoreGhostDeclarationAnnotations.run infer normal state annotation
  let mode := Definitions.bodyMode formed.sort
  let bodyType := bodyInfer mode formedType.state body
  have formation := NativeCoreGhostDeclarationAnnotations.run_progress (state := state) (typeRoot := annotation)
    inferProgress normalProgress room
  have formedRoom := formation.accepted room formed formedOk
  have bodyCost := bodyProgress mode formedType.state body formedRoom
  have bodyRoom := bodyCost.accepted formedRoom inferred inferredOk
  have comparedProgress := requireTypes_progress (state := bodyType.state) (depth := depth)
    (actual := inferred.typeRoot) (expected := annotation) (argument := body)
    (fun after root _ => normalProgress after root) bodyRoom
  have bodyFinal := comparedProgress.kept.trans ambient
  obtain ⟨formedKept,formedBack,validType⟩ := NativeCoreGhostDeclarationAnnotations.run_refines
    normalSound normalProgress inferSound onBase room written formedOk (bodyCost.kept.trans bodyFinal)
    (fun entry member => retained entry (List.mem_append_left _ member))
  obtain ⟨bodyKept,bodyBack,_,typeRep,typed⟩ := bodySound mode (onBase.trans formedKept) formedRoom
    (source.frame formedKept) inferredOk bodyFinal
    (fun entry member => retained entry (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughBody := formedKept.trans bodyKept
  obtain ⟨comparedKept,comparedBack,compatible⟩ := requireTypes_refines normalSound (onBase.trans throughBody)
    typeRep (written.frame throughBody) pairOk ambient (retained pair (by simp))
  exact ⟨throughBody.trans comparedKept,comparedBack ∘ bodyBack ∘ formedBack,formed,formedOk,validType,typed.convert compatible⟩

private def ghostOnly (infer : Infer) : Bool → Infer
  | true => infer
  | false => fun state body => ⟨state,.error (.outsideFragment body)⟩

def run (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (annotation body : Nat) : Outcome (List (Nat × Nat)) :=
  runWithModes infer (ghostOnly infer) normal limit depth state annotation body

private theorem ghostOnly_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root)) :
    ∀ mode state root, state.steps ≤ limit → Progress limit state (ghostOnly infer mode state root) := by
  intro mode state root room
  cases mode
  · exact Progress.atState _ _
  · exact infers _ _ room

private theorem ghostOnly_sound (sound : InferSound env base [] limit infer) :
    BodySound env base limit (ghostOnly infer) := by
  intro mode state root term answer final onBase room represented success ambient retained
  cases mode
  · cases success
  · obtain ⟨kept,backward,typed⟩ := sound onBase room represented success ambient retained
    exact ⟨kept,backward,typed⟩

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth state annotation body) :=
  runWithModes_progress infers (ghostOnly_progress infers) normalizes room

private theorem ghostOnly_sort (success : (run infer normal limit depth state annotation body).result = .ok compared) :
    ∃ written, (NativeCoreGhostDeclarationAnnotations.run infer normal state annotation).result = .ok written ∧
      written.sort = .prop := by
  unfold run runWithModes at success
  obtain ⟨written,accepted,next⟩ := Outcome.next_success success
  rw [next] at success
  refine ⟨written,accepted,?_⟩
  cases sort : written.sort
  · rfl
  · simp [sort,Definitions.bodyMode,ghostOnly,Outcome.next] at success

/-- The ghost-only entry retains the more specific evidence typing theorem. -/
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
  obtain ⟨checked,accepted,proposition⟩ := ghostOnly_sort success
  obtain ⟨kept,backward,selected,selectedOk,formed,typed⟩ := runWithModes_refines normalSound normalProgress inferSound
    inferProgress (ghostOnly_sound inferSound) (ghostOnly_progress inferProgress) onBase room written source success ambient retained
  have same : selected = checked := Except.ok.inj (selectedOk.symm.trans accepted)
  subst selected
  rw [proposition] at formed typed
  exact ⟨kept,backward,formed,typed⟩

/-- Evidence continues using recursive ghost inference. Scalar code uses the
actual code-mode head checker, including rejection of erased local access. -/
def scalarBodies (ghost : Infer) (limit depth : Nat) : Bool → Infer
  | true => ghost
  | false => NativeCoreCodeHeadInference.run limit depth []

theorem scalarBodies_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root)) :
    ∀ mode state root, state.steps ≤ limit → Progress limit state (scalarBodies ghost limit depth mode state root) := by
  intro mode state root room
  cases mode
  · exact NativeCoreCodeHeadInference.run_progress
  · exact ghostProgress _ _ room

theorem scalarBodies_sound (wf : UnifiedProgram.EnvWellFormed env) (ghostSound : InferSound env base [] limit ghost) :
    BodySound env base limit (scalarBodies ghost limit depth) := by
  intro mode state root term answer final onBase room source success ambient retained
  cases mode
  · obtain ⟨kept,backward,typed⟩ := NativeCoreCodeHeadInference.run_sound wf .nil onBase room source success ambient retained
    exact ⟨kept,backward,typed⟩
  · obtain ⟨kept,backward,typed⟩ := ghostSound onBase room source success ambient retained
    exact ⟨kept,backward,typed⟩

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

private def wordSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1,2⟩]
  families := []
  arena := #[.node (.natural 0) [],.node .u64 [],.node (.natural 5) []]

/-- An ordinary word definition traverses both the ghost annotation and
code body on the same clock. Each starts from the originally written root. -/
theorem admitted_word_definition_uses_code_body :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot wordSnapshot) = true ∧
    (let limit := 6
     let infer := NativeCoreGhostSpineInference.run wordSnapshot.definitions 0 limit 128 []
     let normal := NativeCoreGhostLiteralAddition.run wordSnapshot.definitions 0 limit 128
     let checked := runWithModes infer (scalarBodies infer limit 128) normal limit 128 ⟨wordSnapshot.arena,0⟩ 1 2
     checked.state.steps = 6 ∧ checked.result.map List.length = .ok 1) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeCoreGhostDefinitionChecking
