import Jihoo.NativeCoreGhostSpineInference

/-! The first phase of Core.extend checks the original annotation and
uses its inferred sort to choose the body mode. The independently checked
mixed history determines the same mode after authentic global expansion. -/
namespace Jihoo.NativeKernel.NativeCoreGhostDeclarationAnnotations

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred InferSound PairRetained)
open EnvironmentDelta (expand)

structure Annotation where
  sort : SortTag
  compared : List (Nat × Nat)

def run (infer : Infer) (normal : Visit) (state : State) (typeRoot : Nat) : Outcome Annotation :=
  (infer state typeRoot).next fun inferred answer =>
    (NativeCoreGhostSort.sort normal inferred answer.typeRoot).next fun after sort =>
      ⟨after,.ok ⟨sort,answer.compared⟩⟩

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) : Progress limit state (run infer normal state typeRoot) :=
  (infers _ _ room).next (fun _ => (NativeCoreGhostSort.sort_progress normalizes).next (fun _ => Progress.atState _ _))

theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena typeRoot annotation)
    (success : (run infer normal state typeRoot).result = .ok answer)
    (ambient : Prefix (run infer normal state typeRoot).state.arena final)
    (retained : ∀ pair ∈ answer.compared, PairRetained final pair) :
    let after := (run infer normal state typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env annotation) answer.sort.term := by
  unfold run at success ambient ⊢
  obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨sort,sortOk,sortNext⟩ := Outcome.next_success success
  rw [sortNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have sorted := NativeCoreGhostSort.sort_progress (state := (infer state typeRoot).state)
    (typeRoot := inferred.typeRoot) normalProgress
  obtain ⟨kept,inferBack,_,inferredRep,typed⟩ := inferSound onBase room written inferredOk (sorted.kept.trans ambient) retained
  obtain ⟨sortKept,sortBack,converted⟩ := NativeCoreGhostSort.sort_refines normalSound (onBase.trans kept) inferredRep sortOk
  exact ⟨kept.trans sortKept,sortBack ∘ inferBack,typed.convert converted⟩

private theorem definition_at {index : Nat} {row : Roots} (aligned : RepresentsDefinitions arena refs definitions)
    (found : refs[index]? = some row) :
    ∃ source, definitions[index]? = some source ∧ RepresentsDefinition arena row source := by
  induction aligned generalizing index with
  | nil => cases found
  | cons first rest ih =>
    cases index with
    | zero =>
      cases found
      exact ⟨_,rfl,first⟩
    | succ index => exact ih found

private theorem declaration_expansion_at {index : Nat} {source : GlobalDeclaration}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (selected : definitions[index]? = some source) :
    ∃ checked, env.globals[index]? = some checked ∧ GlobalEnvironment.Expansion env.globals source.type checked.type ∧
      GlobalEnvironment.Expansion env.globals source.value checked.value := by
  induction history with
  | empty => cases selected
  | @definition definitions families env raw entry history checked ih =>
    by_cases earlier : index < definitions.length
    · rw [List.getElem?_append_left earlier] at selected
      obtain ⟨original,found,formed,body⟩ := ih selected
      have kept := (Environment.Extends.pushGlobal env entry).globals index original found
      exact ⟨original,kept,formed.extend entry,body.extend entry⟩
    · have inside := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_append,List.length_singleton] at inside
      have atEnd : index = definitions.length := by omega
      subst index
      have matched : raw = source := by simpa using selected
      subst source
      exact ⟨entry,by rw [← history.globalLength,Array.getElem?_push_size],
        checked.typeExpansion.extend entry,checked.valueExpansion.extend entry⟩
  | family _ _ ih => exact ih selected

private theorem sort_rigid {first second : SortTag} (wf : UnifiedProgram.EnvWellFormed env)
    (converted : RawLend.Conv env first.term second.term) : first = second := by
  cases first with
  | prop =>
    cases second with
    | prop => rfl
    | type level =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .prop) (op' := .universe level)
        rfl rfl (by intro impossible; cases impossible) converted wf.admissible)
  | type first =>
    cases second with
    | prop =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .universe first) (op' := .prop)
        rfl rfl (by intro impossible; cases impossible) converted wf.admissible)
    | type second =>
      have same : Op.universe first = Op.universe second :=
        (converted.full_rigid_node_injective rfl rfl wf.admissible).1
      exact congrArg SortTag.type (Op.universe.inj same)

/-- The graph's inferred annotation and sort determine the original
checked body's mode, at the exact declaration type and expanded body
root. No body inference result or externally recorded flag is required. -/
theorem checked_declaration_mode
    {index : Nat} {row : Roots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (rows : RepresentsDefinitions base roots definitions) (selected : roots[index]? = some row)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base [] limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (success : (run infer normal state row.typeRoot).result = .ok answer)
    (ambient : Prefix (run infer normal state row.typeRoot).state.arena final)
    (retained : ∀ pair ∈ answer.compared, PairRetained final pair) :
    ∃ source entry, env.globals[index]? = some entry ∧ RepresentsDefinition base row source ∧
      expand env source.type = entry.type ∧ expand env source.value = entry.value ∧
      LoanTyping.HasType env [] [] true entry.type answer.sort.term ∧
      LoanTyping.HasType env [] [] (Definitions.bodyMode answer.sort) entry.value entry.type := by
  obtain ⟨source,read,represented⟩ := definition_at rows selected
  obtain ⟨entry,found,annotation,body⟩ := declaration_expansion_at history read
  have originalType := EnvironmentDelta.expansion_eq_expand annotation
  have originalBody := EnvironmentDelta.expansion_eq_expand body
  obtain ⟨_,_,inferred⟩ := run_refines normalSound normalProgress inferSound onBase room (represented.1.frame onBase)
    success ambient retained
  rw [originalType] at inferred
  obtain ⟨sort,original,typed⟩ := history.global_typing found
  have agrees := sort_rigid history.wellFormed (inferred.unique history.wellFormed original)
  subst sort
  exact ⟨source,entry,found,represented,originalType,originalBody,inferred,typed⟩

private def annotatedSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1,2⟩,⟨3,4⟩]
  families := []
  arena := #[.node (.natural 0) [],.node .eq [0,0],.node .refl [0],.node .u64 [],.node (.natural 1) []]

private def annotationVisit (visible limit root : Nat) : Outcome Annotation :=
  run (NativeCoreGhostSpineInference.run annotatedSnapshot.definitions visible limit 128 [])
    (NativeCoreGhostLiteralAddition.run annotatedSnapshot.definitions visible limit 128)
    ⟨annotatedSnapshot.arena,0⟩ root

/-- The exact declaration annotation selects ghost mode only for the
proposition. The data annotation selects checked code mode. -/
theorem admitted_annotations_select_body_mode :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot annotatedSnapshot) = true ∧
    (let evidence := annotationVisit 0 10 1
     evidence.state.steps = 10 ∧ evidence.result.map Annotation.sort = .ok .prop) ∧
    (let word := annotationVisit 1 2 3
     word.state.steps = 2 ∧ word.result.map Annotation.sort = .ok (.type 0)) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeCoreGhostDeclarationAnnotations
