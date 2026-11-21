import Jihoo.NativeCoreGhostTypeRequirement

/-! Family elimination reads its parameters and indices from the type
exposed by the original scrutinee inference. -/
namespace Jihoo.NativeKernel.NativeCoreGhostFamilyEvidence

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred InferSound RetainedComparisons next_progress)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def inspect (state : State) (selected family subject : Nat) : Outcome (Nat × List Nat) :=
  match state.arena[selected]? with
  | some (.node (.ind actual arity) indices) =>
    if actual = family then ⟨state,.ok (arity,indices)⟩ else reject state subject
  | _ => reject state subject

def evidence (infer : Infer) (normal : Visit) (state : State) (family subject : Nat) :
    Outcome (Inferred × (Nat × List Nat)) :=
  (infer state subject).next fun inferred answer =>
    (normal inferred answer.typeRoot).next fun after selected =>
      (inspect after selected family subject).next fun checked result => ⟨checked,.ok (answer,result)⟩

theorem evidence_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) : Progress limit state (evidence infer normal state family subject) := by
  unfold evidence
  apply next_progress (childProgress _ _ room) room
  intro _ _ inferredRoom
  exact (normalProgress _ _).next fun _ =>
    by
      unfold inspect
      split
      · split <;> exact Progress.atState _ _
      · exact Progress.atState _ _

private theorem inspect_refines (held : Represents state.arena selected type)
    (success : (inspect state selected family subject).result = .ok (arity,indices)) :
    ∃ values, type = .node (.ind family arity) values ∧ RepresentsList state.arena indices values ∧ indices.length = arity := by
  unfold inspect at success
  split at success
  · rename_i observed count refs read
    split at success
    · rename_i same
      subst observed
      simp only [Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      cases held with
      | var found => rw [read] at found; cases found
      | node found width children => rw [read] at found; cases found; exact ⟨_,rfl,children,width⟩
    · cases success
  · cases success

theorem evidence_trace
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject X)
    (success : (evidence infer normal state family subject).result = .ok (inferred,arity,indices))
    (ambient : Prefix (evidence infer normal state family subject).state.arena final)
    (retained : RetainedComparisons final inferred) :
    let after := (evidence infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ original values, (infer state subject).result = .ok inferred ∧
        Represents (infer state subject).state.arena inferred.typeRoot original ∧
        ExpandedNormalization env original (.node (.ind family arity) values) ∧
        RepresentsList after indices values ∧ indices.length = arity ∧
        LoanTyping.HasType env [] ctx true (expand env X) (.node (.ind family arity) (expandArgs env values)) := by
  unfold evidence at success ambient ⊢
  obtain ⟨answer,answerOk,answerNext⟩ := Outcome.next_success success
  rw [answerNext] at success ambient ⊢
  obtain ⟨selected,selectedOk,selectedNext⟩ := Outcome.next_success success
  rw [selectedNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq,Prod.mk.injEq] at success
  obtain ⟨rfl,rfl⟩ := success
  have plain : (inspect (normal (infer state subject).state answer.typeRoot).state selected family subject).state =
      (normal (infer state subject).state answer.typeRoot).state := by
    unfold inspect
    split
    · split <;> rfl
    · rfl
  rw [plain] at ambient ⊢
  have normalization := normalProgress (infer state subject).state answer.typeRoot
  obtain ⟨inferredKept,inferredBack,type,typeRep,typed⟩ := inferSound onBase room subjectRep answerOk
    (normalization.kept.trans ambient) retained
  obtain ⟨normalKept,normalBack,residual,residualRep,converted⟩ := normalSound
    (onBase.trans inferredKept) typeRep selectedOk
  obtain ⟨values,shape,valuesRep,width⟩ := inspect_refines residualRep resultOk
  rw [shape] at converted
  exact ⟨inferredKept.trans normalKept,normalBack ∘ inferredBack,type,values,answerOk,typeRep,
    converted,valuesRep,width,typed.convert (by simpa only [expand] using converted.converted)⟩

theorem evidence_refines
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject X)
    (success : (evidence infer normal state family subject).result = .ok (inferred,arity,indices))
    (ambient : Prefix (evidence infer normal state family subject).state.arena final)
    (retained : RetainedComparisons final inferred) :
    let after := (evidence infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ values, RepresentsList after indices values ∧ indices.length = arity ∧
        LoanTyping.HasType env [] ctx true (expand env X) (.node (.ind family arity) (expandArgs env values)) := by
  obtain ⟨kept,backward,_,values,_,_,_,represented,width,typed⟩ :=
    evidence_trace normalProgress inferSound normalSound onBase room subjectRep success ambient retained
  exact ⟨kept,backward,values,represented,width,typed⟩

theorem expand_spine (env : Environment) (motive : Term) (indices : List Term) :
    expand env (applications motive indices) = applications (expand env motive) (expandArgs env indices) := by
  induction indices generalizing motive with
  | nil => simp only [applications,List.foldl_nil,expandArgs]
  | cons index indices ih =>
    change expand env (applications (.app motive index) indices) = _
    rw [ih]
    simp only [applications,List.foldl_cons,Term.app,expand,expandArgs]

end Jihoo.NativeKernel.NativeCoreGhostFamilyEvidence
