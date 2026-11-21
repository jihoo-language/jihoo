import Jihoo.NativeCoreGhostFamilyEvidence

/-! Formation of an inferred type is transported by the actual ghost
normalization. A normalized family head then supplies the declared arity
and the word typing of every recovered index. -/
namespace Jihoo.NativeKernel.NativeCoreFamilyHeadFormation

open Environment NativeArena
open EnvironmentDelta (expand expandArgs)
open NativeCorePureComputationNormal (ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)

private def FamilyHead (env : Environment) (loans : Loans.Stack) (ctx : Context) : Term → Prop
  | .node (.ind family count) values =>
      ∃ entry, env.families[family]? = some entry ∧ count = entry.declaration.arity ∧
        values.length = count ∧ ∀ value ∈ values, LoanTyping.HasType env loans ctx true value .u64
  | _ => True

theorem typed_family_head
    (typed : LoanTyping.HasType env loans ctx mode (.node (.ind family count) values) type) :
    ∃ entry, env.families[family]? = some entry ∧ count = entry.declaration.arity ∧
      values.length = count ∧ ∀ value ∈ values, LoanTyping.HasType env loans ctx true value .u64 := by
  have anyHead {term} (typed : LoanTyping.HasType env loans ctx mode term type) : FamilyHead env loans ctx term := by
    apply LoanTyping.HasType.rec (t := typed)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun loans ctx _ term _ _ => FamilyHead env loans ctx term)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | assumption | skip
    case ind => exact ⟨_,by assumption,by assumption,by assumption,by assumption⟩
    case dataElim => split <;> trivial
  exact anyHead typed

/-- The arity premise of an elimination can be proved from independently
formed input when the checker actually normalizes it to a family head. -/
theorem normalized_family_head
    (formed : LoanTyping.HasType env [] ctx true (expand env original) type)
    (replayed : ExpandedNormalization env original (.node (.ind family count) values)) :
    ∃ entry, env.families[family]? = some entry ∧ count = entry.declaration.arity ∧
      values.length = count ∧ ∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64 := by
  have head : LoanTyping.HasType env [] ctx true (.node (.ind family count) (expandArgs env values)) type := by
    simpa only [expand] using replayed.preserves formed
  obtain ⟨entry,seen,arity,width,typed⟩ := typed_family_head head
  refine ⟨entry,seen,arity,by simpa only [EnvironmentDelta.expandArgs_map,List.length_map] using width,?_⟩
  intro term included
  apply typed
  rw [EnvironmentDelta.expandArgs_map]
  exact List.mem_map.mpr ⟨term,included,rfl⟩

theorem normal_visit_family_head
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (input : Represents state.arena root original)
    (formed : LoanTyping.HasType env [] ctx true (expand env original) type)
    (ran : (normal state root).result = .ok selected)
    (output : Represents (normal state root).state.arena selected (.node (.ind family count) values)) :
    ∃ entry, env.families[family]? = some entry ∧ count = entry.declaration.arity ∧
      values.length = count ∧ ∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64 := by
  obtain ⟨_,_,_,represented,replayed⟩ := normalSound onBase input ran
  rw [represented.unique output] at replayed
  exact normalized_family_head formed replayed

/-- The original subject visit plus its checked annotation formation supply
all family index premises for the actual observed elimination head. -/
theorem evidence_refines_formed
    (normalProgress : ∀ state root, NativeCorePureComputationNormal.Progress limit state (normal state root))
    (inferSound : NativeCoreGhostSpineInference.InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject X)
    (formation : ∀ {answer original}, (infer state subject).result = .ok answer →
      Represents (infer state subject).state.arena answer.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term)
    (success : (NativeCoreGhostFamilyEvidence.evidence infer normal state family subject).result = .ok (inferred,arity,indices))
    (ambient : Prefix (NativeCoreGhostFamilyEvidence.evidence infer normal state family subject).state.arena final)
    (retained : NativeCoreGhostSpineInference.RetainedComparisons final inferred) :
    let after := (NativeCoreGhostFamilyEvidence.evidence infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ entry values, env.families[family]? = some entry ∧ arity = entry.declaration.arity ∧
        RepresentsList after indices values ∧ values.length = arity ∧
        (∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64) ∧
        LoanTyping.HasType env [] ctx true (expand env X) (.node (.ind family arity) (expandArgs env values)) := by
  obtain ⟨kept,backward,_,values,inferredOk,originalRep,converted,represented,_,typed⟩ :=
    NativeCoreGhostFamilyEvidence.evidence_trace normalProgress inferSound normalSound onBase room subjectRep success ambient retained
  obtain ⟨_,formed⟩ := formation inferredOk originalRep
  obtain ⟨entry,found,arity,indicesWidth,typedIndices⟩ := normalized_family_head formed converted
  exact ⟨kept,backward,entry,values,found,arity,represented,indicesWidth,typedIndices,typed⟩

end Jihoo.NativeKernel.NativeCoreFamilyHeadFormation
