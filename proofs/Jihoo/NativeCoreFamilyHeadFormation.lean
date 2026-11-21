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

end Jihoo.NativeKernel.NativeCoreFamilyHeadFormation
