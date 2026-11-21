import Jihoo.NativeArena
import Jihoo.NativeTyping

/-! Each codomain in a represented product telescope denotes a strictly
smaller term. A represented product spine therefore uses distinct rows. -/
namespace Jihoo.NativeKernel.NativeCoreProductSpine

open NativeArena

def spineLength : Term → Nat
  | .pi _ _ body => spineLength body+1
  | _ => 1

private def PathRep (arena : Arena) (term : Term) (refs : List Nat) : Prop :=
  refs.length = spineLength term ∧ refs.Nodup ∧
    ∀ root ∈ refs, ∃ represented, Represents arena root represented ∧ sizeOf represented ≤ sizeOf term

private theorem one_row (source : Represents arena root term) (one : spineLength term = 1) :
    PathRep arena term [root] := by
  refine ⟨one.symm,by simp,?_⟩
  intro selected member
  have same := List.mem_singleton.mp member
  subst selected
  exact ⟨term,source,Nat.le_refl _⟩

private theorem body_smaller (erased : Bool) (domain body : Term) :
    sizeOf body < sizeOf (Term.pi erased domain body) := by
  simp [Term.pi]
  omega

private theorem add_row (source : Represents arena root (.pi erased domain body))
    (tail : PathRep arena body refs) :
    PathRep arena (.pi erased domain body) (root :: refs) := by
  obtain ⟨size,distinct,members⟩ := tail
  have smaller := body_smaller erased domain body
  have fresh : root ∉ refs := by
    intro duplicate
    obtain ⟨other,represented,bounded⟩ := members root duplicate
    have same := represented.unique source
    rw [same] at bounded
    omega
  refine ⟨congrArg Nat.succ size,List.nodup_cons.mpr ⟨fresh,distinct⟩,?_⟩
  intro selected found
  rcases List.mem_cons.mp found with rfl | tail
  · exact ⟨_,source,Nat.le_refl _⟩
  · obtain ⟨term,represented,smallerThanBody⟩ := members selected tail
    exact ⟨term,represented,by omega⟩

private theorem path (source : Represents arena root term) : ∃ refs, PathRep arena term refs := by
  cases source with
  | var read => exact ⟨_,one_row (.var read) rfl⟩
  | @node root op refs terms read width children =>
    cases op
    case pi erased =>
      have size : refs.length = 2 := width
      rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at size
      cases children with
      | cons first tail =>
        cases tail with
        | cons body rest =>
          cases rest
          obtain ⟨refs,replayed⟩ := path body
          exact ⟨_,add_row (.node read width (.cons first (.cons body .nil))) replayed⟩
    all_goals exact ⟨_,one_row (.node read width children) rfl⟩
termination_by sizeOf term
decreasing_by
  subst_vars
  exact body_smaller _ _ _

private theorem source_inside (source : Represents arena root term) : root < arena.size := by
  cases source with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1

theorem spineLength_le_arena (source : Represents arena root term) : spineLength term ≤ arena.size := by
  obtain ⟨refs,length,distinct,members⟩ := path source
  have subset : refs ⊆ List.range arena.size := by
    intro ref member
    obtain ⟨_,represented,_⟩ := members ref member
    exact List.mem_range.mpr (source_inside represented)
  rw [←length,←List.length_range (n := arena.size)]
  exact distinct.length_le_of_subset subset

theorem folded_spineLength (fields : List α) (erased : α → Bool) (domain : α → Term) (result : Term) :
    spineLength (fields.foldr (fun field rest => .pi (erased field) (domain field) rest) result) =
      spineLength result + fields.length := by
  induction fields with
  | nil => rfl
  | cons field tail ih => simp only [List.foldr_cons,spineLength,ih,List.length_cons]; omega

end Jihoo.NativeKernel.NativeCoreProductSpine
