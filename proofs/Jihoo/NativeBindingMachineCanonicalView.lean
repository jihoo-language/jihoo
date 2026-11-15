import Jihoo.NativeBindingMachineLoanCoverage

/-! A canonical resource view identifies retained runtime aliases with the
original checker's source slots. The map need not be injective. Origins remain
literal provenance; no effectful origin is converted to an observed value. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

structure CanonicalView (actual source : Code) (indices : Nat → Nat) : Prop where
  termEq : actual.term.rename indices = source.term
  origins : ∀ index, actual.origins index = source.origins (indices index)
  values : ∀ index, actual.values[index]? = source.values[indices index]?

theorem CanonicalView.identity (code : Code) : CanonicalView code code id := by
  exact ⟨Term.rename_id _,fun _ => rfl,fun _ => rfl⟩

theorem CanonicalView.child (view : CanonicalView actual source indices) (term : Term) :
    CanonicalView (actual.child term) (source.child (term.rename indices)) indices :=
  ⟨rfl,view.origins,view.values⟩

/-- Previously normalized alias layers compose without a distinct-slots
premise or a new source check. -/
theorem CanonicalView.compose (first : CanonicalView actual middle indices)
    (second : CanonicalView middle source next) : CanonicalView actual source (next ∘ indices) := by
  refine ⟨?_,fun index => (first.origins index).trans (second.origins (indices index)),
    fun index => (first.values index).trans (second.values (indices index))⟩
  change actual.term.rename (fun index => next (indices index)) = source.term
  rw [← Term.rename_comp actual.term indices next,first.termEq,second.termEq]

theorem CanonicalView.closed (view : CanonicalView actual source indices)
    (related : ∀ index, actualMeanings index = sourceMeanings (indices index)) :
    actual.term.subst actualMeanings = source.term.subst sourceMeanings := by
  rw [← view.termEq,Term.subst_rename]
  exact congrArg (fun meanings => actual.term.subst meanings) (funext related)

theorem CanonicalView.origin (view : CanonicalView actual source indices) : actual.origin = source.origin :=
  view.closed view.origins

/-- The actual and canonical binders retain the same observed argument,
while every old alias index is lifted under that binder. -/
theorem CanonicalView.enter (view : CanonicalView actual source indices)
    (erased : Bool) (domain body origin : Term) (argument : Option Value) :
    CanonicalView
      (enter erased domain body actual.context actual.origins actual.values origin argument)
      (enter erased (domain.rename indices) (body.rename (liftRenaming 1 indices))
        source.context source.origins source.values origin argument) (liftRenaming 1 indices) := by
  refine ⟨rfl,?_,?_⟩
  · intro index
    cases index with
    | zero => rfl
    | succ index => exact view.origins index
  · intro index
    cases index with
    | zero => rfl
    | succ index => exact view.values index

def canonicalContinuation (code : Code) (owner : Nat) (first body resultOrigin : Term) (result : Value) : Code :=
  enter false first (body.rename (Jihoo.Quantity.openOwner (owner+1))) code.context code.origins code.values resultOrigin (some result)

/-- Both real owner slots have exactly the canonical source slot's value and
origin. This constructs the alias map from the actual retained bindings. -/
theorem restored_canonical_view (code : Code)
    (stored : code.values[owner]? = some (some (.owner object)))
    (first again body resultOrigin : Term) (result : Value) :
    CanonicalView
      (restoredContinuation code first again body ((Term.var owner).subst code.origins) resultOrigin object result)
      (canonicalContinuation code owner first body resultOrigin result) (Jihoo.Quantity.openOwner (owner+1)) := by
  refine ⟨rfl,?_,?_⟩
  · intro index
    cases index with
    | zero => simp only [restoredContinuation,canonicalContinuation,enter,consValues,Term.subst,Jihoo.Quantity.openOwner]
    | succ index => rfl
  · exact restored_continuation_slots code stored first again body resultOrigin result

/-- Canonical source Free authority controls its actual alias, without
requiring every duplicated runtime slot to have a separate source loan. -/
theorem reachable_canonical_free_guard (term : Term) (fuel : Nat)
    (view : CanonicalView actual source indices)
    (shape : actual.term = .free (.var owner) tail)
    (stored : actual.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context source.term = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans control)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.stack) :
    freeGuard (run fuel (initial term)).state.heap object = true := by
  have sourceShape : source.term = .free (.var (indices owner)) (tail.rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  have sourceStored : source.values[indices owner]? = some (some (.owner object)) := (view.values owner).symm.trans stored
  rw [sourceShape] at checked
  exact reachable_covered_free_guard term fuel source coverage sourceStored checked budget

end Jihoo.NativeKernel.Environment.BindingMachine
