import Jihoo.NativeBindingMachineCanonicalFrameHandoff

/-! Canonical source code contains only captures retained by the actual code.
The ordered sublist includes every source occurrence and erased None slot;
it does not assume injective alias maps or equate source/runtime reader names.
This supplements CanonicalView without changing its existing interfaces.
Construction at every source/control transition remains a separate obligation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- Recursive token provenance survives deletion of retained or erased slots.
No new source value or source reference bound is supplied. -/
theorem ValuesReferences.sublist (ready : ValuesReferences limit values)
    (selected : sourceValues.Sublist values) : ValuesReferences limit sourceValues := by
  induction selected with
  | slnil => exact .nil
  | cons first previous ih =>
      cases ready with
      | erased before => exact ih before
      | retained kept before => exact ih before
  | cons_cons first previous ih =>
      cases ready with
      | erased before => exact .erased (ih before)
      | retained kept before => exact .retained kept (ih before)

structure CapturedCanonicalView (actual source : Code) (indices : Nat → Nat) : Prop where
  view : CanonicalView actual source indices
  captures : source.values.Sublist actual.values

/-- A plain view can hide an unused source reference outside the index map's
image. Its valid term/origin/slot equations therefore do not transport every
source capture bound. This is a bookkeeping boundary, not an execution fault. -/
theorem CanonicalView.reference_bounds_not_implied :
    ¬ (∀ (actual source : Code) (indices : Nat → Nat) (limit : Nat),
      CanonicalView actual source indices → CodeReferences limit actual → CodeReferences limit source) := by
  intro assumed
  let actual := Code.initial (.integer 0)
  let source := BindingMachine.enter false (.ref (.buffer (.natural 1))) (.integer 0) [] Term.var []
    (.borrow (.alloc (.natural 1) (.integer 7))) (some (.reference 0))
  have view : CanonicalView actual source Nat.succ := by
    refine ⟨?_,fun _ => rfl,?_⟩
    · simp only [actual,source,Code.initial,BindingMachine.enter,Term.rename,renameArgs]
    · intro index
      simp only [actual,source,Code.initial,BindingMachine.enter,List.getElem?_nil,List.getElem?_cons_succ]
  have sourceReady := assumed actual source Nat.succ 0 view ValuesReferences.nil
  have referenceReady : ValueReferences 0 (.reference 0) :=
    ValuesReferences.valueAt (index := 0) sourceReady rfl
  have impossible := referenceReady.referenceBound
  omega

theorem CapturedCanonicalView.identity (code : Code) : CapturedCanonicalView code code id :=
  ⟨CanonicalView.identity code,List.Sublist.refl code.values⟩

theorem CapturedCanonicalView.child (captured : CapturedCanonicalView actual source indices)
    (term : Term) :
    CapturedCanonicalView (actual.child term) (source.child (term.rename indices)) indices :=
  ⟨captured.view.child term,captured.captures⟩

/-- Arbitrary previous alias layers compose without discarding the evidence
that all source capture occurrences are retained in the actual snapshot. -/
theorem CapturedCanonicalView.compose
    (first : CapturedCanonicalView actual middle indices)
    (second : CapturedCanonicalView middle source next) :
    CapturedCanonicalView actual source (next ∘ indices) :=
  ⟨first.view.compose second.view,second.captures.trans first.captures⟩

theorem CapturedCanonicalView.enter (captured : CapturedCanonicalView actual source indices)
    (erased : Bool) (domain body origin : Term) (argument : Option Value) :
    CapturedCanonicalView
      (enter erased domain body actual.context actual.origins actual.values origin argument)
      (enter erased (domain.rename indices) (body.rename (liftRenaming 1 indices))
        source.context source.origins source.values origin argument) (liftRenaming 1 indices) :=
  ⟨captured.view.enter erased domain body origin argument,captured.captures.cons_cons argument⟩

/-- Actual capture bounds imply source capture bounds, including references
inside recursively captured closures. Phantom source slots are excluded by
the sublist component rather than by a separately supplied source oracle. -/
theorem CapturedCanonicalView.references (captured : CapturedCanonicalView actual source indices)
    (ready : CodeReferences limit actual) : CodeReferences limit source :=
  ValuesReferences.sublist ready captured.captures

/-- The first canonical owner restoration keeps result/old-capture slots as
an ordered sublist of the actual owner/result/old-capture slots. -/
theorem restored_captured_canonical_view (code : Code)
    (stored : code.values[owner]? = some (some (.owner object)))
    (first again body resultOrigin : Term) (value : Value) :
    CapturedCanonicalView
      (restoredContinuation code first again body ((Term.var owner).subst code.origins) resultOrigin object value)
      (canonicalContinuation code owner first body resultOrigin value) (Jihoo.Quantity.openOwner (owner+1)) := by
  refine ⟨restored_canonical_view code stored first again body resultOrigin value,?_⟩
  simp only [canonicalContinuation,restoredContinuation,BindingMachine.enter]
  exact (List.Sublist.refl (some value :: code.values)).cons (some (.owner object))

/-- Restoring another owner preserves all earlier source capture occurrences,
even when both alias layers identify several actual runtime slots. -/
theorem CapturedCanonicalView.restored
    (captured : CapturedCanonicalView actualOriginal original originalIndices)
    (stored : actualOriginal.values[owner]? = some (some (.owner object)))
    (first again body resultOrigin : Term) (value : Value) :
    CapturedCanonicalView
      (restoredContinuation actualOriginal first again body
        ((Term.var owner).subst actualOriginal.origins) resultOrigin object value)
      (canonicalContinuation original (originalIndices owner) (first.rename originalIndices)
        (body.rename (liftRenaming 2 originalIndices)) resultOrigin value)
      (Jihoo.Quantity.openOwner (originalIndices owner+1) ∘ liftRenaming 2 originalIndices) := by
  refine ⟨restored_composed_canonical_view captured.view stored first again body resultOrigin value,?_⟩
  simp only [canonicalContinuation,restoredContinuation,BindingMachine.enter]
  exact (captured.captures.cons_cons (some value)).cons (some (.owner object))

/-- An actual saved reader-continuation snapshot bounds every canonical
source capture. The source code may have a different body and fewer slots;
all source reference bounds come from the real execution prefix. -/
theorem CapturedCanonicalView.initial_finish_snapshot (term : Term) (fuel : Nat)
    (captured : CapturedCanonicalView actual source indices)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin (actual.child continuation) :: stack) :
    CodeReferences token source ∧ StackReferences token stack := by
  obtain ⟨actualReady,outerReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  exact ⟨captured.references actualReady,outerReady⟩

/-- A closing reader token occurs in neither the canonical source captures
nor the outer actual frames. No source no-token premise is needed. -/
theorem CapturedCanonicalView.initial_finish_absent (term : Term) (fuel : Nat)
    (captured : CapturedCanonicalView actual source indices)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin (actual.child continuation) :: stack) :
    ¬ CodeReferenceOccurs token source ∧
      ∀ frame ∈ stack, ¬ FrameReferenceOccurs token frame := by
  obtain ⟨sourceReady,outerReady⟩ := captured.initial_finish_snapshot term fuel stackShape
  exact ⟨sourceReady.fresh_absent,by intro frame member; exact outerReady.fresh_absent member⟩

end Jihoo.NativeKernel.Environment.BindingMachine
