import Jihoo.NativeBindingMachineCanonicalHandoff

/-! Source-typed canonical variables drive real lookups in aliased runtime
code. Returned representations and numeric widths are derived; callers supply
no stored value, output typing or successful lookup. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- The actual saved continuation frame constructs readiness of its canonical
single-binder source code, even though the runtime retains two bindings. -/
theorem canonical_continuation_aligned (term : Term) (fuel : Nat) (code : Code)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack) :
    CodeAligned (canonicalContinuation code owner first body resultOrigin (.integer value)) := by
  have frames := (initial_run_aligned term fuel SizedBufferHeap.empty).2
  rw [stackShape] at frames
  have captured : CodeAligned code := frames.head
  exact SlotsAligned.retained .integer captured

/-- Canonical CODE typing and its constructed readiness select an actual
stored value through any composed, non-injective alias map. -/
theorem reachable_canonical_variable_kind (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index) :
    ∃ value, actual.values[index]? = some (some value) ∧ ValueKind env value type ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned value,(run fuel (initial term)).state.stack⟩,none) := by
  have sourceShape : source.term = .var (indices index) := by
    rw [← view.termEq,shape]
    simp only [Term.rename]
  obtain ⟨value,stored,kind⟩ := context.variable_kind history typed aligned sourceShape
  have actualStored := (view.values index).trans stored
  refine ⟨value,actualStored,kind,?_⟩
  simp only [step,action,evaluating,evaluateAction,shape,actualStored,Option.map_some,execute,Option.map_none]

theorem reachable_canonical_integer_variable (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings .i64)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index) :
    ∃ value, actual.values[index]? = some (some (.integer value)) ∧ meanings (indices index) = .integer value ∧
      ValueReduction.signed64 value ∧ LoanTyping.HasType env [] [] false (.integer value) .i64 ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.integer value),(run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨actualValue,stored,kind,next⟩ := reachable_canonical_variable_kind term fuel history evaluating view typed context aligned shape
  obtain ⟨value,rfl⟩ := kind.integer_shape history.wellFormed.admissible
  have sourceStored := (view.values index).symm.trans stored
  have meaning := context.scalars.2 (indices index) value sourceStored
  have sourceShape : source.term = .var (indices index) := by
    rw [← view.termEq,shape]
    simp only [Term.rename]
  have literalTyped : LoanTyping.HasType env [] [] true (.integer value) .i64 := by
    simpa only [sourceShape,Term.subst,meaning] using typed.closed history
  have bounded := literalTyped.integer_bound
  exact ⟨value,stored,meaning,bounded,.integer bounded.1 bounded.2,next⟩

theorem reachable_canonical_natural_variable (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings .u64)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (shape : actual.term = .var index) :
    ∃ value, actual.values[index]? = some (some (.natural value)) ∧ meanings (indices index) = .natural value ∧
      value < 2^64 ∧ LoanTyping.HasType env [] [] false (.natural value) .u64 ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned (.natural value),(run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨actualValue,stored,kind,next⟩ := reachable_canonical_variable_kind term fuel history evaluating view typed context aligned shape
  obtain ⟨value,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have sourceStored := (view.values index).symm.trans stored
  have meaning := context.scalars.1 (indices index) value sourceStored
  have sourceShape : source.term = .var (indices index) := by
    rw [← view.termEq,shape]
    simp only [Term.rename]
  have literalTyped : LoanTyping.HasType env [] [] true (.natural value) .u64 := by
    simpa only [sourceShape,Term.subst,meaning] using typed.closed history
  have bounded := literalTyped.natural_bound
  exact ⟨value,stored,meaning,bounded,.natural bounded,next⟩

end Jihoo.NativeKernel.Environment.BindingMachine
