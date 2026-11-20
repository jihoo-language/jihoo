import Jihoo.NativeLoanComputationPreservation

/-! Bounded observation of computed U64 comparisons in ghost proofs. The
true arms use evidence at the original operands of the checked comparison. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofComparison

inductive Step (env : Environment) : Term → Term → Prop where
  | ltTrue {left right : Fin (2^64)} :
      RawLend.Conv env a (.natural left.val) → RawLend.Conv env b (.natural right.val) → left.val < right.val →
      Step env (.ifLt a b yes no) (yes.subst (single (.decide a b)))
  | ltFalse {left right : Fin (2^64)} :
      RawLend.Conv env a (.natural left.val) → RawLend.Conv env b (.natural right.val) → ¬ left.val < right.val →
      Step env (.ifLt a b yes no) no
  | eqTrue {left right : Fin (2^64)} :
      RawLend.Conv env a (.natural left.val) → RawLend.Conv env b (.natural right.val) → left.val = right.val →
      Step env (.ifEq a b yes no) (yes.subst (single (.refl a)))
  | eqFalse {left right : Fin (2^64)} :
      RawLend.Conv env a (.natural left.val) → RawLend.Conv env b (.natural right.val) → left.val ≠ right.val →
      Step env (.ifEq a b yes no) no

theorem Step.preserves (step : Step env term result) (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) : HasType env [] ctx true result type := by
  cases step with
  | ltTrue left right ordered => exact computed_ifLt_true_preserves wf typed left right (Fin.isLt _) (Fin.isLt _) ordered
  | eqTrue left right same =>
      rw [← same] at right
      exact computed_ifEq_true_preserves wf typed left right
  | ltFalse | eqFalse =>
      obtain ⟨_, noTyped, converted⟩ := typed.principalView
      exact (noTyped.ghost []).convert converted

private def numeral? (env : Environment) (budget fuel : Nat) (operand : Term) : Option (Fin (2^64)) := do
  let .natural value ← RawLend.normalize? env budget fuel operand | none
  if inRange : value < 2^64 then some ⟨value, inRange⟩ else none

private theorem numeral?_sound (checked : numeral? env budget fuel operand = some result) :
    RawLend.Conv env operand (.natural result.val) := by
  unfold numeral? at checked
  obtain ⟨normalized, ran, checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · split at checked
    · cases checked
      exact RawLend.normalize?_sound ran
    · contradiction
  · contradiction

/-- A bounded run branches only once both conditions are observed to be real
U64 numerals. The actual true branch introduces its source evidence binder. -/
def select? (env : Environment) (budget fuel : Nat) : Term → Option Term
  | .ifLt a b yes no => do
      let left ← numeral? env budget fuel a
      let right ← numeral? env budget fuel b
      pure (if left.val < right.val then yes.subst (single (.decide a b)) else no)
  | .ifEq a b yes no => do
      let left ← numeral? env budget fuel a
      let right ← numeral? env budget fuel b
      pure (if left.val = right.val then yes.subst (single (.refl a)) else no)
  | _ => none

theorem select?_sound (selected : select? env budget fuel term = some result) : Step env term result := by
  fun_cases select? env budget fuel term <;> simp only [select?] at selected
  · obtain ⟨left, leftChecked, selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨right, rightChecked, selected⟩ := Option.bind_eq_some_iff.mp selected
    simp only [pure, Option.some.injEq] at selected
    split at selected
    · rename_i ordered
      subst result
      exact .ltTrue (numeral?_sound leftChecked) (numeral?_sound rightChecked) ordered
    · rename_i unordered
      subst result
      exact .ltFalse (numeral?_sound leftChecked) (numeral?_sound rightChecked) unordered
  · obtain ⟨left, leftChecked, selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨right, rightChecked, selected⟩ := Option.bind_eq_some_iff.mp selected
    simp only [pure, Option.some.injEq] at selected
    split at selected
    · rename_i same
      subst result
      exact .eqTrue (numeral?_sound leftChecked) (numeral?_sound rightChecked) same
    · rename_i different
      subst result
      exact .eqFalse (numeral?_sound leftChecked) (numeral?_sound rightChecked) different
  · contradiction

end Jihoo.NativeKernel.Environment.LoanTyping.ProofComparison
