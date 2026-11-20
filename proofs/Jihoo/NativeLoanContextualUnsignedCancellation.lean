import Jihoo.NativeLoanOpenProofNormalization
import Jihoo.NativeBindingMachineMutableUnsignedSubtraction

/-! Typed contextual cancellation for the affine U64 expression fragment.
The erased evidence may use earlier arithmetic hypotheses. The extension
leaves general Loan64 conversion and dependent type formation intact. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ContextualUnsignedCancellation

open AffineSum (Expr)
open PureHypothesisObservation (Entry ScalarSlot ScalarExpr context)
open OpenProofNormalization (Tree typed_affine_inequality)
open WideHypothesisObservation (Satisfies closing)

inductive Expression where
  | affine (value : Expr)
  | subtract (left right : Expr) (evidence : Term)
  | add (left right : Expression)

def Expression.term : Expression → Term
  | .affine value => value.toTerm
  | .subtract left right evidence => .usub left.toTerm right.toTerm evidence
  | .add left right => .uadd left.term right.term

def Expression.eval (words : Nat → Nat) : Expression → Nat
  | .affine value => value.eval words
  | .subtract left right _ => left.eval words - right.eval words
  | .add left right => left.eval words + right.eval words

/-- The existing raw contraction needs one bounded literal numerator per
subtraction. Additions surrounding those subtractions are ghost sums. -/
def Expression.boundedSubtractions (words : Nat → Nat) : Expression → Prop
  | .affine _ => True
  | .subtract left _ _ => left.eval words < 2^64
  | .add left right => left.boundedSubtractions words ∧ right.boundedSubtractions words

/-- Cancellation can occur in either operand of an unsigned sum. The
evidence grammar is the checked open arithmetic fragment. -/
inductive Rewrite (entries : List Entry) : Expression → Expression → Prop where
  | refl (source : Expression) : Rewrite entries source source
  | trans : Rewrite entries source middle → Rewrite entries middle result → Rewrite entries source result
  | cancel : ScalarExpr entries left → ScalarExpr entries right → Tree entries evidence →
      Rewrite entries (.add (.subtract left right evidence) (.affine right)) (.affine left)
  | addLeft : Rewrite entries source result → Rewrite entries (.add source other) (.add result other)
  | addRight : Rewrite entries source result → Rewrite entries (.add other source) (.add other result)

structure CheckedForward (env : Environment) (entries : List Entry)
    (source result : Expression) (type : Term) : Prop where
  formed : ResourceModes.ContextFormed env [] (context entries)
  sourceTyped : HasType env [] (context entries) true source.term type
  rewrite : Rewrite entries source result

private theorem rewrite_preserves_type (step : Rewrite entries source result)
    (typed : HasType env [] (context entries) true source.term type) :
    HasType env [] (context entries) true result.term type := by
  induction step generalizing type with
  | refl => exact typed
  | trans _ _ first second => exact second (first typed)
  | cancel =>
      obtain ⟨subtraction, _, converted⟩ := typed.uadd_inputs
      exact subtraction.usub_inputs.1.convert converted
  | addLeft _ ih =>
      obtain ⟨first, second, converted⟩ := typed.uadd_inputs
      exact (HasType.uadd (ih first) second).convert converted
  | addRight _ ih =>
      obtain ⟨first, second, converted⟩ := typed.uadd_inputs
      exact (HasType.uadd first (ih second)).convert converted

/-- The target has the exact requested type, using the same source
context and conversion of its principal U64 result. -/
theorem CheckedForward.preserves (step : CheckedForward env entries source result type) :
    HasType env [] (context entries) true result.term type :=
  rewrite_preserves_type step.rewrite step.sourceTyped

theorem CheckedForward.then (first : CheckedForward env entries source middle type)
    (second : CheckedForward env entries middle result type) :
    CheckedForward env entries source result type :=
  ⟨first.formed, first.sourceTyped, .trans first.rewrite second.rewrite⟩

theorem CheckedForward.ofChecker
    (formed : ResourceModes.contextOK fuel env [] (context entries) = true)
    (accepted : Checker.check fuel env [] (context entries) true source.term type = true)
    (step : Rewrite entries source result) : CheckedForward env entries source result type :=
  ⟨ResourceModes.contextOK_sound formed, Checker.check_sound accepted, step⟩

private theorem cancellation_guard (wellFormed : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words)
    (leftValid : ScalarExpr entries left) (rightValid : ScalarExpr entries right)
    (tree : Tree entries evidence)
    (typed : HasType env [] (context entries) true (.usub left.toTerm right.toTerm evidence) type) :
    right.eval words ≤ left.eval words := by
  have bound := typed_affine_inequality wellFormed valuation tree rightValid
    (.add leftValid (.literal (by decide))) (.native typed.usub_inputs.2.2)
  change right.eval words < left.eval words + 1 at bound
  omega

private theorem rewrite_preserves_eval (wellFormed : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (step : Rewrite entries source result)
    (typed : HasType env [] (context entries) true source.term type) :
    source.eval words = result.eval words := by
  induction step generalizing type with
  | refl => rfl
  | trans original _ first second =>
      exact (first typed).trans (second (rewrite_preserves_type original typed))
  | cancel left right evidence =>
      exact Nat.sub_add_cancel (cancellation_guard wellFormed valuation left right evidence typed.uadd_inputs.1)
  | addLeft _ ih =>
      simp only [Expression.eval, ih typed.uadd_inputs.1]
  | addRight _ ih =>
      simp only [Expression.eval, ih typed.uadd_inputs.2.1]

/-- Truth of any numerical predicate, including either side of Eq or Lt,
is preserved at every satisfying valuation of the well-formed telescope. -/
theorem CheckedForward.preserves_truth (wellFormed : UnifiedProgram.EnvWellFormed env)
    (step : CheckedForward env entries source result type)
    (valuation : Satisfies entries words) (predicate : Nat → Prop) :
    predicate (source.eval words) ↔ predicate (result.eval words) := by
  rw [rewrite_preserves_eval wellFormed valuation step.rewrite step.sourceTyped]

private theorem rewrite_preserves_width (step : Rewrite entries source result)
    (bounded : source.boundedSubtractions words) : result.boundedSubtractions words := by
  induction step with
  | refl => exact bounded
  | trans _ _ first second => exact second (first bounded)
  | cancel => exact True.intro
  | addLeft _ ih => exact ⟨ih bounded.1, bounded.2⟩
  | addRight _ ih => exact ⟨bounded.1, ih bounded.2⟩

private theorem closed_scalar (slot : ScalarSlot entries index) (words : Nat → Nat) :
    closing entries words index = .natural (words index) := by
  induction slot generalizing words with
  | here => rfl
  | there _ ih => exact ih _

private theorem closed_affine_literal (valid : ScalarExpr entries value) (bound : value.eval words < 2^64) :
    RawValue.Conv env (value.toTerm.subst (closing entries words)) (.natural (value.eval words)) := by
  induction valid with
  | var slot =>
      simp only [Expr.toTerm, Expr.eval, Term.subst, closed_scalar slot words]
      exact .refl _
  | literal =>
      simp only [Expr.toTerm, Expr.eval, Term.natural, Term.subst, substArgs]
      exact .refl _
  | add _ _ first second =>
      simp only [Expr.eval] at bound
      simp only [Expr.toTerm, Term.subst, substArgs, Op.binders, liftSub, Expr.eval]
      exact (RawValue.Conv.node .uadd (.cons (first (by omega)) (.cons (second (by omega)) .nil))).trans
        (.old (.old (.legacy (.add _ _ bound))))

private theorem closed_cancellation (leftValid : ScalarExpr entries left) (rightValid : ScalarExpr entries right)
    (ordered : right.eval words ≤ left.eval words) (width : left.eval words < 2^64) :
    RawValue.Conv env
      ((Term.uadd (.usub left.toTerm right.toTerm evidence) right.toTerm).subst (closing entries words))
      (left.toTerm.subst (closing entries words)) := by
  have leftClosed := closed_affine_literal (env := env) leftValid width
  have rightClosed := closed_affine_literal (env := env) rightValid (Nat.lt_of_le_of_lt ordered width)
  let first := left.eval words
  let second := right.eval words
  let proofTerm := evidence.subst (closing entries words)
  have aligned : RawValue.Conv env (.usub (left.toTerm.subst (closing entries words))
      (right.toTerm.subst (closing entries words)) proofTerm) (.usub (.natural first) (.natural second) proofTerm) :=
    .node .usub (.cons leftClosed (.cons rightClosed (.cons (.refl _) .nil)))
  have subtract : RawValue.Conv env (.usub (.natural first) (.natural second) proofTerm)
      (.natural (first-second)) := .old (.old (.legacy (.sub _ _ _ ordered width)))
  have same : first - second + second = first := Nat.sub_add_cancel ordered
  have sumFits : first - second + second < 2^64 := by
    rw [same]
    exact width
  have combine : RawValue.Conv env (.uadd (.natural (first-second)) (.natural second)) (.natural first) := by
    conv => rhs; rw [← same]
    exact .old (.old (.legacy (.add _ _ sumFits)))
  simp only [Term.uadd, Term.usub, Term.subst, substArgs, Op.binders, liftSub]
  exact (RawValue.Conv.node .uadd (.cons (aligned.trans subtract) (.cons rightClosed .nil))).trans
    (combine.trans leftClosed.symm)

private theorem rewrite_closed_conversion (wellFormed : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (step : Rewrite entries source result)
    (typed : HasType env [] (context entries) true source.term type)
    (bounded : source.boundedSubtractions words) :
    RawValue.Conv env (source.term.subst (closing entries words)) (result.term.subst (closing entries words)) := by
  induction step generalizing type with
  | refl => exact .refl _
  | trans original _ first second =>
      exact (first typed bounded).trans (second (rewrite_preserves_type original typed)
        (rewrite_preserves_width original bounded))
  | cancel left right evidence =>
      exact closed_cancellation left right
        (cancellation_guard wellFormed valuation left right evidence typed.uadd_inputs.1) bounded.1
  | addLeft _ ih =>
      simp only [Expression.term, Term.uadd, Term.subst, substArgs, Op.binders, liftSub]
      exact .node .uadd (.cons (ih typed.uadd_inputs.1 bounded.1) (.cons (.refl _) .nil))
  | addRight _ ih =>
      simp only [Expression.term, Term.uadd, Term.subst, substArgs, Op.binders, liftSub]
      exact .node .uadd (.cons (.refl _) (.cons (ih typed.uadd_inputs.2.1 bounded.2) .nil))

/-- At every satisfying bounded-subtraction valuation, the closed instances
are already convertible by the original RawValue rules. This statement
instantiates local assumptions with the existing type-correct closing. -/
theorem CheckedForward.closed_conversion (wellFormed : UnifiedProgram.EnvWellFormed env)
    (step : CheckedForward env entries source result type) (valuation : Satisfies entries words)
    (bounded : source.boundedSubtractions words) :
    RawValue.Conv env (source.term.subst (closing entries words)) (result.term.subst (closing entries words)) :=
  rewrite_closed_conversion wellFormed valuation step.rewrite step.sourceTyped bounded

/-- A satisfying valuation replays the original context as a typed
substitution. Both closed sides keep exactly the same instantiated type. -/
theorem CheckedForward.closed_replay (wellFormed : UnifiedProgram.EnvWellFormed env)
    (step : CheckedForward env entries source result type) (valuation : Satisfies entries words)
    (bounded : source.boundedSubtractions words) :
    let values := closing entries words
    HasType env [] [] true (source.term.subst values) (type.subst values) ∧
      HasType env [] [] true (result.term.subst values) (type.subst values) ∧
      RawValue.Conv env (source.term.subst values) (result.term.subst values) :=
  ⟨step.sourceTyped.ghostSubstitution wellFormed valuation.realizes,
    step.preserves.ghostSubstitution wellFormed valuation.realizes,
    step.closed_conversion wellFormed valuation bounded⟩

private def demoContext : List Entry :=
  [.less (.var 0) (.add (.var 1) (.literal 1)), .scalar false, .scalar false]

private def demoSource : Expression := .add (.subtract (.var 2) (.var 1) (.var 0)) (.affine (.var 1))
private def demoResult : Expression := .affine (.var 2)

private def demoWords : Nat → Nat
  | 1 | 2 => 2^64 - 1
  | _ => 0

private theorem demoValuation : Satisfies demoContext demoWords :=
  .less (.var .here) (.add (.var (.there .here)) (.literal (by decide)))
    (by decide) (.scalar (by decide) (.scalar (by decide) .empty))

/-- The checker accepts an erased hypothesis whose right side evaluates to
2^64. The subtraction's operands still fit, and closing the checked step
uses the existing RawValue literal contractions. -/
theorem checked_symbolic_hypothesis_replays :
    CheckedForward .empty demoContext demoSource demoResult .u64 ∧
      demoSource.eval demoWords = 2^64 - 1 ∧
      RawValue.Conv .empty (demoSource.term.subst (closing demoContext demoWords))
        (demoResult.term.subst (closing demoContext demoWords)) := by
  have step : CheckedForward .empty demoContext demoSource demoResult .u64 :=
    CheckedForward.ofChecker (fuel := 48) (by cbv) (by cbv)
      (.cancel (.var (.there (.there .here))) (.var (.there .here)) (.arithmetic (.assume .here)))
  have bounded : demoSource.boundedSubtractions demoWords := by
    change (2^64-1 : Nat) < 2^64 ∧ True
    exact ⟨by decide, True.intro⟩
  refine ⟨step, ?_, step.closed_conversion UnifiedProgram.EnvWellFormed.empty demoValuation bounded⟩
  exact (step.preserves_truth UnifiedProgram.EnvWellFormed.empty demoValuation (· = 2^64 - 1)).mpr (by decide)

end Jihoo.NativeKernel.Environment.LoanTyping.ContextualUnsignedCancellation
