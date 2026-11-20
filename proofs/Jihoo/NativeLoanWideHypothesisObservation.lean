import Jihoo.NativeLoanPureHypothesisObservation
import Jihoo.NativeCoreArithmeticMachine
import Jihoo.NativeACUAffine

/-! Erased affine hypotheses can have values wider than U64 even when each
scalar and literal is bounded. Construct their actual native ghost evidence
from mathematical truth using bounded leaves and the checked LtAdd rule. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.WideHypothesisObservation

open PureHypothesisObservation (Entry ScalarSlot ScalarExpr context)
open AffineSum (Expr)
open NativeConstantAccumulator (naturalSum)
open Semantics.PureArithmetic (Formula Recognized UniversalTruth)

private inductive Numeric : Term → Nat → Prop where
  | literal : value < 2^64 → Numeric (.natural value) value
  | add : Numeric left m → Numeric right n → Numeric (.uadd left right) (m+n)

private theorem Numeric.typed (represented : Numeric term n) : HasType env [] [] true term .u64 := by
  induction represented with
  | literal bound => exact .natural bound
  | add _ _ first second => exact .uadd first second

private theorem Numeric.affine (represented : Numeric term n) :
    ∃ expr : Expr, expr.toTerm = term ∧ ∀ words, expr.eval words = n := by
  induction represented with
  | literal bound => exact ⟨.literal _, rfl, fun _ => rfl⟩
  | add _ _ first second =>
      obtain ⟨a, rfl, av⟩ := first
      obtain ⟨b, rfl, bv⟩ := second
      exact ⟨.add a b, rfl, by intro words; simp only [Expr.eval, av, bv]⟩

private theorem Numeric.toOnes (represented : Numeric term n) :
    ACU.Conv term (ACU.sumTerms (List.replicate n (.natural 1))) := by
  induction represented with
  | literal bound => exact ACU.Conv.literal_ones _ bound
  | @add _ m _ n _ _ first second =>
      have concatenated := ACU.Conv.sumTerms_append (List.replicate m (.natural 1))
        (List.replicate n (.natural 1))
      rw [List.replicate_append_replicate] at concatenated
      exact (ACU.Conv.addCong first second).trans concatenated

private theorem Numeric.convert (first : Numeric left n) (second : Numeric right n) :
    RawLend.Conv env left right :=
  .old (.acu (first.toOnes.trans second.toOnes.symm))

private theorem Numeric.naturalSum (n : Nat) : Numeric (naturalSum n) n := by
  rw [NativeConstantAccumulator.naturalSum]
  split
  · exact .literal (by assumption)
  · dsimp only
    have left := Numeric.naturalSum (n / 2)
    split
    · rename_i even
      have total : n / 2 + n / 2 = n := by omega
      simpa only [total] using Numeric.add left left
    · have right := Numeric.naturalSum (n - n / 2)
      have total : n / 2 + (n - n / 2) = n := by omega
      simpa only [total] using Numeric.add left right
termination_by n
decreasing_by all_goals omega

/-- A positive gap is one more than a nonnegative mathematical natural.
The wide arithmetic remains in ghost sums of bounded literals. -/
def lessWitness (left right : Nat) : Term :=
  let gap := naturalSum (right - left - 1)
  .ltAdd (.natural 0) (.uadd gap (.natural 1)) (naturalSum left) (.zeroLe gap)

private theorem lessWitness_typed (ordered : m < n)
    (left : Numeric a m) (right : Numeric b n) :
    HasType env [] [] true (lessWitness m n) (.lt a b) := by
  have below : Numeric (.natural 0) 0 := .literal (by decide)
  have one : Numeric (.natural 1) 1 := .literal (by decide)
  have gap := Numeric.naturalSum (n - m - 1)
  have first := Numeric.naturalSum m
  have larger : Numeric (.uadd (.uadd (naturalSum (n - m - 1)) (.natural 1)) (naturalSum m)) n := by
    have total : n - m - 1 + 1 + m = n := by omega
    simpa only [total] using Numeric.add (Numeric.add gap one) first
  have smaller : Numeric (.uadd (.natural 0) (naturalSum m)) m := by
    simpa only [Nat.zero_add] using Numeric.add below first
  exact HasType.convert
    (.ltAdd below.typed (Numeric.add gap one).typed first.typed (.zeroLe gap.typed))
    (.node .lt (.cons (smaller.convert left) (.cons (larger.convert right) .nil)))

private def older (words : Nat → Nat) : Nat → Nat := fun index => words (index + 1)

/-- A semantic telescope requires a bounded scalar at each scalar slot and
truth of every comparison at its original older slots. Evidence slots carry
no numeric payload and cannot appear in scalar expressions. -/
inductive Satisfies : List Entry → (Nat → Nat) → Prop where
  | empty : Satisfies [] words
  | scalar : words 0 < 2^64 → Satisfies entries (older words) → Satisfies (.scalar erased :: entries) words
  | less : ScalarExpr entries left → ScalarExpr entries right →
      left.eval (older words) < right.eval (older words) → Satisfies entries (older words) →
      Satisfies (.less left right :: entries) words
  | equal : ScalarExpr entries left → ScalarExpr entries right →
      left.eval (older words) = right.eval (older words) → Satisfies entries (older words) →
      Satisfies (.equal left right :: entries) words

private def witness (words : Nat → Nat) : Entry → Term
  | .scalar _ => .natural (words 0)
  | .less left right => lessWitness (left.eval (older words)) (right.eval (older words))
  | .equal left _ => .refl (naturalSum (left.eval (older words)))

def closing : List Entry → (Nat → Nat) → Nat → Term
  | [], _ => fun _ => .natural 0
  | entry :: entries, words => CodeKinds.consValues (witness words entry) (closing entries (older words))

private theorem scalar_representation (valid : Satisfies entries words) (slot : ScalarSlot entries index) :
    Numeric (closing entries words index) (words index) := by
  induction slot generalizing words with
  | here =>
      cases valid with
      | scalar bound _ => exact .literal bound
  | there _ ih =>
      cases valid with
      | scalar _ previous | less _ _ _ previous | equal _ _ _ previous => exact ih previous

private theorem affine_representation (valid : Satisfies entries words) (affine : ScalarExpr entries expr) :
    Numeric (expr.toTerm.subst (closing entries words)) (expr.eval words) := by
  induction affine with
  | var slot => simpa only [Expr.toTerm, Expr.eval, Term.subst] using scalar_representation valid slot
  | literal bound => simpa only [Expr.toTerm, Expr.eval, Term.subst, substArgs] using Numeric.literal bound
  | add _ _ left right =>
      simpa only [Expr.toTerm, Expr.eval, Term.uadd, Term.subst, substArgs, Op.binders, liftSub] using
        Numeric.add left right

/-- Actual type-correct substitutions follow from truthful hypotheses, with
no U64 cap on the value of a whole affine expression. -/
theorem Satisfies.realizes (valid : Satisfies entries words) :
    Ghost.Substitution env (context entries) [] (closing entries words) := by
  induction valid with
  | empty => intro index binding absent; cases absent
  | scalar bound previous ih =>
      exact ih.consValues (by simpa only [witness, Term.u64, Term.subst, substArgs] using
        (HasType.natural (env := env) (loans := []) (ctx := []) (ghost := true) bound))
  | less left right ordered previous ih =>
      apply ih.consValues
      simp only [Term.lt, Term.subst, substArgs]
      exact lessWitness_typed ordered (affine_representation previous left) (affine_representation previous right)
  | @equal _ leftExpr _ words left right same previous ih =>
      apply ih.consValues
      simp only [Term.eq, Term.subst, substArgs]
      have first := Numeric.naturalSum (leftExpr.eval (older words))
      have leftGround := affine_representation previous left
      have rightGround := affine_representation previous right
      rw [← same] at rightGround
      exact HasType.convert (.refl first.typed)
        (.node .eq (.cons (first.convert leftGround) (.cons (first.convert rightGround) .nil)))

def checkObserve? (env : Environment) (limits : PureProofObservation.Limits) (fuel : Nat)
    (entries : List Entry) (words : Nat → Nat) (term requested : Term) : Option Term :=
  PureHypothesisObservation.checkClosing? env limits fuel (context entries) (closing entries words) term requested

theorem checkObserve?_sound (wf : UnifiedProgram.EnvWellFormed env) (valid : Satisfies entries words)
    (accepted : checkObserve? env limits fuel entries words term requested = some residual) :
    ∃ sort : SortTag, HasType env [] [] true (requested.subst (closing entries words)) sort.term ∧
      PureTyping.HasType env [] residual (requested.subst (closing entries words)) ∧ Recognized env residual :=
  PureHypothesisObservation.checkClosing?_sound wf valid.realizes accepted

theorem checked_arithmetic_truth (wf : UnifiedProgram.EnvWellFormed env) (valid : Satisfies entries words)
    (accepted : checkObserve? env limits fuel entries words term requested = some residual) :
    UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨_, _, typed, recognized⟩ := checkObserve?_sound wf valid accepted
  exact Semantics.PureArithmetic.recognized_fundamental wf typed recognized

/-- The conclusion is evaluated in the original semantic valuation, even
when neither of its sides can be written as a single literal. -/
theorem checked_affine_inequality (wf : UnifiedProgram.EnvWellFormed env) (valid : Satisfies entries words)
    (leftAffine : ScalarExpr entries left) (rightAffine : ScalarExpr entries right)
    (accepted : checkObserve? env limits fuel entries words term (.lt left.toTerm right.toTerm) = some residual) :
    left.eval words < right.eval words := by
  have truth := checked_arithmetic_truth wf valid accepted
  obtain ⟨a, leftEq, leftValue⟩ := (affine_representation valid leftAffine).affine
  obtain ⟨b, rightEq, rightValue⟩ := (affine_representation valid rightAffine).affine
  have asFormula : UniversalTruth env (Formula.less a b).syntax := by
    simp only [Formula.syntax, Term.lt, leftEq, rightEq]
    simpa only [Term.lt, Term.subst, substArgs, Op.binders, liftSub] using truth
  have ordered := (UniversalTruth.formula_iff wf (.less a b)).mp asFormula (fun _ => 0)
  simpa only [Formula.truth, leftValue, rightValue] using ordered

theorem rejects_false_inequality (wf : UnifiedProgram.EnvWellFormed env) (valid : Satisfies entries words)
    (leftAffine : ScalarExpr entries left) (rightAffine : ScalarExpr entries right)
    (unordered : ¬ left.eval words < right.eval words) :
    checkObserve? env limits fuel entries words term (.lt left.toTerm right.toTerm) = none := by
  cases observed : checkObserve? env limits fuel entries words term (.lt left.toTerm right.toTerm) with
  | none => rfl
  | some _ => exact False.elim (unordered (checked_affine_inequality wf valid leftAffine rightAffine observed))

private def leftIndex (slot : Nat) : Expr := .add (.var slot) (.literal 1)
private def rightIndex (slot : Nat) : Expr := .add (.var slot) (.literal 2)
private def wideContext : List Entry := [.less (leftIndex 0) (rightIndex 0), .scalar true]
private def wideWords : Nat → Nat
  | 1 => 2^64 - 1
  | _ => 0

private theorem wideValuation : Satisfies wideContext wideWords :=
  .less (.add (.var .here) (.literal (by decide))) (.add (.var .here) (.literal (by decide)))
    (by decide) (.scalar (by decide) .empty)

private def wideLimits : PureProofObservation.Limits := ⟨32, 32, 8192⟩

/-- Both sides of the original checked hypothesis exceed a word under this
valuation. The observer sees actual synthesized evidence at that same type. -/
theorem checked_wide_hypothesis :
    checkObserve? .empty wideLimits 12 wideContext wideWords (.var 0)
      (.lt (leftIndex 1).toTerm (rightIndex 1).toTerm) = some (lessWitness (2^64) (2^64 + 1)) ∧
    2^64 ≤ (leftIndex 1).eval wideWords ∧ (leftIndex 1).eval wideWords < (rightIndex 1).eval wideWords := by
  have accepted : checkObserve? .empty wideLimits 12 wideContext wideWords (.var 0)
      (.lt (leftIndex 1).toTerm (rightIndex 1).toTerm) = some (lessWitness (2^64) (2^64 + 1)) := by cbv
  have validLeft : ScalarExpr wideContext (leftIndex 1) :=
    .add (.var (.there .here)) (.literal (by decide))
  have validRight : ScalarExpr wideContext (rightIndex 1) :=
    .add (.var (.there .here)) (.literal (by decide))
  exact ⟨accepted, by decide,
    checked_affine_inequality UnifiedProgram.EnvWellFormed.empty wideValuation validLeft validRight accepted⟩

end Jihoo.NativeKernel.Environment.LoanTyping.WideHypothesisObservation
