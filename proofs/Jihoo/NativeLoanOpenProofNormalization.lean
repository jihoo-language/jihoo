import Jihoo.NativeLoanWideHypothesisObservation

/-! Mixed local hypotheses can be normalized without first assuming a
successful observation. Arithmetic constructors replay their closed
operands, and a chain of ghost wrappers and witnessed transports reduces
at the exact original instantiated type. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.OpenProofNormalization

open PureHypothesisObservation (Entry ScalarSlot ScalarExpr context)
open WideHypothesisObservation (Satisfies closing lessWitness)
open NativeKernel.Conversion (treeSize)
open AffineSum (Expr)
open Semantics.PureArithmetic (Formula Recognized UniversalTruth)
open Semantics.LoanArithmetic (Supported)
open NativeConstantAccumulator (naturalSum)

private theorem close_scalar (slot : ScalarSlot entries index) (words : Nat → Nat) :
    closing entries words index = .natural (words index) := by
  induction slot generalizing words with
  | here => rfl
  | there _ ih => exact ih _

theorem closed_affine (valid : ScalarExpr entries value) (words : Nat → Nat) :
    ∃ expr : Expr, expr.toTerm = value.toTerm.subst (closing entries words) ∧
      ∀ assignment, expr.eval assignment = value.eval words := by
  induction valid with
  | var slot =>
      exact ⟨.literal _, by simp [Expr.toTerm, Term.subst, close_scalar slot words], fun _ => rfl⟩
  | literal _ =>
      exact ⟨.literal _, by simp [Expr.toTerm, Term.subst, substArgs], fun _ => rfl⟩
  | add _ _ left right =>
      obtain ⟨first, alignedFirst, firstValue⟩ := left
      obtain ⟨second, alignedSecond, secondValue⟩ := right
      exact ⟨.add first second,
        by simp [Expr.toTerm, Term.subst, substArgs, Op.binders, liftSub, alignedFirst, alignedSecond],
        by intro assignment; simp only [Expr.eval, firstValue, secondValue]⟩

private theorem wideAffine (n : Nat) : ∃ expr : Expr, expr.toTerm = naturalSum n := by
  rw [naturalSum]
  split
  · exact ⟨.literal n, rfl⟩
  · dsimp only
    obtain ⟨expr, first⟩ := wideAffine (n / 2)
    split
    · exact ⟨.add expr expr, by simp only [Expr.toTerm, first]⟩
    · obtain ⟨other, second⟩ := wideAffine (n - n / 2)
      exact ⟨.add expr other, by simp only [Expr.toTerm, first, second]⟩
termination_by n
decreasing_by all_goals omega

private theorem wideLess_supported (left right : Nat) : Supported (lessWitness left right) := by
  obtain ⟨gap, gapTerm⟩ := wideAffine (right - left - 1)
  obtain ⟨first, firstTerm⟩ := wideAffine left
  unfold lessWitness
  rw [← gapTerm, ← firstTerm]
  simp only [Supported]
  exact ⟨⟨.literal 0, rfl⟩, ⟨.add gap (.literal 1), rfl⟩, ⟨first, rfl⟩, ⟨gap, rfl⟩⟩

inductive LessSlot : List Entry → Nat → Prop where
  | here : LessSlot (.less left right :: entries) 0
  | there : LessSlot entries index → LessSlot (entry :: entries) (index + 1)

inductive EqualSlot : List Entry → Nat → Prop where
  | here : EqualSlot (.equal left right :: entries) 0
  | there : EqualSlot entries index → EqualSlot (entry :: entries) (index + 1)

private theorem LessSlot.closedSupported (slot : LessSlot entries index) (words : Nat → Nat) :
    Supported (closing entries words index) := by
  induction slot generalizing words with
  | here => exact wideLess_supported _ _
  | there _ ih => exact ih _

private theorem EqualSlot.closedReflexive (slot : EqualSlot entries index) (words : Nat → Nat) :
    ∃ expr : Expr, closing entries words index = .refl expr.toTerm := by
  induction slot generalizing words with
  | here =>
      obtain ⟨expr, aligned⟩ := wideAffine _
      exact ⟨expr, congrArg Term.refl aligned.symm⟩
  | there _ ih => exact ih _

/-- Any finite arithmetic evidence tree, including repeated erased
assumptions in arbitrary proof-operand positions. -/
inductive ArithmeticTree (entries : List Entry) : Term → Prop where
  | assume : LessSlot entries index → ArithmeticTree entries (.var index)
  | decide : ArithmeticTree entries (.decide left right)
  | zeroLe : ScalarExpr entries argument → ArithmeticTree entries (.zeroLe argument.toTerm)
  | ltAdd : ScalarExpr entries left → ScalarExpr entries right → ScalarExpr entries delta →
      ArithmeticTree entries proof →
      ArithmeticTree entries (.ltAdd left.toTerm right.toTerm delta.toTerm proof)
  | ltCancel : ScalarExpr entries left → ScalarExpr entries right → ScalarExpr entries delta →
      ArithmeticTree entries proof →
      ArithmeticTree entries (.ltCancel left.toTerm right.toTerm delta.toTerm proof)
  | ltLe : ScalarExpr entries left → ScalarExpr entries mid → ScalarExpr entries right →
      ArithmeticTree entries first → ArithmeticTree entries second →
      ArithmeticTree entries (.ltLe left.toTerm mid.toTerm right.toTerm first second)
  | absurd : ArithmeticTree entries proof → ArithmeticTree entries (.absurd annotation proof)

theorem ArithmeticTree.closedSupported (tree : ArithmeticTree entries term) (words : Nat → Nat) :
    Supported (term.subst (closing entries words)) := by
  induction tree with
  | assume slot => simpa only [Term.subst] using slot.closedSupported words
  | decide => simp [Term.decide, Term.subst, substArgs, Supported]
  | zeroLe argument =>
      obtain ⟨value, aligned, _⟩ := closed_affine argument words
      simp only [Term.zeroLe, Term.subst, substArgs, Op.binders, liftSub, Supported]
      exact ⟨value, aligned⟩
  | ltAdd left right delta _ recognized =>
      obtain ⟨a, la, _⟩ := closed_affine left words
      obtain ⟨b, rb, _⟩ := closed_affine right words
      obtain ⟨c, dc, _⟩ := closed_affine delta words
      simp only [Term.ltAdd, Term.subst, substArgs, Op.binders, liftSub, Supported]
      exact ⟨⟨a, la⟩, ⟨b, rb⟩, ⟨c, dc⟩, recognized⟩
  | ltCancel left right delta _ recognized =>
      obtain ⟨a, la, _⟩ := closed_affine left words
      obtain ⟨b, rb, _⟩ := closed_affine right words
      obtain ⟨c, dc, _⟩ := closed_affine delta words
      simp only [Term.ltCancel, Term.subst, substArgs, Op.binders, liftSub, Supported]
      exact ⟨⟨a, la⟩, ⟨b, rb⟩, ⟨c, dc⟩, recognized⟩
  | ltLe left mid right _ _ first second =>
      obtain ⟨a, la, _⟩ := closed_affine left words
      obtain ⟨b, mb, _⟩ := closed_affine mid words
      obtain ⟨c, rc, _⟩ := closed_affine right words
      simp only [Term.ltLe, Term.subst, substArgs, Op.binders, liftSub, Supported]
      exact ⟨⟨a, la⟩, ⟨b, mb⟩, ⟨c, rc⟩, first, second⟩
  | absurd _ recognized =>
      simpa only [Term.absurd, Term.subst, substArgs, Op.binders, liftSub, Supported] using recognized

inductive Reflexive (entries : List Entry) : Term → Prop where
  | assume : EqualSlot entries index → Reflexive entries (.var index)
  | refl : ScalarExpr entries expr → Reflexive entries (.refl expr.toTerm)

theorem Reflexive.closed (tree : Reflexive entries term) (words : Nat → Nat) :
    ∃ expr : Expr, term.subst (closing entries words) = .refl expr.toTerm := by
  cases tree with
  | assume slot => simpa only [Term.subst] using slot.closedReflexive words
  | refl scalar =>
      obtain ⟨expr, aligned, _⟩ := closed_affine scalar words
      exact ⟨expr, by simp [Term.refl, Term.subst, substArgs, Op.binders, liftSub, aligned]⟩

inductive TransportEvidence (entries : List Entry) : Term → Prop where
  | reflexive : Reflexive entries equality → TransportEvidence entries equality
  | strict : TransportEvidence entries equality → TransportEvidence entries (.strict (.natural literal) equality)

theorem TransportEvidence.exposes (tree : TransportEvidence entries equality) (words : Nat → Nat) :
    ∃ value, ProofTransportObservation.exposeRefl? (equality.subst (closing entries words)) = some value := by
  induction tree with
  | reflexive proof =>
      obtain ⟨expr, shape⟩ := proof.closed words
      exact ⟨expr.toTerm, by rw [shape, ProofTransportObservation.exposeRefl?]⟩
  | strict _ exposed =>
      obtain ⟨value, found⟩ := exposed
      exact ⟨value, by simpa [Term.strict, Term.natural, Term.subst, substArgs, Op.binders, liftSub,
        ProofTransportObservation.exposeRefl?] using found⟩

/-- Normalization strips any finite head chain of Strict, Free and checked
transports over reflexive equality. Arithmetic operands may themselves
contain arbitrarily many uses of any earlier erased arithmetic assumption. -/
inductive Tree (entries : List Entry) : Term → Prop where
  | arithmetic : ArithmeticTree entries proof → Tree entries proof
  | reflexive : Reflexive entries proof → Tree entries proof
  | transport : TransportEvidence entries equality → Tree entries proof →
      Tree entries (.transport motive equality proof)
  | strict : Tree entries proof → Tree entries (.strict first proof)
  | free : Tree entries proof → Tree entries (.free owner proof)

/-- The terminal syntax is checked by the existing arithmetic recognizer.
Only head steps with established typed replay are performed. -/
def normalize? (env : Environment) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, .strict _ rest => normalize? env fuel rest
  | fuel + 1, .free _ rest => normalize? env fuel rest
  | fuel + 1, .transport _ equality payload => do
      let _ ← ProofTransportObservation.exposeRefl? equality
      normalize? env fuel payload
  | _ + 1, term =>
      if Semantics.PureArithmetic.recognizes env 0 0 1 term then some term else none

theorem normalize?_sound (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx term type)
    (ran : normalize? env fuel term = some residual) :
    PureTyping.HasType env ctx residual type ∧ Recognized env residual := by
  fun_induction normalize? env fuel term generalizing ctx type residual
  · contradiction
  · rename_i ih
    exact ih ((PureProofObservation.Step.strict _ _).preserves wf typed) ran
  · rename_i ih
    exact ih ((PureProofObservation.Step.free _ _).preserves wf typed) ran
  · rename_i ih
    obtain ⟨_, exposed, replayed⟩ := Option.bind_eq_some_iff.mp ran
    exact ih ((PureProofObservation.Step.transport exposed).preserves wf typed) replayed
  · cases ran
    exact ⟨typed, Semantics.PureArithmetic.recognizes_sound (by assumption)⟩
  · contradiction

private theorem supports_recognized (supported : Supported term) :
    Semantics.PureArithmetic.recognizes env 0 0 1 term = true := by
  have ready := (ProofObservation.supported_iff term).mpr supported
  simp [Semantics.PureArithmetic.recognizes, ready]

private theorem lessSlot_terminal (slot : LessSlot entries index) (words : Nat → Nat) (fuel : Nat) :
    normalize? env (fuel + 1) (closing entries words index) = some (closing entries words index) := by
  induction slot generalizing words with
  | @here left right _ =>
      let term := lessWitness (left.eval (fun index => words (index + 1)))
        (right.eval (fun index => words (index + 1)))
      change normalize? env (fuel + 1) term = some term
      have ready : Semantics.PureArithmetic.recognizes env 0 0 1 term = true :=
        supports_recognized (wideLess_supported _ _)
      simp [term, lessWitness, normalize?] at ready ⊢
      exact ready
  | there _ ih => exact ih _

private theorem ArithmeticTree.terminal (tree : ArithmeticTree entries term) (words : Nat → Nat) (fuel : Nat) :
    normalize? env (fuel + 1) (term.subst (closing entries words)) = some (term.subst (closing entries words)) := by
  have ready := supports_recognized (env := env) (tree.closedSupported words)
  cases tree with
  | assume slot => simpa only [Term.subst] using lessSlot_terminal (env := env) slot words fuel
  | decide | zeroLe | ltAdd | ltCancel | ltLe | absurd =>
      simp only [Term.decide, Term.zeroLe, Term.ltAdd, Term.ltCancel, Term.ltLe, Term.absurd,
        Term.subst, substArgs, Op.binders, liftSub] at ready ⊢
      simp [normalize?, ready]

private theorem Reflexive.terminal (tree : Reflexive entries term) (words : Nat → Nat) (fuel : Nat) :
    normalize? env (fuel + 1) (term.subst (closing entries words)) = some (term.subst (closing entries words)) := by
  obtain ⟨expr, aligned⟩ := tree.closed words
  have ready : Semantics.PureArithmetic.recognizes env 0 0 1 (.refl expr.toTerm) = true := by
    change (ProofObservation.supported (.refl expr.toTerm) || (AffineSum.parse expr.toTerm).isSome) = true
    simp [AffineSum.parse_toTerm]
  simp only [Term.refl] at ready
  simp [aligned, Term.refl, normalize?, ready]

/-- The synthetic result of the closing is processed in finite fuel
computed from its actual size. Each transport takes the existing typed
head replay, with its equality exposure derived by construction. -/
theorem Tree.normalization_total (tree : Tree entries term) (words : Nat → Nat)
    (enough : treeSize (term.subst (closing entries words)) < fuel) :
    ∃ result, normalize? env fuel (term.subst (closing entries words)) = some result := by
  induction tree generalizing fuel with
  | arithmetic tree =>
      cases fuel with
      | zero => omega
      | succ fuel => exact ⟨_, tree.terminal words fuel⟩
  | reflexive tree =>
      cases fuel with
      | zero => omega
      | succ fuel => exact ⟨_, tree.terminal words fuel⟩
  | transport evidence _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨_, exposed⟩ := evidence.exposes words
          simp only [Term.transport, Term.subst, substArgs, Op.binders, liftSub] at enough ⊢
          obtain ⟨result, ran⟩ := ih (fuel := fuel) (by
            simp only [treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at enough
            omega)
          exact ⟨result, by rw [normalize?, exposed]; exact ran⟩
  | strict _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Term.strict, Term.subst, substArgs, Op.binders, liftSub] at enough ⊢
          obtain ⟨result, ran⟩ := ih (fuel := fuel) (by
            simp only [treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at enough
            omega)
          exact ⟨result, by rw [normalize?]; exact ran⟩
  | free _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Term.free, Term.subst, substArgs, Op.binders, liftSub] at enough ⊢
          obtain ⟨result, ran⟩ := ih (fuel := fuel) (by
            simp only [treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at enough
            omega)
          exact ⟨result, by rw [normalize?]; exact ran⟩

def checkNormalize? (env : Environment) (limits : PureProofObservation.Limits)
    (entries : List Entry) (words : Nat → Nat) (term requested : Term) : Option Term := do
  let _ ← PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
    (context entries) term requested
  let closed := term.subst (closing entries words)
  normalize? env (treeSize closed + 1) closed

/-- The actual ghost derivation determines the result type. Structural
normalization supplies the arithmetic witness from the source and closes
the derivation with the semantic valuation. -/
theorem typed_normalization (wf : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (tree : Tree entries term)
    (typed : PureTyping.HasType env (context entries) term requested) :
    let closed := term.subst (closing entries words)
    ∃ result, normalize? env (treeSize closed + 1) closed = some result ∧
      PureTyping.HasType env [] result (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨result, ran⟩ := tree.normalization_total (env := env) words
    (Nat.lt_succ_self (treeSize (term.subst (closing entries words))))
  obtain ⟨normalized, ready⟩ := normalize?_sound wf (typed.ghostSubstitution wf valuation.realizes) ran
  exact ⟨result, ran, normalized, Semantics.PureArithmetic.recognized_fundamental wf normalized ready⟩

/-- Actual checking and a syntactic proof tree give a typed finite
normalization and arithmetic truth. No successful run is supplied. -/
theorem checked_normalization {limits : PureProofObservation.Limits} (wf : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (tree : Tree entries term)
    (checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
      (context entries) term requested = some sort) :
    ∃ result, checkNormalize? env limits entries words term requested = some result ∧
      PureTyping.HasType env [] result (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  have admitted := (PureTyping.Checker.check?_sound checked).2
  obtain ⟨result, ran, normalized, truth⟩ := typed_normalization wf valuation tree admitted
  exact ⟨result, by simp [checkNormalize?, checked, ran], normalized, truth⟩

theorem typed_affine_inequality (wf : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (tree : Tree entries term)
    (leftAffine : ScalarExpr entries left) (rightAffine : ScalarExpr entries right)
    (typed : PureTyping.HasType env (context entries) term (.lt left.toTerm right.toTerm)) :
    left.eval words < right.eval words := by
  obtain ⟨_, _, _, truth⟩ := typed_normalization wf valuation tree typed
  obtain ⟨a, leftEq, leftValue⟩ := closed_affine leftAffine words
  obtain ⟨b, rightEq, rightValue⟩ := closed_affine rightAffine words
  have asFormula : UniversalTruth env (Formula.less a b).syntax := by
    simp only [Formula.syntax, Term.lt, leftEq, rightEq]
    simpa only [Term.lt, Term.subst, substArgs, Op.binders, liftSub] using truth
  have ordered := (UniversalTruth.formula_iff wf (.less a b)).mp asFormula (fun _ => 0)
  simpa only [Formula.truth, leftValue, rightValue] using ordered

theorem no_closed_lt_zero_zero (wf : UnifiedProgram.EnvWellFormed env) (tree : Tree [] term) :
    ¬PureTyping.HasType env [] term (.lt (.natural 0) (.natural 0)) := by
  intro typed
  have ordered : (0 : Nat) < 0 :=
    typed_affine_inequality (left := .literal 0) (right := .literal 0) wf
      (Satisfies.empty (words := fun _ => 0)) tree (.literal (by decide)) (.literal (by decide)) typed
  exact Nat.lt_irrefl _ ordered

/-- Original arithmetic indices are interpreted at the specified valuation
even above U64. A false affine inequality in this fragment is rejected by
the source checker itself. -/
theorem rejects_false_checked_inequality {limits : PureProofObservation.Limits} (wf : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (tree : Tree entries term)
    (leftAffine : ScalarExpr entries left) (rightAffine : ScalarExpr entries right)
    (unordered : ¬ left.eval words < right.eval words) :
    PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
      (context entries) term (.lt left.toTerm right.toTerm) = none := by
  cases checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
      (context entries) term (.lt left.toTerm right.toTerm) with
  | none => rfl
  | some _ =>
      have typed := (PureTyping.Checker.check?_sound checked).2
      exact False.elim (unordered (typed_affine_inequality wf valuation tree leftAffine rightAffine typed))

private def demoContext : List Entry :=
  [.equal (.var 1) (.add (.literal 1) (.literal 1)), .less (.var 0) (.literal 3), .scalar false]

private def demoWords : Nat → Nat
  | 2 => 2
  | _ => 0

private theorem demoValuation : Satisfies demoContext demoWords :=
  .equal (.var (.there .here)) (.add (.literal (by decide)) (.literal (by decide))) (by decide)
    (.less (.var .here) (.literal (by decide)) (by decide) (.scalar (by decide) .empty))

private def owner : Term := .alloc (.natural 1) (.integer 0)
private def goalType : Term := .lt (.free owner (.natural 2)) (.natural 4)
private def motive : Term := .lam false .u64 (.lt (.var 0) (.natural 4))
private def source : Term :=
  .strict (.natural 7) (.free owner
    (.transport motive (.strict (.natural 2) (.var 0))
      (.ltLe (.var 2) (.natural 3) (.natural 4) (.var 1) (.decide (.natural 3) (.natural 5)))))

private def residual : Term :=
  .ltLe (.natural 2) (.natural 3) (.natural 4) (lessWitness 2 3) (.decide (.natural 3) (.natural 5))

private theorem demoTree : Tree demoContext source :=
  .strict (.free (.transport (.strict (.reflexive (.assume .here))) (.arithmetic
    (.ltLe (.var (.there (.there .here))) (.literal (by decide)) (.literal (by decide))
      (.assume (.there .here)) .decide))))

private def limits : PureProofObservation.Limits := ⟨32, 32, 8192⟩

/-- Both erased hypotheses are used below their scalar. The checked ghost
transport under Free and Strict normalizes to the composed arithmetic tree. -/
theorem checked_nested_transport_normalizes :
    checkNormalize? .empty limits demoContext demoWords source goalType = some residual ∧ UniversalTruth .empty goalType := by
  have checked : PureTyping.Checker.check? .empty limits.typingFuel limits.conversionFuel limits.budget
      (context demoContext) source goalType = some .prop := by cbv
  obtain ⟨_, _, _, truth⟩ := checked_normalization UnifiedProgram.EnvWellFormed.empty demoValuation demoTree checked
  exact ⟨by cbv, by simpa only [show goalType.subst (closing demoContext demoWords) = goalType by cbv] using truth⟩

end Jihoo.NativeKernel.Environment.LoanTyping.OpenProofNormalization
