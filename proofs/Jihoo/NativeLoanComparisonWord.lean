import Jihoo.NativeLoanWideHypothesisObservation

/-! Evaluate grounded scalar addition for proof comparisons. Successful
results carry the exact conversion of the original operand. The source
grammar obtains bounds from scalar widths and earlier erased assumptions. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonWord

open AffineSum (Expr)
open PureHypothesisObservation (Entry ScalarSlot ScalarExpr)
open WideHypothesisObservation (Satisfies closing)

def word? (value : Nat) : Option (Fin (2^64)) :=
  if width : value < 2^64 then some ⟨value,width⟩ else none

def run? : Nat → Term → Option (Fin (2^64))
  | _ + 1, .natural value => word? value
  | fuel + 1, .uadd left right => do
      let first ← run? fuel left
      let second ← run? fuel right
      word? (first.val + second.val)
  | _, _ => none

private theorem word?_value (ran : word? value = some result) : result.val = value := by
  unfold word? at ran
  split at ran
  · cases ran
    rfl
  · contradiction

theorem run?_sound (ran : run? fuel operand = some result) :
    RawLend.Conv env operand (.natural result.val) := by
  fun_induction run? fuel operand generalizing result
  · rw [word?_value ran]
    exact .refl _
  · rename_i firstIH secondIH
    obtain ⟨a, firstStep, next⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨b, secondStep, accepted⟩ := Option.bind_eq_some_iff.mp next
    rw [word?_value accepted]
    have width : a.val + b.val < 2^64 := (word?_value accepted) ▸ result.isLt
    exact (RawLend.Conv.node .uadd (.cons (firstIH firstStep) (.cons (secondIH secondStep) .nil))).trans
      (.old (.legacy (.add _ _ width)))
  · contradiction

private theorem slot_closed (valuation : Satisfies entries words) (slot : ScalarSlot entries index) :
    words index < 2^64 ∧ closing entries words index = .natural (words index) := by
  induction slot generalizing words with
  | here =>
      cases valuation with
      | scalar width _ => exact ⟨width,rfl⟩
  | there _ ih =>
      cases valuation with
      | scalar _ older | less _ _ _ older | equal _ _ _ older => exact ih older

/-- For any actual scalar valuation, the bounded evaluator returns exactly
the mathematical result or rejects when it exceeds one U64 word. The source
tree determines sufficient depth independently of the result. -/
theorem run_affine (expression : ScalarExpr entries expr) (valuation : Satisfies entries words) :
    ∃ depth, ∀ fuel, depth ≤ fuel →
      run? fuel (expr.toTerm.subst (closing entries words)) = word? (expr.eval words) := by
  induction expression with
  | var slot =>
      refine ⟨1,fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.toTerm,Expr.eval,Term.subst,(slot_closed valuation slot).2,run?]
  | literal width =>
      refine ⟨1,fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simp only [Expr.toTerm,Expr.eval,Term.subst,substArgs,run?]
  | @add left right _ _ first second =>
      obtain ⟨leftDepth,leftRuns⟩ := first
      obtain ⟨rightDepth,rightRuns⟩ := second
      refine ⟨max leftDepth rightDepth + 1,fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          have leftFuel : leftDepth ≤ fuel := by omega
          have rightFuel : rightDepth ≤ fuel := by omega
          simp only [Expr.toTerm,Expr.eval,Term.subst,substArgs,Op.binders,liftSub,run?,
            leftRuns fuel leftFuel,rightRuns fuel rightFuel]
          by_cases leftWidth : left.eval words < 2^64
          · by_cases rightWidth : right.eval words < 2^64
            · simp [word?,leftWidth,rightWidth]
            · have tooBig : ¬ left.eval words + right.eval words < 2^64 := by omega
              simp [word?,leftWidth,rightWidth,tooBig]
          · have tooBig : ¬ left.eval words + right.eval words < 2^64 := by omega
            simp [word?,leftWidth,tooBig]

/-- A scalar can gain a tighter static cap from an earlier checked `<`
assumption with a constant right operand. Later binders shift its slot. -/
inductive SlotCap : List Entry → Nat → Nat → Prop where
  | assume : ScalarSlot entries index →
      SlotCap (.less (.var index) (.literal (cap + 1)) :: entries) (index + 1) cap
  | there : SlotCap entries index cap → SlotCap (entry :: entries) (index + 1) cap

private theorem SlotCap.scalar (cap : SlotCap entries index limit) : ScalarSlot entries index := by
  induction cap with
  | assume slot => exact .there slot
  | there _ earlier => exact .there earlier

private theorem SlotCap.sound (cap : SlotCap entries index limit) (valuation : Satisfies entries words) :
    words index ≤ limit := by
  induction cap generalizing words with
  | assume slot =>
      cases valuation with
      | less _ _ ordered _ =>
          exact Nat.le_of_lt_succ ordered
  | there _ ih =>
      cases valuation with
      | scalar _ earlier | less _ _ _ earlier | equal _ _ _ earlier => exact ih earlier

/-- The source's width checks need only establish caps for literal and slot
leaves and for the sum of the independently derived operand caps. -/
inductive Operand (entries : List Entry) : Nat → Expr → Prop where
  | literal : n < 2^64 → Operand entries n (.literal n)
  | slot : ScalarSlot entries index → Operand entries (2^64 - 1) (.var index)
  | cappedSlot : SlotCap entries index cap → cap < 2^64 → Operand entries cap (.var index)
  | add : Operand entries first left → Operand entries second right → first + second < 2^64 →
      Operand entries (first + second) (.add left right)

private theorem Operand.scalar (operand : Operand entries cap expr) : ScalarExpr entries expr := by
  induction operand with
  | literal width => exact .literal width
  | slot scalar => exact .var scalar
  | cappedSlot cap _ => exact .var cap.scalar
  | add _ _ _ first second => exact .add first second

theorem Operand.bounded (operand : Operand entries cap expr) (valuation : Satisfies entries words) :
    expr.eval words ≤ cap ∧ cap < 2^64 := by
  induction operand with
  | literal width => exact ⟨Nat.le_refl _,width⟩
  | slot scalar =>
      have value := (slot_closed valuation scalar).1
      exact ⟨by simp only [Expr.eval]; omega,by decide⟩
  | cappedSlot cap width => exact ⟨cap.sound valuation,width⟩
  | add _ _ width first second => exact ⟨Nat.add_le_add first.1 second.1,width⟩

theorem Operand.run_total (operand : Operand entries cap expr) (valuation : Satisfies entries words) :
    ∃ (depth : Nat) (width : expr.eval words < 2^64), ∀ fuel, depth ≤ fuel →
      run? fuel (expr.toTerm.subst (closing entries words)) = some ⟨expr.eval words,width⟩ := by
  have bounds := operand.bounded valuation
  have width := Nat.lt_of_le_of_lt bounds.1 bounds.2
  obtain ⟨depth,ran⟩ := run_affine operand.scalar valuation
  exact ⟨depth,width,fun fuel enough => by rw [ran fuel enough]; simp [word?,width]⟩

def select? (fuel : Nat) : Term → Option Term
  | .ifLt left right yes no => do
      let first ← run? fuel left
      let second ← run? fuel right
      pure (if first.val < second.val then yes.subst (single (.decide left right)) else no)
  | .ifEq left right yes no => do
      let first ← run? fuel left
      let second ← run? fuel right
      pure (if first.val = second.val then yes.subst (single (.refl left)) else no)
  | _ => none

/-- Comparison branches use the original source operands as evidence
arguments, even when their scalar values were computed by addition. -/
theorem select?_sound (selected : select? fuel term = some result) : ProofComparison.Step env term result := by
  fun_cases select? fuel term <;> simp only [select?] at selected
  · obtain ⟨first,leftRan,selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨second,rightRan,selected⟩ := Option.bind_eq_some_iff.mp selected
    simp only [pure,Option.some.injEq] at selected
    split at selected
    · subst result
      exact .ltTrue (run?_sound leftRan) (run?_sound rightRan) (by assumption)
    · subst result
      exact .ltFalse (run?_sound leftRan) (run?_sound rightRan) (by assumption)
  · obtain ⟨first,leftRan,selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨second,rightRan,selected⟩ := Option.bind_eq_some_iff.mp selected
    simp only [pure,Option.some.injEq] at selected
    split at selected
    · subst result
      exact .eqTrue (run?_sound leftRan) (run?_sound rightRan) (by assumption)
    · subst result
      exact .eqFalse (run?_sound leftRan) (run?_sound rightRan) (by assumption)
  · contradiction

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonWord
