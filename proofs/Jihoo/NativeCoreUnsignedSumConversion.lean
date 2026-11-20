import Jihoo.NativeCoreUnsignedSum
import Jihoo.NativeLoanPureArithmetic

/-! Separate open symbolic cancellation in Core.sum from literal
subtraction in the existing ghost conversion theory. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedSumConversion

open NativeArena Environment
open NativeKernel.Conversion (ListRel)

private inductive Neutral : Nat → Term → Prop where
  | variable (index : Nat) : Neutral 0 (.var index)
  | difference (left right proof : Nat) : Neutral 1 (.usub (.var left) (.var right) (.var proof))
  | add : Neutral first a → Neutral second b → Neutral (first+second) (.uadd a b)

private def Preserves (input output : Term) : Prop :=
  (∀ {count}, Neutral count input → Neutral count output) ∧
  (∀ index, input = .var index → output = .var index)

private theorem keeps_refl (term : Term) : Preserves term term := ⟨fun unchanged => unchanged, fun _ same => same⟩

private theorem keeps_trans (left : Preserves a b) (right : Preserves b c) : Preserves a c :=
  ⟨fun source => right.1 (left.1 source), fun index same => right.2 index (left.2 index same)⟩

private theorem keeps_head (proof : ∀ {count}, Neutral count (.node op children) → Neutral count result) :
    Preserves (.node op children) result :=
  ⟨proof, by intro _ impossible; cases impossible⟩

private theorem keeps_node (children : ListRel Preserves before after) :
    Preserves (.node op before) (.node op after) := by
  apply keeps_head
  intro count source
  cases source with
  | difference left right proof =>
      cases children with
      | cons first tail =>
          cases tail with
          | cons second tail =>
              cases tail with
              | cons third tail =>
                  cases tail
                  rw [first.2 left rfl, second.2 right rfl, third.2 proof rfl]
                  exact .difference left right proof
  | add left right =>
      cases children with
      | cons first tail =>
          cases tail with
          | cons second tail =>
              cases tail
              exact .add (first.1 left) (second.1 right)

private theorem keeps_arithmetic (step : ACU.ArithmeticRed input result) : Preserves input result := by
  induction step using ACU.ArithmeticRed.rec
    (motive_2 := fun first last _ => ListRel Preserves first last) with
  | refl term => exact keeps_refl term
  | trans _ _ first second => exact keeps_trans first second
  | node _ _ children => exact keeps_node children
  | assocRight =>
      apply keeps_head
      intro _ source
      cases source with
      | add first third =>
          cases first with
          | add one two => simpa only [Nat.add_assoc] using Neutral.add one (.add two third)
  | assocLeft =>
      apply keeps_head
      intro _ source
      cases source with
      | add first pair =>
          cases pair with
          | add two three => simpa only [Nat.add_assoc] using Neutral.add (.add first two) three
  | comm =>
      apply keeps_head
      intro _ source
      cases source with
      | add left right => simpa only [Nat.add_comm] using Neutral.add right left
  | zeroRight =>
      apply keeps_head
      intro _ source
      cases source with
      | add _ right => cases right
  | zeroLeft =>
      apply keeps_head
      intro _ source
      cases source with
      | add left _ => cases left
  | literalSplit =>
      apply keeps_head
      intro _ source
      cases source
  | literalAdd =>
      apply keeps_head
      intro _ source
      cases source with
      | add left _ => cases left
  | nil => exact .nil
  | cons _ _ first tail => exact .cons first tail

private theorem keeps_compute (step : ACU.Computes input result) : Preserves input result := by
  cases step <;> apply keeps_head <;> intro _ source <;> cases source

private theorem keeps_mixed (step : ACU.MixedRed input result) : Preserves input result := by
  induction step using ACU.MixedRed.rec
    (motive_2 := fun first last _ => ListRel Preserves first last) with
  | refl => exact keeps_refl _
  | trans _ _ first second => exact keeps_trans first second
  | node _ _ children => exact keeps_node children
  | arithmetic step => exact keeps_arithmetic step
  | compute step => exact keeps_compute step
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

private theorem keeps_delta (step : EnvironmentDelta.Forward env input result) : Preserves input result := by
  induction step using EnvironmentDelta.Forward.rec
    (motive_2 := fun first last _ => ListRel Preserves first last) with
  | refl => exact keeps_refl _
  | trans _ _ first second => exact keeps_trans first second
  | node _ _ children => exact keeps_node children
  | acu step => exact keeps_mixed step
  | delta =>
      apply keeps_head
      intro _ source
      cases source
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

private theorem keeps_family (step : FamilyIota.Extended.Forward env input result) : Preserves input result := by
  induction step using FamilyIota.Extended.Forward.rec
    (motive_2 := fun first last _ => ListRel Preserves first last) with
  | refl => exact keeps_refl _
  | trans _ _ first second => exact keeps_trans first second
  | node _ _ children => exact keeps_node children
  | old step => exact keeps_delta step
  | iota step => cases step <;> apply keeps_head <;> intro _ source <;> cases source
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

def source : Term := .uadd (.usub (.var 2) (.var 1) (.var 0)) (.var 1)

private def bound : Term := .lt (.var 0) (.uadd (.var 1) (.natural 1))

private def declaration : GlobalDeclaration :=
  ⟨.pi false .u64 (.pi false .u64 (.pi true bound .u64)),
    .lam false .u64 (.lam false .u64 (.lam true bound source))⟩

private def arena : Arena := #[.var 2, .var 1, .var 0, .node .usub [0, 1, 2]]

private theorem variable_count (shape : Neutral count (.var index)) : count = 0 := by
  cases shape
  rfl

/-- The independent checker admits the open body under its erased bound.
Standalone USub retains both symbolic operands; the outer UAdd cancels. -/
theorem admitted_symbolic_sum_cancels :
    LoanTyping.MixedProgram.checkDeclaration 48 96 .empty declaration = some declaration ∧
    NativeCoreUnsignedSubtract.runAfterOperands .empty false arena 20 8 0 3 0 1 2 = ⟨arena, .ok 3, 4⟩ ∧
    NativeCoreUnsignedSum.run .empty false arena 20 8 0 3 1 = ⟨arena, .ok 0, some 6⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- The installed raw ghost theory cannot identify the open source with
the variable returned by production cancellation. Its forward paths keep
the symbolic subtraction occurrence, including after additive reordering. -/
theorem symbolic_sum_not_raw_convertible : ¬ RawValue.Conv .empty source (.var 2) := by
  intro converted
  have admissible := UnifiedProgram.EnvWellFormed.empty.admissible
  have projected := converted.projected admissible
  have same : Semantics.ValueErasure.Loan.project .empty source = source := by cbv
  rw [same, Semantics.ValueErasure.Loan.project_variable] at projected
  obtain ⟨common, fromSource, fromVariable⟩ := projected.church_rosser admissible
  have retained : Neutral 1 common :=
    (keeps_family fromSource).1 (.add (.difference 2 1 0) (.variable 1))
  have unchanged := fromVariable.variable_shape 2 rfl
  rw [unchanged] at retained
  exact Nat.one_ne_zero (variable_count retained)

open Semantics.PureArithmetic (Formula Recognized UniversalTruth recognized_fundamental)
open AffineSum (Expr)

/-- For recognized source evidence, cancellation is valid in every natural
valuation of the affine operands. The bound comes from the actual erased
typing judgment. -/
theorem checked_affine_cancellation (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env ctx proofTerm
      (Formula.less right (.add left (.literal 1))).syntax)
    (recognized : Recognized env proofTerm) (assignment : Nat → Nat) :
    right.eval assignment ≤ left.eval assignment ∧
      left.eval assignment - right.eval assignment + right.eval assignment = left.eval assignment := by
  have truth := recognized_fundamental wellFormed typed recognized
  have bound := (UniversalTruth.formula_iff wellFormed (.less right (.add left (.literal 1)))).mp truth assignment
  change right.eval assignment < left.eval assignment + 1 at bound
  omega

/-- A checked literal instantiation is convertible by the original rules:
literal subtraction followed by the exactly bounded literal addition. -/
theorem checked_literal_cancellation_convertible
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode
      (.usub (.natural left) (.natural right) proofTerm) resultType)
    (recognized : Recognized env proofTerm) :
    RawValue.Conv env (.uadd (.usub (.natural left) (.natural right) proofTerm) (.natural right)) (.natural left) := by
  obtain ⟨leftTyped, _, proofTyped⟩ := typed.usub_inputs
  have evaluated := checked_affine_cancellation (left := .literal left) (right := .literal right) wellFormed
    (.native (proofTyped.ghost [])) recognized (fun _ => 0)
  change right ≤ left ∧ left - right + right = left at evaluated
  have subtract : RawValue.Conv env (.usub (.natural left) (.natural right) proofTerm)
      (.natural (left-right)) :=
    .old (.old (.legacy (.sub left right proofTerm evaluated.1 leftTyped.natural_bound)))
  have fits : left - right + right < 2^64 := by
    rw [evaluated.2]
    exact leftTyped.natural_bound
  have add : RawValue.Conv env (.uadd (.natural (left-right)) (.natural right))
      (.natural (left-right+right)) :=
    .old (.old (.legacy (.add (left-right) right fits)))
  rw [evaluated.2] at add
  exact (RawValue.Conv.node .uadd (.cons subtract (.cons (.refl _) .nil))).trans add

end Jihoo.NativeKernel.NativeCoreUnsignedSumConversion
