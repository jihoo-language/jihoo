import Jihoo.NativeBindingMachineMutable
import Jihoo.NativeLoanArithmeticProofConsistency

/-! Loan64 proof interpretation supplies the mathematical subtraction guard,
while the indexed machine evaluates only the two machine operands. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def UnsignedSubtractionInputs
    (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .usub left right proof =>
      HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64 ∧
      HasType env loans ctx true proof (.lt right (.uadd left (.natural 1)))
  | _ => True

theorem HasType.usub_inputs {proofTerm : Term}
    (typed : HasType env loans ctx mode (.usub left right proofTerm) type) :
    HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64 ∧
    HasType env loans ctx true proofTerm (.lt right (.uadd left (.natural 1))) := by
  suffices view : ∀ {term type}, HasType env loans ctx mode term type →
      UnsignedSubtractionInputs env loans ctx mode term from view typed
  intro term type source
  apply HasType.rec (t := source)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => UnsignedSubtractionInputs env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

/-- The source evidence establishes the unsigned guard in mathematical
naturals, including at the maximum word where `left+1` is only a ghost sum. -/
theorem HasType.literal_usub_bounds {proofTerm : Term} (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.usub (.natural left) (.natural right) proofTerm) type)
    (supported : Semantics.LoanArithmetic.Supported proofTerm) :
    left < 2^64 ∧ right < 2^64 ∧ right ≤ left := by
  obtain ⟨leftTyped,rightTyped,evidence⟩ := typed.usub_inputs
  have truth := Semantics.LoanArithmetic.supported_truth wf evidence supported
  have ordered := truth.affine_less wf (.literal right) (.add (.literal left) (.literal 1)) (fun _ => 0)
  change right < left+1 at ordered
  exact ⟨leftTyped.natural_bound,rightTyped.natural_bound,by omega⟩

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- The two retained operands take five steps. Underflow selects the
arithmetic fault, and neither outcome evaluates the evidence or writes the heap. -/
theorem literal_usub_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .usub (.natural left) (.natural right) evidence)
    (leftWidth : left < 2^64) (rightWidth : right < 2^64) :
    let result := if right ≤ left then BindingMachine.Control.returned (.natural (left-right))
      else .fault .arithmeticOverflow
    run 5 state = ⟨⟨state.heap,result,state.stack,state.pending⟩,[],5⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,executeLegacy,execute,Option.map_none,
    returnAction,resumeBuffer,leftWidth,rightWidth,↓reduceIte]
  rfl

/-- The original typing and supported erased proof suffice to run unsigned
subtraction on literal inputs and preserve the exact converted result type. -/
theorem typed_literal_usub (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .usub (.natural left) (.natural right) evidence)
    (supported : Semantics.LoanArithmetic.Supported evidence) :
    run 5 state = ⟨⟨state.heap,.returned (.natural (left-right)),state.stack,state.pending⟩,[],5⟩ ∧
      LoanTyping.HasType env [] [] false (.natural (left-right)) type := by
  obtain ⟨_,_,original,converted⟩ := typed
  rw [shape] at original
  obtain ⟨leftWidth,rightWidth,ordered⟩ := original.literal_usub_bounds history.wellFormed supported
  have sourceType : LoanTyping.Conversion.Conv env .u64 type := by
    simpa only [Term.subst,substArgs] using
      (original.principalView.substitution meanings history.wellFormed.closed).trans converted
  refine ⟨?_,(LoanTyping.HasType.natural (Nat.lt_of_le_of_lt (Nat.sub_le _ _) leftWidth)).convert sourceType⟩
  simpa only [ordered,↓reduceIte] using literal_usub_steps state evaluating shape leftWidth rightWidth

namespace Examples

set_option maxRecDepth 4096

private def subtract : Term :=
  .usub (.natural 9) (.natural 4) (.decide (.natural 4) (.natural 10))

theorem subtraction_admitted : LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
    ⟨.u64,subtract⟩ = some ⟨.u64,subtract⟩ := by cbv

theorem subtraction_returns : observe (run 5 (initial subtract)) = .natural 5 := by rfl

private def subtract_zero_at_max : Term :=
  let maximum := Term.natural (2^64-1)
  .usub maximum (.natural 0) (.zeroLe maximum)

theorem subtraction_max_word :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
      ⟨.u64,subtract_zero_at_max⟩ = some ⟨.u64,subtract_zero_at_max⟩ ∧
    observe (run 5 (initial subtract_zero_at_max)) = .natural (2^64-1) := by
  constructor
  · cbv
  · rfl

theorem subtraction_underflow :
    observe (run 5 (initial (.usub (.natural 2) (.natural 3) (.natural 0)))) =
      .fault .arithmeticOverflow := by rfl

private def observable_operand (fill : Int) (number : Nat) : Term :=
  .free (.alloc (.natural 1) (.integer fill)) (.natural number)

theorem subtraction_operand_order :
    (run 40 (initial (.usub (observable_operand 11 9) (observable_operand 22 4) (observable_operand 33 0)))).events =
      [.legacy (.heap (.alloc 0 1 (encodeInteger 11))),.legacy (.heap (.free 0)),
        .legacy (.heap (.alloc 1 1 (encodeInteger 22))),.legacy (.heap (.free 1))] := by rfl

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
