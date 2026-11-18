import Jihoo.NativeLoanComputationPreservation

/-! The signed integer branch of Core.normal widens both I64 operands to
128 bits. It narrows an exact mathematical result only after the signed
64-bit check. This models the branch after both children are normalized. -/
namespace Jihoo.NativeKernel.Environment.ValueReduction

private theorem operand_abs_bound (x : Int64) : x.toInt.natAbs ≤ 2 ^ 63 := by
  have low := x.le_toInt
  have high := x.toInt_lt
  omega

theorem arithmetic_fits_i128 (op : Arith) (x y : Int64) :
    -(2 ^ 127 : Int) ≤ arithmetic op x.toInt y.toInt ∧
      arithmetic op x.toInt y.toInt < 2 ^ 127 := by
  have lowX := x.le_toInt
  have highX := x.toInt_lt
  have lowY := y.le_toInt
  have highY := y.toInt_lt
  cases op with
  | add => simp only [arithmetic]; omega
  | sub => simp only [arithmetic]; omega
  | mul =>
      have bounded : (x.toInt * y.toInt).natAbs ≤ 2 ^ 126 := by
        rw [Int.natAbs_mul]
        exact Nat.le_trans (Nat.mul_le_mul (operand_abs_bound x) (operand_abs_bound y)) (by decide)
      simp only [arithmetic]
      omega

def wideArithmetic (op : Arith) (x y : Int64) : BitVec 128 :=
  let a := x.toBitVec.signExtend 128
  let b := y.toBitVec.signExtend 128
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

theorem wideArithmetic_exact (op : Arith) (x y : Int64) :
    (wideArithmetic op x y).toInt = arithmetic op x.toInt y.toInt := by
  have words : wideArithmetic op x y = BitVec.ofInt 128 (arithmetic op x.toInt y.toInt) := by
    cases op <;> simp only [wideArithmetic,arithmetic,BitVec.signExtend,Int64.toInt_toBitVec,
      Int.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.ofInt_add,BitVec.ofInt_neg,BitVec.ofInt_mul]
  rw [words]
  exact BitVec.toInt_ofInt_eq_self (by decide) (arithmetic_fits_i128 op x y).1 (arithmetic_fits_i128 op x y).2

/-- Failure keeps the original arithmetic node, with its normalized children. -/
def foldArithmetic (op : Arith) (x y : Int64) : Option Int64 :=
  let value := (wideArithmetic op x y).toInt
  if -9223372036854775807 - 1 ≤ value ∧ value ≤ 9223372036854775807
  then some (Int64.ofInt value) else none

theorem foldArithmetic_refines (op : Arith) (x y : Int64) :
    (foldArithmetic op x y).map (fun result => Term.integer result.toInt) =
      contract (.arith op (.integer x.toInt) (.integer y.toInt)) := by
  let result := arithmetic op x.toInt y.toInt
  have guard : -9223372036854775807 - 1 ≤ result ∧ result ≤ 9223372036854775807 ↔ signed64 result := by
    unfold signed64
    omega
  simp only [foldArithmetic,wideArithmetic_exact,contract]
  change (if -9223372036854775807 - 1 ≤ result ∧ result ≤ 9223372036854775807
    then some (Int64.ofInt result) else none).map (fun x => Term.integer x.toInt) =
      if signed64 result then some (.integer result) else none
  by_cases within : signed64 result
  · simp only [ite_eq_left within,ite_eq_left (guard.mpr within),Option.map_some,
      Int64.toInt_ofInt_of_le within.1 within.2]
  · simp only [ite_eq_right within,ite_eq_right (fun allowed => within (guard.mp allowed)),Option.map_none]

theorem foldArithmetic_preserves (op : Arith) (x y : Int64)
    (typed : LoanTyping.HasType env loans ctx mode (.arith op (.integer x.toInt) (.integer y.toInt)) type)
    (folded : foldArithmetic op x y = some output) :
    LoanTyping.HasType env [] ctx true (.integer output.toInt) type := by
  have specified := foldArithmetic_refines op x y
  rw [folded,Option.map_some] at specified
  exact LoanTyping.value_root_ghost_preservation (contract_sound specified.symm) typed

end Jihoo.NativeKernel.Environment.ValueReduction
