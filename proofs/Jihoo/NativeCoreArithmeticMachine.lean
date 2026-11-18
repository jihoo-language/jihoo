import Jihoo.NativeLoanComputationPreservation
import Jihoo.NativeNumeralForward

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

/-! Core.collect adds an unsigned literal only after a successful tick. The
cancellation loop can also subtract a collected amount with an explicit guard.
Each occurrence of a shared node that contributes a literal consumes credit. -/
namespace Jihoo.NativeKernel.NativeConstantAccumulator

inductive Update where
  | literal (value : UInt64)
  | cancel (value : BitVec 128)

def literalVisits : List Update → Nat
  | [] => 0
  | .literal _ :: rest => (literalVisits rest).succ
  | .cancel _ :: rest => literalVisits rest

def runNatural : List Update → Nat → Option Nat
  | [], constant => some constant
  | .literal value :: rest, constant => runNatural rest (constant + value.toNat)
  | .cancel value :: rest, constant =>
      if value.toNat ≤ constant then runNatural rest (constant - value.toNat) else none

def runWord : List Update → BitVec 128 → Option (BitVec 128)
  | [], constant => some constant
  | .literal value :: rest, constant => runWord rest (constant + BitVec.ofNat 128 value.toNat)
  | .cancel value :: rest, constant =>
      if value ≤ constant then runWord rest (constant - value) else none

/-- Every intermediate addition is exact. A guarded cancellation only reduces
the accumulator and does not need to consume any of the literal visit budget. -/
theorem runWord_exact (updates : List Update) (constant : BitVec 128)
    (budget : constant.toNat + literalVisits updates * (2^64 - 1) < 2^128) :
    (runWord updates constant).map BitVec.toNat = runNatural updates constant.toNat := by
  induction updates generalizing constant with
  | nil => rfl
  | cons update updates ih =>
      cases update with
      | literal value =>
          have width := value.toNat_lt
          have widened : (BitVec.ofNat 128 value.toNat).toNat = value.toNat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          simp only [literalVisits,Nat.succ_mul] at budget
          have fits : constant.toNat + (BitVec.ofNat 128 value.toNat).toNat < 2^128 := by
            rw [widened]
            omega
          have added := (BitVec.toNat_add_of_lt fits).trans (congrArg (constant.toNat + ·) widened)
          have remaining : (constant + BitVec.ofNat 128 value.toNat).toNat +
              literalVisits updates * (2^64 - 1) < 2^128 := by
            rw [added]
            omega
          simpa only [runWord,runNatural,added] using ih _ remaining
      | cancel value =>
          by_cases allowed : value.toNat ≤ constant.toNat
          · have allowedWords : value ≤ constant := allowed
            have reduced := BitVec.toNat_sub_of_le allowedWords
            have remaining : (constant - value).toNat + literalVisits updates * (2^64 - 1) < 2^128 := by
              simp only [literalVisits] at budget
              rw [reduced]
              omega
            simpa only [runWord,runNatural,ite_eq_left allowed,ite_eq_left allowedWords,reduced]
              using ih _ remaining
          · have rejectedWords : ¬ value ≤ constant := allowed
            simp only [runWord,runNatural,ite_eq_right allowed,ite_eq_right rejectedWords,Option.map_none]

/-- The production STEPS ceiling suffices even at the maximal literal value. -/
theorem runWord_within_core_steps (updates : List Update) (ticks : literalVisits updates ≤ 1000000) :
    (runWord updates 0).map BitVec.toNat = runNatural updates 0 := by
  apply runWord_exact
  have zero : (0 : BitVec 128).toNat = 0 := by decide
  simpa only [zero,Nat.zero_add] using
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2^64 - 1) ticks)
      (by decide : 1000000 * (2^64 - 1) < 2^128)

theorem runNatural_bound (accepted : runNatural updates constant = some result) :
    result ≤ constant + literalVisits updates * (2^64 - 1) := by
  induction updates generalizing constant with
  | nil =>
      have same := Option.some.inj accepted
      simp [literalVisits,← same]
  | cons update updates ih =>
      cases update with
      | literal value =>
          have child := ih accepted
          have width := value.toNat_lt
          simp only [literalVisits,Nat.succ_mul]
          omega
      | cancel value =>
          unfold runNatural at accepted
          split at accepted
          · have child := ih accepted
            simp only [literalVisits]
            omega
          · contradiction

/-- The unfolded syntax of Core.natural_sum. Equal halves in the actual arena
share a node. The other half is computed only when it is distinct. -/
def naturalSum (value : Nat) : Term :=
  if value < 2^64 then .natural value
  else
    let half := value / 2
    let left := naturalSum half
    let right := if value - half = half then left else naturalSum (value - half)
    .uadd left right
termination_by value
decreasing_by all_goals omega

/-- All leaves are well-typed U64 literals. The represented mathematical
natural is exact even when the total is wider than U64. -/
theorem naturalSum_correct (value : Nat) :
    EnvironmentDelta.NumeralForward.Represents (naturalSum value) value ∧
      Environment.LoanTyping.HasType env loans ctx mode (naturalSum value) .u64 := by
  rw [naturalSum]
  split
  · rename_i fits
    exact ⟨.natural value,.natural fits⟩
  · dsimp only
    have left := naturalSum_correct (env := env) (loans := loans) (ctx := ctx) (mode := mode) (value / 2)
    split
    · rename_i even
      have same : value / 2 + value / 2 = value := by omega
      have represented := EnvironmentDelta.NumeralForward.Represents.add left.1 left.1
      rw [same] at represented
      exact ⟨represented,.uadd left.2 left.2⟩
    · have right := naturalSum_correct (env := env) (loans := loans) (ctx := ctx) (mode := mode)
        (value - value / 2)
      have same : value / 2 + (value - value / 2) = value := by omega
      have represented := EnvironmentDelta.NumeralForward.Represents.add left.1 right.1
      rw [same] at represented
      exact ⟨represented,.uadd left.2 right.2⟩
termination_by value
decreasing_by all_goals omega

theorem naturalSum_depth (value levels : Nat) (bound : value ≤ (2^64 - 1) * 2^levels) :
    Conversion.treeDepth (naturalSum value) ≤ levels+1 := by
  induction levels generalizing value with
  | zero =>
      simp only [Nat.pow_zero,Nat.mul_one] at bound
      rw [naturalSum,ite_eq_left (by omega)]
      simp [Term.natural,Conversion.treeDepth]
  | succ levels ih =>
      rw [naturalSum]
      split
      · simp [Term.natural,Conversion.treeDepth]
      · have twice : value ≤ ((2^64 - 1) * 2^levels) * 2 := by
          simpa only [Nat.pow_succ,Nat.mul_assoc] using bound
        have left := ih (value / 2) (by omega)
        have right := ih (value - value / 2) (by omega)
        dsimp only
        split
        · have bounded := Nat.max_le.mpr ⟨left,left⟩
          simp only [Term.uadd,Conversion.treeDepth,List.map_cons,List.map_nil,
            List.foldl_cons,List.foldl_nil,Nat.zero_max]
          omega
        · have bounded := Nat.max_le.mpr ⟨left,right⟩
          simp only [Term.uadd,Conversion.treeDepth,List.map_cons,List.map_nil,
            List.foldl_cons,List.foldl_nil,Nat.zero_max]
          omega

/-- A successful accumulator trace within the Core tick budget needs at most
twenty recursive edges when reconstructed by Core.natural_sum. -/
theorem collected_naturalSum_depth (ticks : literalVisits updates ≤ 1000000)
    (accepted : runWord updates 0 = some constant) :
    Conversion.treeDepth (naturalSum constant.toNat) ≤ 21 := by
  have exactRun := runWord_within_core_steps updates ticks
  rw [accepted,Option.map_some] at exactRun
  have bound := runNatural_bound exactRun.symm
  simp only [Nat.zero_add] at bound
  have visits : literalVisits updates ≤ 2^20 := Nat.le_trans ticks (by decide)
  apply naturalSum_depth constant.toNat 20
  rw [Nat.mul_comm]
  exact Nat.le_trans bound (Nat.mul_le_mul_right (2^64 - 1) visits)

end Jihoo.NativeKernel.NativeConstantAccumulator
