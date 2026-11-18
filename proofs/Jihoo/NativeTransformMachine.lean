import Jihoo.NativeTransform

/-! The integer boundaries of `Core.transform`'s variable and binder cases.
Here the operands are the machine words used by that implementation, and the
widened sum is interpreted as an integer. These theorems connect the scalar
cases to the partial renaming model. They do not execute the Jihoo source or
account for graph traversal, failure state, or allocation order. -/
namespace Jihoo.NativeKernel.NativeTransform

/-- The implementation widens both operands to i128 before adding. -/
theorem variable_sum_fits_i128 (index : UInt32) (delta : Int64) :
    -(2 ^ 127 : Int) ≤ (index.toNat : Int) + delta.toInt ∧
      (index.toNat : Int) + delta.toInt < 2 ^ 127 := by
  have low := delta.le_toInt
  have high := delta.toInt_lt
  have bound := index.toNat_lt
  constructor <;> omega

def shiftVariable (index cutoff : UInt32) (delta : Int64) : Option UInt32 :=
  if index < cutoff then some index else
    let next := (index.toNat : Int) + delta.toInt
    if (cutoff.toNat : Int) ≤ next ∧ next < (indexLimit : Int) then
      some (UInt32.ofNat next.toNat)
    else none

/-- Success and rejection agree with partial renaming followed by the u32
output check, including the entire signed range of the shift amount. -/
theorem shiftVariable_refines (index cutoff : UInt32) (delta : Int64) :
    (shiftVariable index cutoff delta).map UInt32.toNat =
      (shiftIndex delta.toInt cutoff.toNat index.toNat).filter
        (fun next => decide (next < indexLimit)) := by
  by_cases bound : index.toNat < cutoff.toNat
  · have fits : index.toNat < indexLimit := index.toNat_lt
    by_cases positive : 0 ≤ delta.toInt <;>
      simp [shiftVariable, UInt32.lt_iff_toNat_lt, bound, shiftIndex, positive,
        PartialRenaming.raiseIndex, PartialRenaming.lowerIndex, Option.filter_some, fits]
  · by_cases positive : 0 ≤ delta.toInt
    · have low : (cutoff.toNat : Int) ≤ (index.toNat : Int) + delta.toInt := by omega
      have natural : ((index.toNat : Int) + delta.toInt).toNat =
          index.toNat + delta.toInt.toNat := by omega
      have high : (index.toNat : Int) + delta.toInt < (indexLimit : Int) ↔
          index.toNat + delta.toInt.toNat < indexLimit := by omega
      by_cases fits : index.toNat + delta.toInt.toNat < indexLimit
      · have narrowed := Nat.mod_eq_of_lt (show _ < 4294967296 from fits)
        simp [-Int64.toNat_toInt, shiftVariable, UInt32.lt_iff_toNat_lt, bound, shiftIndex, positive,
          PartialRenaming.raiseIndex, low, high, natural, Option.filter_some, fits, narrowed]
      · simp [-Int64.toNat_toInt, shiftVariable, UInt32.lt_iff_toNat_lt, bound, shiftIndex, positive,
          PartialRenaming.raiseIndex, low, high, Option.filter_some, fits]
    · have low : (cutoff.toNat : Int) ≤ (index.toNat : Int) + delta.toInt ↔
          cutoff.toNat + (-delta.toInt).toNat ≤ index.toNat := by omega
      have high : (index.toNat : Int) + delta.toInt < (indexLimit : Int) := by
        have fits : index.toNat < indexLimit := index.toNat_lt
        omega
      by_cases kept : cutoff.toNat + (-delta.toInt).toNat ≤ index.toNat
      · have natural : ((index.toNat : Int) + delta.toInt).toNat =
            index.toNat - (-delta.toInt).toNat := by omega
        have fits : index.toNat - (-delta.toInt).toNat < indexLimit :=
          Nat.lt_of_le_of_lt (Nat.sub_le ..) index.toNat_lt
        have narrowed := UInt32.toNat_ofNat_of_lt' (show _ < UInt32.size from fits)
        simp [shiftVariable, UInt32.lt_iff_toNat_lt, bound, shiftIndex, positive,
          PartialRenaming.lowerIndex, low, high, natural, kept, Option.filter_some, fits, narrowed]
      · simp [shiftVariable, UInt32.lt_iff_toNat_lt, bound, shiftIndex, positive,
          PartialRenaming.lowerIndex, low, kept]

def binderCutoff (cutoff : UInt32) : Option UInt32 :=
  if cutoff.toNat + 1 < indexLimit then some (cutoff + 1) else none

theorem binderCutoff_refines (cutoff : UInt32) :
    (binderCutoff cutoff).map UInt32.toNat =
      if cutoff.toNat + 1 < indexLimit then some (cutoff.toNat + 1) else none := by
  unfold binderCutoff
  split
  · rename_i fits
    simp only [Option.map_some, UInt32.toNat_add, UInt32.toNat_one]
    rw [Nat.mod_eq_of_lt (show _ < 2 ^ 32 from fits)]
  · rfl

end Jihoo.NativeKernel.NativeTransform
