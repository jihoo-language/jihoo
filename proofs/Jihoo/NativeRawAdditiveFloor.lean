import Jihoo.NativeLendRawConversion
import Jihoo.NativeNumeralForward

/-! Genuine raw reduction cannot remove a positive literal summand at the
head of a sum. Other summands may be unresolved dependent computations. -/
namespace Jihoo.NativeKernel.Environment.RawLend
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta.NumeralForward (Represents)

def literalFloor : Term → Nat
  | .var _ => 0
  | .node op kids => match op with
    | .natural value => match kids with
      | [] => value
      | _ :: _ => 0
    | .uadd => match kids with
      | [left, right] => literalFloor left + literalFloor right
      | _ => 0
    | _ => 0

private theorem literalFloor_represented (represented : Represents term value) :
    literalFloor term = value := by
  induction represented with
  | natural => rfl
  | add left right ihLeft ihRight =>
    change literalFloor _ + literalFloor _ = _
    rw [ihLeft, ihRight]

private theorem literalFloor_node
    (kids : ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) :
    literalFloor (.node op xs) ≤ literalFloor (.node op ys) := by
  cases op <;> first | exact Nat.le_refl _ | skip
  case natural =>
    cases kids <;> exact Nat.le_refl _
  case uadd =>
    cases kids with
    | nil => exact Nat.le_refl _
    | cons left rest =>
      cases rest with
      | nil => exact Nat.le_refl _
      | cons right rest =>
        cases rest with
        | nil => exact Nat.add_le_add left right
        | cons => exact Nat.le_refl _

private theorem literalFloor_arithmetic (steps : ACU.ArithmeticRed first second) :
    literalFloor first ≤ literalFloor second := by
  induction steps using ACU.ArithmeticRed.rec
    (motive_2 := fun xs ys _ =>
      ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) with
  | refl => exact Nat.le_refl _
  | trans _ _ left right => exact Nat.le_trans left right
  | node op kids ih => exact literalFloor_node ih
  | assocRight a b c => simp only [literalFloor, Nat.add_assoc, Nat.le_refl]
  | assocLeft a b c => simp only [literalFloor, Nat.add_assoc, Nat.le_refl]
  | comm a b => exact Nat.le_of_eq (Nat.add_comm _ _)
  | zeroRight a => exact Nat.le_refl _
  | zeroLeft a => exact Nat.le_of_eq (Nat.zero_add _)
  | literalSplit n bound =>
    rw [literalFloor_represented (EnvironmentDelta.NumeralForward.replicate_ones n)]
    exact Nat.le_refl _
  | literalAdd m n bound => exact Nat.le_refl _
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

private theorem literalFloor_mixed (steps : ACU.MixedRed first second) :
    literalFloor first ≤ literalFloor second := by
  induction steps using ACU.MixedRed.rec
    (motive_2 := fun xs ys _ =>
      ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) with
  | refl => exact Nat.le_refl _
  | trans _ _ left right => exact Nat.le_trans left right
  | node op kids ih => exact literalFloor_node ih
  | arithmetic reduced => exact literalFloor_arithmetic reduced
  | compute reduced => cases reduced <;> exact Nat.zero_le _
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

private theorem literalFloor_delta (steps : EnvironmentDelta.Forward env first second) :
    literalFloor first ≤ literalFloor second := by
  induction steps using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ =>
      ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) with
  | refl => exact Nat.le_refl _
  | trans _ _ left right => exact Nat.le_trans left right
  | node op kids ih => exact literalFloor_node ih
  | acu reduced => exact literalFloor_mixed reduced
  | delta found => exact Nat.zero_le _
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

private theorem literalFloor_family (steps : FamilyIota.Extended.Forward env first second) :
    literalFloor first ≤ literalFloor second := by
  induction steps using FamilyIota.Extended.Forward.rec
    (motive_2 := fun xs ys _ =>
      ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) with
  | refl => exact Nat.le_refl _
  | trans _ _ left right => exact Nat.le_trans left right
  | node op kids ih => exact literalFloor_node ih
  | old reduced => exact literalFloor_delta reduced
  | iota root => cases root <;> exact Nat.zero_le _
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

theorem Forward.literalFloor_mono (steps : Forward env first second) :
    literalFloor first ≤ literalFloor second := by
  induction steps using Forward.rec
    (motive_2 := fun xs ys _ =>
      ListRel (fun first second => literalFloor first ≤ literalFloor second) xs ys) with
  | refl => exact Nat.le_refl _
  | trans _ _ left right => exact Nat.le_trans left right
  | node op kids ih => exact literalFloor_node ih
  | old reduced => exact literalFloor_family reduced
  | lend => exact Nat.zero_le _
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

theorem Forward.represents (steps : Forward env first second) :
    ∀ {value}, Represents first value → Represents second value := by
  induction steps using Forward.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys) with
  | old original => exact EnvironmentDelta.NumeralForward.family_forward_preserves original
  | lend => intro _ represented; cases represented
  | refl => intro _ represented; exact represented
  | trans _ _ before after => intro _ represented; exact after (before represented)
  | node op kids ih =>
    intro _ represented
    cases represented with
    | natural => cases ih; exact .natural _
    | add left right =>
      cases ih with
      | cons alongLeft rest => cases rest with
        | cons alongRight rest => cases rest; exact .add (alongLeft left) (alongRight right)
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

/-- Conversion to a numeral bounds all already observable literal summands,
regardless of the syntax or typability of the remaining summands. -/
theorem Conv.literalFloor_le_natural (converted : Conv env term (.natural value))
    (admissible : EnvironmentDelta.Admissible env) : literalFloor term ≤ value := by
  obtain ⟨common, left, right⟩ := converted.church_rosser admissible
  have floor := left.literalFloor_mono
  rwa [literalFloor_represented (right.represents (.natural value))] at floor

theorem Conv.successor_ne_zero (admissible : EnvironmentDelta.Admissible env) :
    ¬ Conv env (.uadd input (.natural 1)) (.natural 0) := by
  intro converted
  have bound := converted.literalFloor_le_natural admissible
  change literalFloor input + 1 ≤ 0 at bound
  omega

end Jihoo.NativeKernel.Environment.RawLend
