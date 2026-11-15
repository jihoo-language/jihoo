import Jihoo.NativeFamilyIotaNormalizer

/-! Installed bounded family, delta and ACU search. Successful answers always
carry actual enlarged equations; the explicit fuel and size budget bound search. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Search
abbrev Conv := Extended.Conv
abbrev Forward := Extended.Forward

def normalize? (env : Environment) (fuel : Nat) (term : Term) : Option Term :=
  Extended.normalize? env 200000 (min fuel 128) term

def normalize (env : Environment) (fuel : Nat) (term : Term) : Term :=
  (normalize? env fuel term).getD term

def equal (env : Environment) (fuel : Nat) (first second : Term) : Bool :=
  Extended.equal env 200000 (min fuel 128) first second

theorem normalize?_forward (accepted : normalize? env fuel term = some result) :
    Forward env term result := Extended.normalize?_forward accepted

theorem normalize?_sound (accepted : normalize? env fuel term = some result) :
    Conv env term result := Extended.normalize?_sound accepted

theorem normalize_sound (env : Environment) (fuel : Nat) (term : Term) :
    Conv env term (normalize env fuel term) := by
  unfold normalize
  cases accepted : normalize? env fuel term with
  | none => exact .refl _
  | some result => exact normalize?_sound accepted

theorem equal_sound (accepted : equal env fuel first second = true) :
    Conv env first second := Extended.equal_sound accepted

end Jihoo.NativeKernel.Environment.FamilyIota.Search
