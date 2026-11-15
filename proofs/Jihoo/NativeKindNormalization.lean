import Jihoo.NativeCodeKinds

/-! First-order kinds are fixed by actual forward delta/ACU normalization in
any environment. This is a computation-shape theorem, not checker completeness. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
open Environment.Conversion

private theorem forward_u64_fixed (step : FamilyIota.Extended.Forward env .u64 output) : output = .u64 := by
  obtain ⟨children, shape, changes⟩ := FamilyIota.Extended.Forward.rigid_shape step rfl rfl
  cases changes
  exact shape

theorem Kind.forward_fixed (kind : Kind) (step : FamilyIota.Extended.Forward env kind.term output) :
    output = kind.term := by
  induction kind generalizing output with
  | type level =>
      obtain ⟨children, shape, changes⟩ := FamilyIota.Extended.Forward.rigid_shape step rfl rfl
      cases changes
      exact shape
  | index erased rest ih =>
      obtain ⟨children, shape, changes⟩ := FamilyIota.Extended.Forward.rigid_shape step rfl rfl
      cases changes with
      | cons domainChange remaining =>
          cases remaining with
          | cons resultChange remaining =>
              cases remaining
              have domain := forward_u64_fixed domainChange
              have result := ih resultChange
              simpa only [domain,result,Kind.term] using shape

theorem Kind.normalize?_fixed (kind : Kind)
    (accepted : Conversion.normalize? env fuel kind.term = some output) : output = kind.term :=
  kind.forward_fixed (Conversion.normalize?_forward accepted)

theorem Kind.normalize_fixed (kind : Kind) : Conversion.normalize env fuel kind.term = kind.term := by
  change (Conversion.normalize? env fuel kind.term).getD kind.term = kind.term
  cases found : Conversion.normalize? env fuel kind.term with
  | none => rfl
  | some output => exact kind.normalize?_fixed found

end Jihoo.NativeKernel.Environment.CodeKinds
