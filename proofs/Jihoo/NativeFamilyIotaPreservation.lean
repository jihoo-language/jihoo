import Jihoo.NativeFamilyIotaCasePreservation
import Jihoo.NativeFamilyIotaPropElimPreservation
import Jihoo.NativeFamilyIotaViewRecursivePreservation

/-! Every real family-iota contraction preserves the exact original dependent
type. No output typing, normalization naturality or enlarged confluence is assumed. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

theorem elim_preserves {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env ctx true (elimBody entry signature family motive branch cases values) type := by
  cases kind : entry.declaration.data with
  | false => exact prop_elim_preserves history found sigFound kind selected size typed
  | true => exact data_elim_preserves history found sigFound kind selected size typed

theorem contract_elim_preserves {family count : Nat}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (accepted : contract env (.node (.elim family count) args) = some result)
    (typed : HasType env ctx true (.node (.elim family count) args) type) :
    HasType env ctx true result type := by
  cases contract_sound accepted with
  | elim found signature selected count fields => exact elim_preserves history found signature selected fields typed

theorem view_preserves {recursion : Bool} {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (typed : HasType env ctx true
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    HasType env ctx true (viewBody recursion family entry.declaration.params motive branch cases values plans) type := by
  cases recursion with
  | false => exact view_preserves_one_level history found sigFound selected size planned typed
  | true => exact view_preserves_recursive history found sigFound selected size planned typed

/-- All concrete roots: indexed Prop/data Elim, parameterized Case,
one-level/recursive borrowed View, and pure Drop. -/
theorem Root.preserves (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (step : Root env term result) (typed : HasType env ctx true term type) :
    HasType env ctx true result type := by
  cases step with
  | elim found signature selected count fields => exact elim_preserves history found signature selected fields typed
  | caseOf found data signature selected count fields => exact case_preserves history found signature selected fields typed
  | view found boxed signature selected count fields bound planned =>
    exact view_preserves history found signature selected fields planned typed
  | drop => exact drop_preserves typed

/-- The actual executable contractor preserves every independently typed
input's original result type under authentic mixed declaration history. -/
theorem contract_preserves (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (accepted : contract env term = some result) (typed : HasType env ctx true term type) :
    HasType env ctx true result type :=
  (contract_sound accepted).preserves history typed

end Jihoo.NativeKernel.Environment.FamilyIota
