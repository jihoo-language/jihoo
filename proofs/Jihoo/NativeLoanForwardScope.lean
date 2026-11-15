import Jihoo.NativeFamilyForwardScope
import Jihoo.NativeLendRawConversion
import Jihoo.NativeScopeCheck
import Jihoo.NativeFamilyIotaSearch

/-! Explicit checked input scope survives every genuine raw Lend/family/delta
forward path and the installed bounded family normalizer. Scope is never
inferred from typing, source conversion or successful normalization alone. -/
namespace Jihoo.NativeKernel.Environment.RawLend

theorem Forward.scope (closed : EnvironmentDelta.Basis.Closed env) (step : Forward env term result) :
    ∀ depth,term.Scoped depth → result.Scoped depth := by
  induction step using Forward.rec
    (motive_2 := fun first second _ => NativeKernel.Conversion.ListRel
      (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) with
  | old step => exact step.scope closed
  | lend owner reader continuation =>
    intro depth scope
    have ownerScope : owner.Scoped depth := by simpa only [Op.binders,Nat.add_zero] using scope.child (index := 0) rfl
    have readerScope : reader.Scoped depth := by simpa only [Op.binders,Nat.add_zero] using scope.child (index := 1) rfl
    have continuationScope : continuation.Scoped depth := by simpa only [Op.binders,Nat.add_zero] using scope.child (index := 2) rfl
    have borrowedOwner : (Term.borrow owner).Scoped depth := by
      apply Term.Scoped.nonbinding (by intro index; rfl)
      intro child member
      have same := List.mem_singleton.mp member
      subst child
      exact ownerScope
    exact (continuationScope.application (readerScope.application borrowedOwner)).application ownerScope
  | refl => intro depth scope; exact scope
  | trans _ _ first second => intro depth scope; exact second depth (first depth scope)
  | node op related ih => intro depth scope; exact scope.node_transport ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem Forward.scopeCheck (closed : EnvironmentDelta.Basis.Closed env) (step : Forward env term result)
    (checked : NativeKernel.scopeCheck depth term = true) : NativeKernel.scopeCheck depth result = true :=
  scopeCheck_complete (step.scope closed depth (scopeCheck_sound checked))

end Jihoo.NativeKernel.Environment.RawLend

namespace Jihoo.NativeKernel.Environment.FamilyIota.Search

theorem normalize?_scope (closed : EnvironmentDelta.Basis.Closed env)
    (accepted : normalize? env fuel term = some result) (scope : term.Scoped depth) : result.Scoped depth :=
  (normalize?_forward accepted).scope closed depth scope

theorem normalize?_scopeCheck (closed : EnvironmentDelta.Basis.Closed env)
    (accepted : normalize? env fuel term = some result) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth result = true := scopeCheck_complete (normalize?_scope closed accepted (scopeCheck_sound checked))

theorem normalize_scope (closed : EnvironmentDelta.Basis.Closed env) (scope : term.Scoped depth) :
    (normalize env fuel term).Scoped depth := by
  unfold normalize
  cases accepted : normalize? env fuel term with
  | none => exact scope
  | some result => exact normalize?_scope closed accepted scope

theorem normalize_scopeCheck (closed : EnvironmentDelta.Basis.Closed env) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth (normalize env fuel term) = true :=
  scopeCheck_complete (normalize_scope closed (scopeCheck_sound checked))

end Jihoo.NativeKernel.Environment.FamilyIota.Search
