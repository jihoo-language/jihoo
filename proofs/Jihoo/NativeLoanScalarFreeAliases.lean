import Jihoo.NativeLoanBorrowedBudget

/-! Derive the physical returned-owner alias from the original restored
quantity check. A scalar return cannot discharge a different owner instead. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control}

theorem projectRaw_scalar_free_alias
    (checked : projectRaw (fuel+3) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.free (.var index) (.var 1))))) = some control) :
    index = 0 ∨ index = owner+2 := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,sourceTyped,readTyped,
    binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,same⟩ := dependent_raw_project_contract checked
  rw [restore_body_is_alias] at restProjected
  simp only [Term.rename,renameArgs,Op.binders,liftRenaming] at restProjected
  change projectRaw (fuel+2) env loans (⟨first,false⟩ :: ctx)
    (.free (.var (Jihoo.Quantity.openOwner (owner+1) index)) (.var 0)) = some rest at restProjected
  obtain ⟨binding,tailControl,found,relevant,tailProjected,rfl⟩ := projectRaw_free_variable restProjected
  have projectedVariable : projectRaw (fuel+1) env loans (⟨first,false⟩ :: ctx) (.var 0) = some (.use 0) := rfl
  have tailSame : tailControl = .use 0 := Option.some.inj (tailProjected.symm.trans projectedVariable)
  rw [tailSame] at restOne
  have ownerOne := Jihoo.Quantity.scopes_outer (modes := [mode]) restOne
  by_cases sameIndex : Jihoo.Quantity.openOwner (owner+1) index = owner+1
  · cases index with
    | zero => exact Or.inl rfl
    | succ index =>
        simp only [Jihoo.Quantity.openOwner] at sameIndex
        exact Or.inr (by omega)
  · simp [Control.demand,sameIndex] at ownerOne

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
