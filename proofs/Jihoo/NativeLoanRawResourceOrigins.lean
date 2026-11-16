import Jihoo.NativeBindingMachineLendResources

/-! Internal resource receipts are recovered from the actual recursive query.
They retain original scope and full checker derivations. This is not a new
admission gate; full function projection supplies these internal receipts. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes ResourceReplay
variable {control : Control}

theorem dependent_raw_project_contract
    (checked : projectRaw (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control) :
    ∃ outside sort result reader mode rest,
      (Term.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))).Scoped ctx.length ∧
      (Lending.read (.var owner) readerBody).Scoped ctx.length ∧
      (body.subst (single ((Term.var owner).rename Nat.succ))).Scoped (ctx.length+1) ∧
      HasType env loans ctx false
        (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) outside ∧
      HasType env (Loans.enter ctx.length owner loans) ctx false (Lending.read (.var owner) readerBody) first ∧
      Binder env loans ctx false first sort ∧
      HasType env loans (⟨first,false⟩ :: ctx) false
        (body.subst (single ((Term.var owner).rename Nat.succ))) result ∧
      ResourceModes.Resolved env loans ctx false first mode ∧
      projectRaw fuel env (Loans.enter ctx.length owner loans) ctx (Lending.read (.var owner) readerBody) = some reader ∧
      projectRaw fuel env loans (⟨first,false⟩ :: ctx)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      reader.demand owner = some 0 ∧ (Control.scope mode rest).demand owner = some 1 ∧
      control = .seq reader (.scope mode rest) := by
  obtain ⟨outside,ownerType,reader,mode,rest,inferred,ownerInferred,owned,originalScope,readScope,restScope,
      readProjected,resolved,restProjected,guarded⟩ :=
    projectLend_dependent_origin (projectRaw_lend_origin checked)
  obtain ⟨readerTyped,sort,result,binder,bodyTyped⟩ := infer_dependent_original_types inferred
  obtain ⟨same,readerZero,restOne⟩ := dependentControl_origin guarded
  exact ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,
    Checker.infer_sound inferred,readerTyped,binder,bodyTyped,resolve_sound resolved,
    readProjected,restProjected,readerZero,restOne,same⟩

theorem raw_lend_free_tail_zero
    (selected : index = 0 ∨ index = owner+2)
    (checked : projectRaw (fuel+3) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.free (.var index) tail)))) = some control) :
    ∃ rest,
      projectRaw (fuel+1) env loans (⟨first,false⟩ :: ctx)
        (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      rest.demand (owner+1) = some 0 ∧
      (∀ events, Prefix rest events → events.count (owner+1) = 0) := by
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := dependent_raw_project_contract checked
  have ownerMapping : (Term.var index).subst (single ((Term.var owner).rename Nat.succ)) =
      .var (owner+1) := by
    rcases selected with rfl | rfl
    · exact restored_returned_owner
    · exact restored_original_owner
  rw [subst_free] at restProjected
  rw [ownerMapping] at restProjected
  obtain ⟨binding,tailControl,found,relevant,tailProjected,rfl⟩ := projectRaw_free_variable restProjected
  have residual : tailControl.demand (owner+1) = some 0 := by
    have ownerOne := Jihoo.Quantity.scopes_outer (modes := [mode]) restOne
    simp only [List.length_cons,List.length_nil] at ownerOne
    rw [Control.demand,Control.demand,ite_eq_left rfl] at ownerOne
    change ((tailControl.demand (owner+1)).bind (fun n => some (n+0))).bind
      (fun n => some (1+n)) = some 1 at ownerOne
    cases demand : tailControl.demand (owner+1) with
    | none => simp [demand] at ownerOne
    | some count =>
        simp only [demand,Option.bind_some,Option.some.injEq] at ownerOne
        have zero : count = 0 := by omega
        exact congrArg some zero
  refine ⟨tailControl,tailProjected,residual,?_⟩
  intro events run
  have bound := run.count_le residual
  omega

/-- Full lambda projection contains the exact original body query. -/
theorem projectRaw_lambda_body
    (checked : projectRaw (fuel+1) env loans ctx (.lam false domain body) = some control) :
    ∃ mode bodyControl,
      projectRaw fuel env loans (⟨domain,false⟩ :: ctx) body = some bodyControl ∧
      control = .closure (.scope mode (functionTail body bodyControl)) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  split at checked
  · contradiction
  · obtain ⟨mode,resolved,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyControl,projected,same⟩ := Option.bind_eq_some_iff.mp checked
    exact ⟨mode,bodyControl,projected,Option.some.inj same.symm⟩

/-- One original call query contains the exact original lambda body query,
under its own parameter binder. No separate function/body check is assumed. -/
theorem projectRaw_single_lambda_call_body
    (checked : projectRaw (fuel+3) env loans ctx (.app (.lam false domain body) argument) = some control) :
    ∃ bodyControl, projectRaw (fuel+2) env loans (⟨domain,false⟩ :: ctx) body = some bodyControl := by
  simp only [projectRaw,splitSpine,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨⟨head,supplied⟩,splitSpineChecked,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases splitSpineChecked
  obtain ⟨⟨entries,result⟩,replayed,checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · contradiction
  · obtain ⟨opened,openedProof,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨runtime,runtimeProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyControl,bodyProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    simp only [openHead] at openedProof
    split at openedProof
    · contradiction
    · obtain ⟨mode,resolved,openedProof⟩ := Option.bind_eq_some_iff.mp openedProof
      have identity : opened = ⟨⟨domain,false⟩ :: ctx,[mode],body⟩ := (Option.some.inj openedProof).symm
      subst opened
      exact ⟨bodyControl,bodyProjected⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
