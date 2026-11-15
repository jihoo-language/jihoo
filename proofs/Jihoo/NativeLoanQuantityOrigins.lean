import Jihoo.NativeLoanQuantity
import Jihoo.NativeLoanFunctionInversion

/-! Authentic source evidence of the loan quantity gate. The specialized
reader and restored continuation typing are recovered from the actual complete
checker trace; arbitrary callback typings and code substitution are not inputs.
Original source scope comes from its independent executable scope guard. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes ResourceReplay
variable {control : Control}

theorem infer_dependent_origin
    (checked : Checker.infer (fuel+1) env loans ctx false
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some outside) :
    ∃ ownerType,
      Checker.expose fuel env (Checker.infer fuel env loans ctx false (.var owner)) = some ownerType ∧
      Checker.ownedHead env ownerType = true ∧
      Checker.dependentLend (fun stack mode expression => Checker.infer fuel env stack ctx mode expression)
        (Checker.binder fuel env loans ctx) fuel env loans ctx false owner ownerType domain readerBody first again body =
          some outside := by
  simp only [Checker.infer] at checked
  cases ownerInferred : Checker.expose fuel env (Checker.infer fuel env loans ctx false (.var owner)) with
  | none => simp [ownerInferred] at checked
  | some ownerType =>
      simp only [ownerInferred] at checked
      split at checked
      · rename_i owned
        exact ⟨ownerType,rfl,owned,checked⟩
      · contradiction

theorem dependent_checker_original_types
    (checked : Checker.dependentLend
      (fun stack mode expression => Checker.infer fuel env stack ctx mode expression)
      (Checker.binder fuel env loans ctx) fuel env loans ctx false owner ownerType domain readerBody first again body =
        some outside) :
    HasType env (Loans.enter ctx.length owner loans) ctx false (Lending.read (.var owner) readerBody) first ∧
      ∃ sort result, Binder env loans ctx false first sort ∧
        HasType env loans (⟨first,false⟩ :: ctx) false
          (body.subst (single ((Term.var owner).rename Nat.succ))) result := by
  unfold Checker.dependentLend at checked
  obtain ⟨sort,domainInferred,checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · rename_i domainChecked
    obtain ⟨resultType,readExposed,checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · rename_i readChecked
      obtain ⟨restored,restoreInferred,checked⟩ := Option.bind_eq_some_iff.mp checked
      obtain ⟨restoreNormal,restoreNormalized,checked⟩ := Option.bind_eq_some_iff.mp checked
      split at checked
      · rename_i restoreDomain result restoreShape
        split at checked
        · rename_i restoreChecked
          obtain ⟨readActual,readInferred,readConverted⟩ := Checker.expose_elim readExposed
          have readerTyped := ((Checker.infer_sound readInferred).convert readConverted).convert
            (Conversion.equal_sound readChecked.2.1).symm
          have continuationTyped := (Checker.infer_sound restoreInferred).convert (Conversion.equal_sound restoreChecked)
          obtain ⟨firstSort,bodyType,binder,bodyTyped,_⟩ := continuationTyped.lamView
          exact ⟨readerTyped,firstSort,bodyType,binder,bodyTyped⟩
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem infer_dependent_original_types
    (checked : Checker.infer fuel env loans ctx false
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some outside) :
    HasType env (Loans.enter ctx.length owner loans) ctx false (Lending.read (.var owner) readerBody) first ∧
      ∃ sort result, Binder env loans ctx false first sort ∧
        HasType env loans (⟨first,false⟩ :: ctx) false
          (body.subst (single ((Term.var owner).rename Nat.succ))) result := by
  cases fuel with
  | zero => simp [Checker.infer] at checked
  | succ fuel => exact dependent_checker_original_types (infer_dependent_origin checked).choose_spec.2.2

theorem project_origin (checked : project fuel env loans ctx term = some control) :
    projectRaw fuel env loans ctx term = some control := by
  unfold project at checked
  split at checked
  · contradiction
  · obtain ⟨candidate,projected,checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · cases checked; exact projected
    · contradiction

theorem projectRaw_lend_origin
    (checked : projectRaw (fuel+1) env loans ctx (.lend owner reader continuation) = some control) :
    projectLend (projectRaw fuel env) fuel env loans ctx owner reader continuation = some control := by
  simpa [projectRaw,Term.lend,Op.arity] using checked

theorem projectLend_dependent_origin
    (checked : projectLend visit fuel env loans ctx (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)) = some control) :
    ∃ outside ownerType reader mode rest,
      Checker.infer fuel env loans ctx false
        (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some outside ∧
      Checker.expose fuel env (Checker.infer fuel env loans ctx false (.var owner)) = some ownerType ∧
      Checker.ownedHead env ownerType = true ∧
      (Term.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))).Scoped ctx.length ∧
      (Lending.read (.var owner) readerBody).Scoped ctx.length ∧
      (body.subst (single ((Term.var owner).rename Nat.succ))).Scoped (ctx.length+1) ∧
      visit (Loans.enter ctx.length owner loans) ctx (Lending.read (.var owner) readerBody) = some reader ∧
      resolve fuel env loans ctx false first = some mode ∧
      visit loans (⟨first,false⟩ :: ctx) (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      dependentControl owner mode reader rest = some control := by
  unfold projectLend at checked
  split at checked
  · contradiction
  · rename_i scopeGuard
    have originalScope : NativeKernel.scopeCheck ctx.length
        (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = true := by
      simpa using scopeGuard
    obtain ⟨outside,inferred,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨ownerType,ownerInferred,checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · contradiction
    · rename_i ownerGuard
      have owned : Checker.ownedHead env ownerType = true := by simpa using ownerGuard
      simp only at checked
      split at checked
      · contradiction
      · rename_i scopesGuard
        have scopes : NativeKernel.scopeCheck ctx.length (Lending.read (.var owner) readerBody) = true ∧
            NativeKernel.scopeCheck (ctx.length+1)
              (body.subst (single ((Term.var owner).rename Nat.succ))) = true := by
          simpa using Bool.eq_false_iff.mpr scopesGuard
        obtain ⟨reader,readProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
        obtain ⟨mode,resolved,checked⟩ := Option.bind_eq_some_iff.mp checked
        obtain ⟨rest,restProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
        exact ⟨outside,ownerType,reader,mode,rest,inferred,ownerInferred,owned,
          NativeKernel.scopeCheck_sound originalScope,NativeKernel.scopeCheck_sound scopes.1,
          NativeKernel.scopeCheck_sound scopes.2,readProjected,resolved,restProjected,checked⟩

/-- A single actual resource projection supplies the original typed Lend,
the typed entered reader and restored body, both exact recursive projections,
the first-result mode and the zero/one owner contracts. No function/body safety
or scope facts are supplied by a caller. -/
theorem dependent_project_contract
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control) :
    ∃ outside sort result reader mode rest,
      (Term.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))).Scoped ctx.length ∧
      (Lending.read (.var owner) readerBody).Scoped ctx.length ∧
      (body.subst (single ((Term.var owner).rename Nat.succ))).Scoped (ctx.length+1) ∧
      ResourceModes.ContextFormed env loans ctx ∧ ControlScoped ctx.length control ∧
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
    projectLend_dependent_origin (projectRaw_lend_origin (project_origin checked))
  obtain ⟨readerTyped,sort,result,binder,bodyTyped⟩ := infer_dependent_original_types inferred
  obtain ⟨same,readerZero,restOne⟩ := dependentControl_origin guarded
  have outer := project_scope checked
  exact ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,outer.2.1,outer.2.2,
    Checker.infer_sound inferred,readerTyped,binder,bodyTyped,resolve_sound resolved,
    readProjected,restProjected,readerZero,restOne,same⟩

theorem dependent_project_finished
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control)
    (run : Finishes control events) : events.count owner = 1 := by
  obtain ⟨outside,ownerType,reader,mode,rest,inferred,ownerInferred,owned,originalScope,readScope,restScope,
      readProjected,resolved,restProjected,guarded⟩ :=
    projectLend_dependent_origin (projectRaw_lend_origin (project_origin checked))
  exact dependent_finished guarded run

theorem dependent_project_prefix
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control)
    (run : Prefix control events) : events.count owner ≤ 1 := by
  obtain ⟨outside,ownerType,reader,mode,rest,inferred,ownerInferred,owned,originalScope,readScope,restScope,
      readProjected,resolved,restProjected,guarded⟩ :=
    projectLend_dependent_origin (projectRaw_lend_origin (project_origin checked))
  exact dependent_prefix guarded run

/-- A first result actually classified as an owner has its own fresh linear
obligation, independently of the restored original owner's obligation. -/
theorem dependent_project_owned_first
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control)
    (ownedFirst : firstOwned fuel env first = true) :
    ∃ reader rest,
      projectRaw fuel env (Loans.enter ctx.length owner loans) ctx (Lending.read (.var owner) readerBody) = some reader ∧
      projectRaw fuel env loans (⟨first,false⟩ :: ctx)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      reader.demand owner = some 0 ∧ rest.demand 0 = some 1 ∧ rest.demand (owner+1) = some 1 ∧
      (∀ events, Finishes rest events → events.count 0 = 1 ∧ events.count (owner+1) = 1) ∧
      (∀ events, Prefix rest events → events.count 0 ≤ 1 ∧ events.count (owner+1) ≤ 1) := by
  obtain ⟨outside,ownerType,reader,mode,rest,inferred,ownerInferred,owned,originalScope,readScope,restScope,
      readProjected,resolved,restProjected,guarded⟩ :=
    projectLend_dependent_origin (projectRaw_lend_origin (project_origin checked))
  have sameMode := firstOwned_resolve_linear ownedFirst resolved
  subst mode
  obtain ⟨same,readerZero,restOne⟩ := dependentControl_origin guarded
  have firstOne : rest.demand 0 = some 1 := (NativeQuantity.demand_localScopes _ restOne).1
  have ownerOne : rest.demand (owner+1) = some 1 :=
    Jihoo.Quantity.scopes_outer (modes := [.linear]) restOne
  exact ⟨reader,rest,readProjected,restProjected,readerZero,firstOne,ownerOne,
    fun events run => ⟨run.count_eq firstOne,run.count_eq ownerOne⟩,
    fun events run => ⟨run.count_le firstOne,run.count_le ownerOne⟩⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
