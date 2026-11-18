import Jihoo.NativeLoanComputationPreservation

/-! Load applies its continuation to an observed I64 and the unchanged owner.
Both arguments satisfy the actual dependent callback telescope, including
converted domains and the checked removal of both result binders. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def LoadView (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Term → Prop
  | .load owner _ _ continuation, type =>
      ∃ count valueDomain ownerDomain result normal outside,
        HasType env loans ctx mode owner (.buffer count) ∧
        HasType env loans ctx mode continuation (.pi false valueDomain (.pi false ownerDomain result)) ∧
        Conversion.Conv env valueDomain .i64 ∧
        Conversion.Conv env ownerDomain (.buffer (count.rename Nat.succ)) ∧
        Conversion.Conv env result normal ∧ PartialRenaming.shift (-2) 0 normal = some outside ∧
        Conversion.Conv env outside type
  | _, _ => True

private theorem LoadView.convert (view : LoadView env loans ctx mode term type)
    (converted : Conversion.Conv env type target) : LoadView env loans ctx mode term target := by
  fun_cases LoadView env loans ctx mode term type <;> simp only [LoadView] at view ⊢
  · obtain ⟨count,valueDomain,ownerDomain,result,normal,outside,owner,continuation,
      valueChecked,ownerChecked,resultChecked,lowered,requested⟩ := view
    exact ⟨count,valueDomain,ownerDomain,result,normal,outside,owner,continuation,
      valueChecked,ownerChecked,resultChecked,lowered,requested.trans converted⟩

private theorem load_view (typed : HasType env loans ctx mode term type) :
    LoadView env loans ctx mode term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term type _ => LoadView env loans ctx mode term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case load owner _ _ continuation valueDomain ownerDomain result lowered _ _ _ _ _ =>
      exact ⟨_,_,_,_,_,_,owner,continuation,
        valueDomain,ownerDomain,result,lowered,.refl _⟩
  case dataElim => split <;> trivial
  case convert _ converted ih => exact ih.convert converted

/-- Running a two-binder Load callback retains its original CODE body under
the actual I64 and buffer binders. The result type is the caller's requested
type weakened twice, even when the stored callback annotations use conversion. -/
theorem load_retained_body (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.load owner index proof (.lam false first (.lam false again body))) type) :
    ∃ count, HasType env loans ctx mode owner (.buffer count) ∧
      Conversion.Conv env first .i64 ∧ Conversion.Conv env again (.buffer (count.rename Nat.succ)) ∧
      HasType env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx) mode body
        (type.rename (fun index => index + 2)) := by
  obtain ⟨count,_,_,_,normal,outside,ownerTyped,callback,valueChecked,ownerChecked,
    resultChecked,lowered,requested⟩ := load_view typed
  obtain ⟨_,_,_,inner,firstPi⟩ := callback.lamView
  obtain ⟨_,firstDomain,innerType⟩ := firstPi.pi_injective wf.admissible
  obtain ⟨_,_,_,bodyTyped,againPi⟩ := inner.lamView
  obtain ⟨_,againDomain,bodyResult⟩ := (againPi.trans innerType).pi_injective wf.admissible
  have result : Conversion.Conv env normal (type.rename (fun index => index + 2)) := by
    rw [← load_result_reweakens lowered]
    exact requested.renaming _ wf.closed
  exact ⟨count,ownerTyped,firstDomain.trans valueChecked,againDomain.trans ownerChecked,
    bodyTyped.convert (bodyResult.trans (resultChecked.trans result))⟩

/-- A well-typed I64 observation and the original buffer inhabit the complete
Load continuation telescope. The application retains the original result type. -/
theorem load_ghost_resume
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.load owner index proof continuation) type)
    (observed : HasType env observationLoans ctx observationMode value .i64) :
    HasType env [] ctx true (.app (.app continuation value) owner) type := by
  obtain ⟨count,valueDomain,ownerDomain,result,normal,outside,ownerTyped,callback,
    valueChecked,ownerChecked,resultChecked,lowered,requested⟩ := load_view typed
  have valueArgument := (observed.ghost []).convert valueChecked.symm
  have ownerType : Conversion.Conv env (ownerDomain.subst (single value)) (.buffer count) := by
    simpa only [Term.buffer,Term.subst,substArgs,Op.binders,liftSub,Term.shift_subst_single] using
      ownerChecked.substitution (single value) wf.closed
  have ownerArgument := (ownerTyped.ghost []).convert ownerType.symm
  have application : HasType env [] ctx true (.app continuation value)
      (.pi false (ownerDomain.subst (single value)) (result.subst (liftSub 1 (single value)))) := by
    have applied : HasType env [] ctx true (.app continuation value)
        ((Term.pi false ownerDomain result).subst (single value)) :=
      .app (callback.ghost []) valueArgument (Or.inl rfl)
    simpa only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] using applied
  have resultType := (resultChecked.substitution (liftSub 1 (single value)) wf.closed).substitution
    (single owner) wf.closed
  have outsideType : ((normal.subst (liftSub 1 (single value))).subst (single owner)) = outside := by
    rw [← load_result_reweakens lowered,Term.subst_comp,Term.subst_rename]
    calc
      _ = outside.subst Term.var := by
        congr 1
        funext index
        simp only [liftSub,liftSubOne,single,Term.rename,Term.subst]
      _ = outside := Term.subst_id _
  rw [outsideType] at resultType
  exact (HasType.app application ownerArgument (Or.inl rfl)).convert (resultType.trans requested)

/-- An observed signed machine value constructs the I64 premise directly. An
explicit two-binder continuation then contracts to the actual specialized body. -/
theorem load_ghost_finish
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.load owner index proof (.lam false declaredValue (.lam false declaredOwner body))) type)
    (observed : ValueReduction.signed64 value) :
    HasType env [] ctx true
      ((body.subst (liftSub 1 (single (.integer value)))).subst (single owner)) type := by
  have observation : HasType env [] ctx true (.integer value) .i64 :=
    .integer observed.1 observed.2
  have resumed := load_ghost_resume wf typed observation
  have first : GhostTransform env
      (.app (.lam false declaredValue (.lam false declaredOwner body)) (.integer value))
      (.lam false (declaredOwner.subst (single (.integer value)))
        (body.subst (liftSub 1 (single (.integer value))))) := by
    simpa only [Term.lam,Term.subst,substArgs,Op.binders,liftSub] using
      (compute_ghost_transform wf
        (.beta false declaredValue (.lam false declaredOwner body) (.integer value)))
  have reduced := children_preservation wf resumed .app _ rfl (by decide) _
    (.cons first (.cons (.refl _) .nil))
  exact reduced.ghostBeta wf

end Jihoo.NativeKernel.Environment.LoanTyping
