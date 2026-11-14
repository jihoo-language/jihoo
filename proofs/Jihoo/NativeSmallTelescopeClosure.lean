import Jihoo.NativeClosingDomainClassification

/-! Uniform actual-call closure for all ordinary term/proof dependent binders.
Every source binder has sort Prop or Type0; its type may be neutral, computed,
or aliased. No canonical-domain or domain-classification input is needed. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

inductive SmallTelescope (env : Environment) : Context → Term → Nat → Context → Term → Prop where
  | nil : SmallTelescope env ctx result 0 ctx result
  | cons : Binder env ctx erased domain sort → (sort = .prop ∨ sort = .type 0) →
      SmallTelescope env (⟨domain,erased⟩ :: ctx) body count finalContext result →
      SmallTelescope env ctx (.pi erased domain body) (count + 1) finalContext result

theorem SmallTelescope.telescope
    (source : SmallTelescope env ctx signature count finalContext result) :
    Telescope env ctx signature count finalContext result := by
  induction source with
  | nil => exact .nil
  | cons binder small tail ih => exact .cons binder ih

/-- The source binder's actual formation, followed by the constructed typed
substitution, proves every small closed domain separated from all kinds. -/
theorem RealizedInterpretation.small_domain_not_kind
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (small : sort = .prop ∨ sort = .type 0) :
    ∀ kind : Kind, ¬ Conversion.Conv env (domain.subst values) kind.term := by
  cases binding with
  | intro typed allowed =>
      have closed := typed.ghostSubstitution history.wellFormed closing.typed
      have formed : HasType env [] true (domain.subst values) sort.term := by
        simpa only [SortTag.subst_term] using closed
      exact small_sort_not_kind history formed small

/-- Actual dependent replay closes every Prop/Type0 source binder uniformly.
The function type alignment can be converted; no bounded checker rerun,
canonical-domain certificate, or final interpretation is an input. -/
theorem SmallTelescope.close
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : SmallTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (trace : CallReplay.Steps env [] false actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  induction telescope generalizing values actualSignature arguments entries actualResult with
  | nil =>
      cases trace with
      | nil => exact ⟨values,closing,sameSignature.symm⟩
      | cons => simp at arity
  | @cons ctx erased domain sort body count finalContext result binding small tail ih =>
      cases trace with
      | nil => simp at arity
      | @cons fuel actualSignature actualErased actualDomain actualBody value rest entries actualResult
          normalized checked application safe next =>
          have converted := sameSignature.trans (Conversion.normalize?_sound normalized)
          have piConverted : Conversion.Conv env
              (.pi erased (domain.subst values) (body.subst (liftSubOne values)))
              (.pi actualErased actualDomain actualBody) := by
            simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
          obtain ⟨sameErased,domainConverted,bodyConverted⟩ :=
            piConverted.pi_injective history.wellFormed.admissible
          subst actualErased
          have argumentTyped : HasType env [] true value (domain.subst values) :=
            (Checker.check_sound checked).ghost.convert domainConverted.symm
          have nextClosing := closing.cons history binding argumentTyped (fun kind sourceKind => by
            have forbidden := closing.small_domain_not_kind history binding small kind
            have closedKind : Conversion.Conv env (domain.subst values) kind.term := by
              simpa only [Kind.subst] using sourceKind.substitution values history.wellFormed.closed
            exact False.elim (forbidden closedKind))
          have nextConverted := bodyConverted.substitution (single value) history.wellFormed.closed
          have nextSignature : Conversion.Conv env (body.subst (consValues value values))
              (actualBody.subst (single value)) := by
            simpa only [subst_lift_consValues] using nextConverted
          exact ih nextClosing next nextSignature (by simpa using arity)

/-- Start directly at the same executable checked-call endpoint. Signature
alignment follows from actual inference, ghost substitution, and uniqueness. -/
theorem SmallTelescope.close_checkedCall
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : SmallTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  obtain ⟨actualSignature,actualFunction,steps,applied⟩ :=
    CallReplay.infer_sound (CallReplay.checked_origin checked).2
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing.typed
  have converted := sourceClosed.unique history.wellFormed actualFunction.ghost
  exact telescope.close history closing steps converted arity

/-- The actual closed result preserves the authenticated owner-consuming result
shape for every finite small telescope, with no domain-classification premise. -/
theorem SmallTelescope.close_checkedCall_nonFunction
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : SmallTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count)
    (shape : CallReplay.ResultShape env finalContext result) : PiSeparated env actualResult := by
  obtain ⟨closedValues,completed,converted⟩ := telescope.close_checkedCall history closing sourceFunction checked arity
  have separated := shape.closed_nonFunction_realized (Extends.refl _) history completed
  intro erased domain body pi
  exact separated erased domain body (converted.symm.trans pi)

end Jihoo.NativeKernel.Environment.CodeKinds
