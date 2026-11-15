import Jihoo.NativeRetainedCallBodies

/-! Exact typed stores for the original source prefix of an admitted call.
Code bodies retain their source contexts; actual arguments fill the precise
store slots. This type-only closing theorem needs no kind-output completeness
or representation classification premise. -/
set_option linter.unusedSimpArgs false

namespace Jihoo.NativeKernel.Environment.CallReplay

/-- Split the actual dependent replay at a source prefix boundary. Its
remaining applications retain their actual original checks and modes. -/
theorem Steps.splitAt (steps : Steps env ctx mode signature arguments entries result) (count : Nat) :
    ∃ middle leadingEntries trailingEntries,
      Steps env ctx mode signature (arguments.take count) leadingEntries middle ∧
      Steps env ctx mode middle (arguments.drop count) trailingEntries result ∧
      entries = leadingEntries ++ trailingEntries := by
  induction count generalizing signature arguments entries result with
  | zero => exact ⟨signature,[],entries,.nil,by simpa using steps,rfl⟩
  | succ count ih =>
      cases steps with
      | nil => exact ⟨_,[],[],.nil,.nil,rfl⟩
      | cons normalized checked allowed safe next =>
          obtain ⟨middle,leadingEntries,trailingEntries,left,right,same⟩ := ih next
          refine ⟨middle,_ :: leadingEntries,trailingEntries,.cons normalized checked allowed safe left,right,?_⟩
          simp only [List.cons_append,same]

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Every well-typed source telescope admits a typed store from the exact
actual replay arguments. This proves type closing only; kind realization and
resource interpretation are not silently inferred from ghost typing. -/
theorem Telescope.close_typed_store
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (steps : CallReplay.Steps env [] false actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    ContextFormed env finalContext ∧
      Ghost.Substitution env finalContext [] (pushValues values arguments) ∧
      Conversion.Conv env actualResult (result.subst (pushValues values arguments)) := by
  induction source generalizing values actualSignature arguments entries actualResult with
  | nil =>
      cases steps with
      | nil => exact ⟨formed,closing,sameSignature.symm⟩
      | cons => simp at arity
  | @cons ctx erased domain sort body count finalContext result binding tail ih =>
      cases steps with
      | nil => simp at arity
      | @cons fuel actualSignature actualErased actualDomain actualBody value rest entries actualResult
          normalized checked allowed safe next =>
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
          have nextSignature : Conversion.Conv env (body.subst (consValues value values))
              (actualBody.subst (single value)) := by
            simpa only [subst_lift_consValues] using
              bodyConverted.substitution (single value) history.wellFormed.closed
          have restStore := ih (values := consValues value values)
            (.cons formed binding) (closing.consValues argumentTyped) next nextSignature
            (by simpa using arity)
          simpa only [pushValues_cons] using restStore

/-- The source telescope can be external or dependent on an outer typed
store. The checked call supplies its actual inferred signature. No actual
domain classification or positive-kind inference-spine flag is an input. -/
theorem Telescope.close_typed_checkedCall
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (sourceFunction : HasType env ctx mode function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) :
    ContextFormed env finalContext ∧
      Ghost.Substitution env finalContext [] (pushValues values arguments) ∧
      Conversion.Conv env actualResult (result.subst (pushValues values arguments)) := by
  obtain ⟨actualSignature,actualFunction,steps,applied⟩ :=
    CallReplay.infer_sound (CallReplay.checked_origin checked).2
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing
  exact source.close_typed_store history formed closing steps
    (sourceClosed.unique history.wellFormed actualFunction.ghost) arity

/-- All dependent lookup annotations remain aligned after genuine forward
value observations. No output typing or dependent-type equality is an input. -/
theorem typed_store_forward
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : Ghost.Substitution env ctx [] before)
    (observed : ForwardValues env before after) : Ghost.Substitution env ctx [] after := by
  intro index binding selected
  exact ((closing index binding selected).ghostFamilyForward history (observed index)).convert
    (observed.subst_congr history binding.ty)

/-- Every source sort is supported by this typed-store endpoint, including
positive universes and arbitrary dependent index terms. Representation and
heap interpretation are not inferred from this type-only conclusion. -/
theorem Telescope.close_typed_checkedCall_forward
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (sourceFunction : HasType env ctx mode function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count)
    (observed : ForwardValues env (pushValues values arguments) finalValues) :
    ContextFormed env finalContext ∧ Ghost.Substitution env finalContext [] finalValues ∧
      Conversion.Conv env actualResult (result.subst finalValues) := by
  obtain ⟨finalFormed,store,aligned⟩ :=
    source.close_typed_checkedCall history formed closing sourceFunction checked arity
  exact ⟨finalFormed,typed_store_forward history store observed,
    aligned.trans (observed.subst_congr history result)⟩

theorem Telescope.close_typed_checkedCall_normalized
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (sourceFunction : HasType env ctx mode function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) (valueFuel : Nat) :
    ContextFormed env finalContext ∧
      Ghost.Substitution env finalContext [] (normalizedValues env valueFuel (pushValues values arguments)) ∧
      Conversion.Conv env actualResult
        (result.subst (normalizedValues env valueFuel (pushValues values arguments))) :=
  source.close_typed_checkedCall_forward history formed closing sourceFunction checked arity
    (ForwardValues.normalized _)

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay Jihoo.Quantity NativeQuantity
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Reconstruct the entire opened source telescope from original source
typing and actual opening. Converted nested result types are aligned through
actual Pi congruence, without assuming they are already syntactic Pis. -/
theorem openHead_source_telescope
    (openedHead : openHead fuel env ctx head supplied = some opened)
    (typed : HasType env ctx mode head type) :
    ∃ signature bodyType,
      Telescope env ctx signature opened.modes.length opened.context bodyType ∧
      Conversion.Conv env type signature ∧
      HasType env opened.context mode opened.body bodyType ∧
      opened.modes.length ≤ supplied.length := by
  induction fuel generalizing ctx head supplied opened type with
  | zero => simp [openHead] at openedHead
  | succ fuel ih =>
      simp only [openHead] at openedHead
      split at openedHead
      · rename_i erased domain body argument arguments
        split at openedHead
        · contradiction
        · cases resolved : ContextModes.resolve fuel env ctx erased domain with
          | none => simp [resolved] at openedHead
          | some binderMode =>
              cases rest : openHead fuel env (⟨domain,erased⟩ :: ctx) body arguments with
              | none => simp [resolved,rest] at openedHead
              | some next =>
                  simp only [resolved,rest,Bind.bind,Option.bind,Option.some.injEq] at openedHead
                  cases openedHead
                  obtain ⟨sort,result,binder,bodyTyped,headConverted⟩ := typed.lamView
                  obtain ⟨restSignature,bodyType,telescope,restConverted,retained,bound⟩ :=
                    ih (opened := next) rest bodyTyped
                  refine ⟨.pi erased domain restSignature,bodyType,.cons binder telescope,
                    headConverted.symm.trans ?_,retained,by simpa using Nat.succ_le_succ bound⟩
                  exact .node (.pi erased) (.cons (.refl _) (.cons restConverted .nil))
      · cases openedHead
        exact ⟨type,type,.nil,.refl _,typed,Nat.zero_le _⟩

/-- The same original admitted call supplies its exact opened source store
and its remaining dependent application trace. The store includes erased
arguments, while the original BodyContract concerns actual runtime scopes.
This theorem supplies no unproved positive-kind representation certificate. -/
theorem checked_app_typed_binding_store
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened body bodyType actualSignature middle leadingEntries trailingEntries,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      Checker.infer fuel env [] false head = some actualSignature ∧
      openHead fuel env [] head supplied = some opened ∧
      ContextFormed env opened.context ∧
      HasType env opened.context false opened.body bodyType ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      Ghost.Substitution env opened.context []
        (pushValues Term.var (supplied.take opened.modes.length)) ∧
      HasType env [] true
        (opened.body.subst (pushValues Term.var (supplied.take opened.modes.length)))
        (bodyType.subst (pushValues Term.var (supplied.take opened.modes.length))) ∧
      Conversion.Conv env middle
        (bodyType.subst (pushValues Term.var (supplied.take opened.modes.length))) ∧
      CallReplay.Steps env [] false actualSignature (supplied.take opened.modes.length) leadingEntries middle ∧
      CallReplay.Steps env [] false middle (supplied.drop opened.modes.length) trailingEntries result ∧
      entries = leadingEntries ++ trailingEntries ∧
      (∀ value ∈ runtimeArguments entries,
        (∃ domain, HasType env [] false value domain) ∧ ResourceSafe env value) := by
  obtain ⟨head,supplied,entries,result,opened,body,split,sourceTyped,replayed,
      openedHead,projected,bodyContract,arguments⟩ := checked_app_exact_source_contracts checked
  have inferred := (CallReplay.checked_origin replayed).2
  unfold CallReplay.infer at inferred
  obtain ⟨actualSignature,signatureInferred,actualReplay⟩ := Option.bind_eq_some_iff.mp inferred
  have headTyped := Checker.infer_sound signatureInferred
  have steps := CallReplay.replay_sound actualReplay
  obtain ⟨signature,bodyType,telescope,signatureConverted,retained,bound⟩ :=
    openHead_source_telescope openedHead headTyped
  obtain ⟨middle,leadingEntries,trailingEntries,leadingEntriesSteps,trailingEntriesSteps,entrySplit⟩ := steps.splitAt opened.modes.length
  have closing : Ghost.Substitution env [] [] Term.var := by
    intro index binding found
    simp [lookup] at found
  have store := telescope.close_typed_store history .nil closing leadingEntriesSteps
    (by simpa only [Term.subst_id] using signatureConverted.symm)
    (by simp only [List.length_take,Nat.min_eq_left bound])
  exact ⟨head,supplied,entries,result,opened,body,bodyType,actualSignature,middle,leadingEntries,trailingEntries,
    split,replayed,signatureInferred,openedHead,store.1,retained,projected,bodyContract,store.2.1,
    retained.ghostSubstitution history.wellFormed store.2.1,store.2.2,leadingEntriesSteps,trailingEntriesSteps,entrySplit,arguments⟩

end Jihoo.NativeKernel.Environment.ContextQuantity
