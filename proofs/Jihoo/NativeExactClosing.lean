import Jihoo.NativeEvaluatedResourceModes

/-! Exact actual-argument slot closing. The final substitution is fixed by the
original source argument list, not chosen existentially. Forward value/type
interpretation preserves every dependent annotation and source binder mode. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Source-order arguments occupy new slots from right to left, exactly as
successive native application consumes the source telescope. -/
def pushValues (values : Nat → Term) (arguments : List Term) : Nat → Term :=
  arguments.foldl (fun current argument => consValues argument current) values

theorem pushValues_nil (values : Nat → Term) : pushValues values [] = values := rfl

theorem pushValues_cons (values : Nat → Term) (argument : Term) (rest : List Term) :
    pushValues values (argument :: rest) = pushValues (consValues argument values) rest := rfl

theorem pushValues_outer (values : Nat → Term) (arguments : List Term) (index : Nat) :
    pushValues values arguments (arguments.length + index) = values index := by
  induction arguments generalizing values index with
  | nil => simp [pushValues]
  | cons argument rest ih =>
      simpa only [pushValues_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,consValues] using
        ih (consValues argument values) (index + 1)

theorem pushValues_argument (values : Nat → Term) (arguments : List Term)
    (selected : arguments[index]? = some argument) :
    pushValues values arguments (arguments.length - 1 - index) = argument := by
  induction arguments generalizing values index with
  | nil => simp at selected
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
          subst argument
          simpa only [pushValues_cons,List.length_cons,Nat.add_sub_cancel,Nat.sub_zero,Nat.add_zero,consValues] using
            pushValues_outer (consValues first values) rest 0
      | succ index =>
          have positions : (first :: rest).length - 1 - (index + 1) = rest.length - 1 - index := by
            simp only [List.length_cons]
            omega
          rw [pushValues_cons,positions]
          exact ih (consValues first values) selected

private theorem exact_actual_frame
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (sameSignature : Conversion.Conv env ((Term.pi erased domain body).subst values) signature)
    (normalized : Conversion.normalize? env fuel signature = some (.pi actualErased actualDomain actualBody))
    (checked : Checker.check fuel env [] (false || actualErased) argument actualDomain = true)
    (application : Checker.applicationOK fuel env false actualDomain argument = true)
    (inference : ∀ kind : Kind, Conversion.Conv env domain kind.term →
      ∃ actual, Checker.infer fuel env [] false argument = some actual ∧
        Jihoo.NativeKernel.kindOf actual = true) :
    erased = actualErased ∧
      RealizedInterpretation env (⟨domain,erased⟩ :: ctx) (consValues argument values) ∧
      Conversion.Conv env (body.subst (consValues argument values))
        (actualBody.subst (single argument)) := by
  have converted := sameSignature.trans (Conversion.normalize?_sound normalized)
  have piConverted : Conversion.Conv env
      (.pi erased (domain.subst values) (body.subst (liftSubOne values)))
      (.pi actualErased actualDomain actualBody) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameErased,domainConverted,bodyConverted⟩ :=
    piConverted.pi_injective history.wellFormed.admissible
  subst actualErased
  have argumentTyped : HasType env [] true argument (domain.subst values) :=
    (Checker.check_sound checked).ghost.convert domainConverted.symm
  have nextClosing := closing.cons history binding argumentTyped (fun kind sourceKind => by
    obtain ⟨actual,inferred,kinded⟩ := inference kind sourceKind
    have runtime := binder_kind_runtime history binding sourceKind
    subst erased
    have rawClosed := sourceKind.substitution values history.wellFormed.closed
    have actualKind : Conversion.Conv env actualDomain kind.term :=
      domainConverted.symm.trans (by simpa only [Kind.subst] using rawClosed)
    exact (ArgumentAtKind.of_inferred_kind history inferred kinded
      (by simpa using checked) application actualKind).realizes history)
  refine ⟨rfl,nextClosing,?_⟩
  simpa only [subst_lift_consValues] using
    bodyConverted.substitution (single argument) history.wellFormed.closed

/-- Every final source slot is the actual consumed argument at its precise
position. Actual source-kind checks construct its semantic interpretation. -/
theorem InputTelescope.close_replay_exact
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (replayed : CallReplay.replay fuel env [] false actualSignature arguments = some (entries,actualResult))
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (inputs : source.Inputs fuel arguments) :
    RealizedInterpretation env finalContext (pushValues values arguments) ∧
      Conversion.Conv env actualResult (result.subst (pushValues values arguments)) := by
  induction source generalizing values fuel actualSignature arguments entries actualResult with
  | nil =>
      cases fuel with
      | zero => simp [CallReplay.replay] at replayed
      | succ fuel =>
          change arguments = [] at inputs
          subst arguments
          have steps := CallReplay.replay_sound replayed
          cases steps
          exact ⟨closing,sameSignature.symm⟩
  | @small ctx erased domain sort body count finalContext result binding small tail ih =>
      cases fuel with
      | zero => simp [CallReplay.replay] at replayed
      | succ fuel =>
          cases arguments with
          | nil => simp [InputTelescope.Inputs] at inputs
          | cons argument rest =>
              obtain ⟨actualErased,actualDomain,actualBody,tailEntries,normalized,checked,application,safe,next,sameEntries⟩ :=
                CallReplay.replay_cons_origin replayed
              have noKind : ∀ kind : Kind, ¬ Conversion.Conv env domain kind.term := by
                cases binding with
                | intro typed allowed => exact small_sort_not_kind history typed small
              obtain ⟨_,nextClosing,nextSignature⟩ := exact_actual_frame history closing binding sameSignature
                normalized checked application (fun kind converted => False.elim (noKind kind converted))
              simpa only [pushValues_cons] using ih (values := consValues argument values) nextClosing next nextSignature inputs
  | @kind ctx erased domain sort body count finalContext result binding tail ih =>
      cases fuel with
      | zero => simp [CallReplay.replay] at replayed
      | succ fuel =>
          cases arguments with
          | nil => simp [InputTelescope.Inputs] at inputs
          | cons argument rest =>
              change (∃ actual, Checker.infer fuel env [] false argument = some actual ∧
                Jihoo.NativeKernel.kindOf actual = true) ∧ tail.Inputs fuel rest at inputs
              obtain ⟨actualErased,actualDomain,actualBody,tailEntries,normalized,checked,application,safe,next,sameEntries⟩ :=
                CallReplay.replay_cons_origin replayed
              obtain ⟨_,nextClosing,nextSignature⟩ := exact_actual_frame history closing binding sameSignature
                normalized checked application (fun _ _ => inputs.1)
              simpa only [pushValues_cons] using ih (values := consValues argument values) nextClosing next nextSignature inputs.2

/-- Same actual checked-call endpoint, now with its final substitution fixed
exactly by the actual argument list and original outer closing values. -/
theorem InputTelescope.close_checkedCall_exact
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments) :
    RealizedInterpretation env finalContext (pushValues values arguments) ∧
      Conversion.Conv env actualResult (result.subst (pushValues values arguments)) := by
  have checkedInfer := (CallReplay.checked_origin checked).2
  unfold CallReplay.infer at checkedInfer
  obtain ⟨actualSignature,inferredFunction,replayed⟩ := Option.bind_eq_some_iff.mp checkedInfer
  have actualFunction := Checker.infer_sound inferredFunction
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing.typed
  exact source.close_replay_exact history closing replayed
    (sourceClosed.unique history.wellFormed actualFunction.ghost) inputs

/-- Observed forward computations preserve the exact actual-argument closing
and its original result type, with derived dependent annotation coherence. -/
theorem InputTelescope.close_checkedCall_exact_evaluated
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments)
    (evaluated : ForwardValues env (pushValues values arguments) finalValues) :
    RealizedInterpretation env finalContext finalValues ∧
      Conversion.Conv env actualResult (result.subst finalValues) := by
  have exactClosing := source.close_checkedCall_exact history closing sourceFunction checked inputs
  exact ⟨exactClosing.1.forwardValues history evaluated,
    exactClosing.2.trans (evaluated.subst_congr history result)⟩

/-- Uniform executable value interpretation, with exact slots and no output
safety/type-coherence certificate, or subsequent code checker invocation. -/
theorem InputTelescope.close_checkedCall_exact_normalized
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments) (valueFuel : Nat) :
    RealizedInterpretation env finalContext (normalizedValues env valueFuel (pushValues values arguments)) ∧
      Conversion.Conv env actualResult (result.subst (normalizedValues env valueFuel (pushValues values arguments))) :=
  source.close_checkedCall_exact_evaluated history closing sourceFunction checked inputs
    (ForwardValues.normalized _)

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CallReplay

theorem replay_arguments_lt_fuel
    (accepted : replay fuel env ctx ghost signature arguments = some (entries,result)) :
    arguments.length < fuel := by
  induction fuel generalizing signature arguments entries result with
  | zero => simp [replay] at accepted
  | succ fuel ih =>
      cases arguments with
      | nil => simp
      | cons argument rest =>
          obtain ⟨_,_,_,_,_,_,_,_,next,_⟩ := replay_cons_origin accepted
          have bound := ih next
          simp only [List.length_cons]
          omega

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Ordinary source binders require no positive-kind inference observations.
This derives their complete input description from actual formation alone. -/
theorem SmallTelescope.exact_input_source
    (small : SmallTelescope env ctx signature count finalContext result) :
    ∃ source : InputTelescope env ctx signature count finalContext result,
      ∀ fuel arguments, arguments.length = count → count < fuel → source.Inputs fuel arguments := by
  induction small with
  | nil =>
      refine ⟨.nil,?_⟩
      intro fuel arguments arity enough
      have empty : arguments = [] := List.length_eq_zero_iff.mp arity
      subst arguments
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | cons binding small tail ih =>
      obtain ⟨source,inputs⟩ := ih
      refine ⟨.small binding small source,?_⟩
      intro fuel arguments arity enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases arguments with
          | nil => simp at arity
          | cons argument rest =>
              exact inputs fuel rest (by simpa using arity) (by omega)

/-- All ordinary dependent calls close their exact actual values from the real
checker, with no canonicality, classification, or positive-input observations. -/
theorem SmallTelescope.close_checkedCall_exact
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : SmallTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) :
    RealizedInterpretation env finalContext (pushValues values arguments) ∧
      Conversion.Conv env actualResult (result.subst (pushValues values arguments)) := by
  have checkedInfer := (CallReplay.checked_origin checked).2
  unfold CallReplay.infer at checkedInfer
  obtain ⟨actualSignature,inferredFunction,replayed⟩ := Option.bind_eq_some_iff.mp checkedInfer
  have enough := CallReplay.replay_arguments_lt_fuel replayed
  obtain ⟨inputSource,inputs⟩ := source.exact_input_source
  exact inputSource.close_checkedCall_exact history closing sourceFunction checked
    (inputs fuel arguments arity (by omega))

theorem SmallTelescope.close_checkedCall_exact_normalized
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : SmallTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) (valueFuel : Nat) :
    RealizedInterpretation env finalContext (normalizedValues env valueFuel (pushValues values arguments)) ∧
      Conversion.Conv env actualResult (result.subst (normalizedValues env valueFuel (pushValues values arguments))) := by
  have completed := source.close_checkedCall_exact history closing sourceFunction checked arity
  have evaluated : ForwardValues env (pushValues values arguments)
      (normalizedValues env valueFuel (pushValues values arguments)) := ForwardValues.normalized _
  exact ⟨completed.1.forwardValues history evaluated,completed.2.trans (evaluated.subst_congr history result)⟩

end Jihoo.NativeKernel.Environment.CodeKinds
