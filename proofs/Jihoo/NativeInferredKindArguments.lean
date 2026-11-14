import Jihoo.NativeSmallTelescopeClosure

/-! Recover the actual canonical kind-domain output from the argument's actual
inference/check/application trace. No normalization-success-to-NF principle or
checker completeness is used. Domains may have converted/aliased annotations. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Forward normalization preserves a displayed Pi/Universe kind spine even
when its Pi domains need more computation or are not first-order domains. -/
theorem kindOf_forward (step : EnvironmentDelta.Forward env input output)
    (source : Jihoo.NativeKernel.kindOf input = true) : Jihoo.NativeKernel.kindOf output = true := by
  have wf : WellFounded (fun a b : Term => sizeOf a < sizeOf b) := (measure sizeOf).wf
  induction input using wf.induction generalizing output with
  | h input ih =>
      fun_cases Jihoo.NativeKernel.kindOf input
      · rename_i level
        obtain ⟨children,shape,changes⟩ := forward_rigid_shape step rfl rfl
        cases changes
        subst output
        rfl
      · rename_i erased domain body
        obtain ⟨children,shape,changes⟩ := forward_rigid_shape step rfl rfl
        cases changes with
        | cons domainChange remaining =>
            cases remaining with
            | cons bodyChange remaining =>
                cases remaining
                subst output
                change Jihoo.NativeKernel.kindOf body = true at source
                simpa only [Jihoo.NativeKernel.kindOf] using ih body (by simp; omega) bodyChange source
      · simp only [Jihoo.NativeKernel.kindOf] at source
        contradiction

theorem firstOrderKind_shape (accepted : firstOrderKind term = true) :
    ∃ kind : Kind, term = kind.term := by
  have wf : WellFounded (fun a b : Term => sizeOf a < sizeOf b) := (measure sizeOf).wf
  induction term using wf.induction with
  | h term ih =>
      fun_cases firstOrderKind term
      · rename_i level
        exact ⟨.type level,rfl⟩
      · rename_i erased body
        obtain ⟨rest,same⟩ := ih body (by simp; omega) accepted
        subst body
        exact ⟨.index erased rest,rfl⟩
      · simp only [firstOrderKind] at accepted
        contradiction

/-- The same finite comparison computes both exact normalized outputs. -/
theorem checked_inferred_equal_outputs
    (inferred : Checker.infer fuel env ctx ghost value = some actual)
    (checked : Checker.check fuel env ctx ghost value domain = true) :
    ∃ common, Conversion.normalize? env fuel actual = some common ∧
      Conversion.normalize? env fuel domain = some common := by
  have equal : Conversion.equal env fuel actual domain = true := by
    simpa only [Checker.check,Checker.accepts,inferred] using checked
  change (match Conversion.normalize? env fuel actual, Conversion.normalize? env fuel domain with
    | some first,some second => first.equal second
    | _,_ => false) = true at equal
  cases first : Conversion.normalize? env fuel actual with
  | none => simp [first] at equal
  | some normal =>
      cases second : Conversion.normalize? env fuel domain with
      | none => simp [first,second] at equal
      | some other =>
          have same : normal = other := by
            exact (Term.equal_iff _ _).mp (by simpa only [first,second] using equal)
          subst other
          exact ⟨normal,rfl,rfl⟩

/-- The argument's actual inferred kind spine activates the actual gate.
Canonical kind output is a conclusion, not an extra normalizer certificate. -/
theorem canonical_domain_of_inferred_kind
    (inferred : Checker.infer fuel env ctx ghost value = some actual)
    (kinded : Jihoo.NativeKernel.kindOf actual = true)
    (checked : Checker.check fuel env ctx ghost value domain = true)
    (application : Checker.applicationOK fuel env false domain value = true) :
    ∃ kind : Kind, Conversion.normalize? env fuel domain = some kind.term := by
  obtain ⟨common,inferredNormal,domainNormal⟩ := checked_inferred_equal_outputs inferred checked
  have sourceKind := kindOf_forward (Conversion.normalize?_forward inferredNormal) kinded
  have properties : globalFree common = true ∧ firstOrderKind common = true ∧
      plain env (Conversion.normalize env fuel value) = true := by
    simpa only [Checker.applicationOK,domainNormal,Bool.false_or,sourceKind,Bool.not_true,
      Bool.false_or,Bool.and_eq_true] using application
  obtain ⟨kind,same⟩ := firstOrderKind_shape properties.2.1
  exact ⟨kind,same ▸ domainNormal⟩

/-- Recover an authentic raw-domain kind argument using only actual input
inference/check/gate traces and its source kind conversion. -/
theorem ArgumentAtKind.of_inferred_kind
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (inferred : Checker.infer fuel env [] false value = some actual)
    (kinded : Jihoo.NativeKernel.kindOf actual = true)
    (checked : Checker.check fuel env [] false value domain = true)
    (application : Checker.applicationOK fuel env false domain value = true)
    (converted : Conversion.Conv env domain kind.term) : ArgumentAtKind env kind value := by
  obtain ⟨other,normalized⟩ := canonical_domain_of_inferred_kind inferred kinded checked application
  have same := Kind.conv_injective history.wellFormed.admissible
    ((Conversion.normalize?_sound normalized).symm.trans converted)
  subst other
  exact ⟨fuel,domain,checked,normalized,application⟩

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem DomainCanonical.of_inferred_kind
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (inferred : Checker.infer fuel env [] false value = some actual)
    (kinded : Jihoo.NativeKernel.kindOf actual = true)
    (checked : Checker.check fuel env [] false value domain = true)
    (application : Checker.applicationOK fuel env false domain value = true) :
    DomainCanonical env fuel domain := by
  intro kind converted
  obtain ⟨other,normalized⟩ := canonical_domain_of_inferred_kind inferred kinded checked application
  have same := Kind.conv_injective history.wellFormed.admissible
    ((Conversion.normalize?_sound normalized).symm.trans converted)
  subst other
  exact normalized

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CallReplay

/-- Exact first-frame executable trace; its fuel is the actual argument gate's
fuel, rather than an existentially rerun closed check. -/
theorem replay_cons_origin
    (accepted : replay (fuel + 1) env ctx ghost signature (argument :: rest) = some (entries,result)) :
    ∃ erased domain body tail,
      Conversion.normalize? env fuel signature = some (.pi erased domain body) ∧
      Checker.check fuel env ctx (ghost || erased) argument domain = true ∧
      Checker.applicationOK fuel env ghost domain argument = true ∧
      Conversion.substitutionSafe body argument = true ∧
      replay fuel env ctx ghost (body.subst (single argument)) rest = some (tail,result) ∧
      entries = ⟨erased,domain,argument⟩ :: tail := by
  simp only [replay] at accepted
  obtain ⟨normal,normalized,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i erased domain body
    split at accepted
    · rename_i checks
      have both := Bool.and_eq_true_iff.mp checks
      have argumentChecks := Bool.and_eq_true_iff.mp both.1
      obtain ⟨⟨tail,last⟩,next,accepted⟩ := Option.bind_eq_some_iff.mp accepted
      cases accepted
      exact ⟨erased,domain,body,tail,normalized,argumentChecks.1,argumentChecks.2,both.2,next,rfl⟩
    · contradiction
  · contradiction

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- A whole actual call closes its fresh type/family parameter and every
remaining ordinary dependent binder. The positive-kind output is recovered
from actual input inference; it is not an assumed normalization certificate. -/
theorem close_inferred_kind_then_small
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (tail : SmallTelescope env (⟨domain,erased⟩ :: ctx) body count finalContext result)
    (sourceFunction : HasType env ctx ghost function (.pi erased domain body))
    (checkedCall : CallReplay.checked (fuel + 1) env [] false (function.subst values)
      (argument :: rest) = some (entries,actualResult))
    (inferredArgument : Checker.infer fuel env [] false argument = some argumentType)
    (kinded : Jihoo.NativeKernel.kindOf argumentType = true)
    (arity : rest.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  have checkedInfer := (CallReplay.checked_origin checkedCall).2
  unfold CallReplay.infer at checkedInfer
  obtain ⟨actualSignature,inferredFunction,replayed⟩ := Option.bind_eq_some_iff.mp checkedInfer
  obtain ⟨actualErased,actualDomain,actualBody,tailEntries,normalized,argumentChecked,application,safe,next,sameEntries⟩ :=
    CallReplay.replay_cons_origin replayed
  have actualFunction := Checker.infer_sound inferredFunction
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing.typed
  have sameSignature := sourceClosed.unique history.wellFormed actualFunction.ghost
  have converted := sameSignature.trans (Conversion.normalize?_sound normalized)
  have piConverted : Conversion.Conv env
      (.pi erased (domain.subst values) (body.subst (liftSubOne values)))
      (.pi actualErased actualDomain actualBody) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameErased,domainConverted,bodyConverted⟩ :=
    piConverted.pi_injective history.wellFormed.admissible
  subst actualErased
  have argumentTyped : HasType env [] true argument (domain.subst values) :=
    (Checker.check_sound argumentChecked).ghost.convert domainConverted.symm
  have nextClosing := closing.cons history binding argumentTyped (fun kind sourceKind => by
    have runtime := binder_kind_runtime history binding sourceKind
    subst erased
    have rawClosed := sourceKind.substitution values history.wellFormed.closed
    have actualKind : Conversion.Conv env actualDomain kind.term :=
      domainConverted.symm.trans (by simpa only [Kind.subst] using rawClosed)
    exact (ArgumentAtKind.of_inferred_kind history inferredArgument kinded
      (by simpa using argumentChecked) application actualKind).realizes history)
  have nextConverted := bodyConverted.substitution (single argument) history.wellFormed.closed
  have nextSignature : Conversion.Conv env (body.subst (consValues argument values))
      (actualBody.subst (single argument)) := by
    simpa only [subst_lift_consValues] using nextConverted
  exact tail.close history nextClosing (CallReplay.replay_sound next) nextSignature arity

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Arbitrarily many fresh type/family and ordinary dependent source binders.
Positive binders retain actual input inference observations; ordinary binders
are discharged uniformly from their genuine Prop/Type0 formation. -/
inductive InputTelescope (env : Environment) : Context → Term → Nat → Context → Term → Type where
  | nil : InputTelescope env ctx result 0 ctx result
  | small : Binder env ctx erased domain sort → (sort = .prop ∨ sort = .type 0) →
      InputTelescope env (⟨domain,erased⟩ :: ctx) body count finalContext result →
      InputTelescope env ctx (.pi erased domain body) (count + 1) finalContext result
  | kind : Binder env ctx erased domain sort →
      InputTelescope env (⟨domain,erased⟩ :: ctx) body count finalContext result →
      InputTelescope env ctx (.pi erased domain body) (count + 1) finalContext result

/-- Fuel positions are determined by the original replay, not chosen for a
second check. Only positive-parameter positions retain kind-spine observations. -/
def InputTelescope.Inputs : {ctx : Context} → {signature : Term} → {count : Nat} →
    {finalContext : Context} → {result : Term} → Nat →
    InputTelescope env ctx signature count finalContext result → List Term → Prop
  | _,_,_,_,_,_,.nil,arguments => arguments = []
  | _,_,_,_,_,fuel+1,.small _ _ tail,_argument :: rest => tail.Inputs fuel rest
  | _,_,_,_,_,fuel+1,.kind _ tail,argument :: rest =>
      (∃ actual, Checker.infer fuel env [] false argument = some actual ∧
        Jihoo.NativeKernel.kindOf actual = true) ∧ tail.Inputs fuel rest
  | _,_,_,_,_,_,_,_ => False

private theorem advance_actual_frame
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

/-- Uniform closing of an arbitrary mixed dependent telescope from the
original replay and actual positive-argument input inference observations. -/
theorem InputTelescope.close_replay
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (replayed : CallReplay.replay fuel env [] false actualSignature arguments = some (entries,actualResult))
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (inputs : source.Inputs fuel arguments) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  induction source generalizing values fuel actualSignature arguments entries actualResult with
  | nil =>
      cases fuel with
      | zero => simp [CallReplay.replay] at replayed
      | succ fuel =>
          change arguments = [] at inputs
          subst arguments
          have steps := CallReplay.replay_sound replayed
          cases steps
          exact ⟨values,closing,sameSignature.symm⟩
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
              obtain ⟨_,nextClosing,nextSignature⟩ := advance_actual_frame history closing binding sameSignature
                normalized checked application (fun kind converted => False.elim (noKind kind converted))
              exact ih nextClosing next nextSignature inputs
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
              obtain ⟨_,nextClosing,nextSignature⟩ := advance_actual_frame history closing binding sameSignature
                normalized checked application (fun _ _ => inputs.1)
              exact ih nextClosing next nextSignature inputs.2

/-- End-to-end actual checked-call endpoint for any number/order of fresh kind
parameters and ordinary binders. No domain-output or representation-safety
certificate is supplied by the caller. -/
theorem InputTelescope.close_checkedCall
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  have checkedInfer := (CallReplay.checked_origin checked).2
  unfold CallReplay.infer at checkedInfer
  obtain ⟨actualSignature,inferredFunction,replayed⟩ := Option.bind_eq_some_iff.mp checkedInfer
  have actualFunction := Checker.infer_sound inferredFunction
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing.typed
  exact source.close_replay history closing replayed
    (sourceClosed.unique history.wellFormed actualFunction.ghost) inputs

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem InputTelescope.close_checkedCall_nonFunction
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : InputTelescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (inputs : source.Inputs fuel arguments)
    (shape : CallReplay.ResultShape env finalContext result) : PiSeparated env actualResult := by
  obtain ⟨closedValues,completed,converted⟩ := source.close_checkedCall history closing sourceFunction checked inputs
  have separated := shape.closed_nonFunction_realized (Extends.refl _) history completed
  intro erased domain body pi
  exact separated erased domain body (converted.symm.trans pi)

end Jihoo.NativeKernel.Environment.CodeKinds
