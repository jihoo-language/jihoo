import Jihoo.NativeClosingContexts

/-! Closing a dependent runtime telescope from actual closed application traces.
The canonical domain output obligation is local to each bounded application
check. No checker completeness or arbitrary CODE substitution is assumed. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Binder formation follows the actual open dependent telescope. Its final
context retains every dependent source binder and its final uninstantiated body. -/
inductive Telescope (env : Environment) : Context → Term → Nat → Context → Term → Prop where
  | nil : Telescope env ctx result 0 ctx result
  | cons : Binder env ctx erased domain sort →
      Telescope env (⟨domain,erased⟩ :: ctx) body count finalContext result →
      Telescope env ctx (.pi erased domain body) (count + 1) finalContext result

/-- Exact bounded output needed by first-order code closure. Its input is the
actual normalized signature domain, and its fuel is the actual argument gate's
fuel. Conversion alone does not imply this bounded computation. -/
def DomainCanonical (env : Environment) (fuel : Nat) (domain : Term) : Prop :=
  ∀ kind : Kind, Conversion.Conv env domain kind.term →
    Conversion.normalize? env fuel domain = some kind.term

theorem DomainCanonical.of_kind {kind : Kind}
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (domainKind : domain = kind.term)
    (application : Checker.applicationOK fuel env false domain value = true) :
    DomainCanonical env fuel domain := by
  subst domain
  intro other converted
  have same := Kind.conv_injective history.wellFormed.admissible converted
  subst other
  cases normalized : Conversion.normalize? env fuel kind.term with
  | none => simp [Checker.applicationOK,normalized] at application
  | some normal =>
      exact congrArg some (kind.normalize?_fixed normalized)

theorem DomainCanonical.of_nonkind
    (nonkind : ∀ kind : Kind, ¬ Conversion.Conv env domain kind.term) :
    DomainCanonical env fuel domain := by
  intro kind converted
  exact False.elim (nonkind kind converted)

theorem DomainCanonical.u64
    (admissible : EnvironmentDelta.Admissible env) : DomainCanonical env fuel .u64 := by
  apply DomainCanonical.of_nonkind
  intro kind converted
  cases kind with
  | type level =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible
  | index erased result =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible

/-- The semantic endpoint also accommodates actually erased arguments: their
actual argument check runs in ghost mode, while the application gate still
runs in code mode. No forged code-mode recheck is needed. -/
structure RealizedInterpretation (env : Environment) (ctx : Context) (values : Nat → Term) : Prop where
  formed : ContextFormed env ctx
  typed : Ghost.Substitution env ctx [] values
  arguments : ∀ index kind, LookupKind env ctx index kind → Realizes env kind (values index)

theorem TraceInterpretation.realized
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : TraceInterpretation env ctx values) : RealizedInterpretation env ctx values :=
  ⟨closing.formed,closing.typed,fun index kind found => (closing.arguments index kind found).realizes history⟩

theorem RealizedInterpretation.nil (values : Nat → Term) :
    RealizedInterpretation env [] values := by
  refine ⟨.nil,?_,?_⟩
  · intro index binding found; simp [lookup] at found
  · intro index kind found; obtain ⟨binding,selected,_,_⟩ := found; simp [lookup] at selected

theorem RealizedInterpretation.cons
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : RealizedInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (argument : HasType env [] true value (domain.subst values))
    (kindArguments : ∀ kind, Conversion.Conv env domain kind.term → Realizes env kind value) :
    RealizedInterpretation env (⟨domain,erased⟩ :: ctx) (consValues value values) := by
  refine ⟨.cons closing.formed binding,closing.typed.consValues argument,?_⟩
  intro index kind found
  cases index with
  | zero => exact kindArguments kind (found.head history.wellFormed.closed)
  | succ index => exact closing.arguments index kind (found.tail history.wellFormed.closed)

private theorem actual_argument_realizes
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : Checker.check fuel env [] erased value domain = true)
    (application : Checker.applicationOK fuel env false domain value = true)
    (normalized : Conversion.normalize? env fuel domain = some kind.term) :
    Realizes env kind value := by
  have kindTyped : HasType env [] true value kind.term :=
    ((Checker.check_sound typed).convert (Conversion.normalize?_sound normalized)).ghost
  have forward : EnvironmentDelta.Forward env value (Conversion.normalize env fuel value) := by
    change EnvironmentDelta.Forward env value ((Conversion.normalize? env fuel value).getD value)
    cases normalizedValue : Conversion.normalize? env fuel value with
    | none => exact .refl
    | some normal => exact Conversion.normalize?_forward normalizedValue
  have isPlain := normalizedKindArgument_plain normalized application
  exact ⟨kindTyped,_,forward,Representation.PlainIndices.of_familyPlain
    (kindTyped.ghostForward history forward).term_wellFormed
    (plain_familyPlain isPlain) (Bool.and_eq_true_iff.mp isPlain).1⟩

/-- Actual closed CallReplay traces plus their local displayed-kind obligation.
The indexed constructor keeps exactly the same fuel for the argument check,
application gate, and domain normalization. -/
inductive CanonicalSteps (env : Environment) :
    Term → List Term → List CallReplay.Argument → Term → Prop where
  | nil : CanonicalSteps env signature [] [] signature
  | cons : Conversion.normalize? env fuel signature = some (.pi erased domain body) →
      Checker.check fuel env [] erased value domain = true →
      Checker.applicationOK fuel env false domain value = true →
      Conversion.substitutionSafe body value = true → DomainCanonical env fuel domain →
      CanonicalSteps env (body.subst (single value)) rest entries result →
      CanonicalSteps env signature (value :: rest) (⟨erased,domain,value⟩ :: entries) result

theorem CanonicalSteps.replayed (trace : CanonicalSteps env signature arguments entries result) :
    CallReplay.Steps env [] false signature arguments entries result := by
  induction trace with
  | nil => exact .nil
  | cons normalized typed application safe canonical rest ih =>
      exact .cons normalized (by simpa using typed) application safe ih

theorem subst_lift_consValues (term : Term) (values : Nat → Term) (value : Term) :
    (term.subst (liftSubOne values)).subst (single value) = term.subst (consValues value values) := by
  rw [Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [liftSubOne,Term.subst,single,consValues]
  | succ index => exact Term.shift_subst_single (values index) value

/-- Every binder in an arbitrary finite dependent telescope closes from its
actual application checks, including converted source domains and erased U64
arguments. The displayed-kind obligation is explicit at each actual gate. -/
theorem Telescope.close
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : Telescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (trace : CanonicalSteps env actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  induction telescope generalizing values actualSignature arguments entries actualResult with
  | nil =>
      cases trace with
      | nil => exact ⟨values,closing,sameSignature.symm⟩
      | cons => simp at arity
  | @cons ctx erased domain sort body count finalContext result binding tail ih =>
      cases trace with
      | nil => simp at arity
      | @cons fuel actualSignature actualErased actualDomain actualBody value rest entries actualResult
          normalized checked application safe canonical next =>
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
            have domainKind := (sourceKind.substitution values history.wellFormed.closed)
            have actualKind : Conversion.Conv env actualDomain kind.term := by
              exact domainConverted.symm.trans (by simpa only [Kind.subst] using domainKind)
            exact actual_argument_realizes history checked application (canonical kind actualKind))
          have nextConverted := bodyConverted.substitution (single value) history.wellFormed.closed
          have nextSignature : Conversion.Conv env (body.subst (consValues value values))
              (actualBody.subst (single value)) := by
            simpa only [subst_lift_consValues] using nextConverted
          exact ih nextClosing next nextSignature (by simpa using arity)

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- A displayed actual domain is either a literal first-order kind or is
semantically separated from every first-order kind. This is a classification
of the actual replay entry, not a fabricated argument plainness certificate. -/
def DomainClassified (env : Environment) (domain : Term) : Prop :=
  (∃ kind : Kind, domain = kind.term) ∨ ∀ kind : Kind, ¬ Conversion.Conv env domain kind.term

def EntriesClassified (env : Environment) (entries : List CallReplay.Argument) : Prop :=
  ∀ entry ∈ entries, DomainClassified env entry.domain

/-- For classified displayed domains, the original successful replay supplies
the entire closing trace. Its actual checks and fuel are reused verbatim. -/
theorem CanonicalSteps.of_replayed
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (trace : CallReplay.Steps env [] false signature arguments entries result)
    (classified : EntriesClassified env entries) : CanonicalSteps env signature arguments entries result := by
  induction trace with
  | nil => exact .nil
  | @cons fuel signature erased domain body value rest entries result normalized typed application safe next ih =>
      have domainClassified := classified ⟨erased,domain,value⟩ (by simp)
      have canonical : DomainCanonical env fuel domain := by
        rcases domainClassified with ⟨kind,same⟩ | nonkind
        · exact DomainCanonical.of_kind history same application
        · exact DomainCanonical.of_nonkind nonkind
      exact .cons normalized (by simpa using typed) application safe canonical
        (ih (fun entry member => classified entry (by simp [member])))

/-- The actual checked closed call supplies its own inferred signature. Ghost
substitution and uniqueness align it to the open source telescope, so no
external signature conversion or CODE-substitution derivation is assumed. -/
theorem Telescope.close_checkedCall
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (telescope : Telescope env ctx signature count finalContext result)
    (closing : RealizedInterpretation env ctx values)
    (sourceFunction : HasType env ctx ghost function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (classified : EntriesClassified env entries)
    (arity : arguments.length = count) :
    ∃ closedValues, RealizedInterpretation env finalContext closedValues ∧
      Conversion.Conv env actualResult (result.subst closedValues) := by
  obtain ⟨actualSignature,actualFunction,steps,applied⟩ :=
    CallReplay.infer_sound (CallReplay.checked_origin checked).2
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing.typed
  have converted := sourceClosed.unique history.wellFormed actualFunction.ghost
  exact telescope.close history closing (CanonicalSteps.of_replayed history steps classified) converted arity

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds

theorem DomainClassified.u64 (admissible : EnvironmentDelta.Admissible env) :
    DomainClassified env .u64 := by
  apply Or.inr
  intro kind converted
  cases kind with
  | type level =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible
  | index erased result =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible

theorem EntriesClassified.nil : EntriesClassified env [] := by
  intro entry member
  cases member

theorem EntriesClassified.cons (head : DomainClassified env entry.domain)
    (tail : EntriesClassified env entries) : EntriesClassified env (entry :: entries) := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail selected member

end Jihoo.NativeKernel.Environment.CodeKinds
