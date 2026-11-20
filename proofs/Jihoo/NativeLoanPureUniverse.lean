import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanPureMixedAdmission
import Jihoo.NativeMultiUniverseComputedFundamental

set_option maxUniverseOffset 40

/-! Reconstruct the finite model of polymorphic values from the extended
ghost judgment. Computed annotations still have the original binder policy.
Their reconstructed types now agree by the full RawValue conversion. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed.Pure

open ValueErasure.Loan (project project_variable project_ordinary_node project_pi)

private theorem project_mono (type : Mono count) (depth : Nat) :
    project env (type.syntax depth) = type.syntax depth := by
  induction type generalizing depth with
  | parameter index => exact project_variable _ _
  | natural => exact project_ordinary_node (op := .u64) rfl (by intro same; cases same) []
  | arrow domain codomain domainIH bodyIH =>
      rw [Mono.syntax_arrow, project_pi, domainIH, bodyIH]

private theorem mono_injective (wf : UnifiedProgram.EnvWellFormed env) {first second : Mono count}
    (converted : RawValue.Conv env (first.syntax depth) (second.syntax depth)) : first = second := by
  have projected := converted.projected wf.admissible
  rw [project_mono, project_mono] at projected
  exact Mono.syntax_injective wf projected

private def ValueContext (env : Environment) (Γ : List (Mono count)) (ctx : Context) : Prop :=
  ∀ {A index}, Member A Γ index → ∃ binding, NativeKernel.lookup ctx index = some binding ∧
    RawValue.Conv env binding.ty (A.syntax Γ.length)

private theorem ValueContext.extend (wf : UnifiedProgram.EnvWellFormed env)
    (agreement : ValueContext env Γ ctx) (converted : RawValue.Conv env original (A.syntax Γ.length)) :
    ValueContext env (A :: Γ) (⟨original, false⟩ :: ctx) := by
  intro B index member
  cases member with
  | here =>
      refine ⟨⟨original.rename Nat.succ, false⟩, rfl, ?_⟩
      simpa only [Mono.syntax_shift, List.length_cons] using converted.renaming Nat.succ wf.admissible
  | there previous =>
      obtain ⟨binding, found, prior⟩ := agreement previous
      refine ⟨⟨binding.ty.rename Nat.succ, binding.erased⟩, ?_, ?_⟩
      · simp only [NativeKernel.lookup, found, Option.map]
      · simpa only [Mono.syntax_shift, List.length_cons] using prior.renaming Nat.succ wf.admissible

private def atomicValue : Term → Bool
  | .var _ | .natural _ => true
  | _ => false

private theorem native_atom (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (atom : atomicValue term = true) : ∃ principal,
      LoanTyping.HasType env [] ctx true term principal ∧ RawValue.Conv env principal type := by
  induction typed with
  | native original => exact ⟨_, original, .refl _⟩
  | convert _ _ converted ih =>
      obtain ⟨principal, original, prior⟩ := ih atom
      exact ⟨principal, original, prior.trans converted⟩
  | pi | lam | app => simp [atomicValue] at atom

private def NaturalBound : Term → Prop
  | .natural value => value < 2^64
  | _ => True

private theorem native_natural_bound (typed : LoanTyping.HasType env loans ctx mode term type) :
    NaturalBound term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => NaturalBound term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

private theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized count depth term) :
    ∀ (Γ : List (Mono count)), Γ.length = depth → ∀ {ctx type}, ValueContext env Γ ctx →
      LoanTyping.PureTyping.HasType env ctx term type → ∃ A, ∃ expression : Expression Γ A,
        RawValue.Conv env expression.syntax term ∧ RawValue.Conv env (A.syntax Γ.length) type := by
  induction recognized with
  | var bound =>
      intro Γ length ctx type agreement typed
      cases length
      obtain ⟨A, member⟩ := Member.at Γ _ bound
      obtain ⟨_, original, outer⟩ := native_atom typed rfl
      obtain ⟨binding, found, converted⟩ := original.principalView
      obtain ⟨other, selected, canonical⟩ := agreement member
      rw [found] at selected
      cases selected
      exact ⟨A, .var member, .refl _, canonical.symm.trans ((RawValue.Conv.old converted).trans outer)⟩
  | natural value =>
      intro Γ _ _ _ _ typed
      obtain ⟨_, original, outer⟩ := native_atom typed rfl
      exact ⟨.natural, .natural value (native_natural_bound original), .refl _,
        (RawValue.Conv.old original.principalView).trans outer⟩
  | lam domain recognized ih =>
      intro Γ length ctx type agreement typed
      cases length
      obtain ⟨_, bodyTyped, converted⟩ := LoanTyping.PureTyping.lambda_replay typed _ _ _ rfl
      have domainConversion : RawValue.Conv env (domain.syntax Γ.length) (domain.normal.syntax Γ.length) :=
        .old (.old (domain.normalizes _))
      obtain ⟨B, bodyExpression, bodyConversion, resultConversion⟩ :=
        ih (domain.normal :: Γ) rfl (agreement.extend wf domainConversion) bodyTyped
      refine ⟨.arrow domain.normal B, .lam bodyExpression, ?_, ?_⟩
      · exact .node (.lam false) (.cons domainConversion.symm (.cons bodyConversion .nil))
      · rw [Mono.syntax_arrow]
        exact (RawValue.Conv.node (.pi false)
          (.cons domainConversion.symm (.cons resultConversion .nil))).trans converted
  | @app depth function argument recognizedFunction recognizedArgument ihf iha =>
      intro Γ length ctx type agreement typed
      obtain ⟨erased, domain, codomain, functionTyped, argumentTyped, resultConverted⟩ :=
        LoanTyping.PureTyping.application_replay typed _ _ rfl
      obtain ⟨F, functionExpression, functionConversion, functionConverted⟩ := ihf Γ length agreement functionTyped
      cases F with
      | parameter index =>
          have projected := functionConverted.projected wf.admissible
          rw [project_mono, project_pi] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl projected wf.admissible)
      | natural =>
          have projected := functionConverted.projected wf.admissible
          rw [project_mono, project_pi] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint (op := .u64) (op' := .pi erased)
            rfl rfl (by intro same; cases same) projected wf.admissible)
      | arrow A B =>
          rw [Mono.syntax_arrow] at functionConverted
          have components := functionConverted.pi_injective wf.admissible
          obtain ⟨C, argumentExpression, argumentConversion, argumentConverted⟩ :=
            iha Γ length agreement (.native argumentTyped)
          have same : C = A := mono_injective wf (argumentConverted.trans components.2.1.symm)
          subst C
          refine ⟨B, .app functionExpression argumentExpression, ?_, ?_⟩
          · exact .node .app (.cons functionConversion (.cons argumentConversion .nil))
          · have result := components.2.2.substitution (single argument) wf.admissible
            rw [Mono.syntax_instantiate] at result
            exact result.trans resultConverted

/-- Actual ghost typing reconstructs a finite semantic inhabitant, uniformly
over all assignments to the abstract universe parameters. -/
theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term type)
    (recognized : UniverseRecognized levels term) :
    ∃ scheme : Scheme levels, RawValue.Conv env scheme.syntax term ∧ RawValue.Conv env scheme.type type ∧
      ∀ assignment : Assignment levels.get, Nonempty (Finite.Carrier (scheme.code assignment)) := by
  revert type
  induction recognized with
  | @body termBody levels recognized =>
      intro type typed
      have agreement : ValueContext env ([] : List (Mono levels.length)) (parameterContext levels) := by
        intro A index member
        cases member
      obtain ⟨_, expression, source, converted⟩ := recognized_principal wf recognized [] rfl agreement typed
      exact ⟨.body expression, source, converted, fun assignment => ⟨(Scheme.body expression).meaning assignment⟩⟩
  | abstract level recognized ih =>
      intro type typed
      obtain ⟨_, bodyTyped, converted⟩ := LoanTyping.PureTyping.lambda_replay typed _ _ _ rfl
      obtain ⟨inner, source, bodyConversion, _⟩ := ih bodyTyped
      exact ⟨.abstract level inner, .node (.lam false) (.cons (.refl _) (.cons source .nil)),
        (RawValue.Conv.node (.pi false) (.cons (.refl _) (.cons bodyConversion .nil))).trans converted,
        fun assignment => ⟨(Scheme.abstract level inner).meaning assignment⟩⟩

/-- Choosing the empty code for a universe parameter rules out an inhabitant
of the polymorphic bottom type even through the enlarged conversion. -/
theorem no_abstract_result (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (typed : LoanTyping.PureTyping.HasType env [] (.lam false (.univ level.val) body) requested)
    (recognized : Recognized 1 0 body)
    (converted : RawValue.Conv env requested (.pi false (.univ level.val) (.var 0))) : False := by
  obtain ⟨_, bodyTyped, principal⟩ := LoanTyping.PureTyping.lambda_replay typed _ _ _ rfl
  have agreement : ValueContext env ([] : List (Mono 1)) [⟨.univ level.val, false⟩] := by
    intro A index member
    cases member
  obtain ⟨A, expression, _, bodyConverted⟩ := recognized_principal wf recognized [] rfl agreement bodyTyped
  have result := ((principal.trans converted).pi_injective wf.admissible).2.2
  have aligned : RawValue.Conv env (A.syntax 0) ((Mono.parameter (0 : Fin 1)).syntax 0) :=
    bodyConverted.trans result
  have same := mono_injective wf aligned
  subst A
  exact expression.parameter_uninhabited (fun _ => level)

theorem checker_rejects_abstract_result (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (recognized : Recognized 1 0 body) :
    LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget [] (.lam false (.univ level.val) body)
      (.pi false (.univ level.val) (.var 0)) = none := by
  cases checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget []
      (.lam false (.univ level.val) body) (.pi false (.univ level.val) (.var 0)) with
  | none => rfl
  | some sort =>
      exact False.elim (no_abstract_result wf level
        (LoanTyping.PureTyping.Checker.check?_sound checked).2 recognized (.refl _))

/-- Exact admitted version-6 globals supply the original typing derivation
used for reconstruction. -/
theorem checked_global_universe {env : Environment} {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (recognized : UniverseRecognized [] declaration.value) :
    ∃ scheme : Scheme [], RawValue.Conv env scheme.syntax declaration.value ∧
      RawValue.Conv env scheme.type declaration.type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Nonempty (Finite.Carrier (scheme.code assignment)) := by
  obtain ⟨_, _, _, _, _, history, wf, _⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  exact universe_fundamental wf (history.global_value_and_reference found).1 recognized

private def identity : Term := .lam false (.univ 0) (.lam false (.var 0) (.var 0))

private def identityAnnotation : Term :=
  .pi false (.univ 0) (.pi false (.var 0)
    (.free (.alloc (.natural 1) (.integer 0)) (.var 1)))

/-- The executable pure checker accepts a universe-polymorphic identity
whose independently checked result unfolds only by the Free equation. -/
theorem checked_free_universe_identity :
    LoanTyping.Checker.check 32 .empty [] [] true identity identityAnnotation = false ∧
    ∃ scheme : Scheme [], RawValue.Conv .empty scheme.syntax identity ∧
      RawValue.Conv .empty scheme.type identityAnnotation ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Nonempty (Finite.Carrier (scheme.code assignment)) := by
  refine ⟨by cbv, ?_⟩
  have checked : LoanTyping.PureTyping.Checker.check? .empty 32 32 8192 [] identity identityAnnotation =
      some (.type 1) := by cbv
  have recognizedBody : Recognized 1 0 (.lam false (.var 0) (.var 0)) :=
    .lam (.parameter (0 : Fin 1)) (.var (index := 0) (depth := 1) (by decide))
  have recognized : UniverseRecognized [] identity :=
    .abstract ⟨0, by decide⟩ (.body recognizedBody)
  exact universe_fundamental UnifiedProgram.EnvWellFormed.empty
    (LoanTyping.PureTyping.Checker.check?_sound checked).2 recognized

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed.Pure
