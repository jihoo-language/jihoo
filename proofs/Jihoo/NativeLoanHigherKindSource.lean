import Jihoo.NativeHigherKindSource
import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanMixedProgram
set_option maxUniverseOffset 40

/-! The complete existing higher-kind Recognized grammar is reconstructed
directly from the actual Loan64 judgment and its genuine raw Lend conversion.
The intrinsic Expression and concrete finite denotation are reused, rather
than supplied as semantic candidates. Native input universes remain below 32;
the existing administrative hierarchy also interprets their result kinds.
Recognized is still an explicit source-coverage premise: this is not the
fundamental theorem or consistency theorem for arbitrary Loan64 terms. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

private def InputUniverseBound : Term → Prop
  | .univ level => level < 32
  | _ => True

private theorem universe_bound (typed : LoanTyping.HasType env loans ctx mode term type) :
    InputUniverseBound term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => InputUniverseBound term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim => split <;> trivial

/-- The input ceiling follows from every actual Loan64 typing rule, including
arbitrary result conversions. Administrative Type32 is not an extra input. -/
theorem universe_input_bound (typed : LoanTyping.HasType env loans ctx mode (.univ level) type) :
    level < 32 := universe_bound typed

theorem kind_valid_of_typed (kind : Kind)
    (typed : LoanTyping.HasType env loans ctx mode kind.syntax type) : kind.Valid := by
  induction kind generalizing loans ctx mode type with
  | base level => exact universe_input_bound typed
  | arrow domain codomain hd hc =>
      obtain ⟨domainSort,bodySort,domainTyped,bodyTyped,converted⟩ := typed.principalView
      exact ⟨hd domainTyped,hc bodyTyped⟩

/-- Kind injectivity uses the Loan64 raw Lend relation itself. No certificate
in the earlier, smaller source conversion is an input. -/
theorem kind_syntax_injective (wf : UnifiedProgram.EnvWellFormed env) {first second : Kind}
    (converted : Conv env first.syntax second.syntax) : first = second := by
  induction first generalizing second with
  | base level =>
      cases second with
      | base other =>
          have same := converted.full_universe_injective wf.admissible
          exact congrArg Kind.base (Fin.ext same)
      | arrow domain codomain =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .universe level.val) (op' := .pi false) rfl rfl (by intro h; cases h)
            converted wf.admissible)
  | arrow domain codomain hd hc =>
      cases second with
      | base level =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .pi false) (op' := .universe level.val) rfl rfl (by intro h; cases h)
            converted wf.admissible)
      | arrow other result =>
          obtain ⟨erased,first,second⟩ := converted.pi_injective wf.admissible
          cases hd first
          cases hc second
          rfl

theorem kind_classified_sort (wf : UnifiedProgram.EnvWellFormed env) (kind : Kind) (sort : SortTag)
    (converted : Conv env kind.syntax sort.term) :
    ∃ level, kind = .base level ∧ sort = .type level.val := by
  cases kind with
  | base level =>
      cases sort with
      | prop =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .universe level.val) (op' := .prop) rfl rfl (by intro h; cases h)
            converted wf.admissible)
      | type value =>
          have same := converted.full_universe_injective wf.admissible
          exact ⟨level,rfl,congrArg SortTag.type same.symm⟩
  | arrow domain codomain =>
      cases sort with
      | prop =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .pi false) (op' := .prop) rfl rfl (by intro h; cases h) converted wf.admissible)
      | type value =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .pi false) (op' := .universe value) rfl rfl (by intro h; cases h)
            converted wf.admissible)

/-- All constructors of the existing Recognized grammar are retained, under
arbitrary source prefix binders and arbitrary loan stacks. Source typing
constructs the intrinsic expression and its original requested-type conversion. -/
theorem recognized_principal_frame (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term) (frame : Frame kinds ctx positions)
    (typed : LoanTyping.HasType env loans ctx mode (term.rename positions) type) :
    ∃ kind, ∃ expression : Expression kinds kind,
      expression.syntax = term ∧ Conv env kind.syntax type := by
  induction recognized generalizing kinds loans ctx positions mode type with
  | @var index =>
      simp only [Term.rename] at typed
      obtain ⟨binding,found,converted⟩ := typed.principalView
      rw [frame index] at found
      cases selected : kinds[index]? with
      | none => simp [selected] at found
      | some kind =>
          simp only [selected,Option.map,Option.some.injEq] at found
          cases found
          exact ⟨kind,.var (.ofLookup selected),rfl,converted⟩
  | u64 =>
      have original : LoanTyping.HasType env loans ctx mode .u64 type := by
        simpa only [Term.u64,Term.rename,renameArgs] using typed
      exact ⟨.base ⟨0,by decide⟩,.u64,rfl,original.principalView⟩
  | univ level =>
      have original : LoanTyping.HasType env loans ctx mode (.univ level.val) type := by
        simpa only [Term.univ,Term.rename,renameArgs] using typed
      exact ⟨.base ⟨level.val+1,by omega⟩,.univ level,rfl,original.principalView⟩
  | @lam body domain recognized ih =>
      simp only [Term.lam,Term.rename,renameArgs,Op.binders,Kind.syntax_rename,liftRenaming] at typed
      obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
      have domainTyped := by cases binder with | intro formed allowed => exact formed
      have valid := kind_valid_of_typed domain domainTyped
      obtain ⟨codomain,bodyExpression,source,bodyConverted⟩ := ih (frame.extend domain) bodyTyped
      refine ⟨.arrow domain codomain,.lam valid bodyExpression,?_,?_⟩
      · simp only [Expression.syntax,source]
      · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted
  | @app function argument recognizedFunction recognizedArgument ihf iha =>
      simp only [Term.app,Term.rename,renameArgs,Op.binders,liftRenaming] at typed
      obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
      obtain ⟨functionKind,functionExpression,functionSource,functionConverted⟩ := ihf frame functionTyped
      cases functionKind with
      | base level =>
          exact False.elim (RawLend.Conv.full_rigid_disjoint
            (op := .universe level.val) (op' := .pi erased) rfl rfl (by intro h; cases h)
            functionConverted wf.admissible)
      | arrow input output =>
          have components := functionConverted.pi_injective wf.admissible
          obtain ⟨argumentKind,argumentExpression,argumentSource,argumentConverted⟩ := iha frame argumentTyped
          have same : argumentKind = input :=
            kind_syntax_injective wf (argumentConverted.trans components.2.1.symm)
          subst argumentKind
          refine ⟨output,.app functionExpression argumentExpression,?_,?_⟩
          · simp only [Expression.syntax,functionSource,argumentSource]
          · have result := components.2.2.substitution (single (argument.rename positions)) wf.closed
            rw [Kind.syntax_subst] at result
            exact result.trans resultConverted
  | @arrowCode domain codomain recognizedDomain recognizedCodomain ihd ihc =>
      simp only [Term.pi,Term.rename,renameArgs,Op.binders] at typed
      have shifted : (codomain.rename Nat.succ).rename (liftRenaming 1 positions) =
          codomain.rename (fun index => positions index + 1) := by
        rw [Term.rename_comp]
        congr 1
      rw [shifted] at typed
      obtain ⟨domainSort,bodySort,domainTyped,bodyTyped,converted⟩ := typed.principalView
      obtain ⟨domainKind,domainExpression,domainSource,domainConverted⟩ := ihd frame domainTyped
      obtain ⟨bodyKind,bodyExpression,bodySource,bodyConverted⟩ :=
        ihc (frame.weaken ⟨domain.rename positions,false⟩) bodyTyped
      obtain ⟨first,domainShape,domainSortShape⟩ :=
        kind_classified_sort wf domainKind domainSort domainConverted
      obtain ⟨second,bodyShape,bodySortShape⟩ :=
        kind_classified_sort wf bodyKind bodySort bodyConverted
      subst domainKind
      subst bodyKind
      subst domainSort
      subst bodySort
      refine ⟨.base (maxLevel first second),.arrowCode domainExpression bodyExpression,?_,converted⟩
      simp only [Expression.syntax,domainSource,bodySource]

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term)
    (typed : LoanTyping.HasType env loans (context kinds) mode term type) :
    ∃ kind, ∃ expression : Expression kinds kind,
      expression.syntax = term ∧ Conv env kind.syntax type :=
  recognized_principal_frame wf recognized (Frame.identity kinds)
    (by simpa only [Term.rename_id] using typed)

/-- Actual Loan64 typing constructs the same concrete finite semantic value
as the existing higher-kind model, at every semantic input valuation. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans (context kinds) mode term type)
    (recognized : Recognized term) :
    ∃ kind, ∃ expression : Expression kinds kind,
      expression.syntax = term ∧ Conv env kind.syntax type ∧
      ∀ _values : Values kinds, Nonempty (Finite.Carrier kind.code) := by
  obtain ⟨kind,expression,source,converted⟩ := recognized_principal wf recognized typed
  exact ⟨kind,expression,source,converted,fun values => ⟨expression.meaning values⟩⟩

theorem checked_fundamental
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans (context kinds) mode term type)
    (recognized : Recognized term) :
    ∃ kind, ∃ expression : Expression kinds kind,
      expression.syntax = term ∧ Conv env kind.syntax type ∧
      ∀ _values : Values kinds, Nonempty (Finite.Carrier kind.code) :=
  native_fundamental history.wellFormed typed recognized

/-- Universe outputs are decoded from the source-constructed expression. No
normal form, old-conversion witness, candidate or output realization is given. -/
theorem native_code_fundamental (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 33)
    (typed : LoanTyping.HasType env loans (context kinds) mode term (.univ level.val))
    (recognized : Recognized term) :
    ∃ expression : Expression kinds (.base level), expression.syntax = term ∧
      ∀ values : Values kinds, ∃ code : Finite.Universe (.type ⟨level.val,by omega⟩),
        code = Finite.AdministrativeValues.decode level (expression.meaning values) := by
  obtain ⟨kind,expression,source,converted⟩ := recognized_principal wf recognized typed
  have same : kind = .base level := kind_syntax_injective wf converted
  subst kind
  exact ⟨expression,source,fun values => ⟨_,rfl⟩⟩

theorem checked_code_fundamental
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env) (level : Fin 33)
    (typed : LoanTyping.HasType env loans (context kinds) mode term (.univ level.val))
    (recognized : Recognized term) :
    ∃ expression : Expression kinds (.base level), expression.syntax = term ∧
      ∀ values : Values kinds, ∃ code : Finite.Universe (.type ⟨level.val,by omega⟩),
        code = Finite.AdministrativeValues.decode level (expression.meaning values) :=
  native_code_fundamental history.wellFormed level typed recognized

/-- Complete mixed admission supplies the closed Loan64 body derivation at
its exact expanded annotation. Only the existing syntax-coverage premise
remains local; the expression and concrete inhabitant are constructed. -/
theorem checked_declaration_fundamental
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source expanded)
    (recognized : Recognized expanded.value) :
    ∃ kind, ∃ expression : Expression [] kind,
      expression.syntax = expanded.value ∧ Conv env kind.syntax expanded.type ∧
      Nonempty (Finite.Carrier kind.code) := by
  obtain ⟨sort,formed,typed,resource⟩ := checked.valid.typing
  obtain ⟨kind,expression,sourceEq,converted,model⟩ :=
    checked_fundamental (kinds := []) history typed recognized
  exact ⟨kind,expression,sourceEq,converted,model .nil⟩

theorem admitted_declaration_fundamental
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source = some expanded)
    (recognized : Recognized expanded.value) :
    ∃ kind, ∃ expression : Expression [] kind,
      expression.syntax = expanded.value ∧ Conv env kind.syntax expanded.type ∧
      Nonempty (Finite.Carrier kind.code) :=
  checked_declaration_fundamental history (LoanTyping.MixedProgram.checkDeclaration_sound accepted) recognized

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64
