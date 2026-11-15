import Jihoo.NativeHigherKindModel
import Jihoo.NativeHigherKindFrames
set_option maxUniverseOffset 40

/-! Syntax-only coverage and actual source reconstruction for arbitrary
higher-kinded type-level lambda/application. Result types need only be in the
right genuine conversion class; no raw formation, normalization or same-source
semantic membership premise is supplied. Ordinary value-dependent family
contexts and arbitrary native type primitives remain outside this grammar. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds
open Jihoo.NativeKernel.Environment.Conversion

inductive Recognized : Term → Prop where
  | var : Recognized (.var index)
  | u64 : Recognized .u64
  | univ (level : Fin 32) : Recognized (.univ level.val)
  | lam (domain : Kind) : Recognized body → Recognized (.lam false domain.syntax body)
  | app : Recognized function → Recognized argument → Recognized (.app function argument)
  | arrowCode : Recognized domain → Recognized codomain → Recognized (.pi false domain (codomain.rename Nat.succ))

theorem Expression.recognized (expression : Expression kinds kind) : Recognized expression.syntax := by
  induction expression with
  | var => exact .var
  | u64 => exact .u64
  | univ level => exact .univ level
  | @lam domain kinds codomain valid body ih => exact .lam domain ih
  | app function argument ihf iha => exact .app ihf iha
  | arrowCode domain codomain hd hc => exact .arrowCode hd hc

theorem recognized_principal_frame (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term) (frame : Frame kinds ctx positions)
    (typed : HasType env ctx mode (term.rename positions) type) :
    ∃ kind,∃ expression : Expression kinds kind,expression.syntax = term ∧ Conv env kind.syntax type := by
  induction recognized generalizing kinds ctx positions mode type with
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
    have original : HasType env ctx mode .u64 type := by simpa only [Term.u64,Term.rename,renameArgs] using typed
    exact ⟨.base ⟨0,by decide⟩,.u64,rfl,original.principalView⟩
  | univ level =>
    have original : HasType env ctx mode (.univ level.val) type := by simpa only [Term.univ,Term.rename,renameArgs] using typed
    exact ⟨.base ⟨level.val+1,by omega⟩,.univ level,rfl,original.principalView⟩
  | @lam body domain recognized ih =>
    simp only [Term.lam,Term.rename,renameArgs,Op.binders,Kind.syntax_rename,liftRenaming] at typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    have valid := domain.valid_of_typed domainTyped
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
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .universe level.val) (op' := .pi erased) rfl rfl (by intro h; cases h) functionConverted wf.admissible)
    | arrow input output =>
      have components := functionConverted.pi_injective wf.admissible
      obtain ⟨argumentKind,argumentExpression,argumentSource,argumentConverted⟩ := iha frame argumentTyped
      have same : argumentKind = input := Kind.syntax_injective wf (argumentConverted.trans components.2.1.symm)
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
    obtain ⟨domainSort,bodySort,binder,bodyTyped,converted⟩ := typed.piView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    obtain ⟨domainKind,domainExpression,domainSource,domainConverted⟩ := ihd frame domainTyped
    obtain ⟨bodyKind,bodyExpression,bodySource,bodyConverted⟩ :=
      ihc (frame.weaken ⟨domain.rename positions,false⟩) bodyTyped
    obtain ⟨first,domainShape,domainSortShape⟩ := domainKind.classified_sort wf domainSort domainConverted
    obtain ⟨second,bodyShape,bodySortShape⟩ := bodyKind.classified_sort wf bodySort bodyConverted
    subst domainKind
    subst bodyKind
    subst domainSort
    subst bodySort
    refine ⟨.base (maxLevel first second),.arrowCode domainExpression bodyExpression,?_,converted⟩
    simp only [Expression.syntax,domainSource,bodySource]

theorem recognized_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term) (typed : HasType env (context kinds) mode term type) :
    ∃ kind,∃ expression : Expression kinds kind,expression.syntax = term ∧ Conv env kind.syntax type :=
  recognized_principal_frame wf recognized (Frame.identity kinds)
    (by simpa only [Term.rename_id] using typed)

/-- Actual typing reconstructs the higher-kind intrinsic source and its
concrete finite semantic value at every arbitrary input valuation. -/
theorem native_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context kinds) mode term type) (recognized : Recognized term) :
    ∃ kind,∃ expression : Expression kinds kind,expression.syntax = term ∧ Conv env kind.syntax type ∧
      ∀ _values : Values kinds,Nonempty (Finite.Carrier kind.code) := by
  obtain ⟨kind,expression,source,converted⟩ := recognized_principal wf recognized typed
  exact ⟨kind,expression,source,converted,fun values => ⟨expression.meaning values⟩⟩

/-- At a genuine universe output the exact finite Tarski code is computed
from the reconstructed source, rather than supplied by an output oracle. -/
theorem native_code_fundamental (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 33)
    (typed : HasType env (context kinds) mode term (.univ level.val)) (recognized : Recognized term) :
    ∃ expression : Expression kinds (.base level),expression.syntax = term ∧
      ∀ values : Values kinds,∃ code : Finite.Universe (.type ⟨level.val,by omega⟩),
        code = Finite.AdministrativeValues.decode level (expression.meaning values) := by
  obtain ⟨kind,expression,source,converted⟩ := recognized_principal wf recognized typed
  have same : kind = .base level := Kind.syntax_injective wf converted
  subst kind
  exact ⟨expression,source,fun values => ⟨_,rfl⟩⟩

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds
