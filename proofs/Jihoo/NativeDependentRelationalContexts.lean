import Jihoo.NativeDependentLogicalRelation
import Jihoo.NativeLendRawBinding
set_option maxUniverseOffset 40

/-! Arbitrarily interleaved dependent valuation contexts for the concrete
gluing model. These are semantic contexts, not a claim that every native
annotation has already been reconstructed into this model. Lambda/application
clauses use the body/argument induction hypotheses and genuine raw beta only. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

structure Ctx (env : Environment) where
  meaning : Contextual.Context
  realizes : (Nat → Term) → meaning → Prop

def empty (env : Environment) : Ctx env where
  meaning := Contextual.empty
  realizes _ _ := True

def Ctx.extend (Γ : Ctx env) (A : Ty env Γ.meaning sort) : Ctx env where
  meaning := Contextual.extend Γ.meaning A.code
  realizes values point := Γ.realizes (fun index => values (index+1)) point.1 ∧
    A.realizes point.1 (values 0) point.2

def push (values : Nat → Term) (value : Term) : Nat → Term
  | 0 => value
  | index+1 => values index

theorem Ctx.extend_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    {values : Nat → Term} {point : Γ.meaning} {term : Term} {value : Finite.Carrier (A.code point)}
    (context : Γ.realizes values point) (argument : A.realizes point term value) :
    (Γ.extend A).realizes (push values term) ⟨point,value⟩ := ⟨context,argument⟩

def Realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort) (term : Term) (meaning : Contextual.Tm A.code) : Prop :=
  ∀ values point,Γ.realizes values point → A.realizes point (term.subst values) (meaning point)

theorem newest_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort) :
    Realizes (Γ.extend A) (A.substitution (Contextual.weaken (A := A.code))) (.var 0)
      (Contextual.newest (A := A.code)) := by
  intro values point related
  simpa only [Term.subst,Ty.substitution,Contextual.newest,Contextual.weaken] using related.2

theorem weaken_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort) (B : Ty env Γ.meaning otherSort)
    {term : Term} {meaning : Contextual.Tm A.code}
    (realized : Realizes Γ A term meaning) :
    Realizes (Γ.extend B) (A.substitution (Contextual.weaken (A := B.code))) (term.rename Nat.succ)
      (Contextual.termSubst meaning (Contextual.weaken (A := B.code))) := by
  intro values point related
  simpa only [Term.subst_rename,Ty.substitution,Contextual.weaken,Contextual.termSubst] using
    realized (fun index => values (index+1)) point.1 related.1

theorem conversion_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    {term replacement : Term} {meaning : Contextual.Tm A.code}
    (closed : EnvironmentDelta.Basis.Closed env) (converted : RawLend.Conv env term replacement)
    (realized : Realizes Γ A term meaning) : Realizes Γ A replacement meaning := by
  intro values point related
  exact (A.conversion point (converted.substitution values closed)).mp (realized values point related)

theorem lifted_instantiation (body : Term) (values : Nat → Term) (argument : Term) :
    (body.subst (liftSub 1 values)).subst (single argument) = body.subst (push values argument) := by
  rw [Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp only [liftSub,liftSubOne,Term.subst,single,push]
  | succ index => exact Term.shift_subst_single (values index) argument

/-- All dependent Pi fibers are supported, including impredicative Prop and
code-valued fibers. The body induction hypothesis is used in the genuinely
extended context, with no supplied realization of the lambda itself. -/
theorem lambda_realizes (Γ : Ctx env) (A : Ty env Γ.meaning domainSort)
    (B : Ty env (Contextual.extend Γ.meaning A.code) bodySort)
    {body : Term} {bodyMeaning : Contextual.Tm B.code}
    (bodyRealized : Realizes (Γ.extend A) B body bodyMeaning) (erased : Bool) (domain : Term) :
    Realizes Γ (pi A B) (.lam erased domain body) (Contextual.lam (A := A.code) (B := B.code) bodyMeaning) := by
  intro values point related argument argumentValue admitted
  have result := bodyRealized (push values argument) ⟨point,argumentValue⟩
    (Γ.extend_realizes A related admitted)
  have beta : RawLend.Conv env (.app ((Term.lam erased domain body).subst values) argument)
      (body.subst (push values argument)) := by
    simp only [Term.lam,Term.subst,substArgs,Op.binders,liftSub]
    exact (RawLend.Conv.old (.legacy (.beta erased (domain.subst values) _ argument))).trans
      (by
        have same := lifted_instantiation body values argument
        simp only [liftSub] at same
        rw [same]
        exact .refl _)
  have semanticBeta := (Finite.piMeaning (A.code point) bodySort (fun value => B.code ⟨point,value⟩)).beta
    (fun value => bodyMeaning ⟨point,value⟩) argumentValue
  change B.realizes ⟨point,argumentValue⟩ _ _
  simp only [Contextual.lam]
  rw [semanticBeta]
  exact (B.conversion ⟨point,argumentValue⟩ beta).mpr result

theorem application_realizes (Γ : Ctx env) (A : Ty env Γ.meaning domainSort)
    (B : Ty env (Contextual.extend Γ.meaning A.code) bodySort)
    {function argument : Term} {functionMeaning : Contextual.Tm (pi A B).code} {argumentMeaning : Contextual.Tm A.code}
    (functionRealized : Realizes Γ (pi A B) function functionMeaning)
    (argumentRealized : Realizes Γ A argument argumentMeaning) :
    Realizes Γ (B.substitution (Contextual.pair Contextual.identity argumentMeaning))
      (.app function argument) (Contextual.app (A := A.code) (B := B.code) functionMeaning argumentMeaning) := by
  intro values point related
  simpa only [Term.app,Term.subst,substArgs,Op.binders,liftSub,Ty.substitution,
    Contextual.app,Contextual.pair,Contextual.identity,id_eq] using
    functionRealized values point related _ _ (argumentRealized values point related)

theorem numeral_realizes (Γ : Ctx env) (value : Nat) (bound : value < 2^64) :
    Realizes Γ (natural env Γ.meaning) (.natural value) (Contextual.numeral value) := by
  intro values point related
  simpa only [Term.natural,Term.subst,substArgs,Contextual.numeral] using natural_literal (env := env) (Γ := Γ.meaning) (point := point) value bound

theorem addition_realizes (Γ : Ctx env)
    {a b : Term} {firstMeaning secondMeaning : Contextual.Tm (Contextual.natural (Γ := Γ.meaning))}
    (first : Realizes Γ (natural env Γ.meaning) a firstMeaning)
    (second : Realizes Γ (natural env Γ.meaning) b secondMeaning) :
    Realizes Γ (natural env Γ.meaning) (.uadd a b) (Contextual.add firstMeaning secondMeaning) := by
  intro values point related
  simpa only [Term.uadd,Term.subst,substArgs,Op.binders,liftSub,Contextual.add] using
    natural_add (first values point related) (second values point related)

def SubstitutionRealizes (Γ Δ : Ctx env) (native : Nat → Term) (semantic : Contextual.Sub Γ.meaning Δ.meaning) : Prop :=
  ∀ values point,Γ.realizes values point → Δ.realizes (fun index => (native index).subst values) (semantic point)

theorem substitution_identity (Γ : Ctx env) : SubstitutionRealizes Γ Γ Term.var Contextual.identity := by
  intro values point related
  simpa only [Term.subst,Contextual.identity,id_eq] using related

theorem substitution_composition (Γ Δ Θ : Ctx env)
    {nativeFirst nativeSecond : Nat → Term}
    {semanticFirst : Contextual.Sub Γ.meaning Δ.meaning} {semanticSecond : Contextual.Sub Δ.meaning Θ.meaning}
    (first : SubstitutionRealizes Γ Δ nativeFirst semanticFirst)
    (second : SubstitutionRealizes Δ Θ nativeSecond semanticSecond) :
    SubstitutionRealizes Γ Θ (fun index => (nativeSecond index).subst nativeFirst)
      (Contextual.compose semanticFirst semanticSecond) := by
  intro values point related
  simpa only [Term.subst_comp,Contextual.compose,Function.comp_apply] using second _ _ (first values point related)

theorem substitution_pair (Γ Δ : Ctx env) (A : Ty env Δ.meaning sort)
    {native : Nat → Term} {semantic : Contextual.Sub Γ.meaning Δ.meaning}
    {term : Term} {meaning : Contextual.Tm (Contextual.typeSubst A.code semantic)}
    (substitution : SubstitutionRealizes Γ Δ native semantic)
    (argument : Realizes Γ (A.substitution semantic) term meaning) :
    SubstitutionRealizes Γ (Δ.extend A) (push native term) (Contextual.pair semantic meaning) := by
  intro values point related
  exact ⟨substitution values point related,argument values point related⟩

/-- A genuine dependent source substitution lifts across the next arbitrary
semantic binder, regardless of how earlier source roles were interleaved. -/
theorem substitution_lift (Γ Δ : Ctx env) (A : Ty env Δ.meaning sort)
    {native : Nat → Term} {semantic : Contextual.Sub Γ.meaning Δ.meaning}
    (substitution : SubstitutionRealizes Γ Δ native semantic) :
    SubstitutionRealizes (Γ.extend (A.substitution semantic)) (Δ.extend A)
      (liftSubOne native) (Contextual.lift semantic) := by
  intro values point related
  constructor
  · simpa only [liftSubOne,Term.subst_rename,Contextual.lift] using
      substitution (fun index => values (index+1)) point.1 related.1
  · simpa only [liftSubOne,Term.subst,Ty.substitution,Contextual.lift] using related.2

theorem substitution_realizes (Γ Δ : Ctx env) (A : Ty env Δ.meaning sort)
    {native : Nat → Term} {semantic : Contextual.Sub Γ.meaning Δ.meaning}
    {term : Term} {meaning : Contextual.Tm A.code}
    (substitution : SubstitutionRealizes Γ Δ native semantic)
    (realized : Realizes Δ A term meaning) :
    Realizes Γ (A.substitution semantic) (term.subst native) (Contextual.termSubst meaning semantic) := by
  intro values point related
  simpa only [Term.subst_comp,Ty.substitution,Contextual.termSubst] using
    realized _ _ (substitution values point related)

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
