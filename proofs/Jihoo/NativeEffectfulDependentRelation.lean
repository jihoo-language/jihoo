import Jihoo.NativeDependentRelationalContexts
import Jihoo.NativeLoanValueProjection
set_option maxUniverseOffset 40

/-! Effectful value clauses for the general dependent gluing relation. The
same concrete value projection handles arbitrary nested Strict/Free and raw
Lend macros. All finite Pi fibers and valuation contexts remain available;
this is a ghost interpretation, not a heap execution equality. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

/-- Candidate stability under the concrete composed projection, with genuine
family conversion as target. This is stronger than source-Conv saturation. -/
def ProjectedSaturated (A : Ty env Γ sort) : Prop :=
  ∀ point {term replacement value},FamilyIota.Extended.Conv env
    (ValueErasure.Loan.project env term) (ValueErasure.Loan.project env replacement) →
      (A.realizes point term value ↔ A.realizes point replacement value)

/-- Pullback computes a new candidate, retaining its concrete finite code.
Source conversion preservation follows from the proved composed projection. -/
def Ty.projected (A : Ty env Γ sort) (admissible : EnvironmentDelta.Admissible env) : Ty env Γ sort where
  code := A.code
  realizes point term value := A.realizes point (ValueErasure.Loan.project env term) value
  conversion := by
    intro point term replacement value converted
    exact A.conversion point (.old (ValueErasure.Loan.conversion admissible converted))

theorem Ty.projected_saturated (A : Ty env Γ sort) (admissible : EnvironmentDelta.Admissible env) :
    ProjectedSaturated (A.projected admissible) := by
  intro point term replacement value converted
  exact A.conversion point (.old converted)

theorem pi_projected_saturated (A : Ty env Γ domainSort)
    (B : Ty env (Contextual.extend Γ A.code) bodySort) (body : ProjectedSaturated B) :
    ProjectedSaturated (pi A B) := by
  intro point term replacement value converted
  constructor <;> intro realized argument argumentValue admitted
  · apply (body ⟨point,argumentValue⟩ (term := .app term argument) (replacement := .app replacement argument)
      (by
        rw [ValueErasure.Loan.project_application,ValueErasure.Loan.project_application]
        exact .node .app (.cons converted (.cons (.refl _) .nil)))).mp
    exact realized argument argumentValue admitted
  · apply (body ⟨point,argumentValue⟩ (term := .app term argument) (replacement := .app replacement argument)
      (by
        rw [ValueErasure.Loan.project_application,ValueErasure.Loan.project_application]
        exact .node .app (.cons converted (.cons (.refl _) .nil)))).mpr
    exact realized argument argumentValue admitted

theorem substitution_projected_saturated (A : Ty env Δ sort) (stable : ProjectedSaturated A)
    (σ : Contextual.Sub Γ Δ) : ProjectedSaturated (A.substitution σ) := by
  intro point term replacement value converted
  exact stable (σ point) converted

theorem proposition_projected_saturated (truth : Γ → Prop) :
    ProjectedSaturated (proposition env Γ truth) := by
  unfold ProjectedSaturated
  intros
  exact Iff.rfl

theorem strict_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort) (stable : ProjectedSaturated A)
    {first result : Term} {meaning : Contextual.Tm A.code}
    (realized : Realizes Γ A result meaning) : Realizes Γ A (.strict first result) meaning := by
  intro values point related
  have projected : FamilyIota.Extended.Conv env
      (ValueErasure.Loan.project env (.strict (first.subst values) (result.subst values)))
      (ValueErasure.Loan.project env (result.subst values)) := by
    rw [ValueErasure.Loan.project_strict]
    exact .refl _
  have result := (stable point projected).mpr (realized values point related)
  simpa only [Term.strict,Term.subst,substArgs,Op.binders,liftSub] using result

theorem free_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort) (stable : ProjectedSaturated A)
    {owner result : Term} {meaning : Contextual.Tm A.code}
    (realized : Realizes Γ A result meaning) : Realizes Γ A (.free owner result) meaning := by
  intro values point related
  have projected : FamilyIota.Extended.Conv env
      (ValueErasure.Loan.project env (.free (owner.subst values) (result.subst values)))
      (ValueErasure.Loan.project env (result.subst values)) := by
    rw [ValueErasure.Loan.project_free]
    exact .refl _
  have result := (stable point projected).mpr (realized values point related)
  simpa only [Term.free,Term.subst,substArgs,Op.binders,liftSub] using result

theorem typed_strict_fundamental (Γ : Ctx env) (A : Ty env Γ.meaning sort) (stable : ProjectedSaturated A)
    {meaning : Contextual.Tm A.code}
    (firstTyped : HasType env ctx mode first firstType) (resultTyped : HasType env ctx mode result resultType)
    (resultRealized : Realizes Γ A result meaning) :
    HasType env ctx mode (.strict first result) resultType ∧ Realizes Γ A (.strict first result) meaning :=
  ⟨.strict firstTyped resultTyped,strict_realizes Γ A stable resultRealized⟩

theorem typed_free_fundamental (Γ : Ctx env) (A : Ty env Γ.meaning sort) (stable : ProjectedSaturated A)
    {meaning : Contextual.Tm A.code}
    (ownerTyped : HasType env ctx mode owner (.buffer size)) (resultTyped : HasType env ctx mode result resultType)
    (resultRealized : Realizes Γ A result meaning) :
    HasType env ctx mode (.free owner result) resultType ∧ Realizes Γ A (.free owner result) meaning :=
  ⟨.free ownerTyped resultTyped,free_realizes Γ A stable resultRealized⟩

/-- Raw pointwise value coherence transports arbitrary dependent instances;
no normalization result or realization of the changed output is supplied. -/
theorem pointwise_substitution_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    (admissible : EnvironmentDelta.Admissible env) (stable : ProjectedSaturated A)
    {first second : Nat → Term} {term : Term} {meaning : Contextual.Tm A.code}
    (values : ∀ index,ValueErasure.Loan.Coherent env (first index) (second index))
    (realized : Realizes Γ A (term.subst first) meaning) : Realizes Γ A (term.subst second) meaning := by
  intro closing point related
  have projected : FamilyIota.Extended.Conv env
      (ValueErasure.Loan.project env (term.subst first))
      (ValueErasure.Loan.project env (term.subst second)) := ValueErasure.Loan.Coherent.subst_congr admissible values term
  have instantiated := projected.substitution (fun index => ValueErasure.Loan.project env (closing index)) admissible.closed
  rw [←ValueErasure.Loan.project_substitution admissible,←ValueErasure.Loan.project_substitution admissible] at instantiated
  exact (stable point instantiated).mp (realized closing point related)

theorem projected_natural_literal (admissible : EnvironmentDelta.Admissible env) (value : Nat) (bound : value < 2^64) :
    ((natural env Γ).projected admissible).realizes point (.natural value) ⟨value⟩ := by
  change RawLend.Conv env (ValueErasure.Loan.project env (.natural value)) (numeralTree value)
  rw [Term.natural,ValueErasure.Loan.project_ordinary_node (by rfl) (by intro h; cases h)]
  exact natural_literal (Γ := Γ) (point := point) value bound

theorem projected_natural_add (admissible : EnvironmentDelta.Admissible env)
    (first : ((natural env Γ).projected admissible).realizes point a firstValue)
    (second : ((natural env Γ).projected admissible).realizes point b secondValue) :
    ((natural env Γ).projected admissible).realizes point (.uadd a b) ⟨firstValue.down+secondValue.down⟩ := by
  change RawLend.Conv env (ValueErasure.Loan.project env (.uadd a b)) _
  rw [Term.uadd,ValueErasure.Loan.project_ordinary_node (by rfl) (by intro h; cases h)]
  exact natural_add (Γ := Γ) (point := point) first second

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
