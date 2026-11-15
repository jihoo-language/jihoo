import Jihoo.NativeGhostValueIotaErasure

/-! Dependent annotation coherence after ghost value projection. This relation
uses the installed genuine family/delta/beta/ACU conversion on projected terms;
it does not add Strict/Free equations to the kernel's source conversion. -/
namespace Jihoo.NativeKernel.Environment.Semantics.ValueErasure

/-- Equality available to the ghost value interpretation. Both projections
expand the same admitted environment and erase only shaped Strict/Free nodes. -/
def Coherent (env : Environment) (first second : Term) : Prop :=
  FamilyIota.Extended.Conv env (project env first) (project env second)

theorem Coherent.refl (term : Term) : Coherent env term term := FamilyIota.Extended.Conv.refl _

theorem Coherent.symm (related : Coherent env first second) : Coherent env second first :=
  FamilyIota.Extended.Conv.symm related

theorem Coherent.trans (first : Coherent env source middle) (second : Coherent env middle target) :
    Coherent env source target := FamilyIota.Extended.Conv.trans first second

theorem Coherent.of_conversion (admissible : EnvironmentDelta.Admissible env)
    (converted : FamilyIota.Extended.Conv env first second) : Coherent env first second :=
  family_conversion admissible converted

theorem Coherent.of_forward (admissible : EnvironmentDelta.Admissible env)
    (forward : FamilyIota.Extended.Forward env first second) : Coherent env first second :=
  family_forward admissible forward

theorem Coherent.strict (first result : Term) : Coherent env (.strict first result) result := by
  unfold Coherent
  rw [project_strict]
  exact .refl _

theorem Coherent.free (owner result : Term) : Coherent env (.free owner result) result := by
  unfold Coherent
  rw [project_free]
  exact .refl _

theorem Coherent.renaming (admissible : EnvironmentDelta.Admissible env)
    (related : Coherent env first second) (indices : Nat → Nat) :
    Coherent env (first.rename indices) (second.rename indices) := by
  unfold Coherent at *
  rw [project_renaming admissible,project_renaming admissible]
  exact related.renaming indices admissible.closed

theorem Coherent.substitution (admissible : EnvironmentDelta.Admissible env)
    (related : Coherent env first second) (values : Nat → Term) :
    Coherent env (first.subst values) (second.subst values) := by
  unfold Coherent at *
  rw [project_substitution admissible,project_substitution admissible]
  exact related.substitution (fun index => project env (values index)) admissible.closed

/-- Pointwise projected values suffice even when their original sources are
not convertible. Every dependent binder edge uses native capture avoidance. -/
theorem Coherent.subst_congr (admissible : EnvironmentDelta.Admissible env)
    (related : ∀ index,Coherent env (first index) (second index)) (term : Term) :
    Coherent env (term.subst first) (term.subst second) := by
  unfold Coherent at *
  rw [project_substitution admissible,project_substitution admissible]
  exact FamilyIota.Extended.Conv.subst_congr admissible.closed related (project env term)

theorem Coherent.substitution_congr (admissible : EnvironmentDelta.Admissible env)
    (terms : Coherent env first second)
    (values : ∀ index,Coherent env (original index) (replacement index)) :
    Coherent env (first.subst original) (second.subst replacement) :=
  (terms.substitution admissible original).trans (Coherent.subst_congr admissible values second)

/-- Exact equality, rather than conversion, is retained for substitutions
whose projected components are equal. -/
theorem project_substitution_eq (admissible : EnvironmentDelta.Admissible env)
    (same : ∀ index,project env (original index) = project env (replacement index)) (term : Term) :
    project env (term.subst original) = project env (term.subst replacement) := by
  rw [project_substitution admissible,project_substitution admissible]
  exact congrArg (fun values => (project env term).subst values) (funext same)

/-- The original checked replay alignment is enough to align a changed value
interpretation with its actual domain. No normalizer-output certificate or
source realization hypothesis is used. -/
theorem closing_annotation_coherent (admissible : EnvironmentDelta.Admissible env)
    {original replacement : Nat → Term}
    (aligned : FamilyIota.Extended.Conv env (annotation.subst original) actualDomain)
    (values : ∀ index,Coherent env (original index) (replacement index)) :
    FamilyIota.Extended.Conv env
      ((project env annotation).subst (fun index => project env (replacement index)))
      (project env actualDomain) := by
  have result := (Coherent.subst_congr admissible values annotation).symm.trans
    (Coherent.of_conversion admissible aligned)
  simpa only [Coherent,project_substitution admissible] using result

/-- In particular the actual replay itself already determines its projected
dependent annotation, without changing any argument. -/
theorem closing_annotation_projection (admissible : EnvironmentDelta.Admissible env)
    (aligned : FamilyIota.Extended.Conv env (annotation.subst values) actualDomain) :
    FamilyIota.Extended.Conv env
      ((project env annotation).subst (fun index => project env (values index)))
      (project env actualDomain) := by
  simpa only [project_substitution admissible] using family_conversion admissible aligned

/-- Actual source lookup and replay values can therefore be projected together.
The existential binding and slot equality remain the original checked ones. -/
theorem source_slot_projection (admissible : EnvironmentDelta.Admissible env)
    (source : ∃ binding,lookup ctx index = some binding ∧ values index = actualValue ∧
      FamilyIota.Extended.Conv env (binding.ty.subst values) actualDomain) :
    ∃ binding,lookup ctx index = some binding ∧ project env (values index) = project env actualValue ∧
      FamilyIota.Extended.Conv env
        ((project env binding.ty).subst (fun slot => project env (values slot)))
        (project env actualDomain) := by
  obtain ⟨binding,found,same,aligned⟩ := source
  exact ⟨binding,found,congrArg (project env) same,closing_annotation_projection admissible aligned⟩

end Jihoo.NativeKernel.Environment.Semantics.ValueErasure
