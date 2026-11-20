import Jihoo.NativeDependentBranchRelation

set_option maxUniverseOffset 40

/-! Equality branches pass the actual reflexive proof to the true arm.
Its raw realization satisfies subsequent dependent Transport operations. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

def ifEqMeaning (A : Ty env Γ sort) (left right : Contextual.Tm (natural env Γ).code)
    (yes : Contextual.Tm (A.substitution (Contextual.weaken (A := (equality env left right).code))).code)
    (no : Contextual.Tm A.code) : Contextual.Tm A.code :=
  fun point => if same : (left point).down = (right point).down then yes ⟨point,⟨⟨same⟩⟩⟩
    else no point

/-- The actual equality conditional uses literal paths after both words
realize their numeric meanings. Its true arm has a canonical reflexivity
witness in the extended context and returns in the original fiber. -/
theorem ifEq_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    {yesMeaning : Contextual.Tm (A.substitution (Contextual.weaken (A := (equality env left right).code))).code}
    {noMeaning : Contextual.Tm A.code}
    (first : Realizes Γ (natural env Γ.meaning) a left)
    (second : Realizes Γ (natural env Γ.meaning) b right)
    (yes : Realizes (Γ.extend (equality env left right)) (A.substitution Contextual.weaken) whenTrue yesMeaning)
    (no : Realizes Γ A whenFalse noMeaning)
    (fits : ∀ values point, Γ.realizes values point → (left point).down < 2^64 ∧ (right point).down < 2^64) :
    Realizes Γ A (.ifEq a b whenTrue whenFalse) (ifEqMeaning A left right yesMeaning noMeaning) := by
  intro values point assigned
  obtain ⟨firstFits,secondFits⟩ := fits values point assigned
  let m := (left point).down
  let n := (right point).down
  have lhs := natural_literal (env := env) (Γ := Γ.meaning) (point := point) m firstFits
  have rhs := natural_literal (env := env) (Γ := Γ.meaning) (point := point) n secondFits
  have leftLiteral := (first values point assigned).trans lhs.symm
  have rightLiteral := (second values point assigned).trans rhs.symm
  have exposed : RawLend.Conv env ((Term.ifEq a b whenTrue whenFalse).subst values)
      (.ifEq (.natural m) (.natural n) (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values)) := by
    simp only [Term.ifEq,Term.subst,substArgs,Op.binders,liftSub]
    exact .node .ifEq (.cons leftLiteral (.cons rightLiteral (.cons (.refl _) (.cons (.refl _) .nil))))
  by_cases same : m = n
  · let proofTerm := Term.refl (.natural m)
    let proofValue : Finite.Carrier ((equality env left right).code point) := ⟨⟨same⟩⟩
    have canonical : (equality env left right).realizes point proofTerm proofValue :=
      .node .refl (.cons lhs .nil)
    have related := Γ.extend_realizes (equality env left right) assigned canonical
    have branch := yes (push values proofTerm) ⟨point,proofValue⟩ related
    have selected := RawLend.Conv.old (env := env) (.legacy (.ifEqTrue m
      (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values)))
    have reduced : RawLend.Conv env ((Term.ifEq a b whenTrue whenFalse).subst values)
        (whenTrue.subst (push values proofTerm)) := by
      rw [← lifted_instantiation]
      rw [← same] at exposed
      exact exposed.trans selected
    have result := (A.conversion point reduced).mpr branch
    have meaning : ifEqMeaning A left right yesMeaning noMeaning point = yesMeaning ⟨point,proofValue⟩ := by
      unfold ifEqMeaning
      exact dite_eq_left (show (left point).down = (right point).down from same)
    rw [meaning]
    exact result
  · have selected := RawLend.Conv.old (env := env) (.legacy (.ifEqFalse m n
      (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values) same))
    have result := (A.conversion point (exposed.trans selected)).mpr (no values point assigned)
    have meaning : ifEqMeaning A left right yesMeaning noMeaning point = noMeaning point := by
      unfold ifEqMeaning
      exact dite_eq_right (show (left point).down ≠ (right point).down from same)
    rw [meaning]
    exact result

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
