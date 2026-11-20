import Jihoo.NativeDependentInequalityRelation
import Jihoo.NativeDependentEqualityRelation

set_option maxUniverseOffset 40

/-! A ghost comparison chooses the same interpreted result as the source
conditional. The successful arm gets its actual erased proof substitution,
including in an open dependent context. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

def ifLtMeaning (A : Ty env Γ sort) (left right : Contextual.Tm (natural env Γ).code)
    (yes : Contextual.Tm (A.substitution (Contextual.weaken (A := (less env left right).code))).code)
    (no : Contextual.Tm A.code) : Contextual.Tm A.code :=
  fun point => if ordered : (left point).down < (right point).down then yes ⟨point,⟨⟨ordered⟩⟩⟩
    else no point

/-- A true comparison gives the checked branch the original erased evidence
and leaves the dependent result in the enclosing fiber. The false
comparison preserves the enclosing valuation without extending it. -/
theorem ifLt_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    {yesMeaning : Contextual.Tm (A.substitution (Contextual.weaken (A := (less env left right).code))).code}
    {noMeaning : Contextual.Tm A.code}
    (first : Realizes Γ (natural env Γ.meaning) a left)
    (second : Realizes Γ (natural env Γ.meaning) b right)
    (yes : Realizes (Γ.extend (less env left right)) (A.substitution Contextual.weaken) whenTrue yesMeaning)
    (no : Realizes Γ A whenFalse noMeaning)
    (fits : ∀ values point, Γ.realizes values point → (left point).down < 2^64 ∧ (right point).down < 2^64) :
    Realizes Γ A (.ifLt a b whenTrue whenFalse) (ifLtMeaning A left right yesMeaning noMeaning) := by
  intro values point assigned
  obtain ⟨firstFits,secondFits⟩ := fits values point assigned
  let m := (left point).down
  let n := (right point).down
  have leftLiteral : RawLend.Conv env (a.subst values) (.natural m) :=
    (first values point assigned).trans (natural_literal (Γ := Γ.meaning) (point := point) m firstFits).symm
  have rightLiteral : RawLend.Conv env (b.subst values) (.natural n) :=
    (second values point assigned).trans (natural_literal (Γ := Γ.meaning) (point := point) n secondFits).symm
  have exposed : RawLend.Conv env ((Term.ifLt a b whenTrue whenFalse).subst values)
      (.ifLt (.natural m) (.natural n) (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values)) := by
    simp only [Term.ifLt,Term.subst,substArgs,Op.binders,liftSub]
    exact .node .ifLt (.cons leftLiteral (.cons rightLiteral (.cons (.refl _) (.cons (.refl _) .nil))))
  by_cases smaller : m < n
  · let proofTerm := Term.decide (.natural m) (.natural n)
    let proofValue : Finite.Carrier ((less env left right).code point) := ⟨⟨smaller⟩⟩
    have related := Γ.extend_realizes (less env left right) (term := proofTerm) (value := proofValue) assigned trivial
    have branch := yes (push values proofTerm) ⟨point,proofValue⟩ related
    have selected := RawLend.Conv.old (env := env) (.legacy (.ifLtTrue m n
      (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values) smaller))
    have reduced : RawLend.Conv env ((Term.ifLt a b whenTrue whenFalse).subst values)
        (whenTrue.subst (push values proofTerm)) := by
      rw [← lifted_instantiation]
      exact exposed.trans selected
    have result := (A.conversion point reduced).mpr branch
    have meaning : ifLtMeaning A left right yesMeaning noMeaning point = yesMeaning ⟨point,proofValue⟩ := by
      unfold ifLtMeaning
      exact dite_eq_left (show (left point).down < (right point).down from smaller)
    rw [meaning]
    exact result
  · have selected := RawLend.Conv.old (env := env) (.legacy (.ifLtFalse m n
      (whenTrue.subst (liftSub 1 values)) (whenFalse.subst values) (Nat.le_of_not_gt smaller)))
    have result := (A.conversion point (exposed.trans selected)).mpr (no values point assigned)
    have meaning : ifLtMeaning A left right yesMeaning noMeaning point = noMeaning point := by
      unfold ifLtMeaning
      exact dite_eq_right (show ¬ (left point).down < (right point).down from smaller)
    rw [meaning]
    exact result

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
