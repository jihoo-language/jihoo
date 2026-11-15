import Jihoo.NativeLoanPermissions

/-! The source Lend lifetime-head policy is structural under renaming. These
lemmas concern type representation, not execution of a heap release. -/
namespace Jihoo.NativeKernel.Environment.Lending

theorem outlivedHead_rename (term : Term) (ρ : Nat → Nat) :
    outlivedHead env (term.rename ρ) = outlivedHead env term := by
  cases term with
  | var => simp [outlivedHead,Term.rename]
  | node op args =>
    cases op <;> cases args with
    | nil => simp [outlivedHead,Term.rename,renameArgs]
    | cons first rest =>
      cases rest with
      | nil => simp [outlivedHead,Term.rename,renameArgs]
      | cons second tail =>
        cases tail <;> simp [outlivedHead,Term.rename,renameArgs]

theorem Outlived.renaming (closed : Conversion.Closed env)
    (allowed : Outlived env type) (ρ : Nat → Nat) : Outlived env (type.rename ρ) := by
  obtain ⟨normal,converted,head⟩ := allowed
  exact ⟨normal.rename ρ,converted.renaming ρ closed,by simpa only [outlivedHead_rename] using head⟩

theorem outlivedHead_subst (term : Term) (σ : Nat → Term)
    (allowed : outlivedHead env term = true) : outlivedHead env (term.subst σ) = true := by
  cases term with
  | var => simp [outlivedHead] at allowed
  | node op args =>
    cases op <;> cases args with
    | nil => simp_all [outlivedHead,Term.subst,substArgs]
    | cons first rest =>
      cases rest with
      | nil => simp_all [outlivedHead,Term.subst,substArgs]
      | cons second tail =>
        cases tail <;> simp_all [outlivedHead,Term.subst]

theorem Outlived.substitution (closed : Conversion.Closed env)
    (allowed : Outlived env type) (σ : Nat → Term) : Outlived env (type.subst σ) := by
  obtain ⟨normal,converted,head⟩ := allowed
  exact ⟨normal.subst σ,converted.substitution σ closed,outlivedHead_subst normal σ head⟩

end Jihoo.NativeKernel.Environment.Lending
