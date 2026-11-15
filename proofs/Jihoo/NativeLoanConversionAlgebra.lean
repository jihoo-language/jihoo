import Jihoo.NativeLoanConversion
import Jihoo.NativeEnvironmentUniquenessAlgebra
import Jihoo.NativeLendReduction

/-! Pure cancellation and scope-removal algebra for Loan64's own raw Lend
conversion. The default60 relation and representation policies stay separate. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem buffer_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.buffer n) (.buffer m)) : Conv env n m := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases kids with | cons hn _ => exact hn

theorem ref_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.ref A) (.ref B)) : Conv env A B := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases kids with | cons hA _ => exact hA

theorem ind_injective (wf : UnifiedProgram.EnvWellFormed env) (h : Conv env (.node (.ind f n) xs) (.node (.ind g m) ys)) :
    f = g ∧ n = m ∧ ListRel (Conv env) xs ys := by
  obtain ⟨op,kids⟩ := h.full_rigid_node_injective rfl rfl wf.admissible
  cases op
  exact ⟨rfl,rfl,kids⟩

theorem applications_congr (hf : Conv env f g) (hxs : ListRel (Conv env) xs ys) :
    Conv env (applications f xs) (applications g ys) := by
  induction hxs generalizing f g with
  | nil => exact hf
  | cons harg htail ih =>
    exact ih (.node .app (.cons hf (.cons harg .nil)))

/-- Substitution by a total unshift map cancels two inserted binders, without
requiring a typed substitution for the discarded variables. -/
def unshiftTwo : Nat → Term
  | 0 | 1 => .natural 0
  | n + 2 => .var n

theorem shifted_two_cancel (t : Term) :
    (t.rename (fun x => x + 2)).subst unshiftTwo = t := by
  rw [Term.subst_rename]
  change t.subst (fun x => .var x) = t
  exact Term.subst_id t

theorem lowered_conversion (wf : UnifiedProgram.EnvWellFormed env) (left : PartialRenaming.shift (-2) 0 a = some outside)
    (right : PartialRenaming.shift (-2) 0 b = some outside') (h : Conv env a b) :
    Conv env outside outside' := by
  rw [←load_result_reweakens left, ←load_result_reweakens right] at h
  simpa only [shifted_two_cancel] using h.substitution unshiftTwo wf.closed

theorem viewMotiveType_dependency_unique (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env (viewMotiveType first owner) (viewMotiveType second owner')) : first = second := by
  cases first <;> cases second
  · rfl
  · exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .universe 0) (op' := .pi false)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  · exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .pi false) (op' := .universe 0)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  · rfl

private theorem related_drop (related : ListRel (Conv env) xs ys) (n : Nat) :
    ListRel (Conv env) (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih =>
    cases related with
    | nil => exact .nil
    | cons first rest => exact ih rest

theorem eliminationResult_congr (entry : CheckedFamily) (motive scrutinee : Term)
    (indices : ListRel (Conv env) xs ys) :
    Conv env (eliminationResult entry motive xs scrutinee) (eliminationResult entry motive ys scrutinee) := by
  unfold eliminationResult
  split
  · exact .node .app (.cons (applications_congr (.refl _) (related_drop indices _)) (.cons (.refl _) .nil))
  · exact applications_congr (.refl _) indices


theorem result_outside (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside) :
    Conv env (result.subst (single value)) outside := by
  have reweakens := Environment.Checker.branch_type_reweakens removed
  have substituted := converted.substitution (single value) wf.closed
  simpa only [← reweakens,Term.shift_subst_single] using substituted

end Jihoo.NativeKernel.Environment.LoanTyping
