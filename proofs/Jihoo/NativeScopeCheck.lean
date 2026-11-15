import Jihoo.NativeSyntax

/-! Executable finite scope checking for every native constructor and actual
binder edge. This check is independent of arity, typing and conversion: an
unbound variable in a beta-erased argument is still rejected. -/
namespace Jihoo.NativeKernel

mutual
  def scopeCheck (depth : Nat) : Term → Bool
    | .var index => decide (index < depth)
    | .node op children => scopeCheckArgs depth op 0 children
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf; all_goals omega

  def scopeCheckArgs (depth : Nat) (op : Op) (offset : Nat) : List Term → Bool
    | [] => true
    | term :: rest => scopeCheck (depth + op.binders offset) term && scopeCheckArgs depth op (offset+1) rest
  termination_by children => sizeOf children
  decreasing_by all_goals simp_wf; all_goals omega
end

private theorem and_checked (first second : Bool) :
    (first && second) = true ↔ first = true ∧ second = true := by
  cases first <;> cases second <;> decide

/-- Exact scope completeness and soundness on arbitrary native syntax, even
when an operator has malformed arity or forged metadata payloads. -/
theorem scopeCheck_iff (term : Term) (depth : Nat) : scopeCheck depth term = true ↔ term.Scoped depth := by
  induction term using Term.rec
    (motive_2 := fun children => ∀ depth op offset,
      scopeCheckArgs depth op offset children = true ↔
        ∀ (index : Nat) (term : Term),children[index]? = some term → term.Scoped (depth + op.binders (offset+index)))
    generalizing depth with
  | var index =>
    simp only [scopeCheck,decide_eq_true_eq]
    exact ⟨Term.Scoped.var,by intro h; cases h; assumption⟩
  | node op children ih =>
    constructor
    · intro checked
      rw [scopeCheck] at checked
      apply Term.Scoped.node
      intro index child selected
      simpa only [Nat.zero_add] using (ih depth op 0).mp checked index child selected
    · intro scope
      rw [scopeCheck]
      cases scope with
      | node scopes => exact (ih depth op 0).mpr (by simpa only [Nat.zero_add] using scopes)
  | nil =>
    rename_i depth op offset
    constructor
    · intro checked index term selected; cases selected
    · intro scopes; simp only [scopeCheckArgs]
  | cons first rest ihfirst ihrest =>
    rename_i depth op offset
    constructor
    · intro checked index term selected
      rw [scopeCheckArgs] at checked
      obtain ⟨head,tail⟩ := (and_checked _ _).mp checked
      cases index with
      | zero =>
        cases selected
        simpa only [Nat.add_zero] using (ihfirst (depth + op.binders offset)).mp head
      | succ index =>
        have scope := (ihrest depth op (offset+1)).mp tail index term selected
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using scope
    · intro scopes
      rw [scopeCheckArgs]
      apply (and_checked _ _).mpr
      constructor
      · exact (ihfirst _).mpr (by simpa only [Nat.add_zero] using scopes 0 first rfl)
      · apply (ihrest depth op (offset+1)).mpr
        intro index term selected
        have scope := scopes (index+1) term selected
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using scope

theorem scopeCheck_sound (checked : scopeCheck depth term = true) : term.Scoped depth :=
  (scopeCheck_iff term depth).mp checked

theorem scopeCheck_complete (scope : term.Scoped depth) : scopeCheck depth term = true :=
  (scopeCheck_iff term depth).mpr scope

theorem scopeCheck_rejects (unbound : ¬ term.Scoped depth) : scopeCheck depth term = false := by
  cases checked : scopeCheck depth term with
  | false => rfl
  | true => exact False.elim (unbound (scopeCheck_sound checked))

end Jihoo.NativeKernel
