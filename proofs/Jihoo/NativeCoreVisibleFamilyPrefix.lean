import Jihoo.NativeScopedProgramHistory

/-! A definition sees exactly the signatures in its checked earlier family
prefix. Filtering the final immutable table by declaration position is
equivalent to that actual intermediate table. -/
namespace Jihoo.NativeKernel.ScopedProgram

open Environment UnifiedProgram

def visibleFamily (env : Environment) (definition family : Nat) : Option CheckedFamily :=
  (env.families[family]?).bind fun entry =>
    if entry.declaration.globals ≤ definition then some entry else none

private theorem family_globally_available {family : Nat} {entry : CheckedFamily}
    (history : History definitions declarations env)
    (found : env.families[family]? = some entry) : entry.declaration.globals ≤ env.globals.size := by
  induction history with
  | empty => simp [Environment.empty] at found
  | @definition definitions declarations env source added history checked ih =>
    exact Nat.le_trans (ih found) (by simp only [Array.size_push]; omega)
  | @family definitions declarations env source added history checked ih =>
    by_cases earlier : family < env.families.size
    · apply ih
      rw [Array.getElem?_eq_getElem earlier]
      simpa only [Array.getElem?_push_lt earlier] using found
    · have inside := (Array.getElem?_eq_some_iff.mp found).1
      simp only [Array.size_push] at inside
      have latest : family = env.families.size := by omega
      subst family
      simp only [Array.getElem?_push_size,Option.some.injEq] at found
      subst entry
      rw [checked.declaration,checked.metadata.1]
      exact Nat.le_refl _

private theorem visible_at_latest (history : History definitions declarations env) (family : Nat) :
    visibleFamily env env.globals.size family = env.families[family]? := by
  unfold visibleFamily
  cases found : env.families[family]? with
  | none => rfl
  | some entry =>
    have available := family_globally_available history found
    simp only [Option.bind_some,ite_eq_left available]

private theorem later_family_hidden (checked : Families.FamilyChecked env source entry)
    (earlier : definition < env.globals.size) (family : Nat) :
    visibleFamily ⟨env.globals,env.families.push entry⟩ definition family = visibleFamily env definition family := by
  unfold visibleFamily
  by_cases previous : family < env.families.size
  · rw [Array.getElem?_push_lt previous,Array.getElem?_eq_getElem previous]
  · by_cases current : family = env.families.size
    · subst family
      have hidden : ¬ entry.declaration.globals ≤ definition := by
        rw [checked.declaration,checked.metadata.1]
        omega
      rw [Array.getElem?_push_size]
      simp only [Option.bind_some,ite_eq_right hidden,Array.getElem?_eq_none (Nat.le_refl _),Option.bind_none]
    · have outside : env.families.size < family := by omega
      have beyond : (env.families.push entry).size ≤ family := by simp only [Array.size_push]; omega
      rw [Array.getElem?_eq_none beyond,Array.getElem?_eq_none (Nat.le_of_lt outside)]

/-- The family descriptor query uses precisely the earlier mixed-history
prefix at the selected checked definition, including declarations placed at
that same global position before checking the definition. -/
theorem History.global_prefix_visible_families
    (history : History definitions declarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      History prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.globals.size = index ∧
      DeclarationChecked earlierEnv source entry ∧
      (∀ family, earlierEnv.families[family]? = visibleFamily env index family) := by
  induction history with
  | empty => contradiction
  | @definition definitions declarations env source added history checked ih =>
    by_cases earlier : index < env.globals.size
    · have previous : env.globals[index]? = some entry := by
        rw [Array.getElem?_eq_getElem earlier]
        simpa only [Array.getElem?_push_lt earlier] using found
      obtain ⟨ds,fs,earlierEnv,raw,prior,size,valid,visible⟩ := ih previous
      exact ⟨ds,fs,earlierEnv,raw,prior,size,valid,visible⟩
    · have inside := (Array.getElem?_eq_some_iff.mp found).1
      simp only [Array.size_push] at inside
      have latest : index = env.globals.size := by omega
      subst index
      simp only [Array.getElem?_push_size,Option.some.injEq] at found
      subst entry
      exact ⟨definitions,declarations,env,source,history,rfl,checked,fun family =>
        (visible_at_latest history family).symm⟩
  | @family definitions declarations env source added history checked ih =>
    have earlier := (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨ds,fs,earlierEnv,raw,prior,size,valid,visible⟩ := ih found
    refine ⟨ds,fs,earlierEnv,raw,prior,size,valid,fun family => ?_⟩
    rw [later_family_hidden checked earlier]
    exact visible family

end Jihoo.NativeKernel.ScopedProgram
