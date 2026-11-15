import Jihoo.NativeLoanMixedProgram

/-! Authentic family metadata only needs closed transparent global storage and
actual checked family telescopes. Global typing/resource evidence is retained
by the stronger program histories, which construct this common dependency. -/
namespace Jihoo.NativeKernel.ScopedProgram
open Environment UnifiedProgram

structure DeclarationChecked (env : Environment) (source expanded : GlobalDeclaration) : Prop where
  typeExpansion : GlobalEnvironment.Expansion env.globals source.type expanded.type
  valueExpansion : GlobalEnvironment.Expansion env.globals source.value expanded.value
  closed : expanded.type.Scoped 0 ∧ expanded.value.Scoped 0 ∧
    expanded.type.WellFormed ∧ expanded.value.WellFormed
  transparent : GlobalEnvironment.GlobalFree expanded.type ∧ GlobalEnvironment.GlobalFree expanded.value

inductive History : List GlobalDeclaration → List FamilyDeclaration → Environment → Prop where
  | empty : History [] [] Environment.empty
  | definition : History definitions familyDeclarations env → DeclarationChecked env source expanded →
      History (definitions ++ [source]) familyDeclarations ⟨env.globals.push expanded, env.families⟩
  | family : History definitions familyDeclarations env → Families.FamilyChecked env source entry →
      History definitions (familyDeclarations ++ [source]) ⟨env.globals, env.families.push entry⟩

theorem History.wellFormed (history : History definitions familyDeclarations env) :
    UnifiedProgram.EnvWellFormed env := by
  induction history with
  | empty => exact UnifiedProgram.EnvWellFormed.empty
  | definition history checked ih =>
      exact ih.pushGlobal checked.closed checked.transparent
  | family history checked ih => exact ih.pushFamily checked.signatures_scoped

theorem History.globalLength (history : History definitions familyDeclarations env) :
    env.globals.size = definitions.length := by
  induction history <;> simp_all [Environment.empty]

theorem History.familyLength (history : History definitions familyDeclarations env) :
    env.families.size = familyDeclarations.length := by
  induction history <;> simp_all [Environment.empty]

/-- Lookup provenance retains the exact validated earlier mixed prefix. -/
theorem History.global_prefix
    (history : History definitions familyDeclarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      History prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.globals.size = index ∧
      DeclarationChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      have bounded : index < env.globals.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.globals.size
      · have old : env.globals[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushGlobal env added)⟩
      · have same : index = env.globals.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushGlobal env entry⟩
  | @family definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushFamily env added)⟩

theorem History.family_prefix
    (history : History definitions familyDeclarations env)
    {index : Nat} {entry : CheckedFamily} (found : env.families[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      History prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.families.size = index ∧
      Families.FamilyChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushGlobal env added)⟩
  | @family definitions families env source added history checked ih =>
      have bounded : index < env.families.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.families.size
      · have old : env.families[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushFamily env added)⟩
      · have same : index = env.families.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushFamily env entry⟩


theorem History.ofUnified (history : UnifiedProgramChecked definitions declarations env) :
    History definitions declarations env := by
  induction history with
  | empty => exact .empty
  | @definition definitions families earlier source expanded previous checked ih =>
      have globalsFree : ∀ entry ∈ earlier.globals.toList, GlobalEnvironment.GlobalFree entry.value := by
        intro entry member
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
        exact (ih.wellFormed.transparent index entry (by simpa using selected)).2
      exact .definition ih ⟨checked.typeExpansion,checked.valueExpansion,checked.closed,
        checked.typeExpansion.globalFree globalsFree,checked.valueExpansion.globalFree globalsFree⟩
  | family previous checked ih => exact .family ih checked

theorem History.ofLoanMixed
    (history : Environment.LoanTyping.MixedProgram.History definitions declarations env) :
    History definitions declarations env := by
  induction history with
  | empty => exact .empty
  | definition previous checked ih =>
      exact .definition ih ⟨checked.typeExpansion,checked.valueExpansion,checked.closed,
        checked.valid.typeTransparent,checked.valid.valueTransparent⟩
  | family previous checked ih => exact .family ih checked

end Jihoo.NativeKernel.ScopedProgram
