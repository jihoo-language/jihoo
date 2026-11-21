import Jihoo.NativeLoanMixedAdmission

/-! The same mixed history authenticates the annotation in the original
global table, including references through earlier declarations. -/
namespace Jihoo.NativeKernel.NativeCoreGlobalAnnotation

open NativeArena NativeProgramWire Environment
open EnvironmentDelta (expand)

private theorem represented_at {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (found : roots[index]? = some row) :
    ∃ source, definitions[index]? = some source ∧ RepresentsDefinition arena row source := by
  induction aligned generalizing index with
  | nil => simp at found
  | @cons _ source _ _ head _ tail =>
      cases index with
      | zero => cases found; exact ⟨source, rfl, head⟩
      | succ index => exact tail found

private theorem type_expansion_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : definitions[index]? = some source) :
    ∃ entry, env.globals[index]? = some entry ∧ GlobalEnvironment.Expansion env.globals source.type entry.type := by
  induction history with
  | empty => simp at found
  | @definition definitions declarations env raw entry history checked ih =>
      by_cases earlier : index < definitions.length
      · rw [List.getElem?_append_left earlier] at found
        obtain ⟨previous, previousFound, expanded⟩ := ih found
        have inside : index < env.globals.size := history.globalLength.symm ▸ earlier
        refine ⟨previous, ?_, expanded.extend entry⟩
        rw [Array.getElem?_eq_getElem inside] at previousFound
        exact (Array.getElem?_push_lt (x := entry) inside).trans previousFound
      · have bound := (List.getElem?_eq_some_iff.mp found).1
        have atEnd : index = definitions.length := by simp only [List.length_append, List.length_singleton] at bound; omega
        subst index
        have same : raw = source := by simpa using found
        subst source
        exact ⟨entry, by rw [← history.globalLength, Array.getElem?_push_size], checked.typeExpansion.extend entry⟩
  | family _ _ ih => exact ih found

theorem checked_type_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions arena roots definitions) (found : roots[index]? = some row) :
    ∃ entry written, env.globals[index]? = some entry ∧ Represents arena row.typeRoot written ∧
      expand env written = entry.type := by
  obtain ⟨source, sourceFound, represented⟩ := represented_at aligned found
  obtain ⟨entry, recorded, expanded⟩ := type_expansion_at history sourceFound
  exact ⟨entry, source.type, recorded, represented.1, EnvironmentDelta.expansion_eq_expand expanded⟩

end Jihoo.NativeKernel.NativeCoreGlobalAnnotation
