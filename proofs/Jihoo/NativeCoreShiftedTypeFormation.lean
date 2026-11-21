import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreShiftedApplications
import Jihoo.NativeCoreGlobalAnnotation
import Jihoo.NativeLoanResourceModes

/-! Local and global inference returns a shifted copy of an original
annotation. Its formation follows from the original checked context or
declaration, independently of the typing of the inferred value. -/
namespace Jihoo.NativeKernel.NativeCoreShiftedTypeFormation

open NativeArena NativeProgramWire Environment
open EnvironmentDelta (expand)
open NativeCoreGhostSpineInference (ContextRep)
open NativeCoreShiftedApplications (shiftRoot shift_refines)

theorem lookup_annotation_formed
    (wf : UnifiedProgram.EnvWellFormed env)
    (context : LoanTyping.ResourceModes.ContextFormed env loans ctx)
    {index : Nat} (found : lookup ctx index = some binding) :
    ∃ sort : SortTag, LoanTyping.HasType env [] ctx true binding.ty sort.term := by
  induction context generalizing index binding with
  | nil => cases found
  | @cons ctx erased domain sort _ bound _ ih =>
    cases index with
    | zero =>
      simp only [lookup,Option.some.injEq] at found
      subst binding
      cases bound with
      | intro typed _ =>
        exact ⟨sort,by simpa only [SortTag.rename_term] using typed.ghostWeaken wf domain erased⟩
    | succ index =>
      obtain ⟨previous,selected,rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨sort,typed⟩ := ih selected
      exact ⟨sort,by simpa only [SortTag.rename_term] using typed.ghostWeaken wf domain erased⟩

/-- The type root returned by the actual local annotation shift is formed
at the original binding's sort in the full source context. -/
theorem shifted_local_annotation_formed
    (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env state.arena bindings ctx)
    (formed : LoanTyping.ResourceModes.ContextFormed env loans ctx)
    {index : Nat} (found : bindings[index]? = some binding)
    (success : (shiftRoot limit depth state binding.typeRoot (index+1)).result = .ok selected)
    (output : Represents (shiftRoot limit depth state binding.typeRoot (index+1)).state.arena selected original) :
    ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term := by
  obtain ⟨written,represented,lookup⟩ := context.lookup_type found
  obtain ⟨_,_,shifted⟩ := shift_refines represented success
  rw [output.unique shifted,EnvironmentDelta.expand_renaming wf.admissible]
  exact lookup_annotation_formed wf formed lookup

/-- A visible global's shifted annotation retains the sort originally
checked in the declaration's prefix. Scope ensures the annotation itself
is closed, including in a nonempty reference context. -/
theorem shifted_global_annotation_formed
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions)
    {index : Nat} (found : roots[index]? = some row)
    (success : (shiftRoot limit depth state row.typeRoot amount).result = .ok selected)
    (output : Represents (shiftRoot limit depth state row.typeRoot amount).state.arena selected original) :
    ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term := by
  obtain ⟨entry,written,lookup,represented,expanded⟩ :=
    NativeCoreGlobalAnnotation.checked_type_at history aligned found
  obtain ⟨_,_,_,_,_,_,checked,extension⟩ := history.global_prefix lookup
  obtain ⟨sort,typed,_,_⟩ := checked.valid.typing
  have wf := history.wellFormed
  have renamed := (typed.extend extension).ghostRenaming wf (Δ := ctx) (ρ := id)
    (by intro index binding selected; cases selected)
  obtain ⟨_,_,shifted⟩ := shift_refines represented success
  rw [output.unique shifted,EnvironmentDelta.expand_renaming wf.admissible,expanded,
    Environment.closed_rename checked.valid.typeScoped]
  exact ⟨sort,by simpa only [Term.rename_id] using renamed⟩

end Jihoo.NativeKernel.NativeCoreShiftedTypeFormation
