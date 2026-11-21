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

private theorem shift_result_from_visit
    (selected : (NativeCoreTransformExact.run limit depth entered root (.shift (Int.ofNat amount)) 0).result = .ok result)
    (same : (NativeCoreTransformExact.run limit depth entered root (.shift (Int.ofNat amount)) 0).state = after)
    (output : Represents after.arena result original) :
    (shiftRoot limit depth entered root amount).result = .ok result ∧
      Represents (shiftRoot limit depth entered root amount).state.arena result original := by
  let transformed := NativeCoreTransformExact.run limit depth entered root (.shift (Int.ofNat amount)) 0
  change transformed.result.mapError _ = .ok result ∧ Represents transformed.state.arena result original
  have accepted : transformed.result = .ok result := selected
  have retained : transformed.state = after := same
  rw [accepted,retained]
  exact ⟨rfl,output⟩

/-- A successful local visit supplies the independently checked
annotation formation used when the local is a View subject. -/
theorem local_visit_annotation_formed
    (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env state.arena bindings ctx)
    (formed : LoanTyping.ResourceModes.ContextFormed env loans ctx)
    (read : state.arena[root]? = some (.var index))
    (found : bindings[index]? = some binding)
    (success : (NativeCoreGhostSpineInference.runVisitsWithViews normal roots visible limit isData isBoxed
      shapeTable constructorRoots familyEliminations viewEnv (visits+1) (depth+1) bindings state root).result = .ok answer)
    (output : Represents
      (NativeCoreGhostSpineInference.runVisitsWithViews normal roots visible limit isData isBoxed shapeTable constructorRoots
        familyEliminations viewEnv (visits+1) (depth+1) bindings state root).state.arena answer.typeRoot original) :
    ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term := by
  obtain ⟨selected,same,_⟩ := NativeCoreGhostSpineInference.runVisitsWithViews_local_annotation read found success
  let entered := {state with steps := state.steps+1}
  obtain ⟨accepted,represented⟩ := shift_result_from_visit (entered := entered) selected same output
  exact shifted_local_annotation_formed (state := entered) wf context formed found accepted represented

/-- The global visit uses the historical declaration's checked sort at
the original shifted annotation, in any caller context. -/
theorem global_visit_annotation_formed
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions)
    (read : state.arena[root]? = some (.node (.global index) []))
    (visibleGlobal : index < visible) (found : roots[index]? = some declaration)
    (success : (NativeCoreGhostSpineInference.runVisitsWithViews normal roots visible limit isData isBoxed
      shapeTable constructorRoots familyEliminations viewEnv (visits+1) (depth+1) bindings state root).result = .ok answer)
    (output : Represents
      (NativeCoreGhostSpineInference.runVisitsWithViews normal roots visible limit isData isBoxed shapeTable constructorRoots
        familyEliminations viewEnv (visits+1) (depth+1) bindings state root).state.arena answer.typeRoot original) :
    ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term := by
  obtain ⟨selected,same,_⟩ :=
    NativeCoreGhostSpineInference.runVisitsWithViews_global_annotation read visibleGlobal found success
  let entered := {state with steps := state.steps+1}
  obtain ⟨accepted,represented⟩ := shift_result_from_visit (entered := entered) selected same output
  exact shifted_global_annotation_formed (state := entered) history aligned found accepted represented

end Jihoo.NativeKernel.NativeCoreShiftedTypeFormation
