import Jihoo.NativeCoreDataMotiveDomain
import Jihoo.NativeCorePropCaseType
import Jihoo.NativeCoreCaseNormal

/-! After instantiating the written parameters, the data case forms the
motive application at the constructor's indices and value. It uses the
original field annotations from that instantiated telescope. -/
namespace Jihoo.NativeKernel.NativeCoreDataCaseResult

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreShiftedApplications (shiftRoot shift_progress shift_refines)
open NativeCoreDataMotiveDomain (parameters parameters_progress parameters_refines variables variables_progress variables_refines represented_append)
open NativeCorePropCaseType (FieldsRep wrapFields wrapFields_progress wrapFields_refines)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreCaseNormal (appendApplications appendApplications_progress appendApplications_refines)

def run (limit depth : Nat) (state : State) (family constructor params motive : Nat)
    (parametersAt resultIndices : List Nat) (fields : List (Bool × Nat)) : Outcome Nat :=
  let count := fields.length
  (shiftRoot limit depth state motive count).next fun shifted initial =>
    (appendApplications shifted initial (resultIndices.drop params)).next fun indexed spine =>
      (parameters limit depth count parametersAt indexed).next fun withParams leading =>
        (variables ((List.range count).map fun j => count-1-j) withParams).next fun withFields localRefs =>
          let refs := leading ++ localRefs
          (append withFields (.con family constructor refs.length) refs).next fun formed value =>
            (append formed .app [spine,value]).next fun after result =>
              wrapFields fields after result

private theorem applications_progress (state : State) (motive : Nat) (indices : List Nat) :
    Progress limit state (appendApplications state motive indices) := by
  obtain ⟨retained,ticks,_,_⟩ := appendApplications_progress state motive indices
  exact Progress.uncharged retained ticks

theorem run_progress : Progress limit state (run limit depth state family constructor params motive parametersAt resultIndices fields) := by
  unfold run
  exact shift_progress.next fun _ =>
    (applications_progress _ _ _).next fun _ =>
      parameters_progress.next fun _ =>
        variables_progress.next fun _ =>
          (append_progress _ _ _).next fun _ =>
            (append_progress _ _ _).next fun _ => wrapFields_progress _ _ _

private theorem represented_drop (count : Nat) (held : RepresentsList arena refs terms) :
    RepresentsList arena (refs.drop count) (terms.drop count) := by
  induction count generalizing refs terms with
  | zero => exact held
  | succ count ih =>
    cases held with
    | nil => exact .nil
    | cons _ tail => exact ih tail

/-- The graph appends the final constructor value and authentic motive
spine at the checked telescope, with parameters in their new field scope. -/
theorem run_refines (motiveRep : Represents state.arena motive M)
    (paramRep : RepresentsList state.arena parametersAt values) (indexRep : RepresentsList state.arena resultIndices indices)
    (fieldsRep : FieldsRep state.arena fields observedFields)
    (success : (run limit depth state family constructor params motive parametersAt resultIndices fields).result = .ok selected) :
    let after := (run limit depth state family constructor params motive parametersAt resultIndices fields).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected
      (observedFields.foldr (fun field tail => .pi field.erased field.domain tail)
        (dataCaseResult family constructor params observedFields.length 0 values M indices)) := by
  unfold run at success ⊢
  obtain ⟨shifted,shiftedOk,nextShift⟩ := Outcome.next_success success
  rw [nextShift] at success ⊢
  obtain ⟨spine,spineOk,nextSpine⟩ := Outcome.next_success success
  rw [nextSpine] at success ⊢
  obtain ⟨leading,leadingOk,nextLeading⟩ := Outcome.next_success success
  rw [nextLeading] at success ⊢
  obtain ⟨localRefs,localsOk,nextLocals⟩ := Outcome.next_success success
  rw [nextLocals] at success ⊢
  obtain ⟨ctor,ctorOk,nextCtor⟩ := Outcome.next_success success
  rw [nextCtor] at success ⊢
  obtain ⟨result,resultOk,nextResult⟩ := Outcome.next_success success
  rw [nextResult] at success ⊢
  obtain ⟨shiftKept,shiftBack,shiftRep⟩ := shift_refines motiveRep shiftedOk
  obtain ⟨spineKept,spineBack,_,spineRep⟩ := appendApplications_refines shiftRep
    (represented_drop params (indexRep.frame shiftKept)) spineOk
  have throughSpine := shiftKept.trans spineKept
  obtain ⟨leadingKept,leadingBack,leadingRep⟩ := parameters_refines (paramRep.frame throughSpine) leadingOk
  obtain ⟨localsKept,localsBack,localsRep⟩ := variables_refines localsOk
  have valueRep := represented_append (leadingRep.frame localsKept) localsRep
  obtain ⟨ctorKept,ctorBack,ctorRep⟩ := append_refines valueRep rfl ctorOk
  have spineThroughCtor := leadingKept.trans (localsKept.trans ctorKept)
  obtain ⟨resultKept,resultBack,resultRep⟩ :=
    append_refines (.cons (spineRep.frame spineThroughCtor) (.cons ctorRep .nil)) rfl resultOk
  have beforeFields := throughSpine.trans (spineThroughCtor.trans resultKept)
  obtain ⟨fieldKept,fieldBack,wrapped⟩ := wrapFields_refines (fieldsRep.frame beforeFields) resultRep success
  refine ⟨beforeFields.trans fieldKept,fieldBack ∘ resultBack ∘ ctorBack ∘ localsBack ∘ leadingBack ∘ spineBack ∘ shiftBack,?_⟩
  have arity := NativeCoreIdentical.represented_length valueRep
  have unchanged : (indices.drop params).map (Term.rename (fun i => i)) = indices.drop params := by
    change (indices.drop params).map (Term.rename id) = indices.drop params
    have renameId : Term.rename id = id := by
      funext term
      exact Term.rename_id term
    rw [renameId,List.map_id]
  simpa only [dataCaseResult,← fieldsRep.length_eq,Nat.add_zero,List.map_map,Function.comp_def,Term.app,
    unchanged,arity] using wrapped

/-- The field changes the scope of the motive and original parameter.
The result index participates in the motive spine, while only the field
and the original parameter are passed to the constructor. -/
theorem open_parameter_appends_constructor_value :
    let input : Arena := #[.node (.natural 2) [],.node .u64 [],.var 0,.var 1,.node .i64 [],.var 1]
    run 2 16 ⟨input,0⟩ 0 0 1 2 [2] [5,0] [(false,4)] =
      ⟨⟨input ++ #[.var 1,.node .app [6,0],.var 1,.var 0,.node (.con 0 0 2) [8,9],
        .node .app [7,10],.node (.pi false) [4,11]],2⟩,.ok 12⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreDataCaseResult
