import Jihoo.NativeCoreGlobalAnnotation
import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeLoanFunctionInversion
import Jihoo.NativeCoreShiftedApplications
import Jihoo.NativeCoreMeteredVisit

/-! Code inference refers to the original admitted declaration. An
expanded proof body can require ghost mode even when its global name
has an inference rule in code mode. -/
namespace Jihoo.NativeKernel.NativeCoreCodeGlobal

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreGhostSpineInference (Inferred)
open NativeCoreMeteredVisit (charge charge_progress)
open NativeCoreShiftedApplications (shiftRoot shift_progress shift_refines)
open EnvironmentDelta (expand)
open NativeCoreGlobalAnnotation (checked_type_at)

private def afterEntry (limit depth : Nat) (state : State) (root : Nat)
    (roots : List Roots) (visible contextDepth : Nat) : Outcome Inferred :=
  match state.arena[root]? with
  | some (.node (.global index) []) =>
    if index < visible then
      match roots[index]? with
      | some row => (shiftRoot limit depth state row.typeRoot contextDepth).next fun next type =>
          ⟨next,.ok ⟨type,[]⟩⟩
      | none => ⟨state,.error (.invisibleGlobal root)⟩
    else ⟨state,.error (.invisibleGlobal root)⟩
  | _ => ⟨state,.error (.outsideFragment root)⟩

def run (limit depth : Nat) (state : State) (root : Nat)
    (roots : List Roots) (visible contextDepth : Nat) : Outcome Inferred :=
  (charge limit depth state root).next fun entered _ =>
    afterEntry limit (depth-1) entered root roots visible contextDepth

theorem run_progress : Progress limit state (run limit depth state root roots visible contextDepth) := by
  unfold run
  apply (charge_progress _ _ _ _).next
  intro _
  unfold afterEntry
  split
  · split
    · split
      · exact shift_progress.next (fun _ => Progress.atState _ _)
      · exact Progress.atState _ _
    · exact Progress.atState _ _
  · exact Progress.atState _ _

/-- The original global is typed in code mode at the independently admitted
declaration type. Only the selected annotation is delta-expanded. -/
theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (rootsRep : RepresentsDefinitions state.arena roots definitions)
    (source : Represents state.arena root (.node (.global index) []))
    (success : (run limit depth state root roots visible ctx.length).result = .ok answer) :
    let after := (run limit depth state root roots visible ctx.length).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ written, Represents after answer.typeRoot written ∧
        LoanTyping.HasType env loans ctx false (.node (.global index) []) (expand env written) := by
  unfold run at success ⊢
  obtain ⟨⟨⟩,_,entered⟩ := Outcome.next_success success
  rw [entered] at success ⊢
  have node : state.arena[root]? = some (.node (.global index) []) := by
    cases source with
    | node read _ children => cases children; exact read
  simp only [afterEntry,charge,node] at success ⊢
  split at success
  · rename_i visible
    simp only [ite_eq_left visible]
    split at success
    · rename_i row found
      obtain ⟨selected,shifted,continued⟩ := Outcome.next_success success
      rw [continued] at success ⊢
      simp only [Except.ok.injEq] at success
      subst answer
      obtain ⟨entry,written,checked,represented,expanded⟩ := checked_type_at history rootsRep found
      let paid := (charge limit depth state root).state
      obtain ⟨kept,backward,typeRep⟩ := shift_refines (state := paid) represented shifted
      refine ⟨kept,backward,_,typeRep,?_⟩
      rw [EnvironmentDelta.expand_renaming history.wellFormed.admissible,expanded]
      exact .global checked
    · cases success
  · cases success

private def readable (ctx : Context) (ghost : Bool) : Term → Prop
  | .var index => ∃ binding, lookup ctx index = some binding ∧ (ghost = true ∨ binding.erased = false)
  | .node _ _ => True

private theorem typed_readable (typed : LoanTyping.HasType env loans ctx ghost term type) : readable ctx ghost term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx ghost term _ _ => readable ctx ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | exact ⟨_,by assumption,by assumption⟩ | skip

private def equality : Term := .eq (.natural 0) (.natural 0)
private def annotation : Term := .pi true equality equality
private def proofIdentity : Term := .lam true equality (.var 0)
private def proofDeclaration : GlobalDeclaration := ⟨annotation,proofIdentity⟩

/-- Substituting the body into code typing would incorrectly require a
ghost-only erased local to be readable at runtime. -/
theorem ghost_proof_body_not_code :
    ¬ LoanTyping.HasType env loans ctx false proofIdentity output := by
  intro typed
  obtain ⟨_,_,_,body,_⟩ := typed.lamView
  obtain ⟨binding,selected,relevant⟩ := typed_readable body
  simp only [lookup,Option.some.injEq] at selected
  subst binding
  rcases relevant with impossible | impossible <;> cases impossible

theorem admitted_global_does_not_require_code_body
    (found : env.globals[0]? = some proofDeclaration) :
    LoanTyping.HasType env loans ctx false (.node (.global 0) [])
      (annotation.rename (fun i => i+ctx.length)) ∧
    ¬ LoanTyping.HasType env loans ctx false (expand env (.node (.global 0) [])) output := by
  refine ⟨.global found,?_⟩
  rw [EnvironmentDelta.expand_global found]
  exact ghost_proof_body_not_code

/-- Runtime inference keeps the type of the original global and rejects
the same occurrence before its declaration becomes visible. -/
theorem original_global_reference_schedule :
    let arena : Arena := #[.node (.natural 0) [],.node .eq [0,0],.var 0,.node (.lam true) [1,2],
      .node (.pi true) [1,1],.node (.global 0) []]
    let input : State := ⟨arena,0⟩
    run 8 32 input 5 [⟨4,3⟩] 1 0 = ⟨⟨arena,8⟩,.ok ⟨4,[]⟩⟩ ∧
      run 8 32 input 5 [⟨4,3⟩] 0 0 = ⟨⟨arena,1⟩,.error (.invisibleGlobal 5)⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeGlobal
