import Jihoo.NativeCoreGhostTypeRequirement

/-! Native code borrowing searches the newest reader first. Each eligible
snapshot shifts its stored owner root to the current context and compares
the variable trees. A match ends the search without visiting older rows. -/
namespace Jihoo.NativeKernel.NativeCoreCodeLeaseLookup

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreGhostSpineInference (next_progress)
open FamilyEnvironment (RelList)

structure Snapshot where
  depth : Nat
  root : Nat

def FramesRep (arena : Arena) (snapshots : List Snapshot) (loans : Loans.Stack) : Prop :=
  RelList (fun snapshot frame => snapshot.depth = frame.depth ∧ Represents arena snapshot.root (.var frame.owner))
    snapshots loans

private def raiseOwner (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  let shifted := NativeCoreTransformExact.run limit depth state root (.shift (Int.ofNat amount)) 0
  ⟨shifted.state,shifted.result.mapError .substitution⟩

private def identical (limit depth : Nat) (state : State) (left right : Nat) : Outcome Bool :=
  let compared := NativeCoreIdentical.runArena state.arena limit depth state.steps left right
  ⟨{state with steps := compared.2},compared.1.mapError .tick⟩

private def visit (limit depth current owner : Nat) : List Snapshot → State → Outcome Bool
  | [],state => ⟨state,.ok false⟩
  | snapshot :: older,state =>
    if snapshot.depth ≤ current then
      (raiseOwner limit depth state snapshot.root (current-snapshot.depth)).next fun shifted formed =>
        (identical limit depth shifted formed owner).next fun checked same =>
          if same then ⟨checked,.ok true⟩ else visit limit depth current owner older checked
    else visit limit depth current owner older state

def run (limit depth current : Nat) (state : State) (snapshots : List Snapshot) (owner : Nat) : Outcome Bool :=
  match state.arena[owner]? with
  | some (.var _) => visit limit depth current owner snapshots state
  | _ => ⟨state,.ok false⟩

private theorem raised_ok (success : (raiseOwner limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift (Int.ofNat amount)) 0).result = .ok selected := by
  unfold raiseOwner at success
  cases status : (NativeCoreTransformExact.run limit depth state root (.shift (Int.ofNat amount)) 0).result <;>
    simp only [status,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

private theorem raiseOwner_progress : Progress limit state (raiseOwner limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift (Int.ofNat amount)) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ success => progress.accepted room _ (raised_ok success)⟩

private theorem identical_progress (room : state.steps ≤ limit) :
    Progress limit state (identical limit depth state left right) := by
  unfold identical
  generalize compared : NativeCoreIdentical.runArena state.arena limit depth state.steps left right = output
  have ⟨monotone,bounded,accepted⟩ := NativeCoreIdentical.runArena_step_bounds
    (arena := state.arena) (depth := depth) (a := left) (b := right) room
  rw [compared] at monotone bounded accepted
  refine ⟨.refl _,monotone,fun _ => bounded,?_⟩
  intro _ answer success
  apply accepted answer
  obtain ⟨status,steps⟩ := output
  cases status with
  | error reason => simp only [Except.mapError,reduceCtorEq] at success
  | ok actual =>
    have same : actual = answer := Except.ok.inj (by simpa only [Except.mapError] using success)
    cases same
    rfl

private theorem visit_progress (room : state.steps ≤ limit) :
    Progress limit state (visit limit depth current owner snapshots state) := by
  induction snapshots generalizing state with
  | nil => exact Progress.atState _ _
  | cons snapshot older ih =>
    unfold visit
    split
    · apply next_progress raiseOwner_progress room
      intro _ _ shiftedRoom
      apply next_progress (identical_progress shiftedRoom) shiftedRoom
      intro same _ checkedRoom
      cases same
      · exact ih checkedRoom
      · exact Progress.atState _ _
    · exact ih room

theorem run_progress (room : state.steps ≤ limit) :
    Progress limit state (run limit depth current state snapshots owner) := by
  unfold run
  split
  · exact visit_progress room
  · exact Progress.atState _ _

private theorem FramesRep.frame (represented : FramesRep arena snapshots loans) (kept : Prefix arena after) :
    FramesRep after snapshots loans := by
  unfold FramesRep at represented ⊢
  induction represented with
  | nil => exact .nil
  | cons represented _ ih => exact .cons ⟨represented.1,represented.2.frame kept⟩ ih

private theorem raised_rep (represented : Represents state.arena root (.var original))
    (success : (raiseOwner limit depth state root amount).result = .ok selected) :
    Represents (raiseOwner limit depth state root amount).state.arena selected (.var (original+amount)) := by
  obtain ⟨_,_,term,shifted,output⟩ := (NativeCoreTransformExact.run_refines
    (mode := .shift (Int.ofNat amount)) (binders := 0) (value := .var original)
    represented trivial (raised_ok success)).1
  change PartialRenaming.shift (amount : Int) 0 (.var original) = some term at shifted
  rw [PartialRenaming.shift_nonnegative (Int.natCast_nonneg amount)] at shifted
  have same : term = .var (original+amount) := by
    simpa [PartialRenaming.raiseIndex,Term.rename] using shifted.symm
  rw [same] at output
  exact output

private theorem identical_refines (leftRep : Represents state.arena left (.var x))
    (rightRep : Represents state.arena right (.var y))
    (success : (identical limit depth state left right).result = .ok result) :
    result = true ↔ x = y := by
  unfold identical at success
  cases resultPair : NativeCoreIdentical.runArena state.arena limit depth state.steps left right with
  | mk compared steps =>
    rw [resultPair] at success
    cases compared with
    | error reason => cases success
    | ok same =>
      cases success
      have equality := NativeCoreIdentical.runArena_reflects_fully_retained leftRep rightRep (.var _) (.var _) resultPair
      simpa only [Term.var.injEq] using equality

private theorem visit_refines (frames : FramesRep state.arena snapshots loans)
    (ownerRep : Represents state.arena owner (.var index))
    (success : (visit limit depth current owner snapshots state).result = .ok available) :
    available = Loans.active current loans index := by
  induction snapshots generalizing loans state available with
  | nil =>
    cases frames
    cases success
    rfl
  | cons snapshot older ih =>
    cases frames with
    | @cons _ frame _ remaining head tail =>
      unfold visit at success
      split at success
      · rename_i inScope
        obtain ⟨lifted,liftedOk,next⟩ := Outcome.next_success success
        rw [next] at success
        obtain ⟨equal,equalOk,compared⟩ := Outcome.next_success success
        rw [compared] at success
        have kept := (raiseOwner_progress (limit := limit) (depth := depth) (state := state)
          (root := snapshot.root) (amount := current-snapshot.depth)).kept
        have raised := raised_rep head.2 liftedOk
        have equalIff := identical_refines raised (ownerRep.frame kept) equalOk
        have expected : frame.indexAt current = some index ↔ frame.owner+(current-snapshot.depth) = index := by
          have bound := head.1 ▸ inScope
          rw [Loans.Frame.indexAt,ite_eq_left bound,← head.1]
          exact ⟨Option.some.inj,congrArg some⟩
        have found : (frame.indexAt current == some index) = equal := by
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro matchFound
            exact equalIff.mpr (expected.mp (beq_iff_eq.mp matchFound))
          · intro same
            exact beq_iff_eq.mpr (expected.mpr (equalIff.mp same))
        cases equal with
        | false =>
          let compared := (identical limit depth (raiseOwner limit depth state snapshot.root (current-snapshot.depth)).state lifted owner).state
          have result := ih (state := compared) (FramesRep.frame tail kept) (ownerRep.frame kept)
            (by simpa only [Bool.false_eq_true,ite_false] using success)
          rw [result]
          simp only [Loans.active,List.any_cons,found,Bool.false_or]
        | true =>
          cases success
          simp only [Loans.active,List.any_cons,found,Bool.true_or]
      · rename_i future
        rw [ih tail ownerRep success]
        have missing : (frame.indexAt current == some index) = false := by
          rw [Loans.Frame.indexAt,← head.1,ite_eq_right future]
          rfl
        simp only [Loans.active,List.any_cons,missing,Bool.false_or]

/-- A successful graph lookup returns exactly the loan permission of the
represented variable at the current context depth, even after shadowing. -/
theorem run_refines (frames : FramesRep state.arena snapshots loans)
    (ownerRep : Represents state.arena owner (.var index))
    (success : (run limit depth current state snapshots owner).result = .ok available) :
    available = Loans.active current loans index := by
  cases ownerRep with
  | var read =>
    simp only [run,read] at success
    exact visit_refines frames (.var read) success

private theorem visit_backward (frames : FramesRep state.arena snapshots loans)
    (success : (visit limit depth current owner snapshots state).result = .ok available)
    (backward : Backward state.arena) : Backward (visit limit depth current owner snapshots state).state.arena := by
  induction snapshots generalizing state loans available with
  | nil => exact backward
  | cons snapshot older ih =>
    cases frames with
    | @cons _ frame _ remaining head tail =>
      unfold visit at success ⊢
      split at success
      · rename_i inScope
        simp only [ite_eq_left inScope]
        obtain ⟨formed,formedOk,formedNext⟩ := Outcome.next_success success
        rw [formedNext] at success ⊢
        obtain ⟨same,sameOk,sameNext⟩ := Outcome.next_success success
        rw [sameNext] at success ⊢
        obtain ⟨kept,shiftBack,_⟩ := (NativeCoreTransformExact.run_refines
          (mode := .shift (Int.ofNat (current-snapshot.depth))) (binders := 0)
          (value := .var frame.owner) head.2 trivial (raised_ok formedOk)).1
        cases same
        · simp only [Bool.false_eq_true,ite_false] at success ⊢
          exact ih (FramesRep.frame tail kept) success (shiftBack backward)
        · exact shiftBack backward
      · rename_i future
        simp only [ite_eq_right future]
        exact ih tail success backward

theorem run_backward (frames : FramesRep state.arena snapshots loans)
    (ownerRep : Represents state.arena owner (.var index))
    (success : (run limit depth current state snapshots owner).result = .ok available)
    (backward : Backward state.arena) : Backward (run limit depth current state snapshots owner).state.arena := by
  cases ownerRep with
  | var read =>
    simp only [run,read] at success ⊢
    exact visit_backward frames success backward

/-- A future entry is skipped. A later matching entry shifts the owner
under two binders, and the older history after the match is untouched. -/
theorem reader_search_rebases_and_stops :
    let input : Arena := #[.var 0,.var 1,.var 2]
    let snapshots : List Snapshot := [⟨4,0⟩,⟨3,1⟩,⟨1,0⟩,⟨3,2⟩]
    run 4 8 3 ⟨input,0⟩ snapshots 2 = ⟨⟨input.push (.var 2),4⟩,.ok true⟩ ∧
      run 2 8 3 ⟨input,0⟩ [⟨4,0⟩,⟨3,1⟩] 2 = ⟨⟨input,2⟩,.ok false⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeLeaseLookup
