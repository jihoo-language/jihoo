import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeOwnedLoopSyntax

/-! Core.fold_body_type and Core.loop_body_type allocate a three-binder
callback type in source order. Shifts operate on the original shared count,
accumulator, or motive roots, at the same depth and on one clock. -/
namespace Jihoo.NativeKernel.NativeCoreIterationTelescope

open NativeArena NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_refines append_progress)

private def appendVariable (state : State) (index : Nat) : Outcome Nat :=
  match addNode state.arena (.var index) with
  | .error reason => ⟨state,.error (.add reason)⟩
  | .ok (arena,root) => ⟨{state with arena},.ok root⟩

private def shifted (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  let result := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨result.state,result.result.mapError .substitution⟩

private def telescope (state : State) (erased : Bool) (word bound domain result : Nat) : Outcome Nat :=
  (append state (.pi erased) [domain,result]).next fun withAcc acc =>
    (append withAcc (.pi true) [bound,acc]).next fun withProof proof =>
      append withProof (.pi false) [word,proof]

def fold (limit depth : Nat) (state : State) (count accumulator : Nat) : Outcome Nat :=
  (append state .u64 []).next fun wordState word =>
    (appendVariable wordState 0).next fun indexState index =>
      (shifted limit depth indexState count 1).next fun countState countAtIndex =>
        (append countState .lt [index,countAtIndex]).next fun boundState bound =>
          (shifted limit depth boundState accumulator 2).next fun domainState domain =>
            (shifted limit depth domainState accumulator 3).next fun resultState result =>
              telescope resultState false word bound domain result

def loop (limit depth : Nat) (state : State) (proof : Bool) (count motive : Nat) : Outcome Nat :=
  (append state .u64 []).next fun wordState word =>
    (appendVariable wordState 0).next fun indexState index =>
      (appendVariable indexState 1).next fun accState accIndex =>
        (appendVariable accState 2).next fun resultState resultIndex =>
          (append resultState (.natural 1) []).next fun oneState one =>
            (shifted limit depth oneState count 1).next fun countState countAtIndex =>
              (append countState .lt [index,countAtIndex]).next fun boundState bound =>
                (shifted limit depth boundState motive 2).next fun domainState before =>
                  (append domainState .app [before,accIndex]).next fun beforeState domain =>
                    (append beforeState .uadd [resultIndex,one]).next fun nextState successor =>
                      (shifted limit depth nextState motive 3).next fun motiveState after =>
                        (append motiveState .app [after,successor]).next fun finishState result =>
                          telescope finishState proof word bound domain result

private theorem shift_answer (checked : (shifted limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shifted at checked
  cases read : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [read,Except.mapError,reduceCtorEq,Except.ok.injEq] at checked ⊢
  exact checked

private theorem variable_progress : Progress limit state (appendVariable state index) := by
  cases added : addNode state.arena (.var index) with
  | error reason =>
    simpa only [appendVariable,added] using (Progress.atState (limit := limit) state (.error (.add reason)) : Progress limit state _)
  | ok result =>
    obtain ⟨arena,root⟩ := result
    simp only [appendVariable,added]
    exact ⟨(addNode_commits added).1,Nat.le_refl _,Nat.le_succ_of_le,fun room _ _ => room⟩

private theorem shifted_progress : Progress limit state (shifted limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room root accepted =>
    progress.accepted room root (shift_answer accepted)⟩

private theorem telescope_progress : Progress limit state (telescope state erased word bound domain result) :=
  (append_progress _ _ _).next fun _ => (append_progress _ _ _).next fun _ => append_progress _ _ _

theorem fold_progress : Progress limit state (fold limit depth state count accumulator) :=
  (append_progress _ _ _).next fun _ => variable_progress.next fun _ => shifted_progress.next fun _ =>
    (append_progress _ _ _).next fun _ => shifted_progress.next fun _ => shifted_progress.next fun _ => telescope_progress

theorem loop_progress : Progress limit state (loop limit depth state proof count motive) :=
  (append_progress _ _ _).next fun _ => variable_progress.next fun _ => variable_progress.next fun _ =>
    variable_progress.next fun _ => (append_progress _ _ _).next fun _ => shifted_progress.next fun _ =>
      (append_progress _ _ _).next fun _ => shifted_progress.next fun _ => (append_progress _ _ _).next fun _ =>
        (append_progress _ _ _).next fun _ => shifted_progress.next fun _ => (append_progress _ _ _).next fun _ =>
          telescope_progress

private def Builds (state : State) (outcome : Outcome Nat) (term : Term) : Prop :=
  ∀ {root}, outcome.result = .ok root →
    Prefix state.arena outcome.state.arena ∧ (Backward state.arena → Backward outcome.state.arena) ∧
      Represents outcome.state.arena root term

private theorem Builds.next {first : Outcome Nat} {thenBuild : State → Nat → Outcome Nat}
    (before : Builds start first value)
    (after : ∀ ref, Prefix start.arena first.state.arena → Represents first.state.arena ref value →
      Builds first.state (thenBuild first.state ref) result) :
    Builds start (first.next thenBuild) result := by
  intro root accepted
  obtain ⟨child,done,next⟩ := Outcome.next_success accepted
  rw [next] at accepted ⊢
  obtain ⟨previous,backward,represented⟩ := before done
  obtain ⟨suffix,suffixBack,selected⟩ := after child previous represented accepted
  exact ⟨previous.trans suffix,suffixBack ∘ backward,selected⟩

private theorem append_builds (children : RepresentsList state.arena refs terms) (arity : refs.length = op.arity) :
    Builds state (append state op refs) (.node op terms) := fun supplied => append_refines children arity supplied

private theorem variable_builds : Builds state (appendVariable state index) (.var index) := by
  intro root accepted
  cases added : addNode state.arena (.var index) with
  | error reason => simp [appendVariable,added] at accepted
  | ok result =>
    obtain ⟨arena,atRoot⟩ := result
    simp only [appendVariable,added,Except.ok.injEq] at accepted ⊢
    subst root
    obtain ⟨kept,_,_,_,_,held⟩ := addNode_commits added
    exact ⟨kept,fun valid => addNode_preserves_backward valid added (by simp [Node.references]),.var held⟩

private theorem shifted_builds (source : Represents state.arena root term) :
    Builds state (shifted limit depth state root amount) (term.rename (fun index => index+amount)) := by
  intro selected accepted
  obtain ⟨kept,backward,residual,expected,represented⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift amount) (binders := 0) (value := term)
      source trivial (shift_answer accepted)).1
  change PartialRenaming.shift amount 0 term = some residual at expected
  rw [PartialRenaming.shift_nonnegative (by omega)] at expected
  have raise : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun x => x+amount := by
    funext index
    simp [PartialRenaming.raiseIndex]
  rw [raise] at expected
  cases expected
  exact ⟨kept,backward,represented⟩

private theorem telescope_builds (wordRep : Represents state.arena word .u64)
    (boundRep : Represents state.arena bound P) (domainRep : Represents state.arena domain A)
    (resultRep : Represents state.arena result B) :
    Builds state (telescope state erased word bound domain result) (.pi false .u64 (.pi true P (.pi erased A B))) := by
  unfold telescope
  apply Builds.next (append_builds (.cons domainRep (.cons resultRep .nil)) rfl)
  intro acc throughAcc inner
  apply Builds.next (append_builds (.cons (boundRep.frame throughAcc) (.cons inner .nil)) rfl)
  intro proof throughProof tail
  exact append_builds (.cons (wordRep.frame (throughAcc.trans throughProof)) (.cons tail .nil)) rfl

/-- The dependent bound refers to the original count weakened into the
index binder. The payload domain and result use distinct weakenings. -/
theorem fold_refines (countRep : Represents state.arena count n) (accRep : Represents state.arena accumulator A)
    (success : (fold limit depth state count accumulator).result = .ok root) :
    let after := (fold limit depth state count accumulator).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after root (foldAccumulatorBodyType n A) := by
  revert root
  change Builds state (fold limit depth state count accumulator) (foldAccumulatorBodyType n A)
  unfold fold foldAccumulatorBodyType
  apply Builds.next (append_builds .nil rfl)
  intro word first wordRep
  apply Builds.next variable_builds
  intro index second indexRep
  apply Builds.next (shifted_builds (countRep.frame (first.trans second)))
  intro shiftedCount third countAtIndex
  have renamedCount : n.rename (fun index => index+1) = n.rename Nat.succ := rfl
  rw [renamedCount] at countAtIndex
  apply Builds.next (append_builds (.cons (indexRep.frame third) (.cons countAtIndex .nil)) rfl)
  intro bound fourth boundRep
  have accHere := accRep.frame (first.trans (second.trans (third.trans fourth)))
  apply Builds.next (shifted_builds accHere)
  intro domain fifth domainRep
  apply Builds.next (shifted_builds (accHere.frame fifth))
  intro result sixth resultRep
  exact telescope_builds (wordRep.frame (second.trans (third.trans (fourth.trans (fifth.trans sixth)))))
    (boundRep.frame (fifth.trans sixth)) (domainRep.frame sixth) resultRep

/-- A dependent Loop uses the actual weakened motive twice, at `i` and
`i+1`. The proof bit controls the accumulator binder in the built graph. -/
theorem loop_refines (countRep : Represents state.arena count n) (motiveRep : Represents state.arena motive M)
    (success : (loop limit depth state proof count motive).result = .ok root) :
    let after := (loop limit depth state proof count motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after root (loopBodyType n M proof) := by
  revert root
  change Builds state (loop limit depth state proof count motive) (loopBodyType n M proof)
  unfold loop loopBodyType
  apply Builds.next (append_builds .nil rfl)
  intro word first wordRep
  apply Builds.next variable_builds
  intro index second indexRep
  apply Builds.next variable_builds
  intro accIndex third accIndexRep
  apply Builds.next variable_builds
  intro resultIndex fourth resultIndexRep
  apply Builds.next (append_builds .nil rfl)
  intro one fifth oneRep
  have beforeCount := first.trans (second.trans (third.trans (fourth.trans fifth)))
  apply Builds.next (shifted_builds (countRep.frame beforeCount))
  intro boundIndex sixth countAtIndex
  have renamedCount : n.rename (fun index => index+1) = n.rename Nat.succ := rfl
  rw [renamedCount] at countAtIndex
  apply Builds.next (append_builds (.cons (indexRep.frame (third.trans (fourth.trans (fifth.trans sixth))))
    (.cons countAtIndex .nil)) rfl)
  intro bound seventh boundRep
  have motiveHere := motiveRep.frame (beforeCount.trans (sixth.trans seventh))
  apply Builds.next (shifted_builds motiveHere)
  intro before eighth motiveBefore
  apply Builds.next (append_builds (.cons motiveBefore
    (.cons (accIndexRep.frame (fourth.trans (fifth.trans (sixth.trans (seventh.trans eighth))))) .nil)) rfl)
  intro domain ninth domainRep
  have afterOne := sixth.trans (seventh.trans (eighth.trans ninth))
  apply Builds.next (append_builds (.cons (resultIndexRep.frame (fifth.trans afterOne))
    (.cons (oneRep.frame afterOne) .nil)) rfl)
  intro successor tenth successorRep
  apply Builds.next (shifted_builds (motiveHere.frame (eighth.trans (ninth.trans tenth))))
  intro after eleventh motiveAfter
  apply Builds.next (append_builds (.cons motiveAfter (.cons (successorRep.frame eleventh) .nil)) rfl)
  intro result twelfth resultRep
  have finished := eighth.trans (ninth.trans (tenth.trans (eleventh.trans twelfth)))
  intro selected accepted
  exact telescope_builds (erased := proof) (wordRep.frame (second.trans (third.trans (fourth.trans (fifth.trans
    (sixth.trans (seventh.trans finished))))))) (boundRep.frame finished)
    (domainRep.frame (tenth.trans (eleventh.trans twelfth))) resultRep accepted

private def openInputs : Arena := #[.var 0,.node .buffer [0],.var 1,.node (.natural 0) []]

/-- The three Fold shifts share five ticks, and Loop spends three ticks on
its count and two motive shifts. Append order preserves all binder edges. -/
theorem open_telescope_rows_and_cost :
    (let built := fold 5 16 ⟨openInputs,0⟩ 0 1
     built.state.steps = 5 ∧ built.result = .ok 14 ∧ built.state.arena = openInputs ++
       #[.node .u64 [],.var 0,.var 1,.node .lt [5,6],.var 2,.node .buffer [8],.var 3,
         .node .buffer [10],.node (.pi false) [9,11],.node (.pi true) [7,12],.node (.pi false) [4,13]]) ∧
    (let built := loop 3 16 ⟨openInputs,0⟩ true 0 2
     built.state.steps = 3 ∧ built.result = .ok 18 ∧ built.state.arena = openInputs ++
       #[.node .u64 [],.var 0,.var 1,.var 2,.node (.natural 1) [],.var 1,.node .lt [5,9],.var 3,
         .node .app [11,6],.node .uadd [7,8],.var 4,.node .app [14,13],.node (.pi true) [12,15],
         .node (.pi true) [10,16],.node (.pi false) [4,17]]) := by cbv

end Jihoo.NativeKernel.NativeCoreIterationTelescope
