import Jihoo.NativeCoreGhostTypeRequirement

/-! Constructor branch types apply the original motive under fresh binders.
Each argument is shifted and appended before the next one is visited, so
failure retains exactly the earlier graph allocations. -/
namespace Jihoo.NativeKernel.NativeCoreShiftedApplications

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)

def shiftRoot (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  let shifted := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨shifted.state,shifted.result.mapError .substitution⟩

private theorem shift_success (success : (shiftRoot limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shiftRoot at success
  cases observed : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [observed,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

theorem shift_progress : Progress limit state (shiftRoot limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room root success =>
    progress.accepted room root (shift_success success)⟩

theorem shift_refines (source : Represents state.arena root written)
    (success : (shiftRoot limit depth state root amount).result = .ok selected) :
    let after := (shiftRoot limit depth state root amount).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (written.rename (fun index => index + amount)) := by
  obtain ⟨kept,backward,residual,shifted,represented⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift amount) (binders := 0) (value := written)
      source trivial (shift_success success)).1
  change PartialRenaming.shift amount 0 written = some residual at shifted
  rw [PartialRenaming.shift_nonnegative (by omega)] at shifted
  have shape : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun index => index + amount := by
    funext index
    simp [PartialRenaming.raiseIndex]
  rw [shape] at shifted
  cases shifted
  exact ⟨kept,backward,represented⟩

def arguments (limit depth amount : Nat) : List Nat → State → Nat → Outcome Nat
  | [], state, callee => ⟨state,.ok callee⟩
  | root :: rest, state, callee =>
      (shiftRoot limit depth state root amount).next fun shifted argument =>
        (append shifted .app [callee,argument]).next fun after applied =>
          arguments limit depth amount rest after applied

def run (limit depth : Nat) (state : State) (callee calleeShift argumentShift : Nat) (roots : List Nat) : Outcome Nat :=
  (shiftRoot limit depth state callee calleeShift).next fun shifted function =>
    arguments limit depth argumentShift roots shifted function

theorem arguments_progress (limit depth amount : Nat) (roots : List Nat) (state : State) (callee : Nat) :
    Progress limit state (arguments limit depth amount roots state callee) := by
  induction roots generalizing state callee with
  | nil => exact Progress.atState _ _
  | cons root rest ih =>
    exact shift_progress.next fun _ => (append_progress _ _ _).next fun _ => ih _ _

theorem run_progress : Progress limit state (run limit depth state callee calleeShift argumentShift roots) :=
  shift_progress.next (fun _ => arguments_progress _ _ _ _ _ _)

theorem arguments_refines (calleeRep : Represents state.arena callee fn)
    (args : RepresentsList state.arena roots terms)
    (success : (arguments limit depth amount roots state callee).result = .ok selected) :
    let after := (arguments limit depth amount roots state callee).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (applications fn (terms.map fun value => value.rename (fun index => index + amount))) := by
  induction roots generalizing state callee terms fn selected with
  | nil =>
    cases args
    simp only [arguments,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,calleeRep⟩
  | cons root rest ih =>
    cases args with
    | cons argument remaining =>
      unfold arguments at success ⊢
      obtain ⟨shifted,shiftedOk,shiftedNext⟩ := Outcome.next_success success
      rw [shiftedNext] at success ⊢
      obtain ⟨applied,appliedOk,appliedNext⟩ := Outcome.next_success success
      rw [appliedNext] at success ⊢
      obtain ⟨shiftKept,shiftBack,shiftedRep⟩ := shift_refines argument shiftedOk
      obtain ⟨appKept,appBack,appRep⟩ := append_refines (.cons (calleeRep.frame shiftKept) (.cons shiftedRep .nil)) rfl appliedOk
      have throughApp := shiftKept.trans appKept
      obtain ⟨restKept,restBack,represented⟩ := ih appRep (remaining.frame throughApp) success
      exact ⟨throughApp.trans restKept,restBack ∘ appBack ∘ shiftBack,represented⟩

/-- The result represents the motive weakened beneath all the new binders,
applied from left to right to the correctly weakened written indices. -/
theorem run_refines (calleeRep : Represents state.arena callee fn)
    (args : RepresentsList state.arena roots terms)
    (success : (run limit depth state callee calleeShift argumentShift roots).result = .ok selected) :
    let after := (run limit depth state callee calleeShift argumentShift roots).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (applications (fn.rename (fun index => index + calleeShift))
        (terms.map fun value => value.rename (fun index => index + argumentShift))) := by
  unfold run at success ⊢
  obtain ⟨shifted,shiftOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨shiftKept,shiftBack,shiftedRep⟩ := shift_refines calleeRep shiftOk
  obtain ⟨kept,backward,represented⟩ := arguments_refines shiftedRep (args.frame shiftKept) success
  exact ⟨shiftKept.trans kept,backward ∘ shiftBack,represented⟩

theorem open_motive_applies_shifted_indices :
    let arena : Arena := #[.var 0,.var 1]
    run 3 8 ⟨arena,0⟩ 0 2 1 [0,1] = ⟨⟨arena ++ #[.var 2,.var 1,.node .app [2,3],.var 2,.node .app [4,5]],3⟩,.ok 6⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreShiftedApplications
