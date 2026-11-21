import Jihoo.NativeCoreDataMotiveDomain
import Jihoo.NativeDataSyntax
import Jihoo.NativeLoanFamilyIotaViewAlgebra

/-! Borrowing a field changes its occurrences in the remaining telescope
to dereferences. The field binder and every surrounding index stay in
place, including across subsequent field binders. -/
namespace Jihoo.NativeKernel.NativeCoreViewReading

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreDataMotiveDomain (addVariable variable_progress variable_refines)
open NativeCoreCaseStrict (append append_progress append_refines)

private def transformed (result : NativeCoreTransformExact.Outcome Nat) : Outcome Nat :=
  ⟨result.state,result.result.mapError .substitution⟩

private theorem transform_success (found : (transformed result).result = .ok root) :
    result.result = .ok root := by
  cases status : result.result <;> simp [transformed,status,Except.mapError] at found ⊢
  exact found

private theorem transform_progress (held : NativeCoreTransformExact.Progress limit state result) :
    Progress limit state (transformed result) :=
  ⟨held.kept,held.monotone,held.bounded,fun room root found => held.accepted room root (transform_success found)⟩

def run (limit depth : Nat) (state : State) (body : Nat) : Outcome Nat :=
  (addVariable state 0).next fun withVariable reference =>
    (append withVariable .deref [reference]).next fun withDeref deref =>
      transformed (NativeCoreTransformExact.rewrite limit depth withDeref body 0 deref)

theorem run_progress : Progress limit state (run limit depth state body) := by
  unfold run
  exact variable_progress.next fun _ => (append_progress _ _ _).next fun _ =>
    transform_progress (NativeCoreTransformExact.run_progress _ _ _ _ _ _)

/-- The selected graph root applies the reading substitution at the
original scope, with no removal of the borrowed field's binder. -/
theorem run_refines (source : Represents state.arena body term)
    (success : (run limit depth state body).result = .ok selected) :
    let after := (run limit depth state body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (reading term) := by
  unfold run at success ⊢
  obtain ⟨reference,varOk,varNext⟩ := Outcome.next_success success
  rw [varNext] at success ⊢
  obtain ⟨deref,derefOk,derefNext⟩ := Outcome.next_success success
  rw [derefNext] at success ⊢
  obtain ⟨first,firstBackward,variableRep⟩ := variable_refines varOk
  obtain ⟨second,secondBackward,derefRep⟩ := append_refines (.cons variableRep .nil) rfl derefOk
  have added := first.trans second
  obtain ⟨kept,backward,held⟩ := NativeCoreTransformExact.rewrite_refines
    (target := 0) (source.frame added) derefRep (transform_success success)
  refine ⟨added.trans kept,backward ∘ secondBackward ∘ firstBackward,?_⟩
  rw [PartialRenaming.rewrite_eq_subst] at held
  have same : PartialRenaming.replaceIndex 0 (Term.deref (.var 0)) =
      (fun | 0 => Term.deref (.var 0) | n+1 => .var (n+1)) := by
    funext index
    cases index <;> simp [PartialRenaming.replaceIndex]
  have observed : term.subst (PartialRenaming.replaceIndex 0 (Term.deref (.var 0))) = reading term := by
    unfold reading
    exact congrArg (fun replacement => term.subst replacement) same
  exact observed ▸ held

private theorem reading_weakened (term : Term) :
    reading (term.rename Nat.succ) = term.rename Nat.succ := by
  unfold reading
  rw [Term.subst_rename,←Environment.variable_subst_eq_rename]

/-- Extending the field prefix either retains the new binder's ordinary
value or reads it through the borrow. Every older field moves under the
same binder without another dereference. -/
theorem viewRead_append (previous : List Bool) (borrowed : Bool) (tail : Term) :
    viewRead (previous ++ [borrowed]) tail =
      let opened := tail.subst (liftSubOne (viewReadAt previous))
      if borrowed then reading opened else opened := by
  cases borrowed
  · simp only [viewRead,Bool.false_eq_true,ite_false]
    apply congrArg (fun values => tail.subst values)
    funext index
    cases index with
    | zero =>
      rw [LoanTyping.FamilyIota.viewReadAt_last]
      rfl
    | succ index =>
      exact LoanTyping.FamilyIota.viewReadAt_previous previous false index
  · simp only [viewRead,ite_true,reading,Term.subst_comp]
    apply congrArg (fun values => tail.subst values)
    funext index
    cases index with
    | zero =>
      rw [LoanTyping.FamilyIota.viewReadAt_last]
      simp only [ite_true,liftSubOne,Term.subst]
    | succ index =>
      rw [LoanTyping.FamilyIota.viewReadAt_previous]
      exact (reading_weakened (viewReadAt previous index)).symm

private def readFixture : Arena :=
  #[.var 0,.var 1,.node .u64 [],.node .app [0,1],.node .app [1,0],.node (.pi false) [2,4]]

/-- Native reading retains the surrounding slot at the root and the
locally bound slot inside the Pi. Only the borrowed field is dereferenced. -/
theorem reading_matches_native_scope :
    run 5 16 ⟨readFixture,0⟩ 3 =
      ⟨⟨readFixture ++ #[.var 0,.node .deref [6],.node .app [7,1]],5⟩,.ok 8⟩ ∧
    run 7 16 ⟨readFixture,0⟩ 5 =
      ⟨⟨readFixture ++ #[.var 0,.node .deref [6],.var 1,.node .deref [8],.node .app [9,0],
        .node (.pi false) [2,10]],7⟩,.ok 11⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreViewReading
