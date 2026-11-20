import Jihoo.NativeCoreGhostReferenceTypes
import Jihoo.NativeLoanLendQuantity

/-! A runtime binder is first inspected for an owner-return pair.
Other heads are normalized again by the native owned-value query. -/
namespace Jihoo.NativeKernel.NativeCoreCodeLinearity

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSort (Visit)
open NativeCoreGhostReferenceTypes (BoxedFamilies)
open EnvironmentDelta (expand expandArgs)

private def isBack : Option Node → Bool
  | some (.node (.back _) _) => true
  | _ => false

private def isOwned (boxed : Nat → Bool) : Option Node → Bool
  | some (.node .buffer _) => true
  | some (.node (.ind family _) _) => boxed family
  | _ => false

def run (normal : Visit) (boxed : Nat → Bool) (state : State) (type : Nat) : Outcome Bool :=
  (normal state type).next fun exposed candidate =>
    if isBack exposed.arena[candidate]? then ⟨exposed,.ok true⟩
    else
      (normal exposed candidate).next fun after selected => ⟨after,.ok (isOwned boxed after.arena[selected]?)⟩

theorem run_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (run normal boxed state type) := by
  unfold run
  apply (normalProgress _ _).next
  intro candidate
  split
  · exact Progress.atState _ _
  · exact (normalProgress _ _).next (fun _ => Progress.atState _ _)

private theorem back_is_linear (held : Represents arena selected term) (classified : isBack arena[selected]? = true) :
    LoanTyping.ResourceReplay.linearDomain env (expand env term) = true := by
  cases held with
  | var found => simp only [found,isBack,reduceCtorEq] at classified
  | @node _ op refs children found width represented =>
    simp only [found] at classified
    cases op
    case back flag =>
      have length : children.length = 2 := (NativeCoreIdentical.represented_length represented).symm.trans width
      rcases children with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
      simp only [expand,expandArgs,LoanTyping.ResourceReplay.linearDomain]
    all_goals cases classified

private theorem owned_is_linear (metadata : BoxedFamilies env boxed) (held : Represents arena selected term)
    (classified : isOwned boxed arena[selected]? = true) :
    LoanTyping.ResourceReplay.linearDomain env (expand env term) = true := by
  cases held with
  | var found => simp only [found,isOwned,reduceCtorEq] at classified
  | @node _ op refs children found width represented =>
    simp only [found] at classified
    cases op
    case buffer =>
      have length : children.length = 1 := (NativeCoreIdentical.represented_length represented).symm.trans width
      rcases children with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp at length
      simp only [expand,expandArgs,LoanTyping.ResourceReplay.linearDomain,LoanTyping.Checker.ownedHead]
    case ind family arity =>
      obtain ⟨entry,familyFound,heap⟩ := metadata family classified
      simp only [expand,LoanTyping.ResourceReplay.linearDomain,LoanTyping.Checker.ownedHead,familyFound,Option.any_some,heap]
    all_goals cases classified

/-- Positive classification exposes a convertible linear head from the
actual arena, for both owner-return pairs and checked heap types. -/
theorem run_refines (metadata : BoxedFamilies env boxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena type written)
    (success : (run normal boxed state type).result = .ok result) :
    let after := (run normal boxed state type).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      (result = true → ∃ residual, RawLend.Conv env (expand env written) residual ∧
        LoanTyping.ResourceReplay.linearDomain env residual = true) := by
  unfold run at success ⊢
  obtain ⟨candidate,firstOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,_,candidateRep,converted⟩ := normalSound onBase source firstOk
  split at success
  · rename_i isPair
    simp only [ite_eq_left isPair]
    exact ⟨kept,backward,fun _ => ⟨_,converted.converted,back_is_linear candidateRep isPair⟩⟩
  · rename_i other
    simp only [ite_eq_right other]
    obtain ⟨root,secondOk,secondNext⟩ := Outcome.next_success success
    rw [secondNext] at success ⊢
    obtain ⟨nextKept,nextBack,_,represented,related⟩ :=
      normalSound (onBase.trans kept) candidateRep secondOk
    refine ⟨kept.trans nextKept,nextBack ∘ backward,?_⟩
    intro linear
    have selected := (Except.ok.inj success).trans linear
    exact ⟨_,converted.converted.trans related.converted,owned_is_linear metadata represented selected⟩

/-- These are the three binder annotations used by native lambda
inference. Only a direct Back bypasses the separate owned-type visit. -/
theorem operational_linearity_meter :
    let arena : Arena := #[.node (.natural 2) [],.node .u64 [],.node .buffer [0],
      .node (.lam false) [2,1],.node (.back false) [2,3]]
    let input : State := ⟨arena,0⟩
    let normal := NativeCorePureComputationNormal.run 16 16
    run normal (fun _ => false) input 1 = ⟨⟨arena,2⟩,.ok false⟩ ∧
      run normal (fun _ => false) input 2 = ⟨⟨arena,4⟩,.ok true⟩ ∧
      run normal (fun _ => false) input 4 = ⟨⟨arena,7⟩,.ok true⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeLinearity
