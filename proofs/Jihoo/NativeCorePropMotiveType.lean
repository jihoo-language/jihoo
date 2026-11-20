import Jihoo.NativeCoreGhostTypeRequirement

/-! The proposition eliminator builds one shared word row and a proposition
row, then wraps the requested number of relevant index domains. -/
namespace Jihoo.NativeKernel.NativeCorePropMotiveType

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)

private def addDomains (word : Nat) : Nat → State → Nat → Outcome Nat
  | 0, state, range => ⟨state,.ok range⟩
  | count+1, state, range =>
    (append state (.pi false) [word,range]).next fun after root => addDomains word count after root

def run (state : State) (arity : Nat) : Outcome Nat :=
  (append state .u64 []).next fun withWord word =>
    (append withWord .prop []).next fun withProp prop =>
      addDomains word arity withProp prop

private theorem addDomains_progress (word arity : Nat) (state : State) (range : Nat) :
    Progress limit state (addDomains word arity state range) := by
  induction arity generalizing state range with
  | zero => exact Progress.atState _ _
  | succ arity ih => exact (append_progress _ _ _).next (fun _ => ih _ _)

theorem run_progress (state : State) (arity : Nat) : Progress limit state (run state arity) :=
  (append_progress _ _ _).next fun _ => (append_progress _ _ _).next fun _ => addDomains_progress _ _ _ _

private theorem addDomains_refines
    (wordRep : Represents state.arena word .u64) (rangeRep : Represents state.arena range body)
    (success : (addDomains word count state range).result = .ok selected) :
    let after := (addDomains word count state range).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after selected type ∧ type = (List.replicate count (false,Term.u64)).foldr
        (fun binder range => .pi binder.1 binder.2 range) body := by
  induction count generalizing state range body selected with
  | zero =>
    simp only [addDomains,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,body,rangeRep,rfl⟩
  | succ count ih =>
    unfold addDomains at success ⊢
    obtain ⟨root,added,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨addedKept,addedBack,product⟩ := append_refines (.cons wordRep (.cons rangeRep .nil)) rfl added
    obtain ⟨kept,backward,type,represented,built⟩ := ih (wordRep.frame addedKept) product success
    refine ⟨addedKept.trans kept,backward ∘ addedBack,type,represented,?_⟩
    -- Appending at the outer end yields the same repeated word domains.
    rw [List.replicate_succ',List.foldr_append]
    exact built

private theorem folded_is_motive (arity : Nat) :
    (List.replicate arity (false,Term.u64)).foldr (fun binder range => .pi binder.1 binder.2 range) .prop = propMotiveType arity := by
  induction arity with
  | zero => rfl
  | succ count ih => simp only [List.replicate_succ,List.foldr_cons,propMotiveType,ih]

theorem run_refines (success : (run state arity).result = .ok selected) :
    let after := (run state arity).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected (propMotiveType arity) := by
  unfold run at success ⊢
  obtain ⟨word,wordOk,wordNext⟩ := Outcome.next_success success
  rw [wordNext] at success ⊢
  obtain ⟨prop,propOk,propNext⟩ := Outcome.next_success success
  rw [propNext] at success ⊢
  obtain ⟨wordKept,wordBack,wordRep⟩ := append_refines .nil rfl wordOk
  obtain ⟨propKept,propBack,propRep⟩ := append_refines .nil rfl propOk
  obtain ⟨kept,backward,_,represented,shape⟩ := addDomains_refines (wordRep.frame propKept) propRep success
  rw [shape,folded_is_motive] at represented
  exact ⟨wordKept.trans (propKept.trans kept),backward ∘ propBack ∘ wordBack,represented⟩

/-- Both new Pi rows share the original freshly appended word type, and the
eliminator does not spend a normalization tick while forming this type. -/
theorem two_indices_share_word :
    let input : Arena := #[.node (.natural 0) []]
    run ⟨input,5⟩ 2 = ⟨⟨input ++ #[.node .u64 [],.node .prop [],.node (.pi false) [1,2],.node (.pi false) [1,3]],5⟩,.ok 4⟩ := by cbv

end Jihoo.NativeKernel.NativeCorePropMotiveType
