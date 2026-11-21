import Jihoo.NativeCoreShiftedApplications

/-! The graph checked by a data eliminator binds only nonparameter
indices. Outer parameters are shifted under those binders and precede
the freshly allocated index variables in the family domain. -/
namespace Jihoo.NativeKernel.NativeCoreDataMotiveDomain

open NativeArena NativeCoreGraph Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreShiftedApplications (shiftRoot shift_progress shift_refines)
open NativeCoreCaseStrict (append append_progress append_refines)

def parameters (limit depth count : Nat) : List Nat → State → Outcome (List Nat)
  | [],state => ⟨state,.ok []⟩
  | root :: rest,state =>
    (shiftRoot limit depth state root count).next fun shifted parameter =>
      (parameters limit depth count rest shifted).next fun after suffix =>
        ⟨after,.ok (parameter :: suffix)⟩

def addVariable (state : State) (index : Nat) : Outcome Nat :=
  match addNode state.arena (.var index) with
  | .error reason => ⟨state,.error (.add reason)⟩
  | .ok (arena,root) => ⟨{state with arena},.ok root⟩

def variables : List Nat → State → Outcome (List Nat)
  | [],state => ⟨state,.ok []⟩
  | index :: rest,state =>
    (addVariable state index).next fun added root =>
      (variables rest added).next fun after suffix => ⟨after,.ok (root :: suffix)⟩

def run (limit depth : Nat) (state : State) (family count arity : Nat) (params : List Nat) : Outcome Nat :=
  let indexCount := arity-count
  (parameters limit depth indexCount params state).next fun shifted roots =>
    (variables ((List.range indexCount).map fun j => indexCount-1-j) shifted).next fun formed indices =>
      append formed (.ind family arity) (roots ++ indices)

theorem variable_progress : Progress limit state (addVariable state index) := by
  unfold addVariable
  split
  · exact Progress.atState _ _
  · rename_i arena root success
    exact Progress.uncharged (addNode_commits success).1 rfl

theorem parameters_progress : Progress limit state (parameters limit depth count params state) := by
  induction params generalizing state with
  | nil => exact Progress.atState _ _
  | cons _ _ ih => exact shift_progress.next (fun _ => ih.next (fun _ => Progress.atState _ _))

theorem variables_progress : Progress limit state (variables indices state) := by
  induction indices generalizing state with
  | nil => exact Progress.atState _ _
  | cons _ _ ih => exact variable_progress.next (fun _ => ih.next (fun _ => Progress.atState _ _))

theorem run_progress : Progress limit state (run limit depth state family count arity params) := by
  unfold run
  exact parameters_progress.next (fun _ => variables_progress.next (fun _ => append_progress _ _ _))

theorem parameters_refines
    (written : RepresentsList state.arena params args)
    (success : (parameters limit depth count params state).result = .ok selected) :
    let after := (parameters limit depth count params state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RepresentsList after selected (args.map fun type => type.rename (fun i => i+count)) := by
  induction params generalizing args state selected with
  | nil =>
    cases written
    cases success
    exact ⟨.refl _,id,.nil⟩
  | cons parameter params ih =>
    cases written with
    | cons represented tail =>
      unfold parameters at success ⊢
      obtain ⟨lifted,liftedOk,next⟩ := Outcome.next_success success
      rw [next] at success ⊢
      obtain ⟨rest,restOk,restNext⟩ := Outcome.next_success success
      rw [restNext] at success ⊢
      cases success
      obtain ⟨liftKept,liftBack,liftRep⟩ := shift_refines represented liftedOk
      obtain ⟨restKept,restBack,restRep⟩ := ih (tail.frame liftKept) restOk
      exact ⟨liftKept.trans restKept,restBack ∘ liftBack,.cons (liftRep.frame restKept) restRep⟩

theorem variable_refines (success : (addVariable state index).result = .ok selected) :
    let after := (addVariable state index).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected (.var index) := by
  unfold addVariable at success ⊢
  split at success
  · cases success
  · rename_i arena root added
    cases success
    obtain ⟨kept,_,_,_,_,found⟩ := addNode_commits added
    refine ⟨kept,fun backward => addNode_preserves_backward backward added ?_,.var found⟩
    intro child member
    cases member

theorem variables_refines (success : (variables indices state).result = .ok selected) :
    let after := (variables indices state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RepresentsList after selected (indices.map Term.var) := by
  induction indices generalizing state selected with
  | nil => cases success; exact ⟨.refl _,id,.nil⟩
  | cons index indices ih =>
    unfold variables at success ⊢
    obtain ⟨first,firstOk,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨rest,restOk,restNext⟩ := Outcome.next_success success
    rw [restNext] at success ⊢
    cases success
    obtain ⟨firstKept,firstBack,firstRep⟩ := variable_refines firstOk
    obtain ⟨restKept,restBack,restRep⟩ := ih restOk
    exact ⟨firstKept.trans restKept,restBack ∘ firstBack,.cons (firstRep.frame restKept) restRep⟩

theorem represented_append (first : RepresentsList arena refs xs) (second : RepresentsList arena roots ys) :
    RepresentsList arena (refs ++ roots) (xs ++ ys) := by
  induction first using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact second
  | cons head _ _ ih => exact .cons head ih

/-- The emitted domain uses the original parameters in the right scope and
exactly the nonparameter indices bound by the motive's word telescope. -/
theorem run_refines (written : RepresentsList state.arena params values)
    (parameterCount : params.length = count) (countIn : count ≤ arity)
    (success : (run limit depth state family count arity params).result = .ok selected) :
    let after := (run limit depth state family count arity params).state.arena
    let r := arity-count
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected
      (.node (.ind family arity) (values.map (Term.rename fun i => i+r) ++ (List.range r).map fun j => .var (r-1-j))) := by
  unfold run at success ⊢
  obtain ⟨roots,rootsOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨indices,indicesOk,indicesNext⟩ := Outcome.next_success success
  rw [indicesNext] at success ⊢
  obtain ⟨paramsKept,paramsBack,paramsRep⟩ := parameters_refines written rootsOk
  obtain ⟨indicesKept,indicesBack,indicesRep⟩ := variables_refines indicesOk
  have children := represented_append (paramsRep.frame indicesKept) indicesRep
  have width := NativeCoreIdentical.represented_length children
  have sourceWidth := NativeCoreIdentical.represented_length written
  simp only [List.length_append,List.length_map,List.length_range] at width
  have arityOk : (roots++indices).length = (.ind family arity : Op).arity := by
    simp only [Op.arity, List.length_append]
    omega
  obtain ⟨finalKept,finalBack,domain⟩ := append_refines children arityOk success
  exact ⟨paramsKept.trans (indicesKept.trans finalKept),finalBack ∘ indicesBack ∘ paramsBack,
    by simpa only [List.map_map,Function.comp_def] using domain⟩

/-- The outer parameter is weakened, while the newly bound index starts
at zero. Native data elimination constructs these three rows in order. -/
theorem open_parameter_and_bound_index_have_distinct_slots :
    let base : Arena := #[.var 0]
    run 1 8 ⟨base,0⟩ 0 1 2 [0] =
      ⟨⟨base ++ #[.var 1,.var 0,.node (.ind 0 2) [1,2]],1⟩,.ok 3⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreDataMotiveDomain
