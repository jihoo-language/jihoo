import Jihoo.NativeCoreNestedAliases
import Jihoo.NativeCoreUnsignedSum
import Jihoo.NativeLoanComputationPreservation

/-! The bounded literal branch of ghost UAdd uses the same two collection
visits and the same natural-sum arena append as native Core.sum. It is a
post-operand extension, so surrounding dependent type formation can use it
throughout the recursive ghost traversal. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLiteralAddition

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Error Outcome Progress PostExtension ExpandedNormalization RefinesFor)
open NativeCoreUnsignedCancellation (tick)
open NativeCoreUnsignedCollect (Pool)
open EnvironmentDelta (expand expandArgs)

private def collectVisit (limit depth : Nat) (state : State) (root : Nat) : Outcome Unit :=
  let visited := tick state.arena limit depth state.steps root
  ⟨{state with steps := visited.2}, visited.1.mapError .tick⟩

private theorem collectVisit_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (collectVisit limit depth state root) := by
  unfold collectVisit tick
  by_cases over : limit < state.steps+1
  · simp only [over,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun room => Nat.succ_le_succ room,by intro _ _ failed; cases failed⟩
  have within := Nat.le_of_not_gt over
  by_cases deep : depth = 0
  · simp only [over,deep,ite_false,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),by intro _ _ failed; cases failed⟩
  by_cases missing : state.arena.size ≤ root
  · simp only [over,deep,missing,ite_false,ite_true,Except.mapError]
    exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),by intro _ _ failed; cases failed⟩
  simp only [over,deep,missing,ite_false,Except.mapError]
  exact ⟨.refl _,Nat.le_succ _,fun _ => Nat.le_trans within (Nat.le_succ _),fun _ _ _ => within⟩

private def emit (state : State) (value : Nat) : Outcome Nat :=
  let built := NativeCoreNaturalSum.run value state.arena
  ⟨{state with arena := built.arena}, built.result.mapError .add⟩

def literalSum (limit depth : Nat) (state : State) (left right value : Nat) : Outcome Nat :=
  (collectVisit limit depth state left).next fun afterLeft _ =>
    (collectVisit limit depth afterLeft right).next fun afterRight _ => emit afterRight value

private theorem literalSum_progress (limit depth : Nat) (state : State) (left right value : Nat) :
    Progress limit state (literalSum limit depth state left right value) :=
  (collectVisit_progress _ _ _ _).next (fun _ => (collectVisit_progress _ _ _ _).next (fun _ =>
    Progress.uncharged (NativeCoreNaturalSum.run_prefix _ _) rfl))

private theorem literalSum_refines (success : (literalSum limit depth state left right (m+n)).result = .ok root)
    (fits : m+n < 2^64) :
    let after := (literalSum limit depth state left right (m+n)).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after root (.natural (m+n)) := by
  unfold literalSum at success ⊢
  obtain ⟨_,first,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ⊢
  obtain ⟨_,second,secondNext⟩ := Outcome.next_success success
  rw [secondNext] at success ⊢
  have emitted : (NativeCoreNaturalSum.run (m+n) state.arena).result = .ok root := by
    change ((NativeCoreNaturalSum.run (m+n) state.arena).result.mapError Error.add) = .ok root at success
    cases built : (NativeCoreNaturalSum.run (m+n) state.arena).result with
    | error reason => simp [built,Except.mapError] at success
    | ok selected =>
      have same : selected = root := Except.ok.inj (by simpa only [built,Except.mapError] using success)
      exact congrArg Except.ok same
  obtain ⟨represented,backward,_⟩ := NativeCoreNaturalSum.run_refines _ _ emitted
  rw [NativeConstantAccumulator.naturalSum,ite_eq_left fits] at represented
  exact ⟨NativeCoreNaturalSum.run_prefix _ _,backward,represented⟩

private def finish (limit depth root : Nat) (state : State) (refs : List Nat) : Outcome Nat :=
  match refs with
  | [left,right] =>
    match state.arena[left]?,state.arena[right]? with
    | some (.node (.natural m) []),some (.node (.natural n) []) =>
      if m+n < 2^64 then literalSum limit depth state left right (m+n)
      else ⟨state,.error (.outsideFragment root)⟩
    | _,_ => ⟨state,.error (.outsideFragment root)⟩
  | _ => ⟨state,.error (.outsideFragment root)⟩

def extension : PostExtension where
  accepts op := op == .uadd
  finish _ limit depth root state _ _ refs := finish limit depth root state refs

theorem extension_metered : extension.Metered := by
  intro visit limit depth root state op before after accepted visitMetered
  change Progress limit state (finish limit depth root state after)
  unfold finish
  split
  · split
    · split
      · exact literalSum_progress _ _ _ _ _ _
      · exact Progress.atState _ _
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem extension_sound (history : LoanTyping.MixedProgram.History definitions declarations env) :
    extension.SoundFrom base (ExpandedNormalization env) := by
  constructor
  · intro op accepted
    have isAdd : op = .uadd := by simpa only [extension,beq_iff_eq] using accepted
    subst op
    refine ⟨?_,rfl⟩
    intro impossible
    cases impossible
  intro visit limit depth root state op before after terms selected accepted onBase read children arity next success
  have isAdd : op = .uadd := by simpa only [extension,beq_iff_eq] using accepted
  subst op
  change (finish limit depth root state after).result = .ok selected at success
  change RefinesFor (ExpandedNormalization env) state (.node .uadd terms) (finish limit depth root state after) selected
  unfold finish at success ⊢
  split at success
  · rename_i left right
    split at success
    · rename_i m n leftRead rightRead
      split at success
      · rename_i fits
        have written : terms = [.natural m,.natural n] := by
          cases children with
          | cons first tail =>
            cases tail with
            | cons second last =>
              cases last
              rw [first.unique (.node leftRead rfl .nil),second.unique (.node rightRead rfl .nil)]
        subst terms
        obtain ⟨kept,backward,represented⟩ := literalSum_refines success fits
        have reduced := (LoanTyping.ComputationEvaluation.Steps.arithmetic (.literalAdd _ _ fits) :
          LoanTyping.ComputationEvaluation.Steps env (.uadd (.natural m) (.natural n)) (.natural (m+n))).ghost_transform
            (ScopedProgram.History.ofLoanMixed history)
        simp only [ite_eq_left fits]
        exact ⟨kept,backward,_,represented,
          by simpa only [ExpandedNormalization,Term.natural,Term.uadd,expand,expandArgs] using reduced⟩
      · cases success
    · cases success
  · cases success

def run (roots : List Roots) (visible limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  NativeCorePureComputationNormal.runWithExtensions extension (NativeCoreNestedAliases.extension roots visible)
    limit depth state root

theorem run_progress (roots : List Roots) (visible limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run roots visible limit depth state root) :=
  NativeCorePureComputationNormal.runWithExtensions_progress extension_metered
    (NativeCoreNestedAliases.extension_metered roots visible) limit depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (held : Represents state.arena root term) (success : (run roots visible limit depth state root).result = .ok output) :
    RefinesFor (ExpandedNormalization env) state term (run roots visible limit depth state root) output :=
  NativeCorePureComputationNormal.runWithExtensions_refinesFrom
    (NativeCorePureComputationNormal.expandedRules history.wellFormed) (extension_sound history)
    (NativeCoreNestedAliases.extension_sound history aligned) onBase held success

/-- With two bounded literal operands, the installed Core.sum model visits
exactly the two original references and then emits a single natural word.
The amount charged is independent of the result of the graph append. -/
theorem native_sum_literals_exact (env : Environment) (state : State) (limit depth : Nat)
    (first : state.arena[left]? = some (.node (.natural m) []))
    (second : state.arena[right]? = some (.node (.natural n) []))
    (fits : m+n < 2^64) (room : state.steps+2 ≤ limit) (nested : depth ≠ 0) :
    let emitted := NativeCoreNaturalSum.run (m+n) state.arena
    NativeCoreUnsignedSum.run env false state.arena limit depth state.steps left right =
      ⟨emitted.arena, emitted.result.mapError .graph, some (state.steps+2)⟩ := by
  cases depth with
  | zero => contradiction
  | succ depth =>
    have leftVisible := (Array.getElem?_eq_some_iff.mp first).1
    have rightVisible := (Array.getElem?_eq_some_iff.mp second).1
    have firstRoom : ¬limit < state.steps+1 := by omega
    have secondRoom : ¬limit < state.steps+1+1 := by omega
    let literals : Pool := { constant := BitVec.ofNat 128 m + BitVec.ofNat 128 n }
    have collected : NativeCoreUnsignedCollect.runOperands state.arena limit (depth+1) state.steps left right =
        (.ok literals,state.steps+2) := by
      simp only [NativeCoreUnsignedCollect.runOperands,NativeCoreUnsignedCollect.run,NativeCoreUnsignedCancellation.tick,
        firstRoom,secondRoom, Nat.succ_ne_zero, Nat.not_le.mpr leftVisible, Nat.not_le.mpr rightVisible,
        ite_false,first,second,Option.map_some,NativeCoreUnsignedCollect.nodeView,NativeCoreUnsignedCollect.view,
        UInt64.toNat_ofNat_of_lt' (by omega : m < 2^64),UInt64.toNat_ofNat_of_lt' (by omega : n < 2^64)]
      simp [literals,Nat.add_assoc]
    have stable : NativeCoreUnsignedSumRounds.rounds env false state.arena limit (depth+1) literals (state.steps+2) =
        (.ok (literals,0),state.steps+2) := rfl
    have wider : m+n < 2^128 := by omega
    have value : literals.constant.toNat = m+n := by
      simp only [literals,BitVec.toNat_add,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : m < 2^128),Nat.mod_eq_of_lt (by omega : n < 2^128),Nat.mod_eq_of_lt wider]
    have canonical : NativeCoreUnsignedCanonical.run false state.arena [] literals.constant (limit-(state.steps+2)) =
        let emitted := NativeCoreNaturalSum.run (m+n) state.arena
        ⟨emitted.arena,(emitted.result.map some).mapError .graph,limit-(state.steps+2)⟩ := by
      have sorted : NativeCoreUnsignedOrder.run false state.arena [] (limit-(state.steps+2)) =
          some ([],limit-(state.steps+2)) := rfl
      simp only [NativeCoreUnsignedCanonical.run,Bool.false_and,Bool.false_eq_true,ite_false,sorted,value]
      rfl
    change NativeCoreUnsignedSum.run env false state.arena limit (depth+1) state.steps left right = _
    simp only [NativeCoreUnsignedSum.run,collected,stable]
    change NativeCoreUnsignedSum.finish false state.arena limit (state.steps+2) left right literals = _
    simp only [NativeCoreUnsignedSum.finish,literals]
    rw [canonical]
    dsimp only
    simp only [Nat.sub_sub_self room]
    generalize NativeCoreNaturalSum.run (m+n) state.arena = built
    rcases built with ⟨next,failed | root⟩ <;> rfl

/-- The arithmetic extension agrees with the established native sum model
on the appended arena, graph errors and shared clock. -/
theorem literalSum_matches_native (env : Environment) (state : State) (limit depth : Nat)
    (first : state.arena[left]? = some (.node (.natural m) []))
    (second : state.arena[right]? = some (.node (.natural n) []))
    (fits : m+n < 2^64) (room : state.steps+2 ≤ limit) (nested : depth ≠ 0) :
    let mapped := literalSum limit depth state left right (m+n)
    let native := NativeCoreUnsignedSum.run env false state.arena limit depth state.steps left right
    mapped.state.arena = native.arena ∧ native.steps = some mapped.state.steps ∧
      mapped.result = native.result.mapError (fun failure => match failure with
        | .graph reason => .add reason
        | .traversal reason => .tick reason
        | .order => .outsideFragment left) := by
  have firstRoom : ¬limit < state.steps+1 := by omega
  have secondRoom : ¬limit < state.steps+1+1 := by omega
  have leftVisible := (Array.getElem?_eq_some_iff.mp first).1
  have rightVisible := (Array.getElem?_eq_some_iff.mp second).1
  have modeled : literalSum limit depth state left right (m+n) = emit {state with steps := state.steps+2} (m+n) := by
    simp only [literalSum,collectVisit,tick,firstRoom,secondRoom,nested,
      Nat.not_le.mpr leftVisible,Nat.not_le.mpr rightVisible,ite_false,Except.mapError,Outcome.next]
  dsimp only
  rw [modeled,native_sum_literals_exact env state limit depth first second fits room nested]
  simp only [emit]
  generalize NativeCoreNaturalSum.run (m+n) state.arena = built
  rcases built with ⟨next,failed | root⟩ <;> exact ⟨True.intro,True.intro,rfl⟩

end Jihoo.NativeKernel.NativeCoreGhostLiteralAddition
