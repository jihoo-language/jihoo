import Jihoo.NativeCoreGhostLiteralAddition
import Jihoo.NativeCoreCaseStrict

/-! Native ghost addition keeps the existing variable and places the
literal at the end of the canonical sum. A zero constant disappears.
Both operands consume their original two collection visits. -/
namespace Jihoo.NativeKernel.NativeCoreGhostVariableAddition

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress PostExtension ExpandedNormalization RefinesFor)
open NativeCoreMeteredVisit (charge charge_progress)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

private def emit (state : State) (slot word : Nat) : Outcome Nat :=
  if word = 0 then ⟨state,.ok slot⟩
  else (append state (.natural word) []).next fun after literal => append after .uadd [slot,literal]

def sum (limit depth : Nat) (state : State) (left right slot word : Nat) : Outcome Nat :=
  (charge limit depth state left).next fun afterLeft _ =>
    (charge limit depth afterLeft right).next fun afterRight _ =>
      emit afterRight slot word

theorem sum_progress : Progress limit state (sum limit depth state left right slot word) := by
  unfold sum
  exact (charge_progress _ _ _ _).next fun _ =>
    (charge_progress _ _ _ _).next fun _ => by
      unfold emit
      split
      · exact Progress.atState _ _
      · exact (append_progress _ _ _).next (fun _ => append_progress _ _ _)

private theorem output_refines (variableRep : Represents state.arena slot (.var index))
    (success : (emit state slot word).result = .ok selected) :
    let after := (emit state slot word).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (if word = 0 then .var index else .uadd (.var index) (.natural word)) := by
  unfold emit at success ⊢
  split
  · rename_i none
    simp only [ite_eq_left none,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,variableRep⟩
  · rename_i positive
    simp only [ite_eq_right positive] at success
    obtain ⟨literal,added,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨literalKept,literalBack,literalRep⟩ := append_refines .nil rfl added
    obtain ⟨sumKept,sumBack,total⟩ := append_refines (.cons (variableRep.frame literalKept) (.cons literalRep .nil)) rfl success
    exact ⟨literalKept.trans sumKept,sumBack ∘ literalBack,total⟩

private theorem sum_refines (variableRep : Represents state.arena slot (.var index))
    (success : (sum limit depth state left right slot word).result = .ok selected) :
    let after := (sum limit depth state left right slot word).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (if word = 0 then .var index else .uadd (.var index) (.natural word)) := by
  unfold sum at success ⊢
  obtain ⟨_,_,first⟩ := Outcome.next_success success
  rw [first] at success ⊢
  obtain ⟨_,_,second⟩ := Outcome.next_success success
  rw [second] at success ⊢
  exact output_refines (state := (charge limit depth (charge limit depth state left).state right).state)
    variableRep success

private def finish (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (before refs : List Nat) : Outcome Nat :=
  match refs with
  | [left,right] =>
    match state.arena[left]?,state.arena[right]? with
    | some (.var _),some (.node (.natural word) []) =>
      if word < 2^64 then sum limit depth state left right left word
      else ⟨state,.error (.outsideFragment root)⟩
    | some (.node (.natural word) []),some (.var _) =>
      if word < 2^64 then sum limit depth state left right right word
      else ⟨state,.error (.outsideFragment root)⟩
    | _,_ => NativeCoreGhostLiteralAddition.extension.finish visit limit depth root state .uadd before refs
  | _ => ⟨state,.error (.outsideFragment root)⟩

def extension : PostExtension where
  accepts op := op == .uadd
  finish visit limit depth root state _ before refs := finish visit limit depth root state before refs

theorem extension_metered : extension.Metered := by
  intro visit limit depth root state op before after accepted visited
  change Progress limit state (finish visit limit depth root state before after)
  unfold finish
  split
  · split
    · split
      · exact sum_progress
      · exact Progress.atState _ _
    · split
      · exact sum_progress
      · exact Progress.atState _ _
    · exact NativeCoreGhostLiteralAddition.extension_metered (op := .uadd) rfl visited
  · exact Progress.atState _ _

private theorem normalizes (history : ScopedProgram.History definitions declarations env)
    (swapped : Bool) (index word : Nat) :
    ExpandedNormalization env
      (if swapped then .uadd (.natural word) (.var index) else .uadd (.var index) (.natural word))
      (if word = 0 then .var index else .uadd (.var index) (.natural word)) := by
  cases swapped
  · by_cases zero : word = 0
    · subst word
      simp only [Bool.false_eq_true,ite_false,ite_true,ExpandedNormalization,Term.uadd,Term.natural,expand,expandArgs]
      exact (LoanTyping.ComputationEvaluation.Steps.arithmetic (.zeroRight (.var index))).ghost_transform history
    · simp only [Bool.false_eq_true,ite_false,zero,ExpandedNormalization,Term.uadd,Term.natural,expand,expandArgs]
      exact .refl _
  · by_cases zero : word = 0
    · subst word
      simp only [ite_true,ExpandedNormalization,Term.uadd,Term.natural,expand,expandArgs]
      exact (LoanTyping.ComputationEvaluation.Steps.arithmetic (.zeroLeft (.var index))).ghost_transform history
    · simp only [ite_true,zero,ite_false,ExpandedNormalization,Term.uadd,Term.natural,expand,expandArgs]
      exact (LoanTyping.ComputationEvaluation.Steps.arithmetic (.comm (.natural word) (.var index))).ghost_transform history

private theorem pair_terms (held : RepresentsList arena [left,right] terms)
    (a : Represents arena left first) (b : Represents arena right second) :
    terms = [first,second] := by
  cases held with
  | cons firstRep tail =>
    cases tail with
    | cons secondRep tail =>
      cases tail
      rw [firstRep.unique a,secondRep.unique b]

theorem extension_sound (history : LoanTyping.MixedProgram.History definitions declarations env) :
    extension.SoundFrom base (ExpandedNormalization env) := by
  have literal := NativeCoreGhostLiteralAddition.extension_sound (base := base) history
  refine ⟨?_,?_⟩
  · intro op accepted
    exact literal.1 accepted
  intro visit limit depth root state op before after terms selected accepted onBase read children arity next success
  have isAdd : op = .uadd := by simpa only [extension,beq_iff_eq] using accepted
  subst op
  change (finish visit limit depth root state before after).result = .ok selected at success
  change RefinesFor (ExpandedNormalization env) state (.node .uadd terms)
    (finish visit limit depth root state before after) selected
  unfold finish at success ⊢
  split at success
  · rename_i left right
    split at success
    · rename_i index word leftRead rightRead
      split at success
      · rename_i fits
        have variableRep : Represents state.arena left (.var index) := .var leftRead
        have wordRep : Represents state.arena right (.natural word) := .node rightRead rfl .nil
        have ordered := pair_terms children variableRep wordRep
        subst terms
        obtain ⟨kept,backward,represented⟩ := sum_refines variableRep success
        simp only [ite_eq_left fits]
        exact ⟨kept,backward,_,represented,normalizes (ScopedProgram.History.ofLoanMixed history) false index word⟩
      · cases success
    · rename_i word index leftRead rightRead
      split at success
      · rename_i fits
        have wordRep : Represents state.arena left (.natural word) := .node leftRead rfl .nil
        have variableRep : Represents state.arena right (.var index) := .var rightRead
        have ordered := pair_terms children wordRep variableRep
        subst terms
        obtain ⟨kept,backward,represented⟩ := sum_refines variableRep success
        simp only [ite_eq_left fits]
        exact ⟨kept,backward,_,represented,normalizes (ScopedProgram.History.ofLoanMixed history) true index word⟩
      · cases success
    · exact literal.2 (op := .uadd) rfl onBase read children arity next success
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

/-- Both written orders spend the same visits. A nonzero word rebuilds the
constant and addition, while a zero word selects the existing variable. -/
theorem open_sum_matches_native_graph :
    let arena : Arena := #[.node (.natural 7) [],.var 1,.node (.natural 0) [],
      .node .uadd [1,0],.node .uadd [0,1],.node .uadd [2,1],.node .uadd [1,2]]
    let input : State := ⟨arena,0⟩
    let canonical : Outcome Nat := ⟨⟨arena ++ #[.node (.natural 7) [],.node .uadd [1,7]],5⟩,.ok 8⟩
    run [] 0 5 16 input 3 = canonical ∧ run [] 0 5 16 input 4 = canonical ∧
      run [] 0 5 16 input 5 = ⟨⟨arena,5⟩,.ok 1⟩ ∧ run [] 0 5 16 input 6 = ⟨⟨arena,5⟩,.ok 1⟩ ∧
      run [] 0 4 16 input 4 = ⟨⟨arena,5⟩,.error (.tick (.stepLimit 1))⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreGhostVariableAddition
