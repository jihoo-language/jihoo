import Jihoo.NativeCoreNestedAliases
import Jihoo.NativeCoreUnsignedSum
import Jihoo.NativeLoanComputationPreservation
import Jihoo.NativeNumeralForward

/-! The literal branch of ghost UAdd uses the same two collection visits
and the same balanced natural-sum graph as native Core.sum. It is a
post-operand extension, so surrounding dependent type formation can use it
throughout the recursive ghost traversal. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLiteralAddition

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Error Outcome Progress PostExtension ExpandedNormalization RefinesFor)
open NativeCoreUnsignedCancellation (tick)
open NativeCoreUnsignedCollect (Pool)
open EnvironmentDelta (expand expandArgs)
open EnvironmentDelta.NumeralForward (Represents replicate_ones forward_preserves)
open NativeConstantAccumulator (naturalSum)
open ACU (ArithmeticRed compact)
open NativeKernel.Conversion (ListRel)

private theorem split_nonempty_compact (xs ys : List Term) (first : xs ≠ []) (second : ys ≠ []) :
    ArithmeticRed (compact (xs++ys)) (.uadd (compact xs) (compact ys)) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => contradiction
      | cons y ys => exact .refl _
    | cons y xs =>
      have split := ih (by simp)
      change ArithmeticRed (.uadd x (compact ((y::xs)++ys))) (.uadd (.uadd x (compact (y::xs))) (compact ys))
      exact (ArithmeticRed.addCong (.refl x) split).trans (.assocLeft _ _ _)

private theorem contract_word_tree (represented : Represents input value) (fits : value < 2^64) :
    ArithmeticRed input (.natural value) := by
  induction represented with
  | natural => exact .refl _
  | add first second ihFirst ihSecond =>
    exact (ArithmeticRed.addCong (ihFirst (by omega)) (ihSecond (by omega))).trans (.literalAdd _ _ fits)

private theorem literal_sum_arithmetic (m n : Nat) (leftFits : m < 2^64) (rightFits : n < 2^64) :
    ArithmeticRed (.uadd (.natural m) (.natural n)) (naturalSum (m+n)) := by
  by_cases fits : m+n < 2^64
  · rw [naturalSum,ite_eq_left fits]
    exact .literalAdd m n fits
  let left := (m+n)/2
  let right := m+n-left
  have leftPositive : 0 < left := by dsimp [left]; omega
  have rightPositive : 0 < right := by dsimp [right,left]; omega
  have leftWord : left < 2^64 := by dsimp [left]; omega
  have rightWord : right < 2^64 := by dsimp [right,left]; omega
  have length : left+right = m+n := by dsimp [right,left]; omega
  have tree : naturalSum (m+n) = .uadd (.natural left) (.natural right) := by
    rw [naturalSum,ite_eq_right fits]
    change Term.uadd (naturalSum left) (if right = left then naturalSum left else naturalSum right) = _
    by_cases halves : right = left
    · rw [ite_eq_left halves,halves,naturalSum,ite_eq_left leftWord]
    · rw [ite_eq_right halves,naturalSum,ite_eq_left leftWord,naturalSum,ite_eq_left rightWord]
  let ones := fun value : Nat => List.replicate value (Term.natural 1)
  have combined : ArithmeticRed (.uadd (.natural m) (.natural n)) (compact (ones (m+n))) := by
    have first := ArithmeticRed.addCong (ArithmeticRed.literalSplit m leftFits) (.literalSplit n rightFits)
    have joined := ArithmeticRed.compact_append (ones m) (ones n)
    have same : ones m ++ ones n = ones (m+n) := List.replicate_append_replicate
    exact first.trans (same ▸ joined)
  have reorganized : ArithmeticRed (compact (ones (m+n))) (.uadd (compact (ones left)) (compact (ones right))) := by
    have checked := split_nonempty_compact (ones left) (ones right)
      (by simp [ones,Nat.ne_of_gt leftPositive]) (by simp [ones,Nat.ne_of_gt rightPositive])
    have same : ones left ++ ones right = ones (m+n) := by rw [show ones left ++ ones right = ones (left+right) from List.replicate_append_replicate,length]
    rw [← same]
    exact checked
  rw [tree]
  exact combined.trans (reorganized.trans (.addCong (contract_word_tree (replicate_ones left) leftWord)
    (contract_word_tree (replicate_ones right) rightWord)))

private theorem numeric_arithmetic_steps (reduction : ArithmeticRed input output) :
    ∀ {number}, Represents input number → LoanTyping.ComputationEvaluation.Steps env input output := by
  induction reduction using ArithmeticRed.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {number}, Represents a number → LoanTyping.ComputationEvaluation.Steps env a b) xs ys) with
  | refl => intro _ _; exact .family .refl
  | trans first _ ihFirst ihSecond =>
    intro number represented
    exact .trans (ihFirst represented) (ihSecond (forward_preserves (env := env) (.acu (.arithmetic first)) represented))
  | node op _ ih =>
    intro number represented
    cases represented with
    | natural => cases ih; exact .family .refl
    | add left right =>
      cases ih with
      | cons first tail =>
        cases tail with
        | cons second last =>
          cases last
          exact .node .uadd (by decide) (.cons (first left) (.cons (second right) .nil))
  | assocRight => intro _ _; exact .arithmetic (.assocRight _ _ _)
  | assocLeft => intro _ _; exact .arithmetic (.assocLeft _ _ _)
  | comm => intro _ _; exact .arithmetic (.comm _ _)
  | zeroRight => intro _ _; exact .arithmetic (.zeroRight _)
  | zeroLeft => intro _ _; exact .arithmetic (.zeroLeft _)
  | literalSplit value fits => intro _ _; exact .arithmetic (.literalSplit value fits)
  | literalAdd m n fits => intro _ _; exact .arithmetic (.literalAdd m n fits)
  | nil => exact .nil
  | cons _ _ first tail => exact .cons first tail

private theorem expand_numeric (represented : Represents term value) : expand env term = term := by
  induction represented with
  | natural value => simp only [Term.natural,expand,expandArgs]
  | add left right ihLeft ihRight =>
    simp only [Term.uadd,expand,expandArgs,ihLeft,ihRight]

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

private theorem literalSum_refines (success : (literalSum limit depth state left right value).result = .ok root) :
    let after := (literalSum limit depth state left right value).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after root (naturalSum value) := by
  unfold literalSum at success ⊢
  obtain ⟨_,first,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ⊢
  obtain ⟨_,second,secondNext⟩ := Outcome.next_success success
  rw [secondNext] at success ⊢
  have emitted : (NativeCoreNaturalSum.run value state.arena).result = .ok root := by
    change ((NativeCoreNaturalSum.run value state.arena).result.mapError Error.add) = .ok root at success
    cases built : (NativeCoreNaturalSum.run value state.arena).result with
    | error reason => simp [built,Except.mapError] at success
    | ok selected =>
      have same : selected = root := Except.ok.inj (by simpa only [built,Except.mapError] using success)
      exact congrArg Except.ok same
  obtain ⟨represented,backward,_⟩ := NativeCoreNaturalSum.run_refines _ _ emitted
  exact ⟨NativeCoreNaturalSum.run_prefix _ _,backward,represented⟩

private def finish (limit depth root : Nat) (state : State) (refs : List Nat) : Outcome Nat :=
  match refs with
  | [left,right] =>
    match state.arena[left]?,state.arena[right]? with
    | some (.node (.natural m) []),some (.node (.natural n) []) =>
      if m < 2^64 ∧ n < 2^64 then literalSum limit depth state left right (m+n)
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
        obtain ⟨kept,backward,represented⟩ := literalSum_refines success
        have numeric : Represents (.uadd (.natural m) (.natural n)) (m+n) := .add (.natural _) (.natural _)
        have arithmetic := numeric_arithmetic_steps (env := env) (literal_sum_arithmetic m n fits.1 fits.2) numeric
        have reduced := arithmetic.ghost_transform (ScopedProgram.History.ofLoanMixed history)
        have outputNumeric := (NativeConstantAccumulator.naturalSum_correct (env := env)
          (loans := []) (ctx := []) (mode := true) (m+n)).1
        simp only [ite_eq_left fits]
        exact ⟨kept,backward,_,represented,
          by simpa only [ExpandedNormalization,expand_numeric numeric,expand_numeric outputNumeric] using reduced⟩
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

/-- With two word literals, the installed Core.sum model visits exactly
the two original references and then emits the balanced sum.
The amount charged is independent of the result of the graph append. -/
theorem native_sum_literals_exact (env : Environment) (state : State) (limit depth : Nat)
    (first : state.arena[left]? = some (.node (.natural m) []))
    (second : state.arena[right]? = some (.node (.natural n) []))
    (leftFits : m < 2^64) (rightFits : n < 2^64) (room : state.steps+2 ≤ limit) (nested : depth ≠ 0) :
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
        UInt64.toNat_ofNat_of_lt' leftFits,UInt64.toNat_ofNat_of_lt' rightFits]
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
    (leftFits : m < 2^64) (rightFits : n < 2^64) (room : state.steps+2 ≤ limit) (nested : depth ≠ 0) :
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
  rw [modeled,native_sum_literals_exact env state limit depth first second leftFits rightFits room nested]
  simp only [emit]
  generalize NativeCoreNaturalSum.run (m+n) state.arena = built
  rcases built with ⟨next,failed | root⟩ <;> exact ⟨True.intro,True.intro,rfl⟩

namespace Examples

private def wide : Arena := #[.node (.natural (2^64-1)) [],.node (.natural 1) [],.node .uadd [0,1]]

/-- Both equal halves share one arena row. The fifth tick is the second
collection visit, after which the balanced result is committed. -/
theorem wide_literal_sum_uses_one_halved_leaf :
    let finished := run [] 0 5 8 ⟨wide,0⟩ 2
    finished.state.steps = 5 ∧ finished.result = .ok 4 ∧
      finished.state.arena = wide ++ #[.node (.natural (2^63)) [],.node .uadd [3,3]] := by
  cbv

end Examples

end Jihoo.NativeKernel.NativeCoreGhostLiteralAddition
