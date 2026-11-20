import Jihoo.NativeCorePureStructuralNormal
import Jihoo.NativeCoreTransformWire
import Jihoo.NativeLoanBetaPreservation

/-! The pure Core.normal application path when the normalized lambda body
is a variable. The matched case visits the replacement with shift-by-zero,
under the same counter and native binder checks. The decremented case can
append a new variable. Core.normal then visits the substituted result. -/
namespace Jihoo.NativeKernel.NativeCoreVariableBeta

open NativeArena NativeProgramWire
open NativeCorePureStructuralNormal (Normal runNested runNested_refines runNested_reuses_normal frameDefinitions)
open NativeCoreGlobalNormal (checked_definition_at)
open Environment.LoanTyping.MixedProgram (History)
open Environment.RawValue (Forward)
open NativeKernel.Conversion (treeDepth treeSize)

inductive Error where
  | normal (reason : NativeCorePureStructuralNormal.Error)
  | binderLimit (ref : Nat)
  deriving DecidableEq, Repr

structure Outcome where
  arena : Arena
  result : Except Error Nat
  steps : Nat
  deriving Repr

private def normalError (reason : NativeCoreGlobalNormal.Error) : Error := .normal (.normal reason)

private abbrev Visit := Except Error Unit × Nat

private def shiftChildren (visit : Nat → Nat → Nat → Visit) (op : Op) (cutoff : Nat) :
    List Nat → Nat → Nat → Visit
  | [], _, steps => (.ok (), steps)
  | child :: rest, offset, steps =>
      let inner := cutoff + op.binders offset
      if NativeTransform.indexLimit ≤ inner then (.error (.binderLimit child), steps) else
      match visit inner steps child with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok (), spent) => shiftChildren visit op cutoff rest (offset + 1) spent

/-- A shift by zero still visits every original child. Because no index
changes, the transformed row at each visit keeps its original reference. -/
def shiftZero (arena : Arena) (limit : Nat) : Nat → Nat → Nat → Nat → Visit
  | 0, _, steps, root =>
      if limit < steps + 1 then (.error (normalError (.stepLimit root)), steps + 1)
      else (.error (normalError (.depthLimit root)), steps + 1)
  | depth + 1, cutoff, steps, root =>
      let next := steps + 1
      if limit < next then (.error (normalError (.stepLimit root)), next) else
      match arena[root]? with
      | none => (.error (normalError (.invalidReference root)), next)
      | some (.var _) => (.ok (), next)
      | some (.node op refs) => shiftChildren (shiftZero arena limit depth) op cutoff refs 0 next

private theorem binders_le_one (op : Op) (offset : Nat) : op.binders offset ≤ 1 := by
  rcases offset with _ | _ | _ | _ <;> cases op <;> simp [Op.binders]

private theorem shiftChildren_exact (source : RepresentsList arena refs terms)
    (height : ∀ term ∈ terms, treeDepth term ≤ depth)
    (bounded : cutoff + 1 + depth < NativeTransform.indexLimit)
    (fits : initial + (terms.map treeSize).sum ≤ limit)
    (visitSpec : ∀ {root term cutoff initial}, Represents arena root term → treeDepth term ≤ depth →
      cutoff + depth < NativeTransform.indexLimit → initial + treeSize term ≤ limit →
      visit cutoff initial root = (.ok (), initial + treeSize term)) :
    shiftChildren visit op cutoff refs offset initial = (.ok (), initial + (terms.map treeSize).sum) := by
  induction source using RepresentsList.rec (motive_1 := fun _ _ _ => True) generalizing offset initial with
  | var | node => trivial
  | nil => rfl
  | @cons ref term rest terms first later _ ih =>
      have smaller := binders_le_one op offset
      have bound : cutoff + op.binders offset + depth < NativeTransform.indexLimit := by omega
      have openCutoff : ¬NativeTransform.indexLimit ≤ cutoff + op.binders offset := by omega
      have within : initial + treeSize term ≤ limit := by
        simp only [List.map_cons, List.sum_cons] at fits
        omega
      have visited := visitSpec first (height term (by simp)) bound within
      have continued := ih (offset := offset + 1) (initial := initial + treeSize term)
        (fun item member => height item (by simp [member])) (by
          simp only [List.map_cons, List.sum_cons] at fits
          omega)
      simp only [shiftChildren, ite_eq_right openCutoff, visited, continued, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- On a represented tree with enough depth, cutoff space and work, the
zero shift charges precisely one tick per occurrence, including shared rows. -/
theorem shiftZero_exact (source : Represents arena root term) (height : treeDepth term ≤ depth)
    (bounded : cutoff + depth < NativeTransform.indexLimit) (budget : initial + treeSize term ≤ limit) :
    shiftZero arena limit depth cutoff initial root = (.ok (), initial + treeSize term) := by
  induction depth generalizing root term cutoff initial with
  | zero => cases term <;> simp only [treeDepth] at height <;> omega
  | succ depth ih =>
      cases source with
      | var read =>
          have room : ¬limit < initial + 1 := by simp only [treeSize] at budget; omega
          simp only [shiftZero, ite_eq_right room, read, treeSize]
      | @node _ op refs terms read arity children =>
          have room : ¬limit < initial + 1 := by simp only [treeSize] at budget; omega
          simp only [shiftZero, ite_eq_right room, read, treeSize]
          have childDepths : ∀ child ∈ terms, treeDepth child ≤ depth := by
            intro child found
            have below := Environment.CoreEffectAnalysis.treeDepth_member child terms found 0
            simp only [treeDepth] at height
            omega
          have within : initial + 1 + (terms.map treeSize).sum ≤ limit := by
            simp only [treeSize] at budget
            omega
          have safe : cutoff + 1 + depth < NativeTransform.indexLimit := by omega
          simpa only [Nat.add_assoc] using shiftChildren_exact (visit := shiftZero arena limit depth)
            children childDepths safe within (fun represented withinDepth withinCutoff remaining =>
              ih represented withinDepth withinCutoff remaining)

private def lifted (output : NativeCorePureStructuralNormal.Outcome Nat) : Outcome :=
  ⟨output.arena, output.result.mapError .normal, output.steps⟩

/-- The initial cutoff is zero, so a matched variable shifts the replacement
at zero delta and a greater variable is decremented. -/
def substituteVariable (arena : Arena) (limit depth steps body argument : Nat) : Outcome :=
  let next := steps + 1
  if limit < next then ⟨arena, .error (normalError (.stepLimit body)), next⟩ else
  match depth with
  | 0 => ⟨arena, .error (normalError (.depthLimit body)), next⟩
  | remaining + 1 =>
      match arena[body]? with
      | none => ⟨arena, .error (normalError (.invalidReference body)), next⟩
      | some (.var 0) =>
          let (shifted, spent) := shiftZero arena limit remaining 0 next argument
          ⟨arena, shifted.map (fun _ => argument), spent⟩
      | some (.var (index + 1)) =>
          match NativeCoreGraph.addNode arena (.var index) with
          | .ok (extended, ref) => ⟨extended, .ok ref, next⟩
          | .error reason => ⟨arena, .error (.normal (.add reason)), next⟩
      | _ => ⟨arena, .error (normalError (.outsideFragment body)), next⟩

private def finish (roots : List Roots) (visible limit depth root function argument : Nat)
    (arena : Arena) (steps : Nat) : Outcome :=
  match arena[function]? with
  | some (.node (.lam _) [_, body]) =>
      let opened := substituteVariable arena limit depth steps body argument
      match opened.result with
      | .error _ => opened
      | .ok ref => lifted (runNested roots visible limit depth opened.arena opened.steps ref)
  | _ => ⟨arena, .error (normalError (.outsideFragment root)), steps⟩

private def operands (arena : Arena) (roots : List Roots)
    (visible limit depth initial root function argument : Nat) : Outcome :=
  let first := runNested roots visible limit depth arena initial function
  match first.result with
  | .error _ => lifted first
  | .ok callee =>
      let second := runNested roots visible limit depth first.arena first.steps argument
      match second.result with
      | .error _ => lifted second
      | .ok value => finish roots visible limit depth root callee value second.arena second.steps

/-- The App visit charges once, normalizes the function before the argument,
substitutes when the lambda body is a variable, then normalizes the original
substitution result at the same remaining depth and the current work counter. -/
def run (arena : Arena) (roots : List Roots) (visible limit depth initial root : Nat) : Outcome :=
  let next := initial + 1
  if limit < next then ⟨arena, .error (normalError (.stepLimit root)), next⟩ else
  match depth with
  | 0 => ⟨arena, .error (normalError (.depthLimit root)), next⟩
  | remaining + 1 =>
      match arena[root]? with
      | none => ⟨arena, .error (normalError (.invalidReference root)), next⟩
      | some (.node .app [function, argument]) => operands arena roots visible limit remaining next root function argument
      | _ => ⟨arena, .error (normalError (.outsideFragment root)), next⟩

private theorem read_binary (source : Represents arena root (.node op [first, second])) :
    ∃ x y, arena[root]? = some (.node op [x, y]) ∧
      Represents arena x first ∧ Represents arena y second := by
  cases source with
  | node read _ children =>
      cases children with
      | cons left children =>
          cases children with
          | cons right children =>
              cases children
              exact ⟨_, _, read, left, right⟩

private theorem read_variable (source : Represents arena root (.var index)) :
    arena[root]? = some (.var index) := by
  cases source with
  | var read => exact read

private theorem substitute_refines (bodyRep : Represents arena body bodyTerm)
    (argRep : Represents arena argument argTerm)
    (success : (substituteVariable arena limit depth initial body argument).result = .ok selected) :
    let opened := substituteVariable arena limit depth initial body argument
    (∃ index, bodyTerm = .var index) ∧ Prefix arena opened.arena ∧
      (Backward arena → Backward opened.arena) ∧
      Represents opened.arena selected (bodyTerm.subst (single argTerm)) := by
  by_cases over : limit < initial + 1
  · simp [substituteVariable, over] at success
  cases depth with
  | zero => simp [substituteVariable, over] at success
  | succ depth =>
      cases bodyRep with
      | node read _ _ => simp [substituteVariable, over, read] at success
      | var read =>
          rename_i index
          cases index with
          | zero =>
              rcases shifted : shiftZero arena limit depth 0 (initial + 1) argument with ⟨answer, spent⟩
              cases answer with
              | error reason => simp [substituteVariable, over, read, shifted, Except.map] at success
              | ok _ =>
                  simp [substituteVariable, over, read, shifted, Except.map] at success
                  subst selected
                  have substitution :
                      substituteVariable arena limit (depth + 1) initial body argument = ⟨arena, .ok argument, spent⟩ := by
                    simp [substituteVariable, over, read, shifted, Except.map]
                  rw [substitution]
                  exact ⟨⟨0, rfl⟩, .refl _, id, by simpa only [Term.subst, single] using argRep⟩
          | succ index =>
              rcases built : NativeCoreGraph.addNode arena (.var index) with error | ⟨next, ref⟩
              · simp [substituteVariable, over, read, built] at success
              · simp [substituteVariable, over, read, built] at success
                subst selected
                obtain ⟨kept, _, _, _, _, added⟩ := NativeCoreGraph.addNode_commits built
                have substitution :
                    substituteVariable arena limit (depth + 1) initial body argument = ⟨next, .ok ref, initial + 1⟩ := by
                  simp [substituteVariable, over, read, built]
                rw [substitution]
                exact ⟨⟨index + 1, rfl⟩, kept,
                  fun old => NativeCoreGraph.addNode_preserves_backward old built (by simp [Node.references]),
                  by simpa only [Term.subst, single] using Represents.var added⟩

private theorem finish_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (functionRep : Represents arena function callee) (argumentRep : Represents arena argument operand)
    (success : (finish roots visible limit depth root function argument arena initial).result = .ok selected) :
    let output := finish roots visible limit depth root function argument arena initial
    Prefix arena output.arena ∧ (Backward arena → Backward output.arena) ∧
      ∃ normalized, Represents output.arena selected normalized ∧ Forward env (.app callee operand) normalized := by
  cases functionRep with
  | var read => simp [finish, read] at success
  | @node _ op refs terms read arity children =>
      cases op <;> try solve | simp [finish, read] at success
      case lam erased =>
        cases children with
        | nil => cases arity
        | @cons domainRef domain _ _ _ tail =>
            cases tail with
            | nil => cases arity
            | @cons bodyRef body _ _ bodyRep remaining =>
                cases remaining with
                | cons => cases arity
                | nil =>
                    generalize openedEq :
                      substituteVariable arena limit depth initial bodyRef argument = opened
                    cases openedResult : opened.result with
                    | error reason => simp [finish, read, openedEq, openedResult] at success
                    | ok reduced =>
                        have substitutionOk :
                            (substituteVariable arena limit depth initial bodyRef argument).result = .ok reduced := by
                          rw [openedEq, openedResult]
                        have substitution := substitute_refines bodyRep argumentRep substitutionOk
                        rw [openedEq] at substitution
                        obtain ⟨_, kept, backward, reducedRep⟩ := substitution
                        have refined := runNested_refines (visible := visible) (limit := limit) (depth := depth)
                          (initial := opened.steps) (frameDefinitions aligned kept) history reducedRep
                        generalize finalEq : runNested roots visible limit depth opened.arena opened.steps reduced = final
                        rw [finalEq] at refined
                        cases finalResult : final.result with
                        | error reason =>
                            simp [finish, read, openedEq, openedResult, finalEq, lifted, finalResult, Except.mapError] at success
                        | ok finalRef =>
                            simp [finish, read, openedEq, openedResult, finalEq, lifted, finalResult, Except.mapError] at success
                            subst selected
                            obtain ⟨frame, preserves, reduct⟩ := refined
                            obtain ⟨normalized, represented, forward⟩ := reduct finalRef finalResult
                            refine ⟨?_, ?_, normalized, ?_, ?_⟩
                            · simpa [finish, read, openedEq, openedResult, finalEq, lifted] using kept.trans frame
                            · simpa [finish, read, openedEq, openedResult, finalEq, lifted] using
                                (fun old => preserves (backward old))
                            · simpa [finish, read, openedEq, openedResult, finalEq, lifted] using represented
                            · have beta : Forward env (.app (.lam erased domain body) operand) (body.subst (single operand)) :=
                                .old (.old (.acu (.compute (.beta erased domain body operand))))
                              exact beta.trans forward

/-- Any successful run under the supported application fragment appends only
valid graph rows and represents a reduct of the original application. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (source : Represents arena root (.app first second))
    (success : (run arena roots visible limit depth initial root).result = .ok selected) :
    let output := run arena roots visible limit depth initial root
    Prefix arena output.arena ∧ (Backward arena → Backward output.arena) ∧
      ∃ normalized, Represents output.arena selected normalized ∧ Forward env (.app first second) normalized := by
  obtain ⟨function, argument, read, firstRep, secondRep⟩ := read_binary source
  by_cases over : limit < initial + 1
  · simp [run, over] at success
  cases depth with
  | zero => simp [run, over] at success
  | succ depth =>
      have firstFacts := runNested_refines (visible := visible) (limit := limit) (depth := depth)
        (initial := initial + 1) aligned history firstRep
      generalize firstRun : runNested roots visible limit depth arena (initial + 1) function = left
      rw [firstRun] at firstFacts
      cases firstResult : left.result with
      | error reason => simp [run, over, read, operands, firstRun, firstResult, lifted, Except.mapError] at success
      | ok callee =>
          obtain ⟨firstPrefix, firstBackward, firstReduct⟩ := firstFacts
          obtain ⟨calleeTerm, calleeRep, changedFirst⟩ := firstReduct callee firstResult
          have leftDefinitions := frameDefinitions aligned firstPrefix
          have secondFacts := runNested_refines (visible := visible) (limit := limit) (depth := depth)
            (initial := left.steps) leftDefinitions history (secondRep.frame firstPrefix)
          generalize secondRun : runNested roots visible limit depth left.arena left.steps argument = right
          rw [secondRun] at secondFacts
          cases secondResult : right.result with
          | error reason =>
              simp [run, over, read, operands, firstRun, firstResult, secondRun, secondResult, lifted,
                Except.mapError] at success
          | ok operand =>
              obtain ⟨secondPrefix, secondBackward, secondReduct⟩ := secondFacts
              obtain ⟨operandTerm, operandRep, changedSecond⟩ := secondReduct operand secondResult
              simp only [run, ite_eq_right over, read, operands, firstRun, firstResult,
                secondRun, secondResult] at success ⊢
              obtain ⟨kept, back, value, represents, changed⟩ := finish_refines
                (frameDefinitions leftDefinitions secondPrefix) history (calleeRep.frame secondPrefix) operandRep success
              have operandsReduce : Forward env (.app first second) (.app calleeTerm operandTerm) :=
                .node .app (.cons changedFirst (.cons changedSecond .nil))
              exact ⟨(firstPrefix.trans secondPrefix).trans kept,
                fun old => back (secondBackward (firstBackward old)), value, represents, operandsReduce.trans changed⟩

/-- Exact mixed admission supplies both the graph invariant and the
environment for the general successful variable-body application path. -/
theorem run_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root (.app function argument))
    (success : (run snapshot.arena snapshot.definitions visible limit depth initial root).result = .ok selected) :
    let output := run snapshot.arena snapshot.definitions visible limit depth initial root
    ∃ definitions families env,
      History definitions families env ∧ Prefix snapshot.arena output.arena ∧ Backward output.arena ∧
        ∃ normalized, Represents output.arena selected normalized ∧ Forward env (.app function argument) normalized := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨frame, preserves, reduced⟩ := run_refines aligned history source success
  exact ⟨definitions, _, env, history, frame, preserves backward, reduced⟩

private theorem term_work_positive (term : Term) : 1 ≤ treeSize term := by
  cases term <;> simp only [treeSize] <;> omega

/-- With structurally normal operands, an identity lambda returns the original
argument reference at the original application type. The counter includes its
initial normalization, the zero shift, and the final normalization. -/
theorem run_identity_at_type
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents arena root (.app (.lam erased domain (.var 0)) operand))
    (typed : Environment.LoanTyping.HasType env loans ctx mode
      (.app (.lam erased domain (.var 0)) operand) type)
    (normalCallee : Normal (.lam erased domain (.var 0))) (normalOperand : Normal operand)
    (calleeDepth : treeDepth (.lam erased domain (.var 0)) ≤ depth + 1)
    (operandDepth : treeDepth operand ≤ depth) (cutoff : depth < NativeTransform.indexLimit)
    (budget : initial + treeSize (.lam erased domain (.var 0)) + 3 * treeSize operand + 2 ≤ limit) :
    ∃ selected,
      run arena roots visible limit (depth + 2) initial root =
        ⟨arena, .ok selected, initial + treeSize (.lam erased domain (.var 0)) + 3 * treeSize operand + 2⟩ ∧
      Represents arena selected operand ∧ Environment.LoanTyping.HasType env [] ctx true operand type := by
  obtain ⟨function, argument, read, functionRep, argumentRep⟩ := read_binary source
  obtain ⟨_, body, functionRead, _, bodyRep⟩ := read_binary functionRep
  have bodyRead := read_variable bodyRep
  let calleeWork := treeSize (.lam erased domain (.var 0))
  let operandWork := treeSize operand
  change initial + calleeWork + 3 * operandWork + 2 ≤ limit at budget
  have costs := term_work_positive operand
  change 1 ≤ operandWork at costs
  have rootRoom : ¬limit < initial + 1 := by omega
  let afterCallee := initial + 1 + calleeWork
  let afterOperand := afterCallee + operandWork
  let afterBody := afterOperand + 1
  let afterShift := afterBody + operandWork
  have calleeBudget : initial + 1 + calleeWork ≤ limit := by omega
  have operandBudget : afterCallee + operandWork ≤ limit := by dsimp only [afterCallee]; omega
  have bodyRoom : ¬limit < afterOperand + 1 := by dsimp only [afterOperand, afterCallee]; omega
  have shiftBudget : afterBody + operandWork ≤ limit := by
    dsimp only [afterBody, afterOperand, afterCallee]
    omega
  have finalBudget : afterShift + operandWork ≤ limit := by
    dsimp only [afterShift, afterBody, afterOperand, afterCallee]
    omega
  have calleeRun := runNested_reuses_normal (roots := roots) (visible := visible) normalCallee
    functionRep calleeDepth calleeBudget
  have operandRun := runNested_reuses_normal (roots := roots) (visible := visible) normalOperand
    argumentRep (Nat.le_trans operandDepth (Nat.le_succ _)) operandBudget
  have shiftRun := shiftZero_exact (cutoff := 0) argumentRep operandDepth (by simpa using cutoff) shiftBudget
  have finalRun := runNested_reuses_normal (roots := roots) (visible := visible) normalOperand
    argumentRep (Nat.le_trans operandDepth (Nat.le_succ _)) finalBudget
  refine ⟨argument, ?_, argumentRep, ?_⟩
  · change run arena roots visible limit (depth + 2) initial root =
      ⟨arena, .ok argument, initial + calleeWork + 3 * operandWork + 2⟩
    change runNested roots visible limit (depth + 1) arena (initial + 1) function =
      ⟨arena, .ok function, afterCallee⟩ at calleeRun
    change runNested roots visible limit (depth + 1) arena afterCallee argument =
      ⟨arena, .ok argument, afterOperand⟩ at operandRun
    have reduced : run arena roots visible limit (depth + 2) initial root =
        finish roots visible limit (depth + 1) root function argument arena afterOperand := by
      simp [run, rootRoom, read, operands, calleeRun, operandRun]
    have bodyRun : substituteVariable arena limit (depth + 1) afterOperand body argument =
        ⟨arena, .ok argument, afterShift⟩ := by
      have available : ¬limit < afterBody := bodyRoom
      simp only [substituteVariable, show afterOperand + 1 = afterBody from rfl,
        ite_eq_right available, bodyRead, shiftRun, Except.map]
      rfl
    rw [reduced]
    simp only [finish, functionRead, bodyRun, finalRun, lifted, Except.mapError]
    congr 1
    dsimp only [afterShift, afterBody, afterOperand, afterCallee]
    omega
  · simpa only [Term.subst, single] using typed.ghostBeta wellFormed

private theorem normal_global_free (normal : Normal term) : GlobalEnvironment.GlobalFree term := by
  induction normal with
  | @atom term atomic =>
      cases term with
      | var => simp [GlobalEnvironment.GlobalFree]
      | node op children =>
          cases children with
          | cons => contradiction
          | nil =>
              rw [GlobalEnvironment.GlobalFree]
              refine ⟨?_, by simp⟩
              cases op <;> simp_all [NativeCoreGlobalNormal.Atomic, NativeCoreGlobalNormal.atomicOp,
                GlobalEnvironment.ordinary]
  | @node op _ supported _ ih =>
      rw [GlobalEnvironment.GlobalFree]
      refine ⟨?_, ih⟩
      cases op <;> simp_all [NativeCorePureStructuralNormal.structural, GlobalEnvironment.ordinary]

/-- An exact-byte checked identity application returns its original argument
with the stored declaration type, preserving every arena reference. -/
theorem run_admitted_identity_at_type {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (source : Represents snapshot.arena definition.valueRoot (.app (.lam erased domain (.var 0)) operand))
    (normalCallee : Normal (.lam erased domain (.var 0))) (normalOperand : Normal operand)
    (calleeDepth : treeDepth (.lam erased domain (.var 0)) ≤ depth + 1)
    (operandDepth : treeDepth operand ≤ depth) (cutoff : depth < NativeTransform.indexLimit)
    (budget : initial + treeSize (.lam erased domain (.var 0)) + 3 * treeSize operand + 2 ≤ limit) :
    ∃ definitions families env entry selected,
      History definitions families env ∧ env.globals[index]? = some entry ∧
      run snapshot.arena snapshot.definitions visible limit (depth + 2) initial definition.valueRoot =
        ⟨snapshot.arena, .ok selected,
          initial + treeSize (.lam erased domain (.var 0)) + 3 * treeSize operand + 2⟩ ∧
      Represents snapshot.arena selected operand ∧ Environment.LoanTyping.HasType env [] [] true operand entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, _, found, represented, typed⟩ := checked_definition_at aligned history row
  have free : GlobalEnvironment.GlobalFree (.app (.lam erased domain (.var 0)) operand) := by
    have lhs := normal_global_free normalCallee
    have rhs := normal_global_free normalOperand
    simp [Term.app, GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary, lhs, rhs]
  rw [represented.2.unique source, EnvironmentDelta.expand_globalFree free] at typed
  obtain ⟨selected, ran, rep, preserved⟩ :=
    run_identity_at_type (roots := snapshot.definitions) (visible := visible)
      history.wellFormed source typed normalCallee normalOperand calleeDepth operandDepth cutoff budget
  exact ⟨definitions, _, env, entry, selected, history, found, ran, rep, preserved⟩

theorem reference_and_work_examples :
    let arena : Arena := #[.node .u64 [], .var 0, .node (.lam false) [0, 1], .node (.natural 7) [], .node .app [2, 3]]
    let captured : Arena := #[.node .u64 [], .var 1, .node (.lam false) [0, 1], .node (.natural 7) [], .node .app [2, 3]]
    run arena [] 0 8 3 0 4 = ⟨arena, .ok 3, 8⟩ ∧
    run arena [] 0 7 3 0 4 = ⟨arena, .error (normalError (.stepLimit 3)), 8⟩ ∧
    run captured [] 0 7 3 0 4 = ⟨captured.push (.var 0), .ok 5, 7⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreVariableBeta
