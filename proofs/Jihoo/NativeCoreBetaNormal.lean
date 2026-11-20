import Jihoo.NativeCoreTransformExact
import Jihoo.NativeCorePureStructuralNormal
import Jihoo.NativeLoanBetaPreservation

/-! Pure Core.normal visits the callee and operand, opens the normalized
lambda in the live arena, and normalizes the substituted result. -/
namespace Jihoo.NativeKernel.NativeCoreBetaNormal

open NativeArena NativeProgramWire
open NativeCoreTransformExact (State work workArgs)
open NativeCorePureStructuralNormal (Normal runNested runNested_refines runNested_reuses_normal frameDefinitions)
open Environment.LoanTyping.MixedProgram (History)
open Environment.RawValue (Forward)
open NativeKernel.Conversion (treeDepth treeSize)

inductive Error where
  | tick (reason : NativeCoreIdentical.Error)
  | normal (reason : NativeCorePureStructuralNormal.Error)
  | substitution (reason : NativeCoreTransformExact.Error)
  | outsideFragment (root : Nat)
  deriving Repr, DecidableEq

structure Outcome where
  state : State
  result : Except Error Nat
  deriving Repr

private def Outcome.next (run : Outcome) (remaining : State → Nat → Outcome) : Outcome :=
  match run.result with
  | .error _ => run
  | .ok ref => remaining run.state ref

private theorem Outcome.next_success {previous : Outcome} {remaining : State → Nat → Outcome}
    (success : (previous.next remaining).result = .ok selected) :
    ∃ ref, previous.result = .ok ref ∧ previous.next remaining = remaining previous.state ref := by
  cases found : previous.result with
  | error reason => simp [Outcome.next, found] at success
  | ok ref => exact ⟨ref, rfl, by simp [Outcome.next, found]⟩

private def normal (roots : List Roots) (visible limit depth : Nat) (state : State) (ref : Nat) : Outcome :=
  let result := runNested roots visible limit depth state.arena state.steps ref
  ⟨⟨result.arena, result.steps⟩, result.result.mapError .normal⟩

private def opening (limit depth : Nat) (state : State) (body operand : Nat) : Outcome :=
  let result := NativeCoreTransformExact.substitute limit depth state body operand
  ⟨result.state, result.result.mapError .substitution⟩

private def applyBeta (roots : List Roots) (visible limit depth : Nat) (state : State)
    (callee operand : Nat) : Outcome :=
  match state.arena[callee]? with
  | some (.node (.lam _) [_, body]) =>
      (opening limit depth state body operand).next (normal roots visible limit depth)
  | _ => ⟨state, .error (.outsideFragment callee)⟩

private def operands (roots : List Roots) (visible limit depth : Nat) (state : State)
    (callee operand : Nat) : Outcome :=
  (normal roots visible limit depth state callee).next fun afterCallee function =>
    (normal roots visible limit depth afterCallee operand).next fun afterOperand value =>
      applyBeta roots visible limit depth afterOperand function value

/-- Successful calls may substitute arbitrary lambda bodies represented in
the graph. The surrounding normalization follows the structural fragment
for the callee, operand, and instantiated result. -/
def run (roots : List Roots) (visible limit : Nat) : Nat → State → Nat → Outcome
  | 0, state, root =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root
      match tried.1 with
      | .error reason => ⟨{state with steps := tried.2}, .error (.tick reason)⟩
      | .ok () => ⟨{state with steps := tried.2}, .error (.tick (.depthLimit root))⟩
  | depth + 1, state, root =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root
      let entered := {state with steps := tried.2}
      match tried.1 with
      | .error reason => ⟨entered, .error (.tick reason)⟩
      | .ok () =>
          match state.arena[root]? with
          | none => ⟨entered, .error (.tick (.invalidReference root))⟩
          | some (.node .app [function, argument]) => operands roots visible limit depth entered function argument
          | _ => ⟨entered, .error (.outsideFragment root)⟩

private theorem normal_success (found : (normal roots visible limit depth state ref).result = .ok selected) :
    (runNested roots visible limit depth state.arena state.steps ref).result = .ok selected := by
  generalize original : runNested roots visible limit depth state.arena state.steps ref = raw at ⊢
  cases status : raw.result <;> simp [normal, original, status, Except.mapError] at found ⊢
  assumption

private theorem opening_success (found : (opening limit depth state body operand).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state body operand).result = .ok selected := by
  generalize original : NativeCoreTransformExact.substitute limit depth state body operand = raw at ⊢
  cases status : raw.result <;> simp [opening, original, status, Except.mapError] at found ⊢
  assumption

private theorem binary_read (source : Represents arena root (.node op [first, second])) :
    ∃ x y, arena[root]? = some (.node op [x, y]) ∧ Represents arena x first ∧ Represents arena y second := by
  cases source with
  | node read _ children =>
      cases children with
      | cons left rest =>
          cases rest with
          | cons right tail =>
              cases tail
              exact ⟨_, _, read, left, right⟩

structure Refines (env : Environment) (initial : State) (source : Term) (result : Outcome) (ref : Nat) : Prop where
  kept : Prefix initial.arena result.state.arena
  backward : Backward initial.arena → Backward result.state.arena
  value : ∃ output, Represents result.state.arena ref output ∧ Forward env source output

private theorem normal_refines (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : History definitions families env) (source : Represents state.arena ref term)
    (found : (normal roots visible limit depth state ref).result = .ok selected) :
    Refines env state term (normal roots visible limit depth state ref) selected := by
  obtain ⟨kept, backward, reduced⟩ := runNested_refines (visible := visible) (limit := limit) (depth := depth)
    (initial := state.steps) aligned history source
  exact ⟨kept, backward, reduced _ (normal_success found)⟩

private theorem apply_refines (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : History definitions families env)
    (functionRep : Represents state.arena function calleeTerm) (operandRep : Represents state.arena operand operandTerm)
    (success : (applyBeta roots visible limit depth state function operand).result = .ok selected) :
    Refines env state (.app calleeTerm operandTerm) (applyBeta roots visible limit depth state function operand) selected := by
  cases functionRep with
  | var read => simp [applyBeta, read] at success
  | @node _ op refs terms read arity represented =>
      cases op <;> try solve | simp [applyBeta, read] at success
      case lam erased =>
        cases represented with
        | nil => cases arity
        | @cons _ domain _ _ _ tail =>
            cases tail with
            | nil => cases arity
            | @cons bodyRef body _ _ bodyRep remaining =>
                cases remaining with
                | cons => cases arity
                | nil =>
                    let opened := opening limit depth state bodyRef operand
                    have branch : applyBeta roots visible limit depth state function operand =
                      opened.next (normal roots visible limit depth) := by
                      simp [applyBeta, read, opened]
                    rw [branch] at success ⊢
                    obtain ⟨instantiated, openedFound, openedDone⟩ := Outcome.next_success success
                    rw [openedDone] at success ⊢
                    have built := NativeCoreTransformExact.substitute_refines bodyRep operandRep (opening_success openedFound)
                    obtain ⟨kept, backward, outputRep⟩ := built
                    have normalized := normal_refines (frameDefinitions aligned kept) history outputRep success
                    obtain ⟨extended, preserves, output, represented, reduced⟩ := normalized
                    have beta : Forward env (.app (.lam erased domain body) operandTerm) (body.subst (single operandTerm)) :=
                      .old (.old (.acu (.compute (.beta erased domain body operandTerm))))
                    exact ⟨kept.trans extended, fun old => preserves (backward old), output, represented,
                      beta.trans reduced⟩

private theorem operands_refines (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : History definitions families env)
    (first : Represents state.arena function calleeTerm) (second : Represents state.arena operand operandTerm)
    (success : (operands roots visible limit depth state function operand).result = .ok selected) :
    Refines env state (.app calleeTerm operandTerm) (operands roots visible limit depth state function operand) selected := by
  unfold operands at success ⊢
  obtain ⟨callee, firstFound, firstDone⟩ := Outcome.next_success success
  rw [firstDone] at success ⊢
  obtain ⟨value, secondFound, secondDone⟩ := Outcome.next_success success
  rw [secondDone] at success ⊢
  obtain ⟨kept, backward, calleeNormal, calleeRep, calleeChanged⟩ := normal_refines aligned history first firstFound
  have prefixDefinitions := frameDefinitions aligned kept
  obtain ⟨frame, preserves, operandNormal, operandRep, operandChanged⟩ :=
    normal_refines prefixDefinitions history (second.frame kept) secondFound
  obtain ⟨final, keepBackward, output, represented, reduced⟩ :=
    apply_refines (frameDefinitions prefixDefinitions frame) history (calleeRep.frame frame) operandRep success
  have changed : Forward env (.app calleeTerm operandTerm) (.app calleeNormal operandNormal) :=
    .node .app (.cons calleeChanged (.cons operandChanged .nil))
  exact ⟨(kept.trans frame).trans final, fun old => keepBackward (preserves (backward old)),
    output, represented, changed.trans reduced⟩

theorem run_refines (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : History definitions families env) (source : Represents state.arena root (.app function argument))
    (success : (run roots visible limit depth state root).result = .ok selected) :
    Refines env state (.app function argument) (run roots visible limit depth state root) selected := by
  obtain ⟨callee, operand, read, first, second⟩ := binary_read source
  cases depth with
  | zero =>
      by_cases over : limit < state.steps + 1 <;>
        simp [run, NativeCoreUnsignedCancellation.tick, over] at success
  | succ depth =>
      rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
        ⟨answer, spent⟩
      cases answer with
      | error reason => simp [run, ticked] at success
      | ok charged =>
          cases charged
          let entered := {state with steps := spent}
          have branch : run roots visible limit (depth + 1) state root =
              operands roots visible limit depth entered callee operand := by simp [run, ticked, read, entered]
          rw [branch] at success ⊢
          obtain ⟨kept, backward, value⟩ := operands_refines (state := entered) aligned history first second success
          exact ⟨kept, backward, value⟩

theorem run_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root (.app function argument))
    (success : (run snapshot.definitions visible limit depth ⟨snapshot.arena, initial⟩ root).result = .ok selected) :
    let output := run snapshot.definitions visible limit depth ⟨snapshot.arena, initial⟩ root
    ∃ definitions families env,
      History definitions families env ∧ Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
        ∃ normalized, Represents output.state.arena selected normalized ∧ Forward env (.app function argument) normalized := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨kept, preserves, value⟩ := run_refines aligned history source success
  exact ⟨definitions, _, env, history, kept, preserves backward, value⟩

private theorem normal_rename (valid : Normal term) (rename : Nat → Nat) : Normal (term.rename rename) := by
  induction valid generalizing rename with
  | @atom term atomic =>
      cases term with
      | var index => rw [Term.rename]; exact .atom trivial
      | node op children =>
          cases children with
          | nil => simpa [Term.rename, renameArgs] using Normal.atom atomic
          | cons => contradiction
  | @node op terms supported _ ih =>
      rw [Term.rename]
      refine .node supported ?_
      intro child member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      rw [renameArgs_get] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst child
      exact ih original (List.mem_of_getElem? selected) _

private theorem normal_lift (values : ∀ index, Normal (subst index)) (count : Nat) :
    ∀ index, Normal (liftSub count subst index) := by
  induction count with
  | zero => exact values
  | succ count ih =>
      intro index
      cases index with
      | zero => exact .atom trivial
      | succ index => exact normal_rename (ih index) Nat.succ

/-- Renaming and substituting independent structurally normal terms keeps the
entire instantiated body in the structural normalization fragment. -/
theorem structural_substitution (valid : Normal term) (values : ∀ index, Normal (subst index)) :
    Normal (term.subst subst) := by
  induction valid generalizing subst with
  | @atom term atomic =>
      cases term with
      | var index => simpa [Term.subst] using values index
      | node op children =>
          cases children with
          | nil => simpa [Term.subst, substArgs] using Normal.atom atomic
          | cons => contradiction
  | @node op terms supported _ ih =>
      rw [Term.subst]
      refine .node supported ?_
      intro child member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      rw [substArgs_get] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst child
      exact ih original (List.mem_of_getElem? selected) (normal_lift values _)

private theorem lambda_body_normal (valid : Normal (.lam erased domain body)) : Normal body := by
  cases valid with
  | atom impossible => contradiction
  | node _ children => exact children _ (by simp)

private theorem normal_exact (normalTerm : Normal term) (source : Represents state.arena root term)
    (height : treeDepth term ≤ depth) (budget : state.steps + treeSize term ≤ limit) :
    normal roots visible limit depth state root =
      ⟨{state with steps := state.steps + treeSize term}, .ok root⟩ := by
  simp [normal, runNested_reuses_normal (roots := roots) (visible := visible) normalTerm source height budget,
    Except.mapError]

private theorem work_operand_ref (policy : NativeTransform.ReplacementMode) (value term : Term) (x y binders : Nat) :
    work (.replace policy x) value binders term = work (.replace policy y) value binders term := by
  induction term using Term.rec (motive_2 := fun terms => ∀ op offset binders,
    workArgs (.replace policy x) value binders op offset terms = workArgs (.replace policy y) value binders op offset terms)
      generalizing binders with
  | var => simp [work]
  | node op terms ih => simp [work, ih]
  | nil => simp [workArgs]
  | cons term terms first rest => simp [workArgs, first, rest]

/-- Success on structurally normal operands returns the exact instantiated
body with its original dependent type. The work formula includes the two
operand visits, native substitution and the final visit. -/
theorem run_normal_at_type
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root (.app (.lam erased domain body) operand))
    (typed : Environment.LoanTyping.HasType env loans ctx mode (.app (.lam erased domain body) operand) type)
    (calleeNormal : Normal (.lam erased domain body)) (operandNormal : Normal operand)
    (calleeDepth : treeDepth (.lam erased domain body) ≤ depth) (operandDepth : treeDepth operand ≤ depth)
    (bodyDepth : treeDepth (body.subst (single operand)) ≤ depth)
    (budget : state.steps + 1 + treeSize (.lam erased domain body) + treeSize operand +
      work (.replace .substitute 0) operand 0 body + treeSize (body.subst (single operand)) ≤ limit)
    (success : (run roots visible limit (depth + 1) state root).result = .ok selected) :
    let output := run roots visible limit (depth + 1) state root
    Represents output.state.arena selected (body.subst (single operand)) ∧
      Environment.LoanTyping.HasType env [] ctx true (body.subst (single operand)) type ∧
      output.state.steps = state.steps + 1 + treeSize (.lam erased domain body) + treeSize operand +
        work (.replace .substitute 0) operand 0 body + treeSize (body.subst (single operand)) := by
  obtain ⟨callee, value, appRead, calleeRep, operandRep⟩ := binary_read source
  obtain ⟨domainRef, bodyRef, calleeRead, _, bodyRep⟩ := binary_read calleeRep
  have rootExists := (Array.getElem?_eq_some_iff.mp appRead).1
  have rootBudget : ¬limit < state.steps + 1 := by omega
  have ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root =
      (.ok (), state.steps + 1) := by
    simp [NativeCoreUnsignedCancellation.tick, rootBudget, Nat.not_le.mpr rootExists]
  let entered := {state with steps := state.steps + 1}
  let afterCallee := {entered with steps := entered.steps + treeSize (.lam erased domain body)}
  let prepared := {afterCallee with steps := afterCallee.steps + treeSize operand}
  have calleeBudget : entered.steps + treeSize (.lam erased domain body) ≤ limit := by
    dsimp only [entered]
    omega
  have operandBudget : afterCallee.steps + treeSize operand ≤ limit := by
    dsimp only [afterCallee, entered]
    omega
  have calleeRan : normal roots visible limit depth entered callee = ⟨afterCallee, .ok callee⟩ :=
    normal_exact calleeNormal calleeRep calleeDepth calleeBudget
  have operandRan : normal roots visible limit depth afterCallee value = ⟨prepared, .ok value⟩ :=
    normal_exact operandNormal operandRep operandDepth operandBudget
  have preparedRead : prepared.arena[callee]? = some (.node (.lam erased) [domainRef, bodyRef]) :=
    calleeRead
  let opened := opening limit depth prepared bodyRef value
  have betaPath : run roots visible limit (depth + 1) state root = opened.next (normal roots visible limit depth) := by
    simp [run, ticked, appRead, operands, show {state with steps := state.steps + 1} = entered from rfl,
      calleeRan, operandRan, Outcome.next, applyBeta, preparedRead, opened]
  rw [betaPath] at success ⊢
  obtain ⟨openedRef, openedFound, openedDone⟩ := Outcome.next_success success
  rw [openedDone] at success ⊢
  have graphSubstitute := opening_success openedFound
  obtain ⟨_, _, substitutedRep⟩ := NativeCoreTransformExact.substitute_refines
    (state := prepared) bodyRep operandRep graphSubstitute
  have consumed := (NativeCoreTransformExact.run_refines (mode := .replace .substitute value) (binders := 0)
    (state := prepared) bodyRep operandRep graphSubstitute).2
  have visits : opened.state.steps = prepared.steps + work (.replace .substitute 0) operand 0 body := by
    change (NativeCoreTransformExact.substitute limit depth prepared bodyRef value).state.steps = _
    rwa [work_operand_ref .substitute operand body 0 value 0]
  have resultBudget : opened.state.steps + treeSize (body.subst (single operand)) ≤ limit := by
    rw [visits]
    exact budget
  have resultNormal : Normal (body.subst (single operand)) :=
    structural_substitution (lambda_body_normal calleeNormal) fun index => by
      cases index
      · exact operandNormal
      · exact .atom trivial
  have exactResult : normal roots visible limit depth opened.state openedRef =
      ⟨{opened.state with steps := opened.state.steps + treeSize (body.subst (single operand))}, .ok openedRef⟩ :=
    normal_exact resultNormal substitutedRep bodyDepth resultBudget
  rw [exactResult] at success ⊢
  have same : openedRef = selected := Except.ok.inj success
  subst selected
  refine ⟨substitutedRep, typed.ghostBeta wellFormed, ?_⟩
  change opened.state.steps + treeSize (body.subst (single operand)) = _
  rw [visits]

private theorem structural_global_free (normal : Normal term) : GlobalEnvironment.GlobalFree term := by
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

/-- Exact-byte admission identifies the stored declaration and its original
type for a structurally normal lambda application. -/
theorem run_admitted_normal_at_type {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (source : Represents snapshot.arena definition.valueRoot (.app (.lam erased domain body) operand))
    (calleeNormal : Normal (.lam erased domain body)) (operandNormal : Normal operand)
    (calleeDepth : treeDepth (.lam erased domain body) ≤ depth) (operandDepth : treeDepth operand ≤ depth)
    (bodyDepth : treeDepth (body.subst (single operand)) ≤ depth)
    (budget : initial + 1 + treeSize (.lam erased domain body) + treeSize operand +
      work (.replace .substitute 0) operand 0 body + treeSize (body.subst (single operand)) ≤ limit)
    (success : (run snapshot.definitions visible limit (depth + 1)
      ⟨snapshot.arena, initial⟩ definition.valueRoot).result = .ok selected) :
    let computed := run snapshot.definitions visible limit (depth + 1) ⟨snapshot.arena, initial⟩ definition.valueRoot
    ∃ definitions families env entry,
      History definitions families env ∧ env.globals[index]? = some entry ∧
        Represents computed.state.arena selected (body.subst (single operand)) ∧
        Environment.LoanTyping.HasType env [] [] true (body.subst (single operand)) entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, _, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  have free : GlobalEnvironment.GlobalFree (.app (.lam erased domain body) operand) := by
    have function := structural_global_free calleeNormal
    have argument := structural_global_free operandNormal
    simp [Term.app, GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary, function, argument]
  rw [represented.2.unique source, EnvironmentDelta.expand_globalFree free] at typed
  obtain ⟨rep, preserved, _⟩ :=
    run_normal_at_type (state := ⟨snapshot.arena, initial⟩) history.wellFormed source typed
      calleeNormal operandNormal calleeDepth operandDepth bodyDepth budget success
  exact ⟨definitions, _, env, entry, history, found, rep, preserved⟩

theorem compound_beta_example :
    let arena : Arena := #[.node .u64 [], .var 0, .node .array [1], .node (.lam false) [0, 2],
      .node (.natural 3) [], .node .app [3, 4]]
    run [] 0 11 4 ⟨arena, 0⟩ 5 = ⟨⟨arena.push (.node .array [4]), 11⟩, .ok 6⟩ := by
  rfl

end Jihoo.NativeKernel.NativeCoreBetaNormal
