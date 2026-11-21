import Jihoo.NativeCoreTransformExact
import Jihoo.NativeCorePureStructuralNormal
import Jihoo.NativeCoreRefinementNormal
import Jihoo.NativeLoanComputationPreservation

/-! The pure Core.normal path for structural constructors, applications,
Transport, and unsigned comparisons. Visited children share the budget in
source order. Substitution reenters the same recursive driver. -/
namespace Jihoo.NativeKernel.NativeCorePureComputationNormal

open NativeArena NativeProgramWire
open NativeCoreTransformExact (State)
open NativeCorePureStructuralNormal (structural)
open NativeCoreGlobalNormal (atomicOp)
open NativeCoreRefinementNormal (Projection projectionOf packFields select special pack_selection_computes)
open Environment.LoanTyping (GhostTransform compute_ghost_transform children_preservation raw_forward_lambda_shape)
open EnvironmentDelta (expand expandArgs expandArgs_map expand_substitution)
open NativeKernel.Conversion (ListRel)

inductive Error where
  | tick (reason : NativeCoreIdentical.Error)
  | substitution (reason : NativeCoreTransformExact.Error)
  | add (reason : NativeCoreGraph.Error)
  | invisibleGlobal (root : Nat)
  | outsideFragment (root : Nat)
  deriving Repr, DecidableEq

structure Outcome (α : Type) where
  state : State
  result : Except Error α
  deriving Repr

def Outcome.next (run : Outcome α) (next : State → α → Outcome β) : Outcome β :=
  match run.result with
  | .error reason => ⟨run.state, .error reason⟩
  | .ok ref => next run.state ref

theorem Outcome.next_success {previous : Outcome α} {next : State → α → Outcome β}
    (success : (previous.next next).result = .ok selected) :
    ∃ ref, previous.result = .ok ref ∧ previous.next next = next previous.state ref := by
  cases found : previous.result with
  | error reason => simp [Outcome.next, found] at success
  | ok ref => exact ⟨ref, rfl, by simp [Outcome.next, found]⟩

/-- Keep an unchanged graph row or append its replacement using the native arena limit. -/
def nodeResult (state : State) (root : Nat) (op : Op) (before after : List Nat)
    (reuse : Bool := true) : Outcome Nat :=
  if reuse ∧ before = after then ⟨state, .ok root⟩ else
    match NativeCoreGraph.addNode state.arena (.node op after) with
    | .error reason => ⟨state, .error (.add reason)⟩
    | .ok (extended, selected) => ⟨{state with arena := extended}, .ok selected⟩

private def opening (limit depth : Nat) (state : State) (body operand : Nat) : Outcome Nat :=
  let result := NativeCoreTransformExact.substitute limit depth state body operand
  ⟨result.state, result.result.mapError .substitution⟩

private def lambdaBody : Node → Option Nat
  | .node (.lam _) [_, body] => some body
  | _ => none

private def outerLambda : Node → Bool
  | .node (.lam _) _ => true
  | _ => false

/-- A normalized neutral application follows the unchanged/rebuild branch.
An If, Strict, or kept beta spine would require its respective specialized
native application case. -/
private def neutralCallee (arena : Arena) (callee : Nat) : Bool :=
  match arena[callee]? with
  | none | some (.node (.lam _) _) | some (.node .ifLt _) | some (.node .ifEq _) |
    some (.node .strict _) => false
  | some (.node .app [head, _]) =>
      match arena[head]? with
      | none => false
      | some headRow => !outerLambda headRow
  | some _ => true

private def reflHead : Node → Bool
  | .node .refl [_] => true
  | _ => false

private def supported (op : Op) : Bool :=
  atomicOp op || structural op || op == .app || op == .transport || (projectionOf op).isSome

private def children (visit : State → Nat → Outcome Nat) : State → List Nat → Outcome (List Nat)
  | state, [] => ⟨state, .ok []⟩
  | state, ref :: rest =>
      (visit state ref).next fun afterHead head =>
        (children visit afterHead rest).next fun afterTail tail => ⟨afterTail, .ok (head :: tail)⟩

abbrev visitOperands := children

private def projectRefinement (state : State) (root depth : Nat) (projection : Projection) (before : List Nat)
    (ref : Nat) : Outcome Nat :=
  if projection = .witness ∧ depth = 0 then ⟨state, .error (.tick (.depthLimit ref))⟩ else
    match state.arena[ref]? with
    | none => ⟨state, .error (.tick (.invalidReference ref))⟩
    | some node =>
        match packFields node with
        | some (word, proof) => ⟨state, .ok (select projection word proof)⟩
        | none =>
            if special projection node then ⟨state, .error (.outsideFragment ref)⟩
            else nodeResult state root projection.op before [ref] (decide (projection = .proof))

def finishApplication (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (before after : List Nat) : Outcome Nat :=
  match after with
  | [callee, operand] =>
      match state.arena[callee]?.bind lambdaBody with
      | some body => (opening limit depth state body operand).next visit
      | none =>
          if neutralCallee state.arena callee then nodeResult state root .app before after
          else ⟨state, .error (.outsideFragment callee)⟩
  | _ => ⟨state, .error (.outsideFragment root)⟩

private def post (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (op : Op) (before after : List Nat) : Outcome Nat :=
  if op = .app then finishApplication visit limit depth root state before after
  else if op = .transport then
    match after with
    | [_, evidence, payload] =>
        if (state.arena[evidence]?.map reflHead).getD false then ⟨state, .ok payload⟩
        else nodeResult state root op before after
    | _ => ⟨state, .error (.outsideFragment root)⟩
  else
    match projectionOf op with
    | none => nodeResult state root op before after
    | some projection =>
        match after with
        | [ref] => projectRefinement state root depth projection before ref
        | _ => ⟨state, .error (.outsideFragment root)⟩

private def conditionalOp (equal : Bool) : Op := if equal then .ifEq else .ifLt

private def numberAt (arena : Arena) (ref : Nat) : Option Nat :=
  match arena[ref]? with
  | some (.node (.natural value) []) => some value
  | _ => none

private def compareNumbers (equal : Bool) (left right : Nat) : Bool :=
  if equal then left == right else decide (left < right)

private def openTrue (visit : State → Nat → Outcome Nat) (limit depth : Nat) (state : State)
    (proof : Node) (body : Nat) : Outcome Nat :=
  match NativeCoreGraph.addNode state.arena proof with
  | .error reason => ⟨state, .error (.add reason)⟩
  | .ok (arena, evidence) => (opening limit depth {state with arena} body evidence).next visit

private def conditionalPost (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (equal : Bool) (before : List Nat) (left right yes no : Nat) : Outcome Nat :=
  match numberAt state.arena left, numberAt state.arena right with
  | some a, some b =>
      if compareNumbers equal a b then
        let proof := if equal then Node.node .refl [left] else Node.node .decide [left, right]
        openTrue visit limit depth state proof yes
      else visit state no
  | _, _ => (children visit state [yes, no]).next fun next arms =>
      nodeResult next root (conditionalOp equal) before (left :: right :: arms)

private def conditional (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (equal : Bool) (left right yes no : Nat) : Outcome Nat :=
  (children visit state [left, right]).next fun next operands =>
    match operands with
    | [a, b] => conditionalPost visit limit depth root next equal [left, right, yes, no] a b yes no
    | _ => ⟨next, .error (.outsideFragment root)⟩

private def conditionalKind (enabled : Bool) : Op → Option Bool
  | .ifEq => if enabled then some true else none
  | .ifLt => if enabled then some false else none
  | _ => none

/-- A pure operator which visits every operand, then may reenter the same
normalizer at the child depth. The operands and reentry share the live state. -/
structure PostExtension where
  accepts : Op → Bool
  finish : (State → Nat → Outcome Nat) → Nat → Nat → Nat → State → Op →
    List Nat → List Nat → Outcome Nat

/-- A pure operator that controls which original operands to visit and may
append syntax before asking the same recursive visitor to normalize it. -/
structure EarlyExtension where
  accepts : Op → Bool
  finish : (State → Nat → Outcome Nat) → Nat → Nat → Nat → State → Op → List Nat → Outcome Nat

private def noExtension : PostExtension :=
  ⟨fun _ => false, fun _ _ _ root state _ _ _ => ⟨state, .error (.outsideFragment root)⟩⟩

private def noEarly : EarlyExtension :=
  ⟨fun _ => false, fun _ _ _ root state _ _ => ⟨state, .error (.outsideFragment root)⟩⟩

private def runCore (extension : PostExtension) (early : EarlyExtension) (conditionals : Bool) (limit : Nat) :
    Nat → State → Nat → Outcome Nat
  | 0, state, root =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root
      let entered := {state with steps := tried.2}
      match tried.1 with
      | .error reason => ⟨entered, .error (.tick reason)⟩
      | .ok () => ⟨entered, .error (.tick (.depthLimit root))⟩
  | depth + 1, state, root =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root
      let entered := {state with steps := tried.2}
      match tried.1 with
      | .error reason => ⟨entered, .error (.tick reason)⟩
      | .ok () =>
          match state.arena[root]? with
          | none => ⟨entered, .error (.tick (.invalidReference root))⟩
          | some (.var _) => ⟨entered, .ok root⟩
          | some (.node op refs) =>
              let visit := runCore extension early conditionals limit depth
              if conditionals = true ∧ early.accepts op = true then
                early.finish visit limit depth root entered op refs
              else
                match conditionalKind conditionals op with
                | some equal =>
                    match refs with
                    | [a, b, yes, no] => conditional visit limit depth root entered equal a b yes no
                    | _ => ⟨entered, .error (.outsideFragment root)⟩
                | none =>
                    if supported op then
                      (children visit entered refs).next fun after args =>
                        post visit limit depth root after op refs args
                    else if conditionals = true ∧ extension.accepts op = true then
                      (children visit entered refs).next fun after args =>
                        extension.finish visit limit depth root after op refs args
                    else ⟨entered, .error (.outsideFragment root)⟩

def run (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runCore noExtension noEarly false limit depth state root

/-- Conditional branches supported by the same pure graph driver at every
visited node, including terms exposed by substitution. -/
def runWithConditionals (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runCore noExtension noEarly true limit depth state root

def runWithExtension (extension : PostExtension) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runCore extension noEarly true limit depth state root

def runWithExtensions (extension : PostExtension) (early : EarlyExtension) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  runCore extension early true limit depth state root

def runWithEarlyExtension (early : EarlyExtension) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runWithExtensions noExtension early limit depth state root

/-- Visit an ordered sequence of operands at the same child depth and with a
single clock and arena, stopping at the first rejected operand. -/
def normalizeOperands (limit depth : Nat) (state : State) (refs : List Nat) : Outcome (List Nat) :=
  children (runWithConditionals limit depth) state refs

private def aliasAt (arena : Arena) (root : Nat) : Option Nat := do
  let node ← arena[root]?
  match NativeCoreGlobalNormal.head node with
  | .alias index => some index
  | _ => none

/-- Follow visible raw declaration rows before entering the recursive pure
walk. Alias visits share its clock and lower the same depth bound. -/
def runThroughAliases (roots : List Roots) (visible limit : Nat) : Nat → State → Nat → Outcome Nat
  | 0, state, root => runWithConditionals limit 0 state root
  | depth + 1, state, root =>
      match aliasAt state.arena root with
      | none => runWithConditionals limit (depth + 1) state root
      | some index =>
          let ticked := NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root
          let entered := {state with steps := ticked.2}
          match ticked.1 with
          | .error reason => ⟨entered, .error (.tick reason)⟩
          | .ok () =>
              if index < visible then
                match roots[index]? with
                | some row => runThroughAliases roots visible limit depth entered row.valueRoot
                | none => ⟨entered, .error (.outsideFragment root)⟩
              else ⟨entered, .error (.invisibleGlobal root)⟩

private theorem aliasAt_lookup (found : aliasAt arena root = some index) :
    ∃ node, arena[root]? = some node ∧ NativeCoreGlobalNormal.head node = .alias index := by
  unfold aliasAt at found
  obtain ⟨node, read, selected⟩ := Option.bind_eq_some_iff.mp found
  cases kind : NativeCoreGlobalNormal.head node <;> simp [kind] at selected
  subst index
  exact ⟨node, read, kind⟩

private theorem expand_single (env : Environment) (value : Term) :
    (fun index => expand env (single value index)) = single (expand env value) := by
  funext index
  cases index <;> simp only [single, expand]

private theorem expand_compute (admissible : EnvironmentDelta.Admissible env) (step : ACU.Computes input output) :
    ACU.Computes (expand env input) (expand env output) := by
  cases step with
  | beta erased domain body argument =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Computes.beta erased (expand env domain) (expand env body) (expand env argument)
  | sub left right evidence ordered bound =>
      simpa only [expand, expandArgs] using ACU.Computes.sub left right (expand env evidence) ordered bound
  | read count terms offset evidence value selected =>
      simpa only [expand, expandArgs, expandArgs_map, List.map_cons, List.map_nil] using
        ACU.Computes.read count (terms.map (expand env)) offset (expand env evidence) (expand env output)
          (by simp only [List.getElem?_map, selected, Option.map_some])
  | witnessPack predicate witness evidence =>
      simpa only [expand, expandArgs] using
        ACU.Computes.witnessPack (expand env predicate) (expand env output) (expand env evidence)
  | proofPack predicate witness evidence =>
      simpa only [expand, expandArgs] using
        ACU.Computes.proofPack (expand env predicate) (expand env witness) (expand env output)
  | derefBorrow => simpa only [expand, expandArgs] using ACU.Computes.derefBorrow (expand env output)
  | borrowDeref => simpa only [expand, expandArgs] using ACU.Computes.borrowDeref (expand env output)
  | transportRefl family witness proof =>
      simpa only [expand, expandArgs] using
        ACU.Computes.transportRefl (expand env family) (expand env witness) (expand env output)
  | ifLtTrue left right yes no holds =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Computes.ifLtTrue left right (expand env yes) (expand env no) holds
  | ifLtFalse left right yes no holds =>
      simpa only [expand, expandArgs] using ACU.Computes.ifLtFalse left right (expand env yes) (expand env output) holds
  | ifEqTrue value yes no =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Computes.ifEqTrue value (expand env yes) (expand env no)
  | ifEqFalse left right yes no holds =>
      simpa only [expand, expandArgs] using ACU.Computes.ifEqFalse left right (expand env yes) (expand env output) holds

/-- The represented syntax and its transparent expansion can take the same
typed ghost reductions. Unvisited children may still contain globals. -/
structure GhostNormalization (env : Environment) (input output : Term) : Prop where
  raw : GhostTransform env input output
  expanded : GhostTransform env (EnvironmentDelta.expand env input) (EnvironmentDelta.expand env output)

theorem GhostNormalization.refl (term : Term) : GhostNormalization env term term :=
  ⟨.refl _, .refl _⟩

theorem GhostNormalization.trans (first : GhostNormalization env input middle)
    (second : GhostNormalization env middle output) : GhostNormalization env input output :=
  ⟨first.raw.trans second.raw, first.expanded.trans second.expanded⟩

theorem computeNormalization (wf : UnifiedProgram.EnvWellFormed env) (step : ACU.Computes input output) :
    GhostNormalization env input output :=
  ⟨compute_ghost_transform wf step, compute_ghost_transform wf (expand_compute wf.admissible step)⟩

/-- The graph proof is independent of the congruence used to interpret its
represented endpoints. -/
structure RefinesFor (relation : Term → Term → Prop) (start : State) (term : Term)
    (output : Outcome Nat) (selected : Nat) : Prop where
  kept : Prefix start.arena output.state.arena
  backward : Backward start.arena → Backward output.state.arena
  value : ∃ value, Represents output.state.arena selected value ∧ relation term value

abbrev Refines (env : Environment) := RefinesFor (GhostNormalization env)

structure Rules (relation : Term → Term → Prop) : Prop where
  same : ∀ term, relation term term
  trans : ∀ {input middle output}, relation input middle → relation middle output → relation input output
  compute : ∀ {input output}, ACU.Computes input output → relation input output
  node : ∀ {op ins outs}, op ≠ .lend → GlobalEnvironment.ordinary op = true →
    ListRel relation ins outs → relation (.node op ins) (.node op outs)

private theorem children_known (source : RepresentsList arena refs terms) :
    ∀ ref ∈ refs, ref < arena.size := by
  induction source using RepresentsList.rec (motive_1 := fun ref _ _ => ref < arena.size) with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1
  | nil => simp
  | cons _ _ head tail =>
      intro ref member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail ref member

theorem nodeResult_exact (read : state.arena[root]? = some (.node op before))
    (replaced : RepresentsList state.arena refs terms) (arity : refs.length = op.arity)
    (success : (nodeResult state root op before refs reuse).result = .ok selected) :
    let output := nodeResult state root op before refs reuse
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected (.node op terms) := by
  by_cases same : (reuse : Prop) ∧ before = refs
  · simp [nodeResult, same] at success
    subst selected
    simp only [nodeResult, same]
    exact ⟨.refl _, id, .node (same.2 ▸ read) arity replaced⟩
  · cases added : NativeCoreGraph.addNode state.arena (.node op refs) with
    | error reason => simp [nodeResult, same, added] at success
    | ok output =>
        obtain ⟨next, fresh⟩ := output
        simp [nodeResult, same, added] at success
        subst selected
        obtain ⟨kept, index, _, _, _, lookup⟩ := NativeCoreGraph.addNode_commits added
        have backward (old : Backward state.arena) : Backward next := by
          apply NativeCoreGraph.addNode_preserves_backward old added
          rw [index]
          exact children_known replaced
        simp only [nodeResult, same, ite_false, added]
        exact ⟨kept, backward, .node lookup arity (replaced.frame kept)⟩

theorem nodeResult_refines (read : state.arena[root]? = some (.node op before))
    (replaced : RepresentsList state.arena refs terms) (arity : refs.length = op.arity)
    (success : (nodeResult state root op before refs reuse).result = .ok selected) :
    Refines env state (.node op terms) (nodeResult state root op before refs reuse) selected := by
  obtain ⟨kept, backward, held⟩ := nodeResult_exact read replaced arity success
  exact ⟨kept, backward, _, held, .refl _⟩

private theorem nodeResult_relates (rules : Rules relation) (read : state.arena[root]? = some (.node op before))
    (replaced : RepresentsList state.arena refs terms) (arity : refs.length = op.arity)
    (success : (nodeResult state root op before refs reuse).result = .ok selected) :
    RefinesFor relation state (.node op terms) (nodeResult state root op before refs reuse) selected := by
  obtain ⟨kept, backward, held⟩ := nodeResult_exact read replaced arity success
  exact ⟨kept, backward, _, held, rules.same _⟩

private theorem opening_success (found : (opening limit depth state body operand).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state body operand).result = .ok selected := by
  generalize original : NativeCoreTransformExact.substitute limit depth state body operand = raw at ⊢
  cases status : raw.result <;> simp [opening, original, status, Except.mapError] at found ⊢
  assumption

/-- All graph-walk outcomes retain the old arena. The shared clock charges a
rejected visit at most one unit past the limit. -/
structure Progress (limit : Nat) (start : State) (outcome : Outcome α) : Prop where
  kept : Prefix start.arena outcome.state.arena
  monotone : start.steps ≤ outcome.state.steps
  bounded : start.steps ≤ limit → outcome.state.steps ≤ limit + 1
  accepted : start.steps ≤ limit → ∀ value, outcome.result = .ok value → outcome.state.steps ≤ limit

theorem Progress.atState (state : State) (result : Except Error α) : Progress limit state ⟨state, result⟩ :=
  ⟨.refl _, Nat.le_refl _, fun room => Nat.le_trans room (Nat.le_succ _), fun room _ _ => room⟩

theorem Progress.next {after : State → α → Outcome β} {result : Outcome α}
    (prior : Progress limit start result)
    (following : ∀ value, Progress limit result.state (after result.state value)) :
    Progress limit start (result.next after) := by
  cases status : result.result with
  | error reason =>
      simp only [Outcome.next, status]
      exact ⟨prior.kept, prior.monotone, prior.bounded, fun _ _ found => by cases found⟩
  | ok value =>
      have later := following value
      simp only [Outcome.next, status]
      exact ⟨prior.kept.trans later.kept, Nat.le_trans prior.monotone later.monotone,
        fun room => later.bounded (prior.accepted room value status),
        fun room selected found => later.accepted (prior.accepted room value status) selected found⟩

theorem Progress.fromAppend (kept : Prefix state.arena updated)
    (later : Progress limit {state with arena := updated} result) : Progress limit state result :=
  ⟨kept.trans later.kept, later.monotone, later.bounded, later.accepted⟩

theorem Progress.uncharged (kept : Prefix state.arena outcome.state.arena)
    (clock : outcome.state.steps = state.steps) : Progress limit state outcome :=
  ⟨kept, Nat.le_of_eq clock.symm, fun room => clock.symm ▸ Nat.le.step room, fun room _ _ => clock.symm ▸ room⟩

theorem Progress.map {outcome : Outcome α} (progress : Progress limit start outcome) (f : α → β) :
    Progress limit start (⟨outcome.state, outcome.result.map f⟩ : Outcome β) := by
  refine ⟨progress.kept, progress.monotone, progress.bounded, fun room _ success => ?_⟩
  cases status : outcome.result with
  | error reason => simp [status, Except.map] at success
  | ok value => exact progress.accepted room value status

private theorem Progress.afterTick (room : state.steps + 1 ≤ limit)
    (later : Progress limit {state with steps := state.steps + 1} result) : Progress limit state result :=
  ⟨later.kept, Nat.le_trans (Nat.le_succ _) later.monotone, fun _ => later.bounded room, fun _ => later.accepted room⟩

private theorem rejectedVisit (state : State) (reason : Error) :
    Progress limit state (⟨{state with steps := state.steps + 1}, .error reason⟩ : Outcome Nat) :=
  ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ found => by cases found⟩

theorem nodeResult_progress (state : State) (root : Nat) (op : Op) (before after : List Nat) (reuse : Bool) :
    Progress limit state (nodeResult state root op before after reuse) := by
  by_cases unchanged : (reuse : Prop) ∧ before = after
  · simpa [nodeResult, unchanged] using (Progress.atState (limit := limit) state (.ok root))
  · cases added : NativeCoreGraph.addNode state.arena (.node op after) with
    | error reason => simpa only [nodeResult, unchanged, ite_false, added] using
        (Progress.atState (limit := limit) (α := Nat) state (.error (.add reason)))
    | ok output =>
        obtain ⟨arena, ref⟩ := output
        simp only [nodeResult, unchanged, ite_false, added]
        exact Progress.fromAppend (NativeCoreGraph.addNode_commits added).1 (Progress.atState _ _)

private theorem opening_progress (limit depth : Nat) (state : State) (root argument : Nat) :
    Progress limit state (opening limit depth state root argument) := by
  have facts := NativeCoreTransformExact.substitute_progress limit depth state root argument
  refine ⟨facts.kept, facts.monotone, facts.bounded, fun room value found => ?_⟩
  exact facts.accepted room value (opening_success found)

private theorem children_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (refs : List Nat) : Progress limit state (children visit state refs) := by
  induction refs generalizing state with
  | nil => exact Progress.atState _ _
  | cons ref refs ih =>
      exact (visitProgress state ref).next (fun _ => (ih _).next (fun _ => Progress.atState _ _))

theorem visitOperands_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (refs : List Nat) : Progress limit state (visitOperands visit state refs) :=
  children_progress visitProgress state refs

private theorem openTrue_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (proof : Node) (body : Nat) : Progress limit state (openTrue visit limit depth state proof body) := by
  cases added : NativeCoreGraph.addNode state.arena proof with
  | error reason =>
      simp only [openTrue, added]
      exact Progress.atState _ _
  | ok result =>
      obtain ⟨arena, ref⟩ := result
      simp only [openTrue, added]
      apply Progress.fromAppend (NativeCoreGraph.addNode_commits added).1
      exact (opening_progress limit depth _ body ref).next (fun found => visitProgress _ found)

private theorem projectRefinement_progress (state : State) (root depth : Nat) (projection : Projection)
    (before : List Nat) (ref : Nat) : Progress limit state (projectRefinement state root depth projection before ref) := by
  simp only [projectRefinement]
  repeat' first | exact Progress.atState _ _ | exact nodeResult_progress _ _ _ _ _ _ | split

theorem finishApplication_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (before after : List Nat) :
    Progress limit state (finishApplication visit limit depth root state before after) := by
  simp only [finishApplication]
  repeat' first
    | exact Progress.atState _ _
    | exact nodeResult_progress _ _ _ _ _ _
    | exact (opening_progress limit depth _ _ _).next (fun ref => visitProgress _ ref)
    | split

private theorem post_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (op : Op) (before after : List Nat) :
    Progress limit state (post visit limit depth root state op before after) := by
  simp only [post]
  repeat' first
    | exact finishApplication_progress visitProgress state before after
    | exact Progress.atState _ _
    | exact nodeResult_progress _ _ _ _ _ _
    | exact projectRefinement_progress _ _ _ _ _ _
    | exact (opening_progress limit depth _ _ _).next (fun ref => visitProgress _ ref)
    | split

private theorem conditional_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref))
    (state : State) : Progress limit state (conditional visit limit depth root state equal left right yes no) := by
  simp only [conditional]
  apply (children_progress visitProgress state [left, right]).next
  intro normalized
  split
  · simp only [conditionalPost]
    repeat' first
      | exact visitProgress _ _
      | exact openTrue_progress visitProgress _ _ _
      | exact (children_progress visitProgress _ _).next (fun _ => nodeResult_progress _ _ _ _ _ _)
      | split
  · exact Progress.atState _ _

def PostExtension.Metered (extension : PostExtension) : Prop :=
  ∀ {visit limit depth root state op before after}, extension.accepts op = true →
    (∀ state ref, Progress limit state (visit state ref)) →
    Progress limit state (extension.finish visit limit depth root state op before after)

def EarlyExtension.Metered (early : EarlyExtension) : Prop :=
  ∀ {visit limit depth root state op refs}, early.accepts op = true →
    (∀ state ref, Progress limit state (visit state ref)) →
    Progress limit state (early.finish visit limit depth root state op refs)

private theorem runCore_progress (conditionals : Bool) (limit depth : Nat) (state : State) (root : Nat)
    (metered : extension.Metered) (earlyMetered : early.Metered) :
    Progress limit state (runCore extension early conditionals limit depth state root) := by
  induction depth generalizing state root with
  | zero =>
      by_cases excess : limit < state.steps + 1 <;>
        simp [runCore, NativeCoreUnsignedCancellation.tick, excess, rejectedVisit]
  | succ depth ih =>
      by_cases excess : limit < state.steps + 1
      · simp [runCore, NativeCoreUnsignedCancellation.tick, excess, rejectedVisit]
      · by_cases missing : state.arena.size ≤ root
        · simp [runCore, NativeCoreUnsignedCancellation.tick, excess, missing, rejectedVisit]
        · have room : state.steps + 1 ≤ limit := Nat.le_of_not_gt excess
          have normal : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root =
              (.ok (), state.steps + 1) := by simp [NativeCoreUnsignedCancellation.tick, excess, missing]
          simp only [runCore, normal]
          cases lookup : state.arena[root]? with
          | none => simpa only [lookup] using (rejectedVisit (limit := limit) state (.tick (.invalidReference root)))
          | some node =>
              try simp only [lookup]
              apply Progress.afterTick room
              cases node with
              | var index => exact Progress.atState _ _
              | node op refs =>
                  by_cases enabled : conditionals = true ∧ early.accepts op = true
                  · simp only [ite_eq_left enabled]
                    exact earlyMetered enabled.2 ih
                  · simp only [ite_eq_right enabled]
                    cases conditionalKind conditionals op with
                    | some equal =>
                        simp only
                        split
                        · exact conditional_progress ih _
                        · exact Progress.atState _ _
                    | none =>
                        simp only
                        split
                        · exact (children_progress ih _ _).next (fun inputs => post_progress ih _ op refs inputs)
                        · split
                          · rename_i enabled
                            exact (children_progress ih _ _).next (fun _ => metered enabled.2 ih)
                          · exact Progress.atState _ _

theorem runWithConditionals_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runWithConditionals limit depth state root) :=
  runCore_progress true limit depth state root (fun impossible => by cases impossible)
    (fun impossible => by cases impossible)

theorem runWithExtension_progress (metered : extension.Metered) (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runWithExtension extension limit depth state root) :=
  runCore_progress true limit depth state root metered (fun impossible => by cases impossible)

theorem runWithExtensions_progress (metered : extension.Metered) (earlyMetered : early.Metered)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runWithExtensions extension early limit depth state root) :=
  runCore_progress true limit depth state root metered earlyMetered

theorem runWithEarlyExtension_progress (metered : early.Metered) (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runWithEarlyExtension early limit depth state root) :=
  runWithExtensions_progress (by intro _ _ _ _ _ _ _ _ impossible; cases impossible) metered limit depth state root

theorem normalizeOperands_progress (limit depth : Nat) (state : State) (refs : List Nat) :
    Progress limit state (normalizeOperands limit depth state refs) :=
  children_progress (runWithConditionals_progress limit depth) state refs

theorem runThroughAliases_progress (roots : List Roots) (visible limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runThroughAliases roots visible limit depth state root) := by
  induction depth generalizing state root with
  | zero => exact runWithConditionals_progress _ _ _ _
  | succ depth ih =>
      cases chosen : aliasAt state.arena root with
      | none => simpa only [runThroughAliases, chosen] using runWithConditionals_progress limit (depth + 1) state root
      | some index =>
          by_cases excess : limit < state.steps + 1
          · simp [runThroughAliases, chosen, NativeCoreUnsignedCancellation.tick, excess, rejectedVisit]
          · by_cases missing : state.arena.size ≤ root
            · simp [runThroughAliases, chosen, NativeCoreUnsignedCancellation.tick, excess, missing, rejectedVisit]
            · have normal : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root =
                  (.ok (), state.steps + 1) := by simp [NativeCoreUnsignedCancellation.tick, excess, missing]
              simp only [runThroughAliases, chosen, normal]
              apply Progress.afterTick (Nat.le_of_not_gt excess)
              split
              · split
                · exact ih _ _
                · exact Progress.atState _ _
              · exact Progress.atState _ _

private theorem child_binary (children : RepresentsList arena refs terms) (arity : refs.length = 2) :
    ∃ f a u v, refs = [f, a] ∧ terms = [u, v] ∧ Represents arena f u ∧ Represents arena a v := by
  cases children with
  | nil => cases arity
  | cons first rest =>
      cases rest with
      | nil => cases arity
      | cons second last =>
          cases last with
          | nil => exact ⟨_, _, _, _, rfl, rfl, first, second⟩
          | cons => cases arity

private theorem child_ternary (children : RepresentsList arena refs terms) (arity : refs.length = 3) :
    ∃ f e p u v w, refs = [f, e, p] ∧ terms = [u, v, w] ∧
      Represents arena f u ∧ Represents arena e v ∧ Represents arena p w := by
  cases children with
  | nil => cases arity
  | cons first rest =>
      cases rest with
      | nil => cases arity
      | cons second rest =>
          cases rest with
          | nil => cases arity
          | cons third last =>
              cases last with
              | nil => exact ⟨_, _, _, _, _, _, rfl, rfl, first, second, third⟩
              | cons => cases arity

private theorem child_quaternary (children : RepresentsList arena refs terms) (arity : refs.length = 4) :
    ∃ a b yes no p q y n, refs = [a, b, yes, no] ∧ terms = [p, q, y, n] ∧
      Represents arena a p ∧ Represents arena b q ∧ Represents arena yes y ∧ Represents arena no n := by
  cases children with
  | nil => cases arity
  | cons head rest =>
      obtain ⟨_, _, _, _, _, _, rfl, rfl, second, yes, no⟩ := child_ternary rest (Nat.succ.inj arity)
      exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, head, second, yes, no⟩

private theorem represented_lambda (represented : Represents arena root term)
    (selected : arena[root]?.bind lambdaBody = some body) :
    ∃ erased domain source, term = .lam erased domain source ∧ Represents arena body source := by
  cases represented with
  | var found => simp [found, lambdaBody] at selected
  | @node _ op refs terms found arity children =>
      cases op <;> try solve | simp [found, lambdaBody] at selected
      case lam erased =>
        obtain ⟨_, bodyRef, domain, source, rfl, rfl, _, bodyRep⟩ := child_binary children arity
        simp [found, lambdaBody] at selected
        subst body
        exact ⟨erased, domain, source, rfl, bodyRep⟩

private theorem represented_refl (represented : Represents arena root term)
    (selected : (arena[root]?.map reflHead).getD false = true) :
    ∃ value, term = .refl value := by
  cases represented with
  | var found => simp [found, reflHead] at selected
  | @node _ op refs terms found arity children =>
      cases op <;> try solve | simp [found, reflHead] at selected
      case refl =>
        cases children with
        | nil => cases arity
        | cons value tail =>
            cases tail with
            | nil => exact ⟨_, rfl⟩
            | cons => cases arity

private theorem projectionOf_op (found : projectionOf op = some projection) : op = projection.op := by
  cases projection <;> cases op <;> simp_all [projectionOf, Projection.op]

private theorem projectRefinement_refines (rules : Rules relation)
    (read : state.arena[root]? = some (.node projection.op before))
    (represented : Represents state.arena ref term)
    (success : (projectRefinement state root depth projection before ref).result = .ok selected) :
    RefinesFor relation state (projection.term term) (projectRefinement state root depth projection before ref) selected := by
  obtain ⟨row, known⟩ : ∃ row, state.arena[ref]? = some row := by
    cases represented with
    | var lookup | node lookup => exact ⟨_, lookup⟩
  by_cases tooDeep : projection = .witness ∧ depth = 0
  · simp [projectRefinement, tooDeep] at success
  · cases parts : packFields row with
    | none =>
        by_cases specialized : special projection row = true
        · simp [projectRefinement, tooDeep, known, parts, specialized] at success
        · simp only [projectRefinement, tooDeep, ite_false, known, parts, specialized] at success ⊢
          exact nodeResult_relates rules read (.cons represented .nil) (by cases projection <;> rfl) success
    | some fields =>
        obtain ⟨word, proof⟩ := fields
        simp only [projectRefinement, tooDeep, ite_false, known, parts] at success ⊢
        have exactRef := Except.ok.inj success
        subst selected
        obtain ⟨output, rep, step⟩ := pack_selection_computes (projection := projection) known represented parts
        exact ⟨.refl _, id, output, rep, rules.compute step⟩

theorem emptyPrefix (arena : Arena) : Prefix #[] arena := by
  refine ⟨Nat.zero_le _, ?_⟩
  simp

theorem finishApplication_relatesFrom {relation : Term → Term → Prop}
    (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node .app before))
    (calleeRep : Represents state.arena callee function) (operandRep : Represents state.arena operand argument)
    (visitRelates : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      let output := visit state ref
      Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
        ∃ residual, Represents output.state.arena selected residual ∧ relation term residual)
    (unchanged : ∀ term, relation term term)
    (beta : ∀ {erased domain body argument result}, relation (body.subst (single argument)) result →
      relation (.app (.lam erased domain body) argument) result)
    (success : (finishApplication visit limit depth root state before [callee, operand]).result = .ok selected) :
    let output := finishApplication visit limit depth root state before [callee, operand]
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ relation (.app function argument) residual := by
  cases picked : state.arena[callee]?.bind lambdaBody with
  | none =>
      by_cases neutral : neutralCallee state.arena callee = true
      · simp only [finishApplication, picked, ite_eq_left neutral] at success ⊢
        obtain ⟨kept, backward, held⟩ := nodeResult_exact read (.cons calleeRep (.cons operandRep .nil)) rfl success
        exact ⟨kept, backward, _, held, unchanged _⟩
      · simp [finishApplication, picked, neutral] at success
  | some bodyRef =>
      obtain ⟨erased, domain, body, rfl, bodyRep⟩ := represented_lambda calleeRep picked
      simp only [finishApplication, picked] at success ⊢
      obtain ⟨instantiated, found, done⟩ := Outcome.next_success success
      rw [done] at success ⊢
      obtain ⟨kept, backward, bodyRep⟩ :=
        NativeCoreTransformExact.substitute_refines bodyRep operandRep (opening_success found)
      obtain ⟨later, preserves, term, termRep, change⟩ := visitRelates (onBase.trans kept) bodyRep success
      exact ⟨kept.trans later, fun old => preserves (backward old), term, termRep, beta change⟩

theorem finishApplication_relates {relation : Term → Term → Prop}
    (read : state.arena[root]? = some (.node .app before))
    (calleeRep : Represents state.arena callee function) (operandRep : Represents state.arena operand argument)
    (visitRelates : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      let output := visit state ref
      Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
        ∃ residual, Represents output.state.arena selected residual ∧ relation term residual)
    (unchanged : ∀ term, relation term term)
    (beta : ∀ {erased domain body argument result}, relation (body.subst (single argument)) result →
      relation (.app (.lam erased domain body) argument) result)
    (success : (finishApplication visit limit depth root state before [callee, operand]).result = .ok selected) :
    let output := finishApplication visit limit depth root state before [callee, operand]
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ relation (.app function argument) residual :=
  finishApplication_relatesFrom (emptyPrefix _) read calleeRep operandRep
    (fun _ input computed => visitRelates input computed) unchanged beta success

private theorem post_refines (rules : Rules relation) (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node op before)) (rep : RepresentsList state.arena after terms)
    (arity : after.length = op.arity)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (success : (post visit limit depth root state op before after).result = .ok selected) :
    RefinesFor relation state (.node op terms) (post visit limit depth root state op before after) selected := by
  by_cases app : op = .app
  · subst op
    obtain ⟨callee, operand, function, argument, rfl, rfl, calleeRep, operandRep⟩ := child_binary rep arity
    simp only [post, ite_true] at success ⊢
    obtain ⟨kept, backward, residual⟩ := finishApplication_relatesFrom
      (relation := relation) onBase read calleeRep operandRep
      (fun onBase source done => by
        obtain ⟨kept, backward, value⟩ := visitRefines onBase source done
        exact ⟨kept, backward, value⟩)
      rules.same
      (fun {erased domain body argument _} changed =>
        rules.trans (rules.compute (.beta erased domain body argument)) changed)
      success
    exact ⟨kept, backward, residual⟩
  · by_cases transport : op = .transport
    · subst op
      obtain ⟨familyRef, evidence, payload, family, proof, result, rfl, rfl, _, evidenceRep, payloadRep⟩ :=
        child_ternary rep arity
      by_cases reflexive : (state.arena[evidence]?.map reflHead).getD false = true
      · obtain ⟨value, rfl⟩ := represented_refl evidenceRep reflexive
        have contraction : post visit limit depth root state .transport before [familyRef, evidence, payload] =
            ⟨state, .ok payload⟩ := by simp [post, reflexive]
        rw [contraction] at success ⊢
        have same : payload = selected := Except.ok.inj success
        subst selected
        exact ⟨.refl _, id, result, payloadRep, rules.compute (.transportRefl family value result)⟩
      · have residual : post visit limit depth root state .transport before [familyRef, evidence, payload] =
            nodeResult state root .transport before [familyRef, evidence, payload] := by simp [post, reflexive]
        rw [residual] at success ⊢
        exact nodeResult_relates rules read rep arity success
    · cases projected : projectionOf op with
      | none =>
          have rebuilt : post visit limit depth root state op before after = nodeResult state root op before after := by
            simp [post, app, transport, projected]
          rw [rebuilt] at success ⊢
          exact nodeResult_relates rules read rep arity success
      | some projection =>
          have operator := projectionOf_op projected
          subst op
          have unary : after.length = 1 := arity.trans (by cases projection <;> rfl)
          cases rep with
          | nil => cases unary
          | cons child rest =>
              cases rest with
              | cons => cases unary
              | nil =>
                  simp only [post, app, transport, ite_false, projected] at success ⊢
                  exact projectRefinement_refines rules read child success

private theorem layers_forward (changes : ListRel (GhostTransform env) ins outs) :
    ListRel (Environment.RawLend.Forward env) ins outs := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

private theorem ghost_under_node (wellFormed : UnifiedProgram.EnvWellFormed env) (ordinary : op ≠ .lend)
    (changes : ListRel (GhostTransform env) ins outs) : GhostTransform env (.node op ins) (.node op outs) := by
  have forward := Environment.RawLend.Forward.node op (layers_forward changes)
  exact ⟨forward, raw_forward_lambda_shape forward,
    fun typed => children_preservation wellFormed typed op _ rfl ordinary _ changes⟩

private theorem changes_raw (changes : ListRel (GhostNormalization env) ins outs) :
    ListRel (GhostTransform env) ins outs := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.raw ih

private theorem changes_expanded (changes : ListRel (GhostNormalization env) ins outs) :
    ListRel (GhostTransform env) (EnvironmentDelta.expandArgs env ins) (EnvironmentDelta.expandArgs env outs) := by
  induction changes with
  | nil => simp only [expandArgs]; exact .nil
  | cons first rest ih => simp only [expandArgs]; exact .cons first.expanded ih

theorem GhostNormalization.node (wf : UnifiedProgram.EnvWellFormed env) (ordinary : op ≠ .lend)
    (nonglobal : GlobalEnvironment.ordinary op = true) (changes : ListRel (GhostNormalization env) ins outs) :
    GhostNormalization env (.node op ins) (.node op outs) := by
  refine ⟨ghost_under_node wf ordinary (changes_raw changes), ?_⟩
  rw [EnvironmentDelta.expand_ordinary nonglobal, EnvironmentDelta.expand_ordinary nonglobal]
  exact ghost_under_node wf ordinary (changes_expanded changes)

private theorem ghostRules (wf : UnifiedProgram.EnvWellFormed env) : Rules (GhostNormalization env) :=
  ⟨GhostNormalization.refl, GhostNormalization.trans, computeNormalization wf, GhostNormalization.node wf⟩

/-- Proof of the computation in the transparently expanded term checked by
mixed admission. A delta hop between two raw representations can be the
identity in this relation. -/
abbrev ExpandedNormalization (env : Environment) (input output : Term) :=
  GhostTransform env (expand env input) (expand env output)

theorem expandedRules (wf : UnifiedProgram.EnvWellFormed env) : Rules (ExpandedNormalization env) := by
  refine ⟨fun x => .refl _, fun x y => x.trans y, fun step => compute_ghost_transform wf (expand_compute wf.admissible step), ?_⟩
  intro op ins outs ordinary nonglobal changes
  change GhostTransform env (expand env (.node op ins)) (expand env (.node op outs))
  rw [EnvironmentDelta.expand_ordinary nonglobal, EnvironmentDelta.expand_ordinary nonglobal]
  apply ghost_under_node wf ordinary
  induction changes with
  | nil => simp only [expandArgs]; exact .nil
  | cons first _ rest => simp only [expandArgs]; exact .cons first rest

/-- A sequential batch preserves the arena and the order of the endpoints
for any relation witnessed by its single-operand visitor. -/
theorem visitOperands_relatesFrom {relation : Term → Term → Prop} (onBase : Prefix base start.arena)
    (source : RepresentsList start.arena refs ins)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      let output := visit state ref
      Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
        ∃ term', Represents output.state.arena selected term' ∧ relation term term')
    (success : (visitOperands visit start refs).result = .ok selected) :
    let output := visitOperands visit start refs
    Prefix start.arena output.state.arena ∧ (Backward start.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧
      ∃ outs, RepresentsList output.state.arena selected outs ∧ ListRel relation ins outs := by
  unfold visitOperands at success ⊢
  induction refs generalizing start ins selected with
  | nil =>
      cases source
      simp [children] at success
      subst selected
      exact ⟨.refl _, id, rfl, [], .nil, .nil⟩
  | cons ref refs ih =>
      cases source with
      | @cons _ first _ ins head tail =>
          rw [children] at success ⊢
          obtain ⟨headRef, headFound, headDone⟩ := Outcome.next_success success
          rw [headDone] at success ⊢
          obtain ⟨tailRefs, tailFound, tailDone⟩ := Outcome.next_success success
          rw [tailDone] at success ⊢
          have same : headRef :: tailRefs = selected := Except.ok.inj success
          subst selected
          obtain ⟨kept, backward, firstOut, headRep, headChange⟩ := visitRefines onBase head headFound
          obtain ⟨extended, preserves, exactLength, restOut, tailRep, tailChange⟩ :=
            ih (onBase.trans kept) (tail.frame kept) tailFound
          exact ⟨kept.trans extended, fun old => preserves (backward old), congrArg Nat.succ exactLength,
            firstOut :: restOut, .cons (headRep.frame extended) tailRep, .cons headChange tailChange⟩

theorem visitOperands_relates {relation : Term → Term → Prop} (source : RepresentsList start.arena refs ins)
    (visitRefines : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      let output := visit state ref
      Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
        ∃ term', Represents output.state.arena selected term' ∧ relation term term')
    (success : (visitOperands visit start refs).result = .ok selected) :
    let output := visitOperands visit start refs
    Prefix start.arena output.state.arena ∧ (Backward start.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧
      ∃ outs, RepresentsList output.state.arena selected outs ∧ ListRel relation ins outs :=
  visitOperands_relatesFrom (emptyPrefix _) source (fun _ input computed => visitRefines input computed) success

private theorem children_refines {property : Term → Prop} (onBase : Prefix base start.arena) (source : RepresentsList start.arena refs ins)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      RefinesFor relation state term (visit state ref) selected ∧ property term)
    (success : (children visit start refs).result = .ok selected) :
    let output := children visit start refs
    Prefix start.arena output.state.arena ∧ (Backward start.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧ (∀ x ∈ ins, property x) ∧
      ∃ outs, RepresentsList output.state.arena selected outs ∧ ListRel (relation) ins outs := by
  obtain ⟨kept, backward, length, outs, represented, relations⟩ :=
    visitOperands_relatesFrom (relation := fun a b => relation a b ∧ property a) onBase source
      (fun onBase input done => by
        obtain ⟨⟨kept, backward, value, rep, norm⟩, known⟩ := visitRefines onBase input done
        exact ⟨kept, backward, value, rep, norm, known⟩) success
  have separate {xs ys} (relations : ListRel (fun a b => relation a b ∧ property a) xs ys) :
      (∀ x ∈ xs, property x) ∧ ListRel (relation) xs ys := by
    induction relations with
    | nil => exact ⟨by simp, .nil⟩
    | cons first _ rest =>
        refine ⟨?_, .cons first.1 rest.2⟩
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact first.2
        · exact rest.1 item member
  exact ⟨kept, backward, length, (separate relations).1, outs, represented, (separate relations).2⟩

theorem visitOperands_refines (source : RepresentsList state.arena refs terms)
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (success : (visitOperands visit state refs).result = .ok selected) :
    let output := visitOperands visit state refs
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧
      ∃ residuals, RepresentsList output.state.arena selected residuals ∧ ListRel (GhostNormalization env) terms residuals := by
  obtain ⟨kept, backward, count, _, residuals, rep, changes⟩ :=
    children_refines (property := fun _ => True) (emptyPrefix _) source (fun _ rep done => ⟨visitor rep done, trivial⟩) success
  exact ⟨kept, backward, count, residuals, rep, changes⟩

private theorem numberAt_term (rep : Represents arena ref term)
    (found : numberAt arena ref = some value) : term = .natural value := by
  cases rep with
  | var lookup => simp [numberAt, lookup] at found
  | @node _ op refs source lookup arity children =>
      cases op <;> try solve | simp [numberAt, lookup] at found
      case natural n =>
        cases children with
        | nil =>
            simp [numberAt, lookup] at found
            subst value
            rfl
        | cons => simp [Op.arity] at arity

private theorem openTrue_refines (onBase : Prefix base state.arena) (bodyRep : Represents state.arena body source)
    (argsRep : RepresentsList state.arena refs args) (arity : refs.length = op.arity)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (success : (openTrue visit limit depth state (.node op refs) body).result = .ok selected) :
    RefinesFor relation state (source.subst (single (.node op args)))
      (openTrue visit limit depth state (.node op refs) body) selected := by
  cases added : NativeCoreGraph.addNode state.arena (.node op refs) with
  | error reason => simp [openTrue, added] at success
  | ok output =>
      obtain ⟨extended, evidence⟩ := output
      simp only [openTrue, added] at success ⊢
      obtain ⟨result, found, done⟩ := Outcome.next_success success
      rw [done] at success ⊢
      obtain ⟨kept, index, _, _, _, lookup⟩ := NativeCoreGraph.addNode_commits added
      have extendedBackward (valid : Backward state.arena) : Backward extended := by
        apply NativeCoreGraph.addNode_preserves_backward valid added
        rw [index]
        exact children_known argsRep
      have proofRep : Represents extended evidence (.node op args) := .node lookup arity (argsRep.frame kept)
      obtain ⟨opened, openedBackward, instantiated⟩ :=
        NativeCoreTransformExact.substitute_refines (bodyRep.frame kept) proofRep (opening_success found)
      obtain ⟨frame, backward, residual, represented, change⟩ := visitRefines (onBase.trans (kept.trans opened)) instantiated success
      exact ⟨kept.trans (opened.trans frame), fun old => backward (openedBackward (extendedBackward old)),
        residual, represented, change⟩

private theorem RefinesFor.prepend (rules : Rules relation) (change : relation source middle)
    (rest : RefinesFor relation state middle output selected) : RefinesFor relation state source output selected := by
  obtain ⟨kept, backward, residual, rep, transformed⟩ := rest
  exact ⟨kept, backward, residual, rep, rules.trans change transformed⟩

private theorem conditionalPost_refines {property : Term → Prop} (rules : Rules relation)
    (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (conditionalOp equal) before))
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (yesRep : Represents state.arena yes p) (noRep : Represents state.arena no q)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      RefinesFor relation state term (visit state ref) selected ∧ property term)
    (success : (conditionalPost visit limit depth root state equal before left right yes no).result = .ok selected) :
    RefinesFor relation state (.node (conditionalOp equal) [a, b, p, q])
      (conditionalPost visit limit depth root state equal before left right yes no) selected := by
  have neutral
      (branch : conditionalPost visit limit depth root state equal before left right yes no =
        (children visit state [yes, no]).next fun next arms =>
          nodeResult next root (conditionalOp equal) before (left :: right :: arms)) :
      RefinesFor relation state (.node (conditionalOp equal) [a, b, p, q])
        (conditionalPost visit limit depth root state equal before left right yes no) selected := by
    rw [branch] at success ⊢
    obtain ⟨arms, found, done⟩ := Outcome.next_success success
    rw [done] at success ⊢
    obtain ⟨kept, backward, armCount, _, _, armsRep, changes⟩ :=
      children_refines onBase (.cons yesRep (.cons noRep .nil)) visitRefines found
    have arity : (left :: right :: arms).length = (conditionalOp equal).arity := by
      cases equal <;> simp [conditionalOp, armCount, Op.arity]
    have changed := rules.node (op := conditionalOp equal)
      (by cases equal <;> decide) (by cases equal <;> rfl)
      (.cons (rules.same a) (.cons (rules.same b) changes))
    have normalized := nodeResult_relates rules (kept.lookup read)
      (.cons (leftRep.frame kept) (.cons (rightRep.frame kept) armsRep)) arity success
    obtain ⟨extended, preserves, residual, rep, tail⟩ := normalized
    exact ⟨kept.trans extended, fun old => preserves (backward old), residual, rep, rules.trans changed tail⟩
  cases leftNumber : numberAt state.arena left <;> cases rightNumber : numberAt state.arena right
  case none.none => exact neutral (by simp [conditionalPost, leftNumber, rightNumber])
  case none.some => exact neutral (by simp [conditionalPost, leftNumber, rightNumber])
  case some.none => exact neutral (by simp [conditionalPost, leftNumber, rightNumber])
  rename_i m n
  have leftShape := numberAt_term leftRep leftNumber
  have rightShape := numberAt_term rightRep rightNumber
  subst a b
  cases equal
  · by_cases holds : m < n
    · simp [conditionalPost, leftNumber, rightNumber, compareNumbers, holds] at success ⊢
      exact (openTrue_refines onBase yesRep (.cons leftRep (.cons rightRep .nil)) rfl
        (fun onBase rep done => (visitRefines onBase rep done).1) success).prepend rules
        (rules.compute (.ifLtTrue m n p q holds))
    · simp [conditionalPost, leftNumber, rightNumber, compareNumbers, holds] at success ⊢
      exact (visitRefines onBase noRep success).1.prepend rules
        (rules.compute (.ifLtFalse m n p q (Nat.le_of_not_lt holds)))
  · by_cases same : m = n
    · subst n
      simp [conditionalPost, leftNumber, rightNumber, compareNumbers] at success ⊢
      exact (openTrue_refines onBase yesRep (.cons leftRep .nil) rfl
        (fun onBase rep done => (visitRefines onBase rep done).1) success).prepend rules
        (rules.compute (.ifEqTrue m p q))
    · simp [conditionalPost, leftNumber, rightNumber, compareNumbers, same] at success ⊢
      exact (visitRefines onBase noRep success).1.prepend rules (rules.compute (.ifEqFalse m n p q same))

private theorem conditional_refines {property : Term → Prop} (rules : Rules relation)
    (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (conditionalOp equal) [left, right, yes, no]))
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (yesRep : Represents state.arena yes p) (noRep : Represents state.arena no q)
    (visitRefines : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      RefinesFor relation state term (visit state ref) selected ∧ property term)
    (success : (conditional visit limit depth root state equal left right yes no).result = .ok selected) :
    RefinesFor relation state (.node (conditionalOp equal) [a, b, p, q])
      (conditional visit limit depth root state equal left right yes no) selected := by
  unfold conditional at success ⊢
  obtain ⟨operands, found, done⟩ := Outcome.next_success success
  rw [done] at success ⊢
  obtain ⟨kept, backward, operandCount, _, terms, reps, changes⟩ :=
    children_refines onBase (.cons leftRep (.cons rightRep .nil)) visitRefines found
  obtain ⟨lhs, rhs, first, second, rfl, rfl, firstRep, secondRep⟩ := child_binary reps operandCount
  cases changes with
  | cons firstStep tail =>
      cases tail with
      | cons secondStep empty =>
          cases empty
          have compared := conditionalPost_refines rules (onBase.trans kept) (kept.lookup read) firstRep secondRep
            (yesRep.frame kept) (noRep.frame kept) visitRefines success
          have transformed := rules.node (op := conditionalOp equal) (by cases equal <;> decide)
            (by cases equal <;> rfl)
            (.cons firstStep (.cons secondStep (.cons (rules.same p) (.cons (rules.same q) .nil))))
          obtain ⟨more, preserves, residual, rep, final⟩ := compared
          exact ⟨kept.trans more, fun old => preserves (backward old), residual, rep, rules.trans transformed final⟩

private theorem conditionalKind_op (found : conditionalKind enabled op = some equal) :
    op = conditionalOp equal ∧ enabled = true := by
  cases enabled <;> cases op <;> simp_all [conditionalKind, conditionalOp]

def PostExtension.SoundFor (relation : Term → Term → Prop) (extension : PostExtension) : Prop :=
  (∀ {op}, extension.accepts op = true → op ≠ .lend ∧ GlobalEnvironment.ordinary op = true) ∧
  ∀ {visit limit depth root state op before after terms selected},
    extension.accepts op = true →
    state.arena[root]? = some (.node op before) → RepresentsList state.arena after terms →
    after.length = op.arity →
    (∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected) →
    (extension.finish visit limit depth root state op before after).result = .ok selected →
    RefinesFor relation state (.node op terms) (extension.finish visit limit depth root state op before after) selected

def EarlyExtension.SoundFor (relation : Term → Term → Prop) (early : EarlyExtension) : Prop :=
  ∀ {visit limit depth root state op refs terms selected}, early.accepts op = true →
    state.arena[root]? = some (.node op refs) → RepresentsList state.arena refs terms →
    refs.length = op.arity →
    (∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected) →
    (early.finish visit limit depth root state op refs).result = .ok selected →
    RefinesFor relation state (.node op terms) (early.finish visit limit depth root state op refs) selected

def PostExtension.SoundFrom (base : Arena) (relation : Term → Term → Prop) (extension : PostExtension) : Prop :=
  (∀ {op}, extension.accepts op = true → op ≠ .lend ∧ GlobalEnvironment.ordinary op = true) ∧
  ∀ {visit limit depth root state op before after terms selected},
    extension.accepts op = true → Prefix base state.arena →
    state.arena[root]? = some (.node op before) → RepresentsList state.arena after terms →
    after.length = op.arity →
    (∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected) →
    (extension.finish visit limit depth root state op before after).result = .ok selected →
    RefinesFor relation state (.node op terms) (extension.finish visit limit depth root state op before after) selected

def EarlyExtension.SoundFrom (base : Arena) (relation : Term → Term → Prop) (early : EarlyExtension) : Prop :=
  ∀ {visit limit depth root state op refs terms selected}, early.accepts op = true → Prefix base state.arena →
    state.arena[root]? = some (.node op refs) → RepresentsList state.arena refs terms →
    refs.length = op.arity →
    (∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected) →
    (early.finish visit limit depth root state op refs).result = .ok selected →
    RefinesFor relation state (.node op terms) (early.finish visit limit depth root state op refs) selected

abbrev PostExtension.Sound (env : Environment) (extension : PostExtension) :=
  extension.SoundFor (GhostNormalization env)

abbrev EarlyExtension.Sound (env : Environment) (early : EarlyExtension) :=
  early.SoundFor (GhostNormalization env)

private theorem noEarly_sound (env : Environment) : noEarly.Sound env := by
  intro visit limit depth root state op refs terms selected impossible
  cases impossible

private theorem runCore_refines_from (rules : Rules relation)
    (sound : extension.SoundFrom base relation) (earlySound : early.SoundFrom base relation)
    (onBase : Prefix base state.arena)
    (source : Represents state.arena root term)
    (success : (runCore extension early conditionals limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runCore extension early conditionals limit depth state root) selected ∧
      (conditionals = false → GlobalEnvironment.GlobalFree term) := by
  induction depth generalizing state root term selected with
  | zero =>
      by_cases over : limit < state.steps + 1 <;>
        simp [runCore, NativeCoreUnsignedCancellation.tick, over] at success
  | succ depth ih =>
      rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
        ⟨answer, spent⟩
      cases answer with
      | error reason => simp [runCore, ticked] at success
      | ok charged =>
          cases charged
          let entered := {state with steps := spent}
          let visit := runCore extension early conditionals limit depth
          cases source with
          | @var _ index read =>
              simp [runCore, ticked, read] at success
              subst selected
              simp only [runCore, ticked, read, GlobalEnvironment.GlobalFree]
              exact ⟨⟨.refl _, id, _, .var read, rules.same _⟩, fun _ => trivial⟩
          | @node _ op refs terms read arity childrenRep =>
              by_cases earlyEnabled : conditionals = true ∧ early.accepts op = true
              · have computed : runCore extension early conditionals limit (depth + 1) state root =
                    early.finish visit limit depth root entered op refs := by
                  simp only [runCore, ticked, read, ite_eq_left earlyEnabled, entered, visit]
                rw [computed] at success ⊢
                have verified := earlySound (state := entered) (limit := limit) (depth := depth)
                  earlyEnabled.2 onBase read childrenRep arity
                  (fun prior rep solved => (ih prior rep solved).1) success
                exact ⟨⟨verified.kept, verified.backward, verified.value⟩,
                  fun disabled => by simp [earlyEnabled.1] at disabled⟩
              · cases foundKind : conditionalKind conditionals op with
                  | some equal =>
                      obtain ⟨sameOp, enabled⟩ := conditionalKind_op foundKind
                      subst op
                      have count : refs.length = 4 := arity.trans (by cases equal <;> rfl)
                      obtain ⟨l, r, y, n, a, b, p, q, rfl, rfl, left, right, yes, no⟩ :=
                        child_quaternary childrenRep count
                      have branch : runCore extension early conditionals limit (depth + 1) state root =
                          conditional visit limit depth root entered equal l r y n := by
                        simp [runCore, ticked, read, ite_eq_right earlyEnabled, foundKind, visit, entered]
                      rw [branch] at success ⊢
                      obtain ⟨kept, backward, value⟩ := conditional_refines rules (state := entered) onBase
                        read left right yes no (fun prior rep solved => ih prior rep solved) success
                      exact ⟨⟨kept, backward, value⟩, fun disabled => by simp [enabled] at disabled⟩
                  | none =>
                      by_cases allowed : supported op = true
                      · have ordinary : op ≠ .lend := by intro same; subst op; contradiction
                        have globalFreeHead : GlobalEnvironment.ordinary op = true := by
                          cases op <;> first | rfl | contradiction
                        let computed := children visit entered refs
                        have branch : runCore extension early conditionals limit (depth + 1) state root = computed.next
                            (fun childState childRefs => post visit limit depth root childState op refs childRefs) := by
                          simp [runCore, ticked, read, ite_eq_right earlyEnabled, foundKind, allowed, computed, entered, visit]
                        rw [branch] at success ⊢
                        obtain ⟨selectedRefs, found, done⟩ := Outcome.next_success success
                        rw [done] at success ⊢
                        obtain ⟨kept, preserves, sameArity, freeTerms, outputTerms, outputRep, changes⟩ :=
                          children_refines (start := entered) onBase childrenRep (fun prior child childSuccess => ih prior child childSuccess) found
                        obtain ⟨frame, backward, term, represented, reduced⟩ := post_refines rules (onBase.trans kept) (kept.lookup read)
                          outputRep (sameArity.trans arity) (fun prior child succeeded => (ih prior child succeeded).1) success
                        have rebuilt := rules.node ordinary globalFreeHead changes
                        rw [GlobalEnvironment.GlobalFree]
                        exact ⟨⟨kept.trans frame, fun old => backward (preserves old), term, represented,
                          rules.trans rebuilt reduced⟩, fun disabled => ⟨globalFreeHead, fun child member => freeTerms child member disabled⟩⟩
                      · by_cases enabled : conditionals = true ∧ extension.accepts op = true
                        · let computed := children visit entered refs
                          have branch : runCore extension early conditionals limit (depth + 1) state root = computed.next
                              (fun childState childRefs => extension.finish visit limit depth root childState op refs childRefs) := by
                            simp only [runCore, ticked, read, ite_eq_right earlyEnabled, foundKind, ite_eq_right allowed, ite_eq_left enabled,
                              computed, entered, visit]
                          rw [branch] at success ⊢
                          obtain ⟨selectedRefs, found, done⟩ := Outcome.next_success success
                          rw [done] at success ⊢
                          obtain ⟨kept, preserves, sameArity, _, outputTerms, outputRep, changes⟩ :=
                            children_refines (start := entered) onBase childrenRep (fun prior child childSuccess => ih prior child childSuccess) found
                          obtain ⟨frame, backward, term, represented, reduced⟩ := sound.2 enabled.2 (onBase.trans kept) (kept.lookup read)
                            outputRep (sameArity.trans arity) (fun prior child succeeded => (ih prior child succeeded).1) success
                          obtain ⟨ordinary, nonglobal⟩ := sound.1 enabled.2
                          have rebuilt := rules.node ordinary nonglobal changes
                          exact ⟨⟨kept.trans frame, fun old => backward (preserves old), term, represented,
                            rules.trans rebuilt reduced⟩, fun disabled => by simp [enabled.1] at disabled⟩
                        · simp [runCore, ticked, read, ite_eq_right earlyEnabled, foundKind, allowed, enabled] at success

private theorem runCore_refines_with (rules : Rules relation)
    (sound : extension.SoundFor relation) (earlySound : early.SoundFor relation)
    (source : Represents state.arena root term)
    (success : (runCore extension early conditionals limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runCore extension early conditionals limit depth state root) selected ∧
      (conditionals = false → GlobalEnvironment.GlobalFree term) := by
  have post : extension.SoundFrom #[] relation := by
    refine ⟨sound.1, ?_⟩
    intro visit limit depth root state op before after terms selected accepts _ read termsRep arity visitor done
    exact sound.2 accepts read termsRep arity (fun input computed => visitor (emptyPrefix _) input computed) done
  have early : early.SoundFrom #[] relation := by
    intro visit limit depth root state op refs terms selected accepts _ read termsRep arity visitor done
    exact earlySound accepts read termsRep arity (fun input computed => visitor (emptyPrefix _) input computed) done
  exact runCore_refines_from rules post early (emptyPrefix _) source success

private theorem runCore_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term)
    (success : (runCore noExtension noEarly conditionals limit depth state root).result = .ok selected) :
    Refines env state term (runCore noExtension noEarly conditionals limit depth state root) selected ∧
      (conditionals = false → GlobalEnvironment.GlobalFree term) := by
  have absent : noExtension.Sound env := by
    constructor
    · intro op impossible
      cases impossible
    · intro visit limit depth root state op before after terms selected impossible
      cases impossible
  exact runCore_refines_with (ghostRules wellFormed) absent (noEarly_sound _) source success

theorem runWithExtension_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (sound : extension.Sound env) (source : Represents state.arena root term)
    (success : (runWithExtension extension limit depth state root).result = .ok selected) :
    Refines env state term (runWithExtension extension limit depth state root) selected :=
  (runCore_refines_with (ghostRules wellFormed) sound (noEarly_sound _) source success).1

theorem runWithExtensions_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (sound : extension.Sound env) (earlySound : early.Sound env) (source : Represents state.arena root term)
    (success : (runWithExtensions extension early limit depth state root).result = .ok selected) :
    Refines env state term (runWithExtensions extension early limit depth state root) selected :=
  (runCore_refines_with (ghostRules wellFormed) sound earlySound source success).1

theorem runWithExtensions_refinesFor (rules : Rules relation)
    (sound : extension.SoundFor relation) (earlySound : early.SoundFor relation)
    (source : Represents state.arena root term)
    (success : (runWithExtensions extension early limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runWithExtensions extension early limit depth state root) selected :=
  (runCore_refines_with rules sound earlySound source success).1

theorem runWithEarlyExtension_refinesFor (rules : Rules relation) (earlySound : early.SoundFor relation)
    (source : Represents state.arena root term)
    (success : (runWithEarlyExtension early limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runWithEarlyExtension early limit depth state root) selected := by
  apply runWithExtensions_refinesFor rules _ earlySound source success
  constructor
  · intro _ impossible
    cases impossible
  · intro _ _ _ _ _ _ _ _ _ _ impossible
    cases impossible

theorem runWithExtensions_refinesFrom (rules : Rules relation)
    (postSound : extension.SoundFrom base relation) (earlySound : early.SoundFrom base relation)
    (onBase : Prefix base state.arena) (source : Represents state.arena root term)
    (success : (runWithExtensions extension early limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runWithExtensions extension early limit depth state root) selected :=
  (runCore_refines_from rules postSound earlySound onBase source success).1

theorem runWithEarlyExtension_refinesFrom (rules : Rules relation) (earlySound : early.SoundFrom base relation)
    (onBase : Prefix base state.arena) (source : Represents state.arena root term)
    (success : (runWithEarlyExtension early limit depth state root).result = .ok selected) :
    RefinesFor relation state term (runWithEarlyExtension early limit depth state root) selected := by
  have absent : noExtension.SoundFrom base relation := by
    constructor
    · intro _ impossible
      cases impossible
    · intro _ _ _ _ _ _ _ _ _ _ impossible
      cases impossible
  exact runWithExtensions_refinesFrom rules absent earlySound onBase source success

/-- Both structural and computational branches build an actual typed
forward derivation, including when beta or Transport occurs under a binder. -/
theorem run_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term) (success : (run limit depth state root).result = .ok selected) :
    Refines env state term (run limit depth state root) selected ∧ GlobalEnvironment.GlobalFree term := by
  obtain ⟨refines, free⟩ := runCore_refines wellFormed source success
  exact ⟨refines, free rfl⟩

/-- Normalizing each child constructs a joint typed transformation and keeps
the operand count and order used by the graph's following operation. -/
theorem normalizeOperands_refines (wf : UnifiedProgram.EnvWellFormed env)
    (represented : RepresentsList state.arena refs terms)
    (success : (normalizeOperands limit depth state refs).result = .ok selected) :
    let output := normalizeOperands limit depth state refs
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧
      ∃ residuals, RepresentsList output.state.arena selected residuals ∧ ListRel (GhostNormalization env) terms residuals := by
  obtain ⟨kept, backward, count, _, residuals, rep, changes⟩ :=
    children_refines (start := state) (emptyPrefix _) represented
      (fun _ source solved => runCore_refines (conditionals := true) wf source solved) success
  exact ⟨kept, backward, count, residuals, rep, changes⟩

/-- Recursive pure graph normalization preserves the exact original typing
through branches reached under structural parents or after substitution. -/
theorem runWithConditionals_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term) (typed : Environment.LoanTyping.HasType env loans ctx mode term type)
    (success : (runWithConditionals limit depth state root).result = .ok selected) :
    let output := runWithConditionals limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ Environment.RawLend.Forward env term residual ∧
        Environment.LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨⟨kept, backward, residual, rep, change⟩, _⟩ := runCore_refines wf source success
  exact ⟨kept, backward, residual, rep, change.raw.forward, change.raw.typed typed⟩

theorem run_preserves (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term)
    (typed : Environment.LoanTyping.HasType env loans ctx mode term type)
    (success : (run limit depth state root).result = .ok selected) :
    ∃ residual, Represents (run limit depth state root).state.arena selected residual ∧
      Environment.RawLend.Forward env term residual ∧
      Environment.LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨result, represented, change⟩ := (run_refines wellFormed source success).1.value
  exact ⟨result, represented, change.raw.forward, change.raw.typed typed⟩

theorem run_admitted_definition_preserves {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (success : (run limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot).result = .ok selected) :
    let output := run limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot
    ∃ definitions families env entry residual,
      Environment.LoanTyping.MixedProgram.History definitions families env ∧ env.globals[index]? = some entry ∧
      Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
      Represents output.state.arena selected residual ∧ Environment.LoanTyping.HasType env [] [] true residual entry.type := by
  obtain ⟨decoded, _, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  obtain ⟨⟨kept, preserves, residual, selectedRep, change⟩, free⟩ :=
    run_refines (state := ⟨snapshot.arena, initial⟩) history.wellFormed represented.2 success
  rw [EnvironmentDelta.expand_globalFree free] at typed
  exact ⟨_, _, env, entry, residual, history, found, kept, preserves backward, selectedRep, change.raw.typed typed⟩

/-- A global-free definition from the exact mixed snapshot retains its
stored type through the recursive graph walk with conditional selection. -/
theorem runWithConditionals_admitted_definition_preserves {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (source : Represents snapshot.arena definition.valueRoot term) (free : GlobalEnvironment.GlobalFree term)
    (success : (runWithConditionals limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot).result = .ok selected) :
    let output := runWithConditionals limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot
    ∃ definitions families env entry residual,
      Environment.LoanTyping.MixedProgram.History definitions families env ∧ env.globals[index]? = some entry ∧
      Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
      Represents output.state.arena selected residual ∧ Environment.LoanTyping.HasType env [] [] true residual entry.type := by
  obtain ⟨decoded, _, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have exactSnapshot := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  rw [represented.2.unique source, EnvironmentDelta.expand_globalFree free] at typed
  obtain ⟨kept, preserves, residual, selectedRep, _, retained⟩ :=
    runWithConditionals_preserves history.wellFormed source typed success
  exact ⟨_, _, env, entry, residual, history, found, kept, preserves backward, selectedRep, retained⟩

/-- A successful graph walk preserves the admitted type after transparent
interpretation, even when an unvisited arm still mentions globals. -/
theorem runWithConditionals_admitted_expanded_preserves {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (success : (runWithConditionals limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot).result = .ok selected) :
    let output := runWithConditionals limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot
    ∃ definitions families env entry residual,
      Environment.LoanTyping.MixedProgram.History definitions families env ∧ env.globals[index]? = some entry ∧
      Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
      Represents output.state.arena selected residual ∧
      Environment.LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨decoded, _, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have exactSnapshot := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  obtain ⟨⟨kept, preserves, residual, selectedRep, change⟩, _⟩ :=
    runCore_refines history.wellFormed represented.2 success
  exact ⟨_, _, env, entry, residual, history, found, kept, preserves backward, selectedRep, change.expanded.typed typed⟩

private theorem expanded_result (wf : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term)
    (success : (runWithConditionals limit depth state root).result = .ok selected) :
    let output := runWithConditionals limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ GhostTransform env (expand env term) (expand env residual) := by
  obtain ⟨⟨kept, backward, residual, represented, change⟩, _⟩ := runCore_refines wf source success
  exact ⟨kept, backward, residual, represented, change.expanded⟩

/-- The raw global alias walk uses actual declaration rows. Their interpreted
bodies coincide with the stored checked values before recursive normalization. -/
theorem runThroughAliases_refines (aligned : RepresentsDefinitions state.arena roots definitions)
    (history : Environment.LoanTyping.MixedProgram.History definitions families env)
    (source : Represents state.arena root term)
    (success : (runThroughAliases roots visible limit depth state root).result = .ok selected) :
    let output := runThroughAliases roots visible limit depth state root
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ GhostTransform env (expand env term) (expand env residual) := by
  induction depth generalizing state root term selected with
  | zero => exact expanded_result history.wellFormed source success
  | succ depth ih =>
      cases alias : aliasAt state.arena root with
      | none =>
          simp only [runThroughAliases, alias] at success ⊢
          exact expanded_result history.wellFormed source success
      | some index =>
          rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
            ⟨status, spent⟩
          cases status with
          | error reason => simp [runThroughAliases, alias, ticked] at success
          | ok charged =>
              cases charged
              by_cases permitted : index < visible
              · cases lookup : roots[index]? with
                | none => simp [runThroughAliases, alias, ticked, permitted, lookup] at success
                | some declaration =>
                    obtain ⟨node, read, kind⟩ := aliasAt_lookup alias
                    obtain ⟨body, represented, same⟩ := NativeCoreGlobalNormal.alias_target aligned history source read kind lookup
                    simp only [runThroughAliases, alias, ticked, permitted, ite_true] at success ⊢
                    rw [lookup] at success ⊢
                    rw [same]
                    exact ih (state := {state with steps := spent}) aligned represented success
              · simp [runThroughAliases, alias, ticked, permitted] at success

/-- A checked alias into composite computation retains the type of the
original declaration at its exact byte snapshot. -/
theorem runThroughAliases_admitted_definition_preserves {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (success : (runThroughAliases snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩
      definition.valueRoot).result = .ok selected) :
    let output := runThroughAliases snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot
    ∃ definitions families env entry residual,
      Environment.LoanTyping.MixedProgram.History definitions families env ∧ env.globals[index]? = some entry ∧
      Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
      Represents output.state.arena selected residual ∧ Environment.LoanTyping.HasType env [] [] true
        (expand env residual) entry.type := by
  obtain ⟨decoded, _, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have exactSnapshot := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  obtain ⟨kept, preserves, residual, selectedRep, change⟩ :=
    runThroughAliases_refines (state := ⟨snapshot.arena, initial⟩) aligned history represented.2 success
  exact ⟨_, _, env, entry, residual, history, found, kept, preserves backward, selectedRep, change.typed typed⟩

theorem conditional_false_skips_true_arm :
    let arena : Arena := #[.node (.natural 3) [], .node (.natural 2) [], .node (.global 0) [],
      .node (.integer 7) [], .node .ifLt [0, 1, 2, 3]]
    runWithConditionals 4 3 ⟨arena, 0⟩ 4 = ⟨⟨arena, 4⟩, .ok 3⟩ := rfl

private def skippedGlobalSnapshot : NativeFamilyWire.Snapshot where
  arena := #[.node .i64 [], .node (.integer 7) [], .node (.natural 3) [], .node (.natural 2) [],
    .node (.global 0) [], .node (.integer 9) [], .node .ifLt [2, 3, 4, 5]]
  definitions := [⟨0, 1⟩, ⟨0, 6⟩]
  families := []

/-- The exact mixed checker stores the interpreted branch. The graph walk
keeps the same type without visiting a global in the unselected arm. -/
theorem admitted_conditional_skips_global :
    runWithConditionals 4 3 ⟨skippedGlobalSnapshot.arena, 0⟩ 6 = ⟨⟨skippedGlobalSnapshot.arena, 4⟩, .ok 5⟩ ∧
    ∃ env entry, env.globals[1]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true (.integer 9) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot skippedGlobalSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : runWithConditionals 4 3 ⟨skippedGlobalSnapshot.arena, 0⟩ 6 =
      ⟨⟨skippedGlobalSnapshot.arena, 4⟩, .ok 5⟩ := rfl
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    runWithConditionals_admitted_expanded_preserves (index := 1) (definition := ⟨0, 6⟩)
      (initial := 0) admitted rfl (congrArg Outcome.result computed)
  rw [computed] at selected
  have expected : Represents skippedGlobalSnapshot.arena 5 (.integer 9) := decode_sound (fuel := 2) rfl
  rw [selected.unique expected] at typed
  exact ⟨computed, env, entry, found, by simpa only [Term.integer, expand, expandArgs] using typed⟩

theorem conditional_true_appends_evidence_before_reentry :
    let arena : Arena := #[.node (.natural 0) [], .node (.natural 1) [], .var 0,
      .node (.global 0) [], .node .ifLt [0, 1, 2, 3]]
    runWithConditionals 10 4 ⟨arena, 0⟩ 4 = ⟨⟨arena.push (.node .decide [0, 1]), 10⟩, .ok 5⟩ ∧
      runWithConditionals 3 4 ⟨arena, 0⟩ 4 =
        ⟨⟨arena.push (.node .decide [0, 1]), 4⟩, .error (.substitution (.tick (.stepLimit 2)))⟩ :=
  ⟨rfl, rfl⟩

private def equalityBranchSnapshot : NativeFamilyWire.Snapshot where
  arena := #[.node (.natural 4) [], .var 0, .node .refl [0], .node .ifEq [0, 0, 1, 2], .node .eq [0, 0]]
  definitions := [⟨4, 3⟩]
  families := []

/-- A byte-admitted branch returns its evidence variable. The actual walk
inserts reflexivity and retains the declaration's original checked equality. -/
theorem admitted_equality_branch_returns_reflexivity :
    let output := runWithConditionals 8 4 ⟨equalityBranchSnapshot.arena, 0⟩ 3
    output = ⟨⟨equalityBranchSnapshot.arena.push (.node .refl [0]), 8⟩, .ok 5⟩ ∧
    ∃ env entry, env.globals[0]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true (.refl (.natural 4)) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot equalityBranchSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : runWithConditionals 8 4 ⟨equalityBranchSnapshot.arena, 0⟩ 3 =
      ⟨⟨equalityBranchSnapshot.arena.push (.node .refl [0]), 8⟩, .ok 5⟩ := rfl
  have source : Represents equalityBranchSnapshot.arena 3
      (.ifEq (.natural 4) (.natural 4) (.var 0) (.refl (.natural 4))) := decode_sound (fuel := 4) rfl
  have free : GlobalEnvironment.GlobalFree (.ifEq (.natural 4) (.natural 4) (.var 0) (.refl (.natural 4))) := by
    simp [Term.ifEq, Term.refl, Term.natural, GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary]
  have succeeded := congrArg Outcome.result computed
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    runWithConditionals_admitted_definition_preserves (index := 0) (definition := ⟨4, 3⟩)
      (initial := 0) admitted rfl source free succeeded
  rw [computed] at selected
  have expected : Represents (equalityBranchSnapshot.arena.push (.node .refl [0])) 5 (.refl (.natural 4)) :=
    decode_sound (fuel := 3) rfl
  rw [selected.unique expected] at typed
  exact ⟨computed, env, entry, found, typed⟩

private def betaBranchSnapshot : NativeFamilyWire.Snapshot where
  arena := #[.node .u64 [], .node (.natural 4) [], .var 0, .node (.integer 9) [], .node (.integer 6) [],
    .node .ifEq [2, 1, 3, 4], .node (.lam false) [0, 5], .node .app [6, 1], .node .i64 []]
  definitions := [⟨8, 7⟩]
  families := []

private def betaBranchResult : Arena :=
  (betaBranchSnapshot.arena.push (.node .ifEq [1, 1, 3, 4])).push (.node .refl [1])

/-- A symbolic comparison under the lambda is first rebuilt without
selecting an arm. Beta then supplies its operand and the same driver selects
the numeric result at the original admitted type. -/
theorem admitted_beta_exposes_comparison :
    runWithConditionals 20 6 ⟨betaBranchSnapshot.arena, 0⟩ 7 = ⟨⟨betaBranchResult, 20⟩, .ok 3⟩ ∧
    ∃ env entry, env.globals[0]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true (.integer 9) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot betaBranchSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : runWithConditionals 20 6 ⟨betaBranchSnapshot.arena, 0⟩ 7 =
      ⟨⟨betaBranchResult, 20⟩, .ok 3⟩ := rfl
  let term := Term.app (.lam false .u64 (.ifEq (.var 0) (.natural 4) (.integer 9) (.integer 6))) (.natural 4)
  have source : Represents betaBranchSnapshot.arena 7 term := decode_sound (fuel := 6) rfl
  have free : GlobalEnvironment.GlobalFree term := by
    simp [term, Term.app, Term.lam, Term.u64, Term.ifEq, Term.natural, Term.integer,
      GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary]
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    runWithConditionals_admitted_definition_preserves (index := 0) (definition := ⟨8, 7⟩)
      (initial := 0) admitted rfl source free (congrArg Outcome.result computed)
  rw [computed] at selected
  have expected : Represents betaBranchResult 3 (.integer 9) := decode_sound (fuel := 2) rfl
  rw [selected.unique expected] at typed
  exact ⟨computed, env, entry, found, typed⟩

private def betaAliasSnapshot : NativeFamilyWire.Snapshot :=
  { betaBranchSnapshot with
    arena := betaBranchSnapshot.arena.push (.node (.global 0) [])
    definitions := betaBranchSnapshot.definitions ++ [⟨8, 9⟩] }

private def betaAliasResult : Arena :=
  (betaAliasSnapshot.arena.push (.node .ifEq [1, 1, 3, 4])).push (.node .refl [1])

/-- A visible alias can enter beta and conditional normalization with its
original clock and type. The same reference is rejected before visibility. -/
theorem admitted_alias_enters_beta_branch :
    runThroughAliases betaAliasSnapshot.definitions 1 21 7 ⟨betaAliasSnapshot.arena, 0⟩ 9 =
      ⟨⟨betaAliasResult, 21⟩, .ok 3⟩ ∧
    runThroughAliases betaAliasSnapshot.definitions 0 21 7 ⟨betaAliasSnapshot.arena, 0⟩ 9 =
      ⟨⟨betaAliasSnapshot.arena, 1⟩, .error (.invisibleGlobal 9)⟩ ∧
    ∃ env entry, env.globals[1]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true (.integer 9) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot betaAliasSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : runThroughAliases betaAliasSnapshot.definitions 1 21 7 ⟨betaAliasSnapshot.arena, 0⟩ 9 =
      ⟨⟨betaAliasResult, 21⟩, .ok 3⟩ := rfl
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    runThroughAliases_admitted_definition_preserves (index := 1) (definition := ⟨8, 9⟩)
      (initial := 0) admitted rfl (congrArg Outcome.result computed)
  rw [computed] at selected
  have expected : Represents betaAliasResult 3 (.integer 9) := decode_sound (fuel := 2) rfl
  rw [selected.unique expected] at typed
  exact ⟨computed, rfl, env, entry, found, by simpa only [Term.integer, expand, expandArgs] using typed⟩

private def betaPackSnapshot : NativeFamilyWire.Snapshot where
  arena := #[.node .u64 [], .node (.natural 1) [], .node (.natural 2) [], .var 0, .node .lt [3, 2],
    .node (.lam false) [0, 4], .node .decide [1, 2], .node .pack [5, 1, 6],
    .node (.lam false) [0, 7], .node .app [8, 1], .node .witness [9], .node .proof [9], .node .lt [1, 2]]
  definitions := [⟨12, 11⟩]
  families := []

/-- Both projections visit an application that produces a Pack and take the
existing field reference. The checked proof declaration retains its type. -/
theorem admitted_beta_pack_projection :
    runWithConditionals 35 10 ⟨betaPackSnapshot.arena, 0⟩ 10 = ⟨⟨betaPackSnapshot.arena, 35⟩, .ok 1⟩ ∧
    runWithConditionals 35 10 ⟨betaPackSnapshot.arena, 0⟩ 11 = ⟨⟨betaPackSnapshot.arena, 35⟩, .ok 6⟩ ∧
    ∃ env entry, env.globals[0]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true (.decide (.natural 1) (.natural 2)) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot betaPackSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : runWithConditionals 35 10 ⟨betaPackSnapshot.arena, 0⟩ 11 =
      ⟨⟨betaPackSnapshot.arena, 35⟩, .ok 6⟩ := rfl
  let proof := Term.decide (.natural 1) (.natural 2)
  let packed := Term.pack (.lam false .u64 (.lt (.var 0) (.natural 2))) (.natural 1) proof
  let term := Term.proof (.app (.lam false .u64 packed) (.natural 1))
  have source : Represents betaPackSnapshot.arena 11 term := decode_sound (fuel := 9) rfl
  have free : GlobalEnvironment.GlobalFree term := by
    simp [term, packed, proof, Term.proof, Term.app, Term.lam, Term.u64, Term.pack, Term.lt, Term.natural,
      Term.decide, GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary]
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    runWithConditionals_admitted_definition_preserves (index := 0) (definition := ⟨12, 11⟩)
      (initial := 0) admitted rfl source free (congrArg Outcome.result computed)
  rw [computed] at selected
  have expected : Represents betaPackSnapshot.arena 6 proof := decode_sound (fuel := 3) rfl
  rw [selected.unique expected] at typed
  exact ⟨rfl, computed, env, entry, found, typed⟩

private def nestedTransportSnapshot : NativeFamilyWire.Snapshot where
  arena := #[
    .node .u64 [], .node (.natural 0) [], .node (.natural 1) [], .var 0,
    .node .lt [3, 2], .node (.lam false) [0, 4], .node .refl [3], .node (.lam false) [0, 6],
    .node .app [7, 1], .node .lt [1, 2], .node .decide [1, 2], .node .transport [5, 8, 10],
    .node (.lam true) [0, 11], .node (.pi true) [0, 9]]
  definitions := [⟨13, 12⟩]
  families := []

private def nestedTransportResult : Arena :=
  (nestedTransportSnapshot.arena.push (.node .refl [1])).push (.node (.lam true) [0, 10])

/-- Under an erased binder, a beta-reduced equality proof exposes reflexivity
and the enclosing Transport returns the existing inequality evidence. The
changed lambda retains its stored declaration type. -/
theorem admitted_nested_transport_example :
    run 22 8 ⟨nestedTransportSnapshot.arena, 0⟩ 12 = ⟨⟨nestedTransportResult, 22⟩, .ok 15⟩ ∧
    ∃ env entry, env.globals[0]? = some entry ∧
      Environment.LoanTyping.HasType env [] [] true
        (.lam true .u64 (.decide (.natural 0) (.natural 1))) entry.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 64
      (NativeFamilyWire.encodeSnapshot nestedTransportSnapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : run 22 8 ⟨nestedTransportSnapshot.arena, 0⟩ 12 =
      ⟨⟨nestedTransportResult, 22⟩, .ok 15⟩ := rfl
  have succeeded : (run 22 8 ⟨nestedTransportSnapshot.arena, 0⟩ 12).result = .ok 15 :=
    congrArg Outcome.result computed
  obtain ⟨_, _, env, entry, residual, _, found, _, _, selected, typed⟩ :=
    run_admitted_definition_preserves (index := 0) (definition := ⟨13, 12⟩)
      (initial := 0) admitted rfl succeeded
  rw [computed] at selected
  have expected : Represents nestedTransportResult 15
      (.lam true .u64 (.decide (.natural 0) (.natural 1))) :=
    decode_sound (fuel := 5) rfl
  rw [selected.unique expected] at typed
  exact ⟨computed, env, entry, found, typed⟩

theorem neutral_transport_retains_row :
    let arena : Arena := #[
      .node .u64 [], .node (.natural 0) [], .node (.natural 1) [], .var 0, .node .lt [3, 2],
      .node (.lam false) [0, 4], .node .decide [1, 2], .node .transport [5, 3, 6]]
    run 10 4 ⟨arena, 0⟩ 7 = ⟨⟨arena, 10⟩, .ok 7⟩ :=
  rfl


abbrev ResolvesGlobals (_ : Term) (output : Term) : Prop :=
  GlobalEnvironment.GlobalFree output

private theorem free_children (resolved : ListRel ResolvesGlobals original outputs) :
    ∀ term ∈ outputs, GlobalEnvironment.GlobalFree term := by
  induction resolved with
  | nil => simp
  | cons first _ ih =>
    intro term found
    rcases List.mem_cons.mp found with rfl | found
    · exact first
    · exact ih term found

private theorem conditionalPost_resolves
    (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (conditionalOp equal) before))
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (leftFree : GlobalEnvironment.GlobalFree a) (rightFree : GlobalEnvironment.GlobalFree b)
    (yesRep : Represents state.arena yes p) (noRep : Represents state.arena no q)
    (visitResolves : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor ResolvesGlobals state term (visit state ref) selected)
    (success : (conditionalPost visit limit depth root state equal before left right yes no).result = .ok selected) :
    RefinesFor ResolvesGlobals state (.node (conditionalOp equal) [a,b,p,q])
      (conditionalPost visit limit depth root state equal before left right yes no) selected := by
  have keepArms (branch : conditionalPost visit limit depth root state equal before left right yes no =
      (children visit state [yes,no]).next fun next arms =>
        nodeResult next root (conditionalOp equal) before (left :: right :: arms)) :
      RefinesFor ResolvesGlobals state (.node (conditionalOp equal) [a,b,p,q])
        (conditionalPost visit limit depth root state equal before left right yes no) selected := by
    rw [branch] at success ⊢
    obtain ⟨arms,accepted,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨kept,safe,width,_,terms,represented,free⟩ :=
      children_refines (property := fun _ => True) onBase (.cons yesRep (.cons noRep .nil))
        (fun prior child done => ⟨visitResolves prior child done,True.intro⟩) accepted
    have arity : (left :: right :: arms).length = (conditionalOp equal).arity := by
      cases equal <;> simp [conditionalOp,width,Op.arity]
    obtain ⟨suffix,later,output⟩ := nodeResult_exact (kept.lookup read)
      (.cons (leftRep.frame kept) (.cons (rightRep.frame kept) represented)) arity success
    have residualFree : GlobalEnvironment.GlobalFree (.node (conditionalOp equal) (a :: b :: terms)) := by
      rw [GlobalEnvironment.GlobalFree]
      refine ⟨by cases equal <;> rfl,?_⟩
      intro term found
      rcases List.mem_cons.mp found with rfl | found
      · exact leftFree
      · rcases List.mem_cons.mp found with rfl | found
        · exact rightFree
        · exact free_children free term found
    exact ⟨kept.trans suffix,later ∘ safe,_,output,residualFree⟩
  cases leftNumber : numberAt state.arena left <;> cases rightNumber : numberAt state.arena right
  case none.none => exact keepArms (by simp [conditionalPost,leftNumber,rightNumber])
  case none.some => exact keepArms (by simp [conditionalPost,leftNumber,rightNumber])
  case some.none => exact keepArms (by simp [conditionalPost,leftNumber,rightNumber])
  rename_i aValue bValue
  by_cases chosen : compareNumbers equal aValue bValue = true
  · simp only [conditionalPost,leftNumber,rightNumber,ite_eq_left chosen] at success ⊢
    cases equal
    · have built := openTrue_refines onBase yesRep (.cons leftRep (.cons rightRep .nil)) rfl visitResolves success
      exact ⟨built.kept,built.backward,built.value⟩
    · have built := openTrue_refines onBase yesRep (.cons leftRep .nil) rfl visitResolves success
      exact ⟨built.kept,built.backward,built.value⟩
  · simp only [conditionalPost,leftNumber,rightNumber,ite_eq_right chosen] at success ⊢
    have built := visitResolves onBase noRep success
    exact ⟨built.kept,built.backward,built.value⟩

private theorem conditional_resolves
    (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (conditionalOp equal) [left,right,yes,no]))
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (yesRep : Represents state.arena yes p) (noRep : Represents state.arena no q)
    (visitResolves : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor ResolvesGlobals state term (visit state ref) selected)
    (success : (conditional visit limit depth root state equal left right yes no).result = .ok selected) :
    RefinesFor ResolvesGlobals state (.node (conditionalOp equal) [a,b,p,q])
      (conditional visit limit depth root state equal left right yes no) selected := by
  unfold conditional at success ⊢
  obtain ⟨operands,accepted,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,safe,width,_,terms,represented,free⟩ :=
    children_refines (property := fun _ => True) onBase (.cons leftRep (.cons rightRep .nil))
      (fun prior child done => ⟨visitResolves prior child done,True.intro⟩) accepted
  obtain ⟨newLeft,newRight,normalizedLeft,normalizedRight,rfl,rfl,newLeftRep,newRightRep⟩ :=
    child_binary represented width
  obtain ⟨suffix,later,value,held,resolved⟩ :=
    conditionalPost_resolves (onBase.trans kept) (kept.lookup read) newLeftRep newRightRep
      (free_children free _ (.head _)) (free_children free _ (.tail _ (.head _)))
      (yesRep.frame kept) (noRep.frame kept) visitResolves success
  exact ⟨kept.trans suffix,later ∘ safe,value,held,resolved⟩

private theorem runCore_resolves
    (postRules : Rules (fun a b => GlobalEnvironment.GlobalFree a → GlobalEnvironment.GlobalFree b))
    (canResolve : extension.SoundFrom base ResolvesGlobals) (earlyResolves : early.SoundFrom base ResolvesGlobals)
    (onBase : Prefix base state.arena) (source : Represents state.arena root term)
    (success : (runCore extension early conditionals limit depth state root).result = .ok selected) :
    RefinesFor ResolvesGlobals state term (runCore extension early conditionals limit depth state root) selected := by
  induction depth generalizing state root term selected with
  | zero =>
    by_cases over : limit < state.steps + 1 <;>
      simp [runCore,NativeCoreUnsignedCancellation.tick,over] at success
  | succ depth ih =>
    rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth+1) state.steps root with ⟨answer,spent⟩
    cases answer with
    | error reason => simp [runCore,ticked] at success
    | ok paid =>
      cases paid
      let entered := {state with steps := spent}
      let visit := runCore extension early conditionals limit depth
      cases source with
      | var read =>
        simp [runCore,ticked,read] at success
        subst selected
        simp only [runCore,ticked,read]
        exact ⟨.refl _,id,_,.var read,by simp only [ResolvesGlobals,GlobalEnvironment.GlobalFree]⟩
      | @node _ op refs terms read arity childrenRep =>
        by_cases earlyEnabled : conditionals = true ∧ early.accepts op = true
        · have route : runCore extension early conditionals limit (depth+1) state root =
              early.finish visit limit depth root entered op refs := by
            simp only [runCore,ticked,read,ite_eq_left earlyEnabled,entered,visit]
          rw [route] at success ⊢
          have result := earlyResolves (state := entered) earlyEnabled.2 onBase read childrenRep arity
            (fun prior rep done => ih prior rep done) success
          exact ⟨result.kept,result.backward,result.value⟩
        · cases foundKind : conditionalKind conditionals op with
          | some equal =>
            obtain ⟨sameOp,_⟩ := conditionalKind_op foundKind
            subst op
            have count : refs.length = 4 := arity.trans (by cases equal <;> rfl)
            obtain ⟨l,r,y,n,a,b,p,q,rfl,rfl,left,right,yes,no⟩ := child_quaternary childrenRep count
            have route : runCore extension early conditionals limit (depth+1) state root =
                conditional visit limit depth root entered equal l r y n := by
              simp [runCore,ticked,read,ite_eq_right earlyEnabled,foundKind,entered,visit]
            rw [route] at success ⊢
            have result := conditional_resolves (state := entered) onBase read left right yes no
              (fun prior child done => ih prior child done) success
            exact ⟨result.kept,result.backward,result.value⟩
          | none =>
            let normalized := children visit entered refs
            by_cases allowed : supported op = true
            · have ordinary : GlobalEnvironment.ordinary op = true := by
                cases op <;> first | rfl | contradiction
              have route : runCore extension early conditionals limit (depth+1) state root = normalized.next
                  (fun after output => post visit limit depth root after op refs output) := by
                simp [runCore,ticked,read,ite_eq_right earlyEnabled,foundKind,allowed,normalized,entered,visit]
              rw [route] at success ⊢
              obtain ⟨selectedChildren,childSuccess,childNext⟩ := Outcome.next_success success
              rw [childNext] at success ⊢
              obtain ⟨kept,safe,width,outputTerms,held,free⟩ :=
                visitOperands_relatesFrom (start := entered) (relation := ResolvesGlobals) onBase childrenRep
                  (fun prior child done => by
                    obtain ⟨kept,safe,output⟩ := ih prior child done
                    exact ⟨kept,safe,output⟩) childSuccess
              obtain ⟨suffix,later,output,represented,resolves⟩ := post_refines postRules (onBase.trans kept) (kept.lookup read)
                held (width.trans arity)
                (fun prior placed done => by
                  obtain ⟨kept,safe,output,represented,free⟩ := ih prior placed done
                  exact ⟨kept,safe,output,represented,fun _ => free⟩) success
              have resolvedHead : GlobalEnvironment.GlobalFree (.node op outputTerms) := by
                rw [GlobalEnvironment.GlobalFree]
                exact ⟨ordinary,free_children free⟩
              exact ⟨kept.trans suffix,later ∘ safe,output,represented,resolves resolvedHead⟩
            · by_cases enabled : conditionals = true ∧ extension.accepts op = true
              · have route : runCore extension early conditionals limit (depth+1) state root = normalized.next
                    (fun after output => extension.finish visit limit depth root after op refs output) := by
                  simp only [runCore,ticked,read,ite_eq_right earlyEnabled,foundKind,ite_eq_right allowed,ite_eq_left enabled,
                    normalized,entered,visit]
                rw [route] at success ⊢
                obtain ⟨selectedChildren,childSuccess,childNext⟩ := Outcome.next_success success
                rw [childNext] at success ⊢
                obtain ⟨kept,safe,width,outputTerms,held,free⟩ :=
                  visitOperands_relatesFrom (start := entered) (relation := ResolvesGlobals) onBase childrenRep
                  (fun prior child done => by
                    obtain ⟨kept,safe,output⟩ := ih prior child done
                    exact ⟨kept,safe,output⟩) childSuccess
                obtain ⟨suffix,later,output,represented,resolved⟩ :=
                  canResolve.2 enabled.2 (onBase.trans kept) (kept.lookup read) held (width.trans arity)
                    (fun prior input done => ih prior input done) success
                exact ⟨kept.trans suffix,later ∘ safe,output,represented,resolved⟩
              · simp [runCore,ticked,read,ite_eq_right earlyEnabled,foundKind,allowed,enabled] at success

theorem runWithExtensions_resolves
    (postRules : Rules (fun a b => GlobalEnvironment.GlobalFree a → GlobalEnvironment.GlobalFree b))
    (postSound : extension.SoundFrom base ResolvesGlobals)
    (earlySound : early.SoundFrom base ResolvesGlobals)
    (onBase : Prefix base state.arena) (held : Represents state.arena root term)
    (success : (runWithExtensions extension early limit depth state root).result = .ok selected) :
    RefinesFor ResolvesGlobals state term (runWithExtensions extension early limit depth state root) selected :=
  runCore_resolves postRules postSound earlySound onBase held success

end Jihoo.NativeKernel.NativeCorePureComputationNormal
