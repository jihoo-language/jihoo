import Jihoo.NativeCoreTransformExact
import Jihoo.NativeCorePureStructuralNormal
import Jihoo.NativeLoanComputationPreservation

/-! The pure Core.normal path for structural constructors, applications
and Transport. Children run in source order and reenter the same driver
after native substitution. A neutral Transport keeps its original row
when all three references are unchanged. -/
namespace Jihoo.NativeKernel.NativeCorePureComputationNormal

open NativeArena NativeProgramWire
open NativeCoreTransformExact (State)
open NativeCorePureStructuralNormal (structural)
open NativeCoreGlobalNormal (atomicOp)
open Environment.LoanTyping (GhostTransform compute_ghost_transform children_preservation raw_forward_lambda_shape)
open NativeKernel.Conversion (ListRel)

inductive Error where
  | tick (reason : NativeCoreIdentical.Error)
  | substitution (reason : NativeCoreTransformExact.Error)
  | add (reason : NativeCoreGraph.Error)
  | outsideFragment (root : Nat)
  deriving Repr, DecidableEq

structure Outcome (α : Type) where
  state : State
  result : Except Error α
  deriving Repr

private def Outcome.next (run : Outcome α) (next : State → α → Outcome β) : Outcome β :=
  match run.result with
  | .error reason => ⟨run.state, .error reason⟩
  | .ok ref => next run.state ref

private theorem Outcome.next_success {previous : Outcome α} {next : State → α → Outcome β}
    (success : (previous.next next).result = .ok selected) :
    ∃ ref, previous.result = .ok ref ∧ previous.next next = next previous.state ref := by
  cases found : previous.result with
  | error reason => simp [Outcome.next, found] at success
  | ok ref => exact ⟨ref, rfl, by simp [Outcome.next, found]⟩

private def nodeResult (state : State) (root : Nat) (op : Op) (before after : List Nat) : Outcome Nat :=
  if before = after then ⟨state, .ok root⟩ else
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
  atomicOp op || structural op || op == .app || op == .transport

private def children (visit : State → Nat → Outcome Nat) : State → List Nat → Outcome (List Nat)
  | state, [] => ⟨state, .ok []⟩
  | state, ref :: rest =>
      (visit state ref).next fun afterHead head =>
        (children visit afterHead rest).next fun afterTail tail => ⟨afterTail, .ok (head :: tail)⟩

private def post (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (op : Op) (before after : List Nat) : Outcome Nat :=
  if op = .app then
    match after with
    | [callee, operand] =>
        match state.arena[callee]?.bind lambdaBody with
        | some body => (opening limit depth state body operand).next visit
        | none =>
            if neutralCallee state.arena callee then nodeResult state root op before after
            else ⟨state, .error (.outsideFragment callee)⟩
    | _ => ⟨state, .error (.outsideFragment root)⟩
  else if op = .transport then
    match after with
    | [_, evidence, payload] =>
        if (state.arena[evidence]?.map reflHead).getD false then ⟨state, .ok payload⟩
        else nodeResult state root op before after
    | _ => ⟨state, .error (.outsideFragment root)⟩
  else nodeResult state root op before after

def run (limit : Nat) : Nat → State → Nat → Outcome Nat
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
              if supported op then
                (children (run limit depth) entered refs).next fun after args =>
                  post (run limit depth) limit depth root after op refs args
              else ⟨entered, .error (.outsideFragment root)⟩

structure Refines (env : Environment) (start : State) (term : Term) (output : Outcome Nat) (selected : Nat) : Prop where
  kept : Prefix start.arena output.state.arena
  backward : Backward start.arena → Backward output.state.arena
  value : ∃ value, Represents output.state.arena selected value ∧ GhostTransform env term value

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

private theorem nodeResult_refines (read : state.arena[root]? = some (.node op before))
    (replaced : RepresentsList state.arena refs terms) (arity : refs.length = op.arity)
    (success : (nodeResult state root op before refs).result = .ok selected) :
    Refines env state (.node op terms) (nodeResult state root op before refs) selected := by
  by_cases same : before = refs
  · simp [nodeResult, same] at success
    subst selected
    simp only [nodeResult, same, ite_true]
    exact ⟨.refl _, id, _, .node (same ▸ read) arity replaced, .refl _⟩
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
        exact ⟨kept, backward, _, .node lookup arity (replaced.frame kept), .refl _⟩

private theorem opening_success (found : (opening limit depth state body operand).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state body operand).result = .ok selected := by
  generalize original : NativeCoreTransformExact.substitute limit depth state body operand = raw at ⊢
  cases status : raw.result <;> simp [opening, original, status, Except.mapError] at found ⊢
  assumption

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

private theorem post_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (read : state.arena[root]? = some (.node op before)) (rep : RepresentsList state.arena after terms)
    (arity : after.length = op.arity)
    (visitRefines : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (success : (post visit limit depth root state op before after).result = .ok selected) :
    Refines env state (.node op terms) (post visit limit depth root state op before after) selected := by
  by_cases app : op = .app
  · subst op
    obtain ⟨callee, operand, function, argument, rfl, rfl, calleeRep, operandRep⟩ := child_binary rep arity
    cases picked : state.arena[callee]?.bind lambdaBody with
    | none =>
        by_cases neutral : neutralCallee state.arena callee = true
        · have residual : post visit limit depth root state .app before [callee, operand] =
              nodeResult state root .app before [callee, operand] := by simp [post, picked, neutral]
          rw [residual] at success ⊢
          exact nodeResult_refines read rep arity success
        · simp [post, picked, neutral] at success
    | some bodyRef =>
        obtain ⟨erased, domain, body, rfl, bodyRep⟩ := represented_lambda calleeRep picked
        let opened := opening limit depth state bodyRef operand
        have branch : post visit limit depth root state .app before [callee, operand] = opened.next visit := by
          simp [post, picked, opened]
        rw [branch] at success ⊢
        obtain ⟨instantiated, found, done⟩ := Outcome.next_success success
        rw [done] at success ⊢
        obtain ⟨kept, backward, bodyRep⟩ :=
          NativeCoreTransformExact.substitute_refines bodyRep operandRep (opening_success found)
        obtain ⟨frame, preserves, term, termRep, change⟩ := visitRefines bodyRep success
        exact ⟨kept.trans frame, fun old => preserves (backward old), term, termRep,
          (compute_ghost_transform wellFormed (.beta erased domain body argument)).trans change⟩
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
        exact ⟨.refl _, id, result, payloadRep, compute_ghost_transform wellFormed (.transportRefl family value result)⟩
      · have residual : post visit limit depth root state .transport before [familyRef, evidence, payload] =
            nodeResult state root .transport before [familyRef, evidence, payload] := by simp [post, reflexive]
        rw [residual] at success ⊢
        exact nodeResult_refines read rep arity success
    · have rebuilt : post visit limit depth root state op before after = nodeResult state root op before after := by
        simp [post, app, transport]
      rw [rebuilt] at success ⊢
      exact nodeResult_refines read rep arity success

private theorem layers_forward (changes : ListRel (GhostTransform env) ins outs) :
    ListRel (Environment.RawLend.Forward env) ins outs := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

private theorem under_node (wellFormed : UnifiedProgram.EnvWellFormed env) (ordinary : op ≠ .lend)
    (changes : ListRel (GhostTransform env) ins outs) : GhostTransform env (.node op ins) (.node op outs) := by
  have forward := Environment.RawLend.Forward.node op (layers_forward changes)
  exact ⟨forward, raw_forward_lambda_shape forward,
    fun typed => children_preservation wellFormed typed op _ rfl ordinary _ changes⟩

private theorem children_refines (source : RepresentsList start.arena refs ins)
    (visitRefines : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      Refines env state term (visit state ref) selected ∧ GlobalEnvironment.GlobalFree term)
    (success : (children visit start refs).result = .ok selected) :
    let output := children visit start refs
    Prefix start.arena output.state.arena ∧ (Backward start.arena → Backward output.state.arena) ∧
      selected.length = refs.length ∧ (∀ x ∈ ins, GlobalEnvironment.GlobalFree x) ∧
      ∃ outs, RepresentsList output.state.arena selected outs ∧ ListRel (GhostTransform env) ins outs := by
  induction refs generalizing start ins selected with
  | nil =>
      cases source
      simp [children] at success
      subst selected
      exact ⟨.refl _, id, rfl, by simp, [], .nil, .nil⟩
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
          obtain ⟨⟨kept, backward, firstOut, headRep, headChange⟩, headFree⟩ := visitRefines head headFound
          obtain ⟨extended, preserves, exactLength, tailFree, restOut, tailRep, tailChange⟩ :=
            ih (tail.frame kept) tailFound
          refine ⟨kept.trans extended, fun old => preserves (backward old), congrArg Nat.succ exactLength,
            ?_, firstOut :: restOut, .cons (headRep.frame extended) tailRep, .cons headChange tailChange⟩
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact headFree
          · exact tailFree item member

/-- Both structural and computational branches build an actual typed
forward derivation, including when beta or a Transport reduction occurs
under a binder or exposes the proof needed by an outer Transport. -/
theorem run_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term) (success : (run limit depth state root).result = .ok selected) :
    Refines env state term (run limit depth state root) selected ∧ GlobalEnvironment.GlobalFree term := by
  induction depth generalizing state root term selected with
  | zero =>
      by_cases over : limit < state.steps + 1 <;>
        simp [run, NativeCoreUnsignedCancellation.tick, over] at success
  | succ depth ih =>
      rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
        ⟨answer, spent⟩
      cases answer with
      | error reason => simp [run, ticked] at success
      | ok charged =>
          cases charged
          let entered := {state with steps := spent}
          cases source with
          | @var _ index read =>
              simp [run, ticked, read] at success
              subst selected
              simp only [run, ticked, read, GlobalEnvironment.GlobalFree]
              exact ⟨⟨.refl _, id, _, .var read, .refl _⟩, trivial⟩
          | @node _ op refs terms read arity childrenRep =>
              by_cases allowed : supported op = true
              · have ordinary : op ≠ .lend := by intro same; subst op; contradiction
                have globalFreeHead : GlobalEnvironment.ordinary op = true := by
                  cases op <;> first | rfl | contradiction
                let computed := children (run limit depth) entered refs
                have branch : run limit (depth + 1) state root = computed.next
                    (fun childState childRefs => post (run limit depth) limit depth root childState op refs childRefs) := by
                  simp [run, ticked, read, allowed, computed, entered]
                rw [branch] at success ⊢
                obtain ⟨selectedRefs, found, done⟩ := Outcome.next_success success
                rw [done] at success ⊢
                obtain ⟨kept, preserves, sameArity, freeTerms, outputTerms, outputRep, changes⟩ :=
                  children_refines (start := entered) childrenRep (fun child childSuccess => ih child childSuccess) found
                obtain ⟨frame, backward, term, represented, reduced⟩ := post_refines wellFormed (kept.lookup read)
                  outputRep (sameArity.trans arity) (fun child succeeded => (ih child succeeded).1) success
                have rebuilt := under_node wellFormed ordinary changes
                rw [GlobalEnvironment.GlobalFree]
                exact ⟨⟨kept.trans frame, fun old => backward (preserves old), term, represented,
                  rebuilt.trans reduced⟩, ⟨globalFreeHead, freeTerms⟩⟩
              · simp [run, ticked, read, allowed] at success

theorem run_preserves (wellFormed : UnifiedProgram.EnvWellFormed env)
    (source : Represents state.arena root term)
    (typed : Environment.LoanTyping.HasType env loans ctx mode term type)
    (success : (run limit depth state root).result = .ok selected) :
    ∃ residual, Represents (run limit depth state root).state.arena selected residual ∧
      Environment.RawLend.Forward env term residual ∧
      Environment.LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨result, represented, change⟩ := (run_refines wellFormed source success).1.value
  exact ⟨result, represented, change.forward, change.typed typed⟩

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
  exact ⟨_, _, env, entry, residual, history, found, kept, preserves backward, selectedRep, change.typed typed⟩

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

end Jihoo.NativeKernel.NativeCorePureComputationNormal
