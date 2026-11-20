import Jihoo.NativeCorePureStructuralNormal

/-! Core.normal normalizes the operand of Borrow or Deref before testing for
the opposite constructor. Cancellation returns its contained reference.
A neutral branch reuses an unchanged row or appends the new single child. -/
namespace Jihoo.NativeKernel.NativeCoreReferenceNormal

open NativeArena NativeProgramWire
open NativeCorePureStructuralNormal (Error Outcome Normal runNested runNested_refines runNested_reuses_normal)
open Environment.LoanTyping.MixedProgram (History)
open NativeKernel.Conversion (treeDepth treeSize)
open Environment.RawValue (Forward)

inductive ReferenceAction where
  | borrow
  | dereference
  deriving DecidableEq

def ReferenceAction.op : ReferenceAction → Op
  | .borrow => .borrow
  | .dereference => .deref

def ReferenceAction.opposite : ReferenceAction → ReferenceAction
  | .borrow => .dereference
  | .dereference => .borrow

def ReferenceAction.term (action : ReferenceAction) (value : Term) : Term := .node action.op [value]

private def referenceRow : Node → Option (ReferenceAction × Nat)
  | .node .borrow [ref] => some (.borrow, ref)
  | .node .deref [ref] => some (.dereference, ref)
  | _ => none

private theorem referenceRow_some (found : referenceRow row = some (action, ref)) :
    row = .node action.op [ref] := by
  fun_cases referenceRow row <;> cases action <;> simp_all [referenceRow, ReferenceAction.op]

private theorem referenceRow_op (action : ReferenceAction) (ref : Nat) :
    referenceRow (.node action.op [ref]) = some (action, ref) := by
  cases action <;> rfl

private def neutral (action : ReferenceAction) (root before child : Nat) (arena : Arena) (steps : Nat) : Outcome Nat :=
  if before = child then ⟨arena, .ok root, steps⟩ else
    match NativeCoreGraph.addNode arena (.node action.op [child]) with
    | .ok (extended, ref) => ⟨extended, .ok ref, steps⟩
    | .error reason => ⟨arena, .error (.add reason), steps⟩

private def finish (action : ReferenceAction) (root before : Nat) (normalized : Outcome Nat) : Outcome Nat :=
  match normalized.result with
  | .error reason => ⟨normalized.arena, .error reason, normalized.steps⟩
  | .ok child =>
      match normalized.arena[child]? with
      | none => ⟨normalized.arena, .error (.normal (.invalidReference child)), normalized.steps⟩
      | some row =>
          match referenceRow row with
          | some (other, ref) =>
              if other = action.opposite then ⟨normalized.arena, .ok ref, normalized.steps⟩
              else neutral action root before child normalized.arena normalized.steps
          | none => neutral action root before child normalized.arena normalized.steps

/-- Normalize nested Borrow/Deref nodes and delegate other roots to the
structural normalizer. The fallback's unsupported outcomes remain errors.
Cancellation and neutral handling take no separate work tick. -/
def run (roots : List Roots) (visible limit : Nat) : Nat → Arena → Nat → Nat → Outcome Nat
  | 0, arena, initial, root => runNested roots visible limit 0 arena initial root
  | depth + 1, arena, initial, root =>
      let next := initial + 1
      if limit < next then ⟨arena, .error (.normal (.stepLimit root)), next⟩ else
        match arena[root]?.bind referenceRow with
        | some (action, child) => finish action root child (run roots visible limit depth arena next child)
        | none => runNested roots visible limit (depth + 1) arena initial root

private structure Refines (old : Arena) (computed : Outcome Nat) (valid : Arena → Nat → Prop) : Prop where
  kept : Prefix old computed.arena
  backward : Backward old → Backward computed.arena
  success : ∀ selected, computed.result = .ok selected → valid computed.arena selected

private abbrev Result (env : Environment) (term : Term) (arena : Arena) (selected : Nat) : Prop :=
  ∃ output, Represents arena selected output ∧ Forward env term output

private theorem error_refines (kept : Prefix old current) (backward : Backward old → Backward current) :
    Refines old (⟨current, .error reason, steps⟩ : Outcome Nat) valid :=
  ⟨kept, backward, by simp⟩

private theorem represented_read (rep : Represents arena root source) : ∃ row, arena[root]? = some row := by
  cases rep with
  | var read | node read => exact ⟨_, read⟩

private theorem represented_unary {action : ReferenceAction} (source : Represents arena root term)
    (read : arena[root]? = some (.node action.op [child])) :
    ∃ value, term = action.term value ∧ Represents arena child value := by
  cases source with
  | var other => simp [other] at read
  | node other _ children =>
      have same := Option.some.inj (other.symm.trans read)
      simp only [Node.node.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      cases children with
      | cons child remaining => cases remaining; exact ⟨_, rfl, child⟩

private theorem unary_read {action : ReferenceAction} (source : Represents arena root (action.term value)) :
    ∃ child, arena[root]? = some (.node action.op [child]) ∧ Represents arena child value := by
  unfold ReferenceAction.term at source
  cases source with
  | node read _ children =>
      cases children with
      | cons child remaining => cases remaining; exact ⟨_, read, child⟩

private theorem cancelRoot (action : ReferenceAction) (value : Term) :
    ACU.Computes (action.term (action.opposite.term value)) value := by
  cases action with
  | borrow => exact .borrowDeref value
  | dereference => exact .derefBorrow value

private theorem neutral_refines (read : arena[root]? = some (.node action.op [before]))
    (represented : Represents arena child term) :
    Refines arena (neutral action root before child arena steps)
      (fun after selected => Represents after selected (action.term term)) := by
  have arity : [child].length = action.op.arity := by cases action <;> rfl
  unfold neutral
  split
  · rename_i same
    refine ⟨Prefix.refl _, id, ?_⟩
    intro selected success
    cases success
    exact .node (same ▸ read) arity (.cons represented .nil)
  · cases added : NativeCoreGraph.addNode arena (.node action.op [child]) with
    | error reason => exact error_refines (Prefix.refl _) id
    | ok result =>
        obtain ⟨after, reference⟩ := result
        obtain ⟨kept, fresh, _, _, _, found⟩ := NativeCoreGraph.addNode_commits added
        refine ⟨kept, fun checked => NativeCoreGraph.addNode_preserves_backward checked added ?_, ?_⟩
        · intro ref member
          have same : ref = child := by simpa [Node.references] using member
          subst ref
          rw [fresh]
          obtain ⟨_, existsRow⟩ := represented_read represented
          exact (Array.getElem?_eq_some_iff.mp existsRow).1
        · intro selected success
          cases success
          exact .node found arity (.cons (represented.frame kept) .nil)

private theorem finish_refines (read : arena[root]? = some (.node action.op [before]))
    (normalized : Refines arena computed (Result env term)) :
    Refines arena (finish action root before computed) (Result env (action.term term)) := by
  cases result : computed.result with
  | error reason =>
      simp only [finish, result]
      exact error_refines normalized.kept normalized.backward
  | ok child =>
      obtain ⟨value, represented, changed⟩ := normalized.success child result
      obtain ⟨row, found⟩ := represented_read represented
      have context : Forward env (action.term term) (action.term value) :=
        .node action.op (.cons changed .nil)
      have restored : Refines arena (neutral action root before child computed.arena computed.steps)
          (Result env (action.term term)) := by
        have written := neutral_refines (steps := computed.steps) (normalized.kept.lookup read) represented
        refine ⟨normalized.kept.trans written.kept, fun h => written.backward (normalized.backward h), ?_⟩
        intro selected success
        exact ⟨_, written.success selected success, context⟩
      simp only [finish, result, found]
      cases inverse : referenceRow row with
      | none => exact restored
      | some entry =>
          obtain ⟨other, ref⟩ := entry
          by_cases opposite : other = action.opposite
          · simp only [opposite, ite_true]
            subst other
            have inverseRead : computed.arena[child]? = some (.node action.opposite.op [ref]) :=
              (referenceRow_some inverse) ▸ found
            obtain ⟨retained, rfl, reduced⟩ := represented_unary represented inverseRead
            refine ⟨normalized.kept, normalized.backward, ?_⟩
            intro selected accepted
            cases accepted
            exact ⟨retained, reduced, context.trans (.old (.acu (.compute (cancelRoot action retained))))⟩
          · simp only [ite_eq_right opposite]
            exact restored

private theorem structural_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    Refines arena (runNested roots visible limit depth arena initial root) (Result env term) := by
  obtain ⟨kept, backward, changed⟩ := runNested_refines (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history source
  exact ⟨kept, backward, changed⟩

private theorem run_refines_aux (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    Refines arena (run roots visible limit depth arena initial root) (Result env term) := by
  induction depth generalizing arena root term initial with
  | zero => exact structural_refines aligned history source
  | succ depth ih =>
      by_cases over : limit < initial + 1
      · simp only [run, over, ite_true]
        exact error_refines (Prefix.refl _) id
      obtain ⟨row, read⟩ := represented_read source
      simp only [run, ite_eq_right over, read, Option.bind_some]
      cases visit : referenceRow row with
      | none => exact structural_refines aligned history source
      | some entry =>
          obtain ⟨action, child⟩ := entry
          have unary : arena[root]? = some (.node action.op [child]) := (referenceRow_some visit) ▸ read
          obtain ⟨value, rfl, represented⟩ := represented_unary source unary
          exact finish_refines unary (ih aligned represented)

/-- The returned reference realizes a finite RawValue reduction. Every
outcome preserves already allocated rows and their backward references. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    let computed := run roots visible limit depth arena initial root
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ selected, computed.result = .ok selected →
        ∃ normalized, Represents computed.arena selected normalized ∧ Forward env term normalized := by
  have proof := run_refines_aux (visible := visible) (limit := limit) (depth := depth)
    (initial := initial) aligned history source
  exact ⟨proof.kept, proof.backward, proof.success⟩

theorem run_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root term) :
    let computed := run snapshot.definitions visible limit depth snapshot.arena initial root
    ∃ definitions families env,
      History definitions families env ∧ Prefix snapshot.arena computed.arena ∧ Backward computed.arena ∧
        ∀ selected, computed.result = .ok selected →
          ∃ normalized, Represents computed.arena selected normalized ∧ Forward env term normalized := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨kept, preserves, changed⟩ := run_refines (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history source
  exact ⟨definitions, _, env, history, kept, preserves backward, changed⟩

private theorem normal_not_unary (normal : Normal term) (represented : Represents arena root term) :
    (arena[root]?.bind referenceRow) = none := by
  cases represented with
  | var read => simp [read, referenceRow]
  | @node _ op refs inputs read _ children =>
      simp only [read, Option.bind_some]
      cases op <;> try rfl
      all_goals
        cases normal with
        | atom atomic => cases inputs <;> simp [NativeCoreGlobalNormal.Atomic, NativeCoreGlobalNormal.atomicOp] at atomic
        | node supported _ => contradiction

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

private theorem run_delegates (known : arena[root]?.bind referenceRow = none)
    (available : ¬limit < initial + 1) :
    run roots visible limit depth arena initial root = runNested roots visible limit depth arena initial root := by
  cases depth with
  | zero => rfl
  | succ depth => simp only [run, ite_eq_right available, known]

private theorem run_reference (read : arena[root]? = some (.node action.op [child]))
    (available : ¬limit < initial + 1) :
    run roots visible limit (depth + 1) arena initial root =
      finish action root child (run roots visible limit depth arena (initial + 1) child) := by
  simp only [run, ite_eq_right available, read, Option.bind_some, referenceRow_op]

/-- A structurally normal payload is visited once. The inner reference row
keeps its old reference, and the outer cancellation returns the operand at
the original Loan64 type. -/
theorem normal_cancellation_at_type {action : ReferenceAction}
    (wf : UnifiedProgram.EnvWellFormed env) (normal : Normal payload)
    (source : Represents arena root (action.term (action.opposite.term payload)))
    (typed : Environment.LoanTyping.HasType env loans ctx mode (action.term (action.opposite.term payload)) type)
    (height : treeDepth payload ≤ depth) (budget : initial + 2 + treeSize payload ≤ limit) :
    ∃ selected, run roots visible limit (depth + 2) arena initial root =
        ⟨arena, .ok selected, initial + 2 + treeSize payload⟩ ∧
      Represents arena selected payload ∧ Environment.LoanTyping.HasType env [] ctx true payload type := by
  obtain ⟨middle, parentRead, middleRep⟩ := unary_read source
  obtain ⟨selected, middleRead, payloadRep⟩ := unary_read middleRep
  obtain ⟨row, rowRead⟩ := represented_read payloadRep
  have notHead := normal_not_unary normal payloadRep
  have nonReference : referenceRow row = none := by
    simpa only [rowRead, Option.bind_some] using notHead
  have payloadCost : 1 ≤ treeSize payload := by cases payload <;> simp only [treeSize] <;> omega
  have withinParent : ¬limit < initial + 1 := by omega
  have withinMiddle : ¬limit < initial + 1 + 1 := by omega
  have withinPayload : ¬limit < initial + 1 + 1 + 1 := by omega
  have payloadBudget : (initial + 1 + 1) + treeSize payload ≤ limit := by omega
  have payloadRun := runNested_reuses_normal (roots := roots) (visible := visible)
    normal payloadRep height payloadBudget
  refine ⟨selected, ?_, payloadRep, Environment.LoanTyping.compute_ghost_preservation wf (cancelRoot _ _) typed⟩
  rw [run_reference parentRead withinParent, run_reference middleRead withinMiddle,
    run_delegates notHead withinPayload, payloadRun]
  simp [finish, neutral, rowRead, nonReference, middleRead, referenceRow_op]

/-- The admitted exact bytes identify both the cancellation root and its
original result type. A normal payload is returned at that very type. -/
theorem run_admitted_cancellation_at_type {action : ReferenceAction} {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (source : Represents snapshot.arena definition.valueRoot (action.term (action.opposite.term payload)))
    (normal : Normal payload) (height : treeDepth payload ≤ depth)
    (budget : initial + 2 + treeSize payload ≤ limit) :
    ∃ definitions families env entry selected,
      History definitions families env ∧ env.globals[index]? = some entry ∧
        run snapshot.definitions visible limit (depth + 2) snapshot.arena initial definition.valueRoot =
          ⟨snapshot.arena, .ok selected, initial + 2 + treeSize payload⟩ ∧
        Represents snapshot.arena selected payload ∧ Environment.LoanTyping.HasType env [] [] true payload entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  have free : GlobalEnvironment.GlobalFree (action.term (action.opposite.term payload)) := by
    have payloadFree := normal_global_free normal
    cases action <;> simp [ReferenceAction.term, ReferenceAction.op, ReferenceAction.opposite,
      GlobalEnvironment.GlobalFree, GlobalEnvironment.ordinary, payloadFree]
  rw [represented.2.unique source, EnvironmentDelta.expand_globalFree free] at typed
  obtain ⟨selected, computed, represented, preserved⟩ :=
    normal_cancellation_at_type (roots := snapshot.definitions) (visible := visible) history.wellFormed normal source typed height budget
  exact ⟨definitions, _, env, entry, selected, history, found, computed, represented, preserved⟩

/-- An inner neutral append can be followed by a cancellation. A neutral
parent keeps its reference when its normalized child is unchanged. -/
theorem cancellation_and_neutral_example :
    let arena : Arena := #[.var 0, .node .free [0, 0], .node .borrow [1], .node .deref [2],
      .node .deref [0], .node .borrow [4]]
    run [] 0 4 4 arena 0 3 = ⟨arena.push (.node .borrow [0]), .ok 0, 4⟩ ∧
    run [] 0 2 2 arena 0 4 = ⟨arena, .ok 4, 2⟩ ∧
    run [] 0 3 3 arena 0 5 = ⟨arena, .ok 0, 3⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreReferenceNormal
