import Jihoo.NativeCorePureStructuralNormal

/-! Pure Core.normal visits the whole refinement operand before taking a
Pack field. The Witness helper returns the packed value or appends a neutral
Witness. A neutral Proof uses the usual unchanged-row check. -/
namespace Jihoo.NativeKernel.NativeCoreRefinementNormal

open NativeArena NativeProgramWire
open NativeCorePureStructuralNormal (Error Outcome runNested runNested_refines)
open Environment.LoanTyping.MixedProgram (History)
open Environment.RawValue (Forward)

inductive Projection where
  | witness
  | proof
  deriving DecidableEq

def Projection.op : Projection → Op
  | .witness => .witness
  | .proof => .proof

def Projection.term (projection : Projection) (operand : Term) : Term :=
  .node projection.op [operand]

def projectionOf : Op → Option Projection
  | .witness => some .witness
  | .proof => some .proof
  | _ => none

private theorem projectionOf_op (projection : Projection) : projectionOf projection.op = some projection := by
  cases projection <;> rfl

def packFields : Node → Option (Nat × Nat)
  | .node .pack [_, value, evidence] => some (value, evidence)
  | _ => none

def select (projection : Projection) (value evidence : Nat) : Nat :=
  match projection with
  | .witness => value
  | .proof => evidence

def special : Projection → Node → Bool
  | _, .node .strict [_, _] => true
  | .witness, .node .ifLt [_, _, _, _] | .witness, .node .ifEq [_, _, _, _] => true
  | _, _ => false

private def neutral (projection : Projection) (before child root : Nat) (arena : Arena) (steps : Nat) : Outcome Nat :=
  if projection = .proof ∧ before = child then ⟨arena, .ok root, steps⟩ else
  match NativeCoreGraph.addNode arena (.node projection.op [child]) with
  | .ok (extended, index) => ⟨extended, .ok index, steps⟩
  | .error reason => ⟨arena, .error (.add reason), steps⟩

private def finish (projection : Projection) (before root depth : Nat) (normalized : Outcome Nat) : Outcome Nat :=
  match normalized.result with
  | .error reason => ⟨normalized.arena, .error reason, normalized.steps⟩
  | .ok child =>
      if projection = .witness ∧ depth = 0 then
        ⟨normalized.arena, .error (.normal (.depthLimit child)), normalized.steps⟩
      else
        match normalized.arena[child]? with
        | none => ⟨normalized.arena, .error (.normal (.invalidReference child)), normalized.steps⟩
        | some row =>
            match packFields row with
            | some (value, evidence) => ⟨normalized.arena, .ok (select projection value evidence), normalized.steps⟩
            | none =>
                if special projection row then
                  ⟨normalized.arena, .error (.normal (.outsideFragment child)), normalized.steps⟩
                else neutral projection before child root normalized.arena normalized.steps

/-- Normalize one Witness or Proof whose operand is in the structural
normalizer's fragment. The selected field requires no additional tick.
Recursive Strict and conditional projection helpers are outside this model. -/
def run (arena : Arena) (roots : List Roots) (visible limit depth steps root : Nat) : Outcome Nat :=
  let next := steps + 1
  if limit < next then ⟨arena, .error (.normal (.stepLimit root)), next⟩ else
  match depth with
  | 0 => ⟨arena, .error (.normal (.depthLimit root)), next⟩
  | remaining + 1 =>
      match arena[root]? with
      | none => ⟨arena, .error (.normal (.invalidReference root)), next⟩
      | some (.node op [child]) =>
          match projectionOf op with
          | some projection => finish projection child root remaining (runNested roots visible limit remaining arena next child)
          | none => ⟨arena, .error (.normal (.outsideFragment root)), next⟩
      | _ => ⟨arena, .error (.normal (.outsideFragment root)), next⟩

private structure Refines (old : Arena) (computed : Outcome Nat) (valid : Arena → Nat → Prop) : Prop where
  kept : Prefix old computed.arena
  backward : Backward old → Backward computed.arena
  success : ∀ selected, computed.result = .ok selected → valid computed.arena selected

private abbrev Result (env : Environment) (source : Term) (arena : Arena) (selected : Nat) : Prop :=
  ∃ output, Represents arena selected output ∧ Forward env source output

private theorem error_refines (kept : Prefix arena current) (backward : Backward arena → Backward current) :
    Refines arena (⟨current, .error reason, steps⟩ : Outcome Nat) valid :=
  ⟨kept, backward, by simp⟩

private theorem projection_arity (projection : Projection) : projection.op.arity = 1 := by
  cases projection <;> rfl

private theorem rowIndex (represented : Represents arena index term) : index < arena.size := by
  cases represented with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1

private theorem rowExists (represented : Represents arena index term) : ∃ node, arena[index]? = some node := by
  cases represented with
  | var read | node read => exact ⟨_, read⟩

theorem pack_selection_computes (read : arena[index]? = some row)
    (represented : Represents arena index term) (parts : packFields row = some (value, evidence)) :
    ∃ result, Represents arena (select projection value evidence) result ∧
      ACU.Computes (projection.term term) result := by
  cases represented with
  | var found =>
      rw [found, Option.some.injEq] at read
      cases read
      simp [packFields] at parts
  | @node _ op refs inputs found _ children =>
      rw [found, Option.some.injEq] at read
      cases read
      cases op <;> try contradiction
      case pack =>
        cases children with
        | nil => contradiction
        | cons predicate remaining =>
            cases remaining with
            | nil => contradiction
            | cons witness remaining =>
                cases remaining with
                | nil => contradiction
                | cons proof last =>
                    cases last with
                    | cons => contradiction
                    | nil =>
                        simp only [packFields, Option.some.injEq, Prod.mk.injEq] at parts
                        obtain ⟨rfl, rfl⟩ := parts
                        cases projection with
                        | witness => exact ⟨_, witness, .witnessPack _ _ _⟩
                        | proof => exact ⟨_, proof, .proofPack _ _ _⟩

private theorem pack_selection (read : arena[index]? = some row)
    (represented : Represents arena index term) (parts : packFields row = some (value, evidence)) :
    Result env (projection.term term) arena (select projection value evidence) := by
  obtain ⟨result, selected, step⟩ := pack_selection_computes (projection := projection) read represented parts
  exact ⟨result, selected, .old (.acu (.compute step))⟩

private theorem neutral_refines (read : arena[root]? = some (.node projection.op [before]))
    (represented : Represents arena child term) :
    Refines arena (neutral projection before child root arena steps)
      (fun after output => Represents after output (projection.term term)) := by
  have arity := (projection_arity projection).symm
  unfold neutral
  split
  · rename_i same
    refine ⟨Prefix.refl _, id, ?_⟩
    intro selected successful
    cases successful
    have exactRow : arena[root]? = some (.node projection.op [child]) := same.2 ▸ read
    exact .node exactRow arity (.cons represented .nil)
  · cases added : NativeCoreGraph.addNode arena (.node projection.op [child]) with
    | error reason => exact error_refines (Prefix.refl _) id
    | ok result =>
        obtain ⟨after, index⟩ := result
        obtain ⟨kept, fresh, _, _, _, lookup⟩ := NativeCoreGraph.addNode_commits added
        refine ⟨kept, fun backward => NativeCoreGraph.addNode_preserves_backward backward added ?_, ?_⟩
        · intro ref member
          have same : ref = child := by simpa [Node.references] using member
          subst ref
          rw [fresh]
          exact rowIndex represented
        · intro selected successful
          cases successful
          exact .node lookup arity (.cons (represented.frame kept) .nil)

private theorem finish_refines (read : arena[root]? = some (.node projection.op [before]))
    (kept : Prefix arena normalized.arena) (backward : Backward arena → Backward normalized.arena)
    (reduced : ∀ child, normalized.result = .ok child → Result env source normalized.arena child) :
    Refines arena (finish projection before root depth normalized) (Result env (projection.term source)) := by
  cases computed : normalized.result with
  | error reason =>
      simp only [finish, computed]
      exact error_refines kept backward
  | ok child =>
      obtain ⟨term, represented, changed⟩ := reduced child computed
      have context : Forward env (projection.term source) (projection.term term) :=
        .node projection.op (.cons changed .nil)
      simp only [finish, computed]
      split
      · exact error_refines kept backward
      obtain ⟨row, found⟩ := rowExists represented
      simp only [found]
      cases parts : packFields row with
      | some fields =>
          obtain ⟨value, evidence⟩ := fields
          refine ⟨kept, backward, ?_⟩
          intro selected success
          cases success
          obtain ⟨output, packed, projected⟩ := pack_selection (env := env) (projection := projection) found represented parts
          exact ⟨output, packed, context.trans projected⟩
      | none =>
          by_cases outside : special projection row = true
          · simp only [outside, ite_true]
            exact error_refines kept backward
          simp only [ite_eq_right outside]
          have written := neutral_refines (steps := normalized.steps) (kept.lookup read) represented
          refine ⟨kept.trans written.kept, fun good => written.backward (backward good), ?_⟩
          intro selected success
          exact ⟨projection.term term, written.success selected success, context⟩

private theorem read_projection {projection : Projection} (source : Represents arena root (projection.term term)) :
    ∃ child, arena[root]? = some (.node projection.op [child]) ∧ Represents arena child term := by
  unfold Projection.term at source
  cases source with
  | node read _ children =>
      cases children with
      | cons child remaining => cases remaining; exact ⟨_, read, child⟩

/-- Every successful projection computes a raw forward reduction of the
original term. All outcomes preserve the previous arena and backward
references, even when the operand appended rows before rejection. -/
theorem run_refines {projection : Projection} (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root (projection.term term)) :
    let computed := run arena roots visible limit depth initial root
    Prefix arena computed.arena ∧ (Backward arena → Backward computed.arena) ∧
      ∀ selected, computed.result = .ok selected →
        ∃ reduced, Represents computed.arena selected reduced ∧ Forward env (projection.term term) reduced := by
  have proof : Refines arena (run arena roots visible limit depth initial root) (Result env (projection.term term)) := by
    obtain ⟨child, read, represented⟩ := read_projection source
    by_cases over : limit < initial + 1
    · simp only [run, over, ite_true]
      exact error_refines (Prefix.refl _) id
    cases depth with
    | zero =>
        simp only [run, ite_eq_right over]
        exact error_refines (Prefix.refl _) id
    | succ depth =>
        simp only [run, ite_eq_right over, read, projectionOf_op]
        obtain ⟨kept, backward, reduced⟩ := runNested_refines (visible := visible) (limit := limit)
          (depth := depth) (initial := initial + 1) aligned history represented
        exact finish_refines read kept backward reduced
  exact ⟨proof.kept, proof.backward, proof.success⟩

/-- The admitted snapshot supplies the unchanged global program history
used while normalizing the operand of the original projection. -/
theorem run_checkBytes_refines {projection : Projection}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root (projection.term term)) :
    let computed := run snapshot.arena snapshot.definitions visible limit depth initial root
    ∃ definitions families env,
      History definitions families env ∧ Prefix snapshot.arena computed.arena ∧ Backward computed.arena ∧
        ∀ selected, computed.result = .ok selected →
          ∃ reduced, Represents computed.arena selected reduced ∧ Forward env (projection.term term) reduced := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨kept, preserves, reduced⟩ := run_refines (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history source
  exact ⟨definitions, _, env, history, kept, preserves backward, reduced⟩

/-- Pack normalizes all three fields before projection. Neutral Witness
appends even when its operand keeps the same reference. Proof reuses its row. -/
theorem packed_and_neutral_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node .prop [], .node .refl [0],
      .node .pack [2, 1, 3], .node .witness [4], .node .proof [4], .var 0, .node .witness [7], .node .proof [7]]
    let changed := arena.push (.node .pack [2, 0, 3])
    run arena [] 0 7 4 0 5 = ⟨changed, .ok 0, 7⟩ ∧
    run arena [] 0 7 4 0 6 = ⟨changed, .ok 3, 7⟩ ∧
    run arena [] 0 6 4 0 5 = ⟨arena, .error (.normal (.stepLimit 0)), 7⟩ ∧
    run arena [] 0 2 2 0 8 = ⟨arena.push (.node .witness [7]), .ok 10, 2⟩ ∧
    run arena [] 0 2 2 0 9 = ⟨arena, .ok 9, 2⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreRefinementNormal
