import Jihoo.NativeCoreGlobalNormal

/-! Pure Core.normal visits the children of a structural constructor in order
and shares the work counter across them. If each child follows the atomic
Free/Drop/global path, the children keep the original arena unchanged. The
parent then either keeps its old reference or appends its changed row. -/
namespace Jihoo.NativeKernel.NativeCorePureStructuralNormal

open NativeArena NativeProgramWire
open Environment.LoanTyping.MixedProgram (History)
open NativeCoreGlobalNormal (runPure runPure_conversion)
open NativeKernel.Conversion (ListRel)

/-- A pure normalization branch that rebuilds its constructor directly from
the normalized children. Specialized contractions have their own branches. -/
def structural : Op → Bool
  | .pi _ | .lam _ | .array | .lt | .eq | .refl | .ind .. | .con .. |
      .decide | .index | .zeroLe | .refine | .buffer | .alloc | .load | .store |
      .ref | .back _ | .give _ | .absurd | .pack | .ltAdd | .ltCancel | .ltLe |
      .elements _ => true
  | _ => false

inductive Error where
  | normal (reason : NativeCoreGlobalNormal.Error)
  | add (reason : NativeCoreGraph.Error)
  deriving Repr, DecidableEq

private def runChildren (arena : Arena) (roots : List Roots) (visible limit depth : Nat) :
    List Nat → Nat → Except Error (List Nat) × Nat
  | [], steps => (.ok [], steps)
  | root :: rest, steps =>
      match runPure arena roots visible limit depth steps root with
      | (.error reason, spent) => (.error (.normal reason), spent)
      | (.ok child, spent) =>
          let (children, counter) := runChildren arena roots visible limit depth rest spent
          (children.map (child :: ·), counter)

private def finish (arena : Arena) (root : Nat) (op : Op) (before after : List Nat) :
    Except Error (Arena × Nat) :=
  if before = after then .ok (arena, root) else
    (NativeCoreGraph.addNode arena (.node op after)).mapError .add

/-- The root is charged once. Children share its decremented depth and each
child starts with the preceding child's counter. A changed parent is appended
using the graph's native entry limit. -/
def run (arena : Arena) (roots : List Roots) (visible limit depth steps root : Nat) :
    Except Error (Arena × Nat) × Nat :=
  let next := steps + 1
  if limit < next then (.error (.normal (.stepLimit root)), next) else
  match depth with
  | 0 => (.error (.normal (.depthLimit root)), next)
  | remaining + 1 =>
      match arena[root]? with
      | none => (.error (.normal (.invalidReference root)), next)
      | some (.node op refs) =>
          if structural op then
            let (result, counter) := runChildren arena roots visible limit remaining refs next
            (result.bind (finish arena root op refs), counter)
          else (.error (.normal (.outsideFragment root)), next)
      | some (.var _) => (.error (.normal (.outsideFragment root)), next)

private theorem children_refine (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : RepresentsList arena refs inputs)
    (computed : runChildren arena roots visible limit depth refs initial = (.ok selected, counter)) :
    ∃ outputs, RepresentsList arena selected outputs ∧ selected.length = refs.length ∧
      ListRel (Environment.RawValue.Forward env) inputs outputs := by
  induction source using RepresentsList.rec (motive_1 := fun _ _ _ => True)
      generalizing initial selected counter with
  | var | node => trivial
  | nil =>
      simp only [runChildren, Prod.mk.injEq, Except.ok.injEq] at computed
      obtain ⟨rfl, rfl⟩ := computed
      exact ⟨[], .nil, rfl, .nil⟩
  | @cons root input refs inputs head tail _ ih =>
      rcases step : runPure arena roots visible limit depth initial root with ⟨result, spent⟩
      cases result with
      | error reason => simp [runChildren, step] at computed
      | ok child =>
          rcases sequence : runChildren arena roots visible limit depth refs spent with ⟨result, final⟩
          cases result with
          | error reason => simp [runChildren, step, sequence, Except.map] at computed
          | ok children =>
              simp only [runChildren, step, sequence, Except.map, Prod.mk.injEq, Except.ok.injEq] at computed
              obtain ⟨rfl, rfl⟩ := computed
              obtain ⟨out, headRep, changed⟩ := runPure_conversion aligned history head step
              obtain ⟨outs, tailRep, length, changes⟩ := ih sequence
              exact ⟨out :: outs, .cons headRep tailRep, congrArg Nat.succ length, .cons changed changes⟩

private theorem children_in_arena (children : RepresentsList arena refs terms) :
    ∀ child ∈ refs, child < arena.size := by
  induction children using RepresentsList.rec (motive_1 := fun root _ _ => root < arena.size) with
  | var read | node read =>
      exact (Array.getElem?_eq_some_iff.mp read).1
  | nil => simp
  | cons _ _ first rest =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact first
      · exact rest child later

private theorem finish_refines (read : arena[root]? = some (.node op before))
    (children : RepresentsList arena after outputs) (arity : after.length = op.arity)
    (computed : finish arena root op before after = .ok (extended, selected)) :
    Prefix arena extended ∧ Represents extended selected (.node op outputs) ∧
      (Backward arena → Backward extended) ∧ extended.size ≤ arena.size + 1 := by
  unfold finish at computed
  split at computed
  · rename_i unchanged
    cases computed
    exact ⟨Prefix.refl _, .node (unchanged ▸ read) arity children, id, Nat.le_succ _⟩
  · cases added : NativeCoreGraph.addNode arena (.node op after) with
    | error reason => simp [added, Except.mapError] at computed
    | ok result =>
        simp only [added, Except.mapError, Except.ok.injEq] at computed
        subst result
        obtain ⟨kept, fresh, _, grows, _, lookup⟩ := NativeCoreGraph.addNode_commits added
        have known : ∀ child ∈ (Node.node op after).references, child < selected := by
          rw [fresh]
          exact children_in_arena children
        exact ⟨kept, .node lookup arity (children.frame kept),
          fun checked => NativeCoreGraph.addNode_preserves_backward checked added known, Nat.le_of_eq grows⟩

/-- A successful structural branch extends the original arena and represents
the original term's pure reduct at the returned reference. It keeps backward
references and adds at most the parent. Every child conversion uses the
actual earlier declaration history. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (source : Represents arena root (.node op inputs))
    (computed : run arena roots visible limit depth initial root = (.ok (extended, selected), counter)) :
    ∃ outputs, Prefix arena extended ∧ Represents extended selected (.node op outputs) ∧
      (Backward arena → Backward extended) ∧ extended.size ≤ arena.size + 1 ∧
      Environment.RawValue.Forward env (.node op inputs) (.node op outputs) := by
  have parent : ∃ refs, arena[root]? = some (.node op refs) ∧ refs.length = op.arity ∧
      RepresentsList arena refs inputs := by
    cases source with
    | node read arity children => exact ⟨_, read, arity, children⟩
  obtain ⟨refs, read, arity, children⟩ := parent
  by_cases exceeded : limit < initial + 1
  · simp [run, exceeded] at computed
  cases depth with
  | zero => simp [run, exceeded] at computed
  | succ depth =>
      by_cases structuralOp : structural op = true
      · rcases sequence : runChildren arena roots visible limit depth refs (initial + 1) with ⟨result, spent⟩
        cases result with
        | error reason => simp [run, exceeded, read, structuralOp, sequence, Except.bind] at computed
        | ok result =>
            simp only [run, ite_eq_right exceeded, read, structuralOp, ite_true, sequence,
              Except.bind, Prod.mk.injEq] at computed
            obtain ⟨finished, rfl⟩ := computed
            obtain ⟨outputs, normalized, length, changes⟩ := children_refine aligned history children sequence
            obtain ⟨kept, represented, backward, growth⟩ :=
              finish_refines read normalized (length.trans arity) finished
            exact ⟨outputs, kept, represented, backward, growth, .node op changes⟩
      · simp [run, exceeded, read, structuralOp] at computed

/-- Admission of the exact snapshot bytes authenticates all global lookups
used by a structural branch. -/
theorem run_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root (.node op inputs))
    (computed : run snapshot.arena snapshot.definitions visible limit depth initial root =
      (.ok (extended, selected), counter)) :
    ∃ definitions families env outputs,
      History definitions families env ∧ Prefix snapshot.arena extended ∧
      Represents extended selected (.node op outputs) ∧
      (Backward snapshot.arena → Backward extended) ∧ extended.size ≤ snapshot.arena.size + 1 ∧
      Environment.RawValue.Forward env (.node op inputs) (.node op outputs) := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨outputs, kept, represented, backward, growth, converted⟩ := run_refines aligned history source computed
  exact ⟨definitions, _, env, outputs, history, kept, represented, backward, growth, converted⟩

/-- The first comparison keeps both original references. The second rewrites a
Free child, appends exactly one parent, and charges both children. -/
theorem equality_reference_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0],
      .node .eq [0, 0], .node .eq [1, 0]]
    run arena [] 0 4 3 0 2 = (.ok (arena, 2), 3) ∧
      run arena [] 0 4 3 0 3 = (.ok (arena.push (.node .eq [0, 0]), 4), 4) := by
  exact ⟨rfl, rfl⟩

end Jihoo.NativeKernel.NativeCorePureStructuralNormal
