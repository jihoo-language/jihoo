import Jihoo.NativeCoreGlobalNormal
import Jihoo.NativeCoreEffectAnalysis

/-! Pure Core.normal visits the children of a structural constructor in order
and shares the work counter across them. If each child follows the atomic
Free/Drop/global path, the children keep the original arena unchanged. The
parent then either keeps its old reference or appends its changed row. -/
namespace Jihoo.NativeKernel.NativeCorePureStructuralNormal

open NativeArena NativeProgramWire
open Environment.LoanTyping.MixedProgram (History)
open NativeCoreGlobalNormal (Atomic atomicOp runPure runPure_conversion runPure_expanded_atom
  runPure_step_bounds head discardRest discard_target alias_target checked_definition_at)
open NativeKernel.Conversion (ListRel treeDepth treeSize)

/-- A pure normalization branch that rebuilds its constructor directly from
the normalized children. Specialized contractions have their own branches. -/
def structural : Op → Bool
  | .pi _ | .lam _ | .array | .lt | .eq | .refl | .ind .. | .con .. |
      .decide | .index | .zeroLe | .refine | .buffer | .alloc | .load | .store |
      .ref | .back _ | .give _ | .absurd | .pack | .ltAdd | .ltCancel | .ltLe |
      .elements _ => true
  | _ => false

/-- Normal forms of the structural fragment have only atomic leaves and
parents whose children are already in that fragment's normal form. -/
inductive Normal : Term → Prop where
  | atom : Atomic term → Normal term
  | node : structural op = true → (∀ child ∈ children, Normal child) → Normal (.node op children)

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

structure Outcome (α : Type) where
  arena : Arena
  result : Except Error α
  steps : Nat
  deriving Repr

private def leaf (arena : Arena) (roots : List Roots) (visible limit depth steps root : Nat) : Outcome Nat :=
  let (result, spent) := runPure arena roots visible limit depth steps root
  ⟨arena, result.mapError .normal, spent⟩

private def nestedChildren (visit : Arena → Nat → Nat → Outcome Nat) :
    List Nat → Arena → Nat → Outcome (List Nat)
  | [], arena, steps => ⟨arena, .ok [], steps⟩
  | root :: rest, arena, steps =>
      let first := visit arena steps root
      match first.result with
      | .error reason => ⟨first.arena, .error reason, first.steps⟩
      | .ok child =>
          let later := nestedChildren visit rest first.arena first.steps
          ⟨later.arena, later.result.map (child :: ·), later.steps⟩

private def finishNested (root : Nat) (op : Op) (before : List Nat)
    (children : Outcome (List Nat)) : Outcome Nat :=
  match children.result with
  | .error reason => ⟨children.arena, .error reason, children.steps⟩
  | .ok after =>
      match finish children.arena root op before after with
      | .error reason => ⟨children.arena, .error reason, children.steps⟩
      | .ok (arena, selected) => ⟨arena, .ok selected, children.steps⟩

/-- Visit structural children with the current arena and a shared step
counter. Transparent globals and pure Free and Drop can lead back into
structural normalization. Appends made by earlier children survive an error
in a later child. -/
def runNested (roots : List Roots) (visible limit : Nat) : Nat → Arena → Nat → Nat → Outcome Nat
  | 0, arena, steps, root => leaf arena roots visible limit 0 steps root
  | depth + 1, arena, steps, root =>
      let next := steps + 1
      if limit < next then ⟨arena, .error (.normal (.stepLimit root)), next⟩ else
      match arena[root]? with
      | some (.node op refs) =>
          if structural op then
            finishNested root op refs (nestedChildren (runNested roots visible limit depth) refs arena next)
          else
            match discardRest (.node op refs) with
            | some rest => runNested roots visible limit depth arena next rest
            | none =>
                match head (.node op refs) with
                | .alias index =>
                    if visible ≤ index then ⟨arena, .error (.normal (.invisibleGlobal root index)), next⟩ else
                    match roots[index]? with
                    | none => ⟨arena, .error (.normal (.missingDefinition root index)), next⟩
                    | some definition => runNested roots visible limit depth arena next definition.valueRoot
                | _ => leaf arena roots visible limit (depth + 1) steps root
      | _ => leaf arena roots visible limit (depth + 1) steps root

private structure Cost (arena : Arena) (initial limit : Nat) (computed : Outcome α) : Prop where
  spent : initial ≤ computed.steps
  growth : computed.arena.size + initial ≤ arena.size + computed.steps
  budget : initial ≤ limit → computed.steps ≤ limit + 1
  success : ∀ selected, computed.result = .ok selected → computed.steps ≤ limit

private theorem Cost.tick_error (reason : Error) :
    Cost arena initial limit (⟨arena, .error reason, initial + 1⟩ : Outcome α) := by
  refine ⟨Nat.le_succ _, Nat.add_le_add_left (Nat.le_succ _) _, Nat.succ_le_succ, ?_⟩
  intro _ impossible
  cases impossible

private theorem Cost.prepend (available : initial + 1 ≤ limit)
    (remaining : Cost arena (initial + 1) limit computed) : Cost arena initial limit computed where
  spent := Nat.le_trans (Nat.le_succ _) remaining.spent
  growth := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ _) _) remaining.growth
  budget _ := remaining.budget available
  success := remaining.success

private theorem leaf_cost :
    Cost arena initial limit (leaf arena roots visible limit depth initial root) := by
  have bounds := runPure_step_bounds arena roots visible limit depth initial root
  rcases done : runPure arena roots visible limit depth initial root with ⟨result, spent⟩
  dsimp only at bounds
  rw [done] at bounds
  cases result with
  | error reason =>
      simp only [leaf, done, Except.mapError]
      have spent := Nat.le_of_lt bounds.1
      refine ⟨spent, Nat.add_le_add_left spent _, bounds.2.1, ?_⟩
      intro _ impossible
      cases impossible
  | ok selected =>
      simp only [leaf, done, Except.mapError]
      have spent := Nat.le_of_lt bounds.1
      refine ⟨spent, Nat.add_le_add_left spent _, bounds.2.1, ?_⟩
      intro _ _
      exact bounds.2.2 selected rfl

private theorem nestedChildren_cost (within : initial ≤ limit)
    (visitCost : ∀ arena initial root, Cost arena initial limit (visit arena initial root)) :
    Cost arena initial limit (nestedChildren visit refs arena initial) := by
  induction refs generalizing arena initial with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _, fun room => Nat.le_trans room (Nat.le_succ _), fun _ _ => within⟩
  | cons root refs ih =>
      let first := visit arena initial root
      have cost := visitCost arena initial root
      change Cost arena initial limit first at cost
      cases choice : first.result with
      | error reason =>
          simp only [nestedChildren, show (visit arena initial root).result = .error reason from choice]
          refine ⟨cost.spent, cost.growth, cost.budget, ?_⟩
          intro _ impossible
          cases impossible
      | ok child =>
          let later := nestedChildren visit refs first.arena first.steps
          have room := cost.success child choice
          have rest := ih (arena := first.arena) (initial := first.steps) room
          change Cost first.arena first.steps limit later at rest
          simp only [nestedChildren, show (visit arena initial root).result = .ok child from choice]
          refine ⟨Nat.le_trans cost.spent rest.spent, ?_, fun _ => rest.budget room, ?_⟩
          · have before := cost.growth
            have after := rest.growth
            change later.arena.size + initial ≤ arena.size + later.steps
            omega
          · intro _ chosen
            cases outcome : later.result with
            | error reason =>
                dsimp only [later, first] at outcome
                simp [outcome, Except.map] at chosen
            | ok selected => exact rest.success selected outcome

private theorem finish_growth (added : finish arena root op before after = .ok (extended, selected)) :
    extended.size ≤ arena.size + 1 := by
  unfold finish at added
  split at added
  · cases added
    exact Nat.le_succ _
  · cases append : NativeCoreGraph.addNode arena (.node op after) with
    | error reason => simp [append, Except.mapError] at added
    | ok result =>
        simp only [append, Except.mapError, Except.ok.injEq] at added
        subst result
        exact Nat.le_of_eq (NativeCoreGraph.addNode_commits append).2.2.2.1

private theorem finishNested_cost (available : initial + 1 ≤ limit)
    (childrenCost : Cost arena (initial + 1) limit children) :
    Cost arena initial limit (finishNested root op before children) := by
  have spent := (childrenCost.prepend available).spent
  have budget := (childrenCost.prepend available).budget
  cases choice : children.result with
  | error reason =>
      simp only [finishNested, choice]
      refine ⟨spent, (childrenCost.prepend available).growth, budget, ?_⟩
      intro _ impossible
      cases impossible
  | ok result =>
      cases finished : finish children.arena root op before result with
      | error reason =>
          simp only [finishNested, choice, finished]
          refine ⟨spent, (childrenCost.prepend available).growth, budget, ?_⟩
          intro _ impossible
          cases impossible
      | ok pair =>
          obtain ⟨extended, selected⟩ := pair
          simp only [finishNested, choice, finished]
          refine ⟨spent, ?_, budget, fun _ _ => childrenCost.success result choice⟩
          have before := childrenCost.growth
          have after := finish_growth finished
          change extended.size + initial ≤ arena.size + children.steps
          omega

private theorem nested_cost :
    Cost arena initial limit (runNested roots visible limit depth arena initial root) := by
  induction depth generalizing arena initial root with
  | zero => exact leaf_cost
  | succ depth ih =>
      by_cases over : limit < initial + 1
      · simp only [runNested, over, ite_true]
        exact Cost.tick_error _
      have room := Nat.le_of_not_gt over
      cases read : arena[root]? with
      | none => simpa only [runNested, ite_eq_right over, read] using
          (leaf_cost (arena := arena) (roots := roots) (visible := visible) (limit := limit)
            (depth := depth + 1) (initial := initial) (root := root))
      | some node =>
          cases node with
          | var _ => simpa only [runNested, ite_eq_right over, read] using
              (leaf_cost (arena := arena) (roots := roots) (visible := visible) (limit := limit)
                (depth := depth + 1) (initial := initial) (root := root))
          | node op refs =>
              by_cases supported : structural op = true
              · simp only [runNested, ite_eq_right over, read, supported, ite_true]
                exact finishNested_cost room (nestedChildren_cost room fun _ _ _ => ih)
              · simp only [runNested, ite_eq_right over, read, ite_eq_right supported]
                cases skip : discardRest (.node op refs) with
                | some rest => exact (ih (root := rest)).prepend room
                | none =>
                    simp only
                    cases kind : head (.node op refs) with
                    | atomic | outside => exact leaf_cost
                    | alias index =>
                        simp only
                        by_cases hidden : visible ≤ index
                        · simp only [hidden, ite_true]
                          exact Cost.tick_error _
                        simp only [ite_eq_right hidden]
                        cases lookup : roots[index]? with
                        | none => exact Cost.tick_error _
                        | some definition =>
                            simp only
                            exact (ih (root := definition.valueRoot)).prepend room

/-- Every appended row is accounted for by a charged visit. Failure can
retain earlier appends and can exceed the limit by at most its final tick. -/
theorem runNested_cost (arena : Arena) (roots : List Roots) (visible limit depth initial root : Nat) :
    let computed := runNested roots visible limit depth arena initial root
    computed.arena.size + initial ≤ arena.size + computed.steps ∧
      (initial ≤ limit → computed.steps ≤ limit + 1) ∧
      ∀ selected, computed.result = .ok selected → computed.steps ≤ limit :=
  let proof := nested_cost (arena := arena) (roots := roots) (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) (root := root)
  ⟨proof.growth, proof.budget, proof.success⟩

private theorem atom_dimensions (atom : Atomic term) : treeSize term = 1 ∧ treeDepth term = 1 := by
  cases term with
  | var => simp [treeSize, treeDepth]
  | node op args => cases args <;> simp_all [Atomic, treeSize, treeDepth]

private theorem child_depths_le {terms : List Term} (bounded : ∀ child ∈ terms, treeDepth child ≤ depth)
    (seed : initial ≤ depth) : (terms.map treeDepth).foldl max initial ≤ depth := by
  induction terms generalizing initial with
  | nil => exact seed
  | cons term rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (fun child member => bounded child (List.mem_cons_of_mem _ member))
        (Nat.max_le.mpr ⟨seed, bounded term List.mem_cons_self⟩)

private structure Refines (before : Arena) (computed : Outcome α) (valid : Arena → Nat → α → Prop) : Prop where
  kept : Prefix before computed.arena
  backward : Backward before → Backward computed.arena
  success : ∀ selected, computed.result = .ok selected → valid computed.arena computed.steps selected

private abbrev TermResult (env : Environment) (source : Term) (depth initial : Nat)
    (arena : Arena) (spent selected : Nat) : Prop :=
  ∃ result, Normal result ∧ Represents arena selected result ∧
    treeDepth result ≤ depth ∧ initial + treeSize result ≤ spent ∧
    Environment.RawValue.Forward env (EnvironmentDelta.expand env source) result

private abbrev ChildrenResult (env : Environment) (inputs : List Term) (arity depth initial : Nat)
    (arena : Arena) (spent : Nat) (selected : List Nat) : Prop :=
  ∃ outputs, (∀ child ∈ outputs, Normal child ∧ treeDepth child ≤ depth) ∧
    RepresentsList arena selected outputs ∧ selected.length = arity ∧ initial + (outputs.map treeSize).sum ≤ spent ∧
    ListRel (Environment.RawValue.Forward env) (inputs.map (EnvironmentDelta.expand env)) outputs

private theorem Refines.prepend (rest : Refines arena computed (TermResult env tail depth (initial + 1)))
    (first : Environment.RawValue.Forward env (EnvironmentDelta.expand env source)
      (EnvironmentDelta.expand env tail)) :
    Refines arena computed (TermResult env source (depth + 1) initial) := by
  refine ⟨rest.kept, rest.backward, ?_⟩
  intro selected found
  obtain ⟨result, normal, represented, height, work, changed⟩ := rest.success selected found
  exact ⟨result, normal, represented, by omega, by omega, first.trans changed⟩

private theorem failure_refines (kept : Prefix arena current) (backward : Backward arena → Backward current) :
    Refines arena (⟨current, .error reason, spent⟩ : Outcome α) valid :=
  ⟨kept, backward, by simp⟩

private theorem frameDefinitions (aligned : RepresentsDefinitions arena roots definitions)
    (kept : Prefix arena current) : RepresentsDefinitions current roots definitions := by
  induction aligned with
  | nil => exact .nil
  | cons first _ ih => exact .cons ⟨first.1.frame kept, first.2.frame kept⟩ ih

private theorem leaf_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    Refines arena (leaf arena roots visible limit depth steps root) (TermResult env term depth steps) := by
  rcases ran : runPure arena roots visible limit depth steps root with ⟨result, spent⟩
  cases result with
  | error reason =>
      simp only [leaf, ran, Except.mapError]
      exact failure_refines (Prefix.refl _) id
  | ok result =>
      simp only [leaf, ran, Except.mapError]
      refine ⟨Prefix.refl _, id, ?_⟩
      intro selected found
      cases found
      obtain ⟨term, atom, represented, changed⟩ := runPure_expanded_atom aligned history source ran
      obtain ⟨size, height⟩ := atom_dimensions atom
      have depthBound : 1 ≤ depth := by
        cases depth with
        | zero =>
            simp only [runPure, NativeCoreGlobalNormal.run] at ran
            split at ran <;> cases ran
        | succ depth => omega
      have charged := (runPure_step_bounds arena roots visible limit depth steps root).1
      rw [ran] at charged
      exact ⟨term, .atom atom, represented, by rwa [height], by rw [size]; exact charged, changed⟩

private theorem nestedChildren_refines (aligned : RepresentsDefinitions arena roots definitions)
    (source : RepresentsList arena refs inputs)
    (visitRefines : ∀ {current initial root term}, RepresentsDefinitions current roots definitions →
      Represents current root term → Refines current (visit current initial root) (TermResult env term depth initial)) :
    Refines arena (nestedChildren visit refs arena steps) (ChildrenResult env inputs refs.length depth steps) := by
  induction refs generalizing arena inputs steps with
  | nil =>
      cases source
      refine ⟨Prefix.refl _, id, ?_⟩
      intro selected found
      cases found
      exact ⟨[], by simp, .nil, rfl, by simp [nestedChildren], .nil⟩
  | cons root rest ih =>
      cases source with
      | cons head tail =>
          have first := visitRefines (initial := steps) aligned head
          cases choice : (visit arena steps root).result with
          | error reason =>
              simp only [nestedChildren, choice]
              exact failure_refines first.kept first.backward
          | ok child =>
              have later := ih (steps := (visit arena steps root).steps)
                (frameDefinitions aligned first.kept) (tail.frame first.kept)
              simp only [nestedChildren, choice]
              refine ⟨first.kept.trans later.kept, fun h => later.backward (first.backward h), ?_⟩
              intro selected found
              cases suffix : (nestedChildren visit rest (visit arena steps root).arena
                  (visit arena steps root).steps).result with
              | error reason => simp [suffix, Except.map] at found
              | ok children =>
                  simp only [suffix, Except.map, Except.ok.injEq] at found
                  subst selected
                  obtain ⟨out, normal, represented, height, work, converted⟩ := first.success child choice
                  obtain ⟨outputs, allNormal, representedLater, lengths, laterWork, conversions⟩ :=
                    later.success children suffix
                  refine ⟨out :: outputs, ?_, .cons (represented.frame later.kept) representedLater,
                    congrArg Nat.succ lengths, ?_, .cons converted conversions⟩
                  · intro term occurrence
                    rcases List.mem_cons.mp occurrence with rfl | occurrence
                    · exact ⟨normal, height⟩
                    · exact allNormal term occurrence
                  · simp only [List.map_cons, List.sum_cons]
                    omega

private theorem finishNested_refines (read : arena[root]? = some (.node op before))
    (arity : before.length = op.arity)
    (supported : structural op = true)
    (ordinary : GlobalEnvironment.ordinary op = true)
    (normalized : Refines arena children (ChildrenResult env inputs before.length depth (initial + 1))) :
    Refines arena (finishNested root op before children) (TermResult env (.node op inputs) (depth + 1) initial) := by
  cases childResult : children.result with
  | error reason =>
      simp only [finishNested, childResult]
      exact failure_refines normalized.kept normalized.backward
  | ok refs =>
      cases appended : finish children.arena root op before refs with
      | error reason =>
          simp only [finishNested, childResult, appended]
          exact failure_refines normalized.kept normalized.backward
      | ok row =>
          obtain ⟨extended, selected⟩ := row
          obtain ⟨outputs, allNormal, represented, length, used, changed⟩ := normalized.success refs childResult
          obtain ⟨kept, result, backward, _⟩ :=
            finish_refines (normalized.kept.lookup read) represented (length.trans arity) appended
          simp only [finishNested, childResult, appended]
          refine ⟨normalized.kept.trans kept, fun h => backward (normalized.backward h), ?_⟩
          intro index found
          cases found
          refine ⟨_, .node supported (fun child member => (allNormal child member).1), result, ?_, ?_, ?_⟩
          · have bounded := child_depths_le (fun child member => (allNormal child member).2)
                (Nat.zero_le depth)
            simp only [treeDepth]
            omega
          · simpa only [treeSize, ← Nat.add_assoc] using used
          · rw [EnvironmentDelta.expand_ordinary ordinary, EnvironmentDelta.expandArgs_map]
            exact .node op changed

private theorem structural_ordinary (supported : structural op = true) : GlobalEnvironment.ordinary op = true := by
  cases op <;> simp_all [structural, GlobalEnvironment.ordinary]

private theorem runNested_refines_aux (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    Refines arena (runNested roots visible limit depth arena initial root) (TermResult env term depth initial) := by
  induction depth generalizing arena root term initial with
  | zero => exact leaf_refines aligned history source
  | succ depth ih =>
      by_cases exhausted : limit < initial + 1
      · simp only [runNested, exhausted, ite_true]
        exact failure_refines (Prefix.refl _) id
      cases source with
      | var read =>
          simpa only [runNested, ite_eq_right exhausted, read] using leaf_refines aligned history (.var read)
      | @node _ op refs inputs read arity children =>
          by_cases supported : structural op = true
          · simp only [runNested, ite_eq_right exhausted, read, supported, ite_true]
            exact finishNested_refines read arity supported (structural_ordinary supported)
              (nestedChildren_refines aligned children (fun a h => ih a h))
          · cases skip : discardRest (.node op refs) with
            | some rest =>
                simp only [runNested, ite_eq_right exhausted, read, ite_eq_right supported, skip]
                obtain ⟨_, represented, change, _⟩ :=
                  discard_target (env := env) (.node read arity children) read skip
                exact (ih aligned represented).prepend change
            | none =>
                cases kind : head (.node op refs) with
                | atomic | outside =>
                    simpa only [runNested, ite_eq_right exhausted, read, ite_eq_right supported, skip, kind] using
                      leaf_refines aligned history (.node read arity children)
                | alias index =>
                    by_cases hidden : visible ≤ index
                    · simp only [runNested, ite_eq_right exhausted, read, ite_eq_right supported, skip, kind,
                        hidden, ite_true]
                      exact failure_refines (Prefix.refl _) id
                    · cases lookup : roots[index]? with
                      | none =>
                          simp only [runNested, ite_eq_right exhausted, read, ite_eq_right supported, skip, kind,
                            ite_eq_right hidden, lookup]
                          exact failure_refines (Prefix.refl _) id
                      | some definition =>
                          simp only [runNested, ite_eq_right exhausted, read, ite_eq_right supported, skip, kind,
                            ite_eq_right hidden, lookup]
                          obtain ⟨_, represented, same⟩ :=
                            alias_target aligned history (.node read arity children) read kind lookup
                          exact (ih aligned represented).prepend (by rw [same]; exact .refl)

/-- Arbitrarily nested supported structural nodes preserve arena prefixes and
backward references, even on error. A successful reference represents a pure
reduct under the same checked global declaration history. -/
theorem runNested_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term) :
    let output := runNested roots visible limit depth arena initial root
    Prefix arena output.arena ∧ (Backward arena → Backward output.arena) ∧
      ∀ selected, output.result = .ok selected →
        ∃ normalized, Represents output.arena selected normalized ∧ Environment.RawValue.Forward env term normalized := by
  have proof := runNested_refines_aux (visible := visible) (limit := limit) (depth := depth)
    (initial := initial) aligned history source
  refine ⟨proof.kept, proof.backward, ?_⟩
  intro selected found
  obtain ⟨normalized, _, represented, _, _, changed⟩ := proof.success selected found
  have expanded : Environment.RawValue.Forward env term (EnvironmentDelta.expand env term) :=
    .old (.old (.old (EnvironmentDelta.expand_forward env term)))
  exact ⟨normalized, represented, expanded.trans changed⟩

/-- Every successful recursive run represents a normal form of the supported
fragment, including when the source is a global alias or a discard. -/
theorem runNested_normal_form (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (success : (runNested roots visible limit depth arena initial root).result = .ok selected) :
    let computed := runNested roots visible limit depth arena initial root
    ∃ normalized, Normal normalized ∧ Represents computed.arena selected normalized ∧
      treeDepth normalized ≤ depth ∧ initial + treeSize normalized ≤ computed.steps := by
  have proof := runNested_refines_aux (visible := visible) (limit := limit) (depth := depth)
    (initial := initial) aligned history source
  obtain ⟨normalized, normal, represented, height, work, _⟩ := proof.success selected success
  exact ⟨normalized, normal, represented, height, work⟩

private theorem depth_positive (term : Term) : 1 ≤ treeDepth term := by
  cases term <;> simp only [treeDepth] <;> omega

private theorem atom_reuses (atom : Atomic term) (represented : Represents arena root term)
    (enough : initial + 1 ≤ limit) :
    runNested roots visible limit (depth + 1) arena initial root = ⟨arena, .ok root, initial + 1⟩ := by
  have available := Nat.not_lt.mpr enough
  cases represented with
  | var read => simp [runNested, leaf, runPure, head, discardRest, read, available, Except.mapError]
  | @node _ op refs terms read _ children =>
      cases children with
      | cons => contradiction
      | nil =>
          cases op <;> simp [Atomic, atomicOp] at atom
          all_goals simp [runNested, structural, leaf, runPure, head, atomicOp, discardRest, read, available,
            Except.mapError]

private theorem nestedChildren_reuses (children : RepresentsList arena refs terms)
    (budget : initial + (terms.map treeSize).sum ≤ limit)
    (reuse : ∀ {root term initial}, term ∈ terms → Represents arena root term → initial + treeSize term ≤ limit →
      visit arena initial root = ⟨arena, .ok root, initial + treeSize term⟩) :
    nestedChildren visit refs arena initial = ⟨arena, .ok refs, initial + (terms.map treeSize).sum⟩ := by
  induction refs generalizing terms initial with
  | nil =>
      cases children
      simp [nestedChildren]
  | cons root rest ih =>
      cases children with
      | @cons _ term _ terms first remaining =>
          simp only [List.map_cons, List.sum_cons] at budget
          have resolved := reuse (initial := initial) List.mem_cons_self first (by omega)
          have later := ih remaining (initial := initial + treeSize term) (by omega)
            (fun member => reuse (List.mem_cons_of_mem _ member))
          simp [nestedChildren, resolved, later, Except.map, Nat.add_assoc]

/-- Rerunning on a normal form returns exactly the same arena and reference.
The traversal charges one tick for each tree occurrence, including shared
children, and succeeds with the stated depth and work allowances. -/
theorem runNested_reuses_normal (normal : Normal term) (represented : Represents arena root term)
    (height : treeDepth term ≤ depth) (budget : initial + treeSize term ≤ limit) :
    runNested roots visible limit depth arena initial root = ⟨arena, .ok root, initial + treeSize term⟩ := by
  induction depth generalizing term arena root initial with
  | zero =>
      have positive := depth_positive term
      omega
  | succ depth ih =>
      cases normal with
      | atom atomic =>
          rw [(atom_dimensions atomic).1] at budget ⊢
          exact atom_reuses atomic represented budget
      | @node op terms supported normalChildren =>
          cases represented with
          | node read _ children =>
              simp only [treeDepth] at height
              simp only [treeSize, ← Nat.add_assoc] at budget
              have available : ¬limit < initial + 1 := by omega
              have visited := nestedChildren_reuses (visit := runNested roots visible limit depth) children budget
                (fun {root child spent} member childRep room => by
                  have bounded := Environment.CoreEffectAnalysis.treeDepth_member child terms member 0
                  exact ih (normalChildren child member) childRep (by omega) room)
              simp [runNested, available, read, supported, visited, finishNested, finish, treeSize, Nat.add_assoc]

/-- A successful normalization can be rerun at its result reference from
the original starting counter and depth and work limits. The result arena
and reference are unchanged, and the rerun consumes no more work. -/
theorem runNested_rerun (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (success : (runNested roots visible limit depth arena initial root).result = .ok selected) :
    let computed := runNested roots visible limit depth arena initial root
    let rerun := runNested roots visible limit depth computed.arena initial selected
    rerun.arena = computed.arena ∧ rerun.result = .ok selected ∧ rerun.steps ≤ computed.steps := by
  obtain ⟨_, normal, represented, height, work⟩ := runNested_normal_form aligned history source success
  have within := (runNested_cost arena roots visible limit depth initial root).2.2 selected success
  dsimp only
  rw [runNested_reuses_normal normal represented height (Nat.le_trans work within)]
  exact ⟨rfl, rfl, work⟩

/-- Successful and faulted traversals retain the checked graph prefix from
the admitted bytes and only append nodes with earlier child references. -/
theorem runNested_checkBytes_refines
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (source : Represents snapshot.arena root term) :
    let output := runNested snapshot.definitions visible limit depth snapshot.arena initial root
    ∃ definitions families env,
      History definitions families env ∧ Prefix snapshot.arena output.arena ∧ Backward output.arena ∧
        ∀ selected, output.result = .ok selected →
          ∃ normalized, Represents output.arena selected normalized ∧ Environment.RawValue.Forward env term normalized := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨kept, preserves, reduction⟩ := runNested_refines (visible := visible) (limit := limit)
    (depth := depth) (initial := initial) aligned history source
  exact ⟨definitions, _, env, history, kept, preserves backward, reduction⟩

/-- A definition in an admitted exact-byte snapshot can be rerun at its
normalized reference. Admission supplies the representation of the original
body selected by the definition row. -/
theorem runNested_admitted_definition_rerun {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (success : (runNested snapshot.definitions visible limit depth snapshot.arena initial
      definition.valueRoot).result = .ok selected) :
    let computed := runNested snapshot.definitions visible limit depth snapshot.arena initial definition.valueRoot
    let rerun := runNested snapshot.definitions visible limit depth computed.arena initial selected
    rerun.arena = computed.arena ∧ rerun.result = .ok selected ∧ rerun.steps ≤ computed.steps := by
  obtain ⟨decoded, _, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨_, _, _, represented, _⟩ := checked_definition_at aligned history row
  exact runNested_rerun aligned history represented.2 success

/-- The shared child is visited twice. Each visit appends its own row, then
the parent is appended with those two fresh references. With one fewer tick,
the second visit fails and leaves the first appended row in the arena. -/
theorem nested_shared_child_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node .eq [1, 0], .node .eq [2, 2]]
    let first := arena.push (.node .eq [0, 0])
    runNested [] 0 9 4 arena 0 3 =
      ⟨(first.push (.node .eq [0, 0])).push (.node .eq [4, 5]), .ok 6, 9⟩ ∧
    runNested [] 0 8 4 arena 0 3 = ⟨first, .error (.normal (.stepLimit 0)), 9⟩ := by
  exact ⟨rfl, rfl⟩

/-- An alias through a pure Drop reaches a composite equality. Normalizing
its Free child leaves both operands pointing to the original literal. -/
theorem nested_discard_alias_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node .eq [1, 0],
      .node (.drop 0) [0, 2], .node (.global 0) []]
    runNested [⟨2, 3⟩] 1 6 5 arena 0 4 = ⟨arena.push (.node .eq [0, 0]), .ok 5, 6⟩ ∧
      runNested [⟨2, 3⟩] 1 5 5 arena 0 4 = ⟨arena, .error (.normal (.stepLimit 0)), 6⟩ ∧
      runNested [⟨2, 3⟩] 0 6 5 arena 0 4 = ⟨arena, .error (.normal (.invisibleGlobal 4 0)), 1⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCorePureStructuralNormal
