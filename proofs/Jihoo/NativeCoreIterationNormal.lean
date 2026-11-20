import Jihoo.NativeCorePureComputationNormal

/-! The pure `Core.normal` branch for Fold and Loop. The count and initializer
are visited first, even at zero. A nonempty Loop visits its motive and then
its body at the ordinary child depth, retaining the iteration constructor. -/
namespace Jihoo.NativeKernel.NativeCoreIterationNormal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Error Progress GhostNormalization nodeResult
  nodeResult_progress nodeResult_refines normalizeOperands normalizeOperands_refines normalizeOperands_progress)
open NativeKernel.Conversion (ListRel)

private inductive Layout (α : Type) : Op → List α → α → α → List α → Prop where
  | fold : Layout α .fold [count, initial, body] count initial [body]
  | loop : Layout α .loop [count, motive, initial, body] count initial [motive, body]

private def splitOperands (op : Op) (refs : List α) : Option (α × α × List α) :=
  match op, refs with
  | .fold, [count, initial, body] => some (count, initial, [body])
  | .loop, [count, motive, initial, body] => some (count, initial, [motive, body])
  | _, _ => none

private theorem splitOperands_sound {α : Type} {refs later : List α} {count initial : α}
    (read : splitOperands op refs = some (count, initial, later)) :
    Layout α op refs count initial later := by
  fun_cases splitOperands op refs <;> simp_all [splitOperands]
  · rw [← read.2.2]
    exact .fold
  · rw [← read.2.2]
    exact .loop

private def arrange (op : Op) (count initial : α) (later : List α) : Option (List α) :=
  match op, later with
  | .fold, [body] => some [count, initial, body]
  | .loop, [motive, body] => some [count, motive, initial, body]
  | _, _ => none

private theorem arrange_sound {α : Type} {refs later : List α} {count initial : α}
    (read : arrange op count initial later = some refs) :
    Layout α op refs count initial later := by
  fun_cases arrange op count initial later <;> simp_all [arrange]
  · subst refs
    exact .fold
  · subst refs
    exact .loop

private theorem Layout.represented (layout : Layout Nat op refs count initial later)
    (represented : RepresentsList arena refs terms) :
    ∃ n init tail, Layout Term op terms n init tail ∧ RepresentsList arena [count, initial] [n, init] ∧
      RepresentsList arena later tail := by
  cases layout with
  | fold =>
      cases represented with
      | cons n rest =>
          cases rest with
          | cons initial rest =>
              cases rest with
              | cons body rest =>
                  cases rest
                  exact ⟨_, _, _, .fold, .cons n (.cons initial .nil), .cons body .nil⟩
  | loop =>
      cases represented with
      | cons n rest =>
          cases rest with
          | cons motive rest =>
              cases rest with
              | cons initial rest =>
                  cases rest with
                  | cons body rest =>
                      cases rest
                      exact ⟨_, _, _, .loop, .cons n (.cons initial .nil), .cons motive (.cons body .nil)⟩

private theorem Layout.arranged (layout : Layout Nat op refs count initial later)
    (n : Represents arena count countTerm) (init : Represents arena initial initTerm)
    (tail : RepresentsList arena later laterTerms) :
    ∃ terms, Layout Term op terms countTerm initTerm laterTerms ∧
      RepresentsList arena refs terms ∧ refs.length = op.arity := by
  cases layout with
  | fold =>
      cases tail with
      | cons body empty =>
          cases empty
          exact ⟨_, .fold, .cons n (.cons init (.cons body .nil)), rfl⟩
  | loop =>
      cases tail with
      | cons motive tail =>
          cases tail with
          | cons body empty =>
              cases empty
              exact ⟨_, .loop, .cons n (.cons motive (.cons init (.cons body .nil))), rfl⟩

private theorem Layout.normalization (wf : UnifiedProgram.EnvWellFormed env)
    (before : Layout Term op terms n init tail) (after : Layout Term op residuals n' init' tail')
    (count : GhostNormalization env n n') (initial : GhostNormalization env init init')
    (later : ListRel (GhostNormalization env) tail tail') :
    GhostNormalization env (.node op terms) (.node op residuals) := by
  cases before with
  | fold =>
      cases after
      cases later with
      | cons body empty =>
          cases empty
          exact GhostNormalization.node wf (by decide) rfl (.cons count (.cons initial (.cons body .nil)))
  | loop =>
      cases after
      cases later with
      | cons motive rest =>
          cases rest with
          | cons body empty =>
              cases empty
              exact GhostNormalization.node wf (by decide) rfl
                (.cons count (.cons motive (.cons initial (.cons body .nil))))

private theorem Layout.atZero (layout : Layout Term op terms count initial later) (value : Term) :
    ∃ zeroTerms, Layout Term op zeroTerms (.natural 0) value later ∧
      ValueReduction.Root (.node op zeroTerms) value := by
  cases layout
  · exact ⟨_, .fold, .foldZero _ _⟩
  · exact ⟨_, .loop, .loopZero _ _ _⟩

private def next (first : Outcome α) (visit : State → α → Outcome β) : Outcome β :=
  match first.result with
  | .error reason => ⟨first.state, .error reason⟩
  | .ok value => visit first.state value

private theorem next_progress {α β : Type} {pending : Outcome α} {visit : State → α → Outcome β}
    (first : Progress limit state pending)
    (later : ∀ value, Progress limit pending.state (visit pending.state value)) :
    Progress limit state (next pending visit) := by
  cases status : pending.result with
  | error reason =>
      simp only [next, status]
      exact ⟨first.kept, first.monotone, first.bounded, fun _ _ found => by cases found⟩
  | ok value =>
      have continuation := later value
      simpa only [next, status] using
        (show Progress limit state (visit pending.state value) from
          ⟨first.kept.trans continuation.kept, Nat.le_trans first.monotone continuation.monotone,
            fun room => continuation.bounded (first.accepted room value status),
            fun room output done => continuation.accepted (first.accepted room value status) output done⟩)

abbrev Visit := State → List Nat → Outcome (List Nat)

/-- The immediate branch after the count and initializer have normalized.
Zero returns the selected initializer without starting the second batch. -/
def finish (visit : Visit) (state : State) (root : Nat) (op : Op) (before : List Nat)
    (count initial : Nat) (later : List Nat) (allowZero : Bool := true) : Outcome Nat :=
  if state.arena[count]? = some (.node (.natural 0) []) then
    if allowZero then ⟨state, .ok initial⟩ else ⟨state, .error (.outsideFragment root)⟩
  else next (visit state later) fun after suffix =>
    match arrange op count initial suffix with
    | none => ⟨after, .error (.outsideFragment root)⟩
    | some refs => nodeResult after root op before refs

/-- Both batches use the same child depth by construction of the visitor,
and the second sees the exact clock and arena left by the first. -/
def walk (visit : Visit) (state : State) (root : Nat) (op : Op) (before : List Nat)
    (allowZero : Bool := true) : Outcome Nat :=
  match splitOperands op before with
  | none => ⟨state, .error (.outsideFragment root)⟩
  | some (count, initial, later) =>
      next (visit state [count, initial]) fun after prefixRefs =>
        match prefixRefs with
        | [n, init] => finish visit after root op before n init later allowZero
        | _ => ⟨after, .error (.outsideFragment root)⟩

/-- Pay the iteration root tick before visiting either operand batch. -/
def runWith (visit : Nat → Visit) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let paid := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := paid.2}
  match paid.1 with
  | .error reason => ⟨entered, .error (.tick reason)⟩
  | .ok () =>
      match entered.arena[root]? with
      | some (.node op refs) => walk (visit (depth - 1)) entered root op refs
      | _ => ⟨entered, .error (.outsideFragment root)⟩

/-- Exact iteration-root entry with the existing child driver. -/
def run (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runWith (normalizeOperands limit) limit depth state root

theorem finish_zero (selected : state.arena[count]? = some (.node (.natural 0) [])) :
    finish visit state root op before count initial later = ⟨state, .ok initial⟩ := by
  simp only [finish, selected, ite_true]

theorem finish_nonzero (nonzero : state.arena[count]? ≠ some (.node (.natural 0) []))
    (done : visit state later = ⟨after, .ok suffix⟩)
    (arranged : arrange op count initial suffix = some refs) :
    finish visit state root op before count initial later = nodeResult after root op before refs := by
  simp only [finish, ite_eq_right nonzero, done, next, arranged]

theorem walk_progress
    (visit : Visit) (visitor : ∀ state refs, Progress limit state (visit state refs)) :
    Progress limit state (walk visit state root op before allowZero) := by
  unfold walk
  split
  · exact Progress.atState _ _
  · apply next_progress (visitor _ _)
    intro prefixRefs
    split
    · unfold finish
      split
      · split <;> exact Progress.atState _ _
      · apply next_progress (visitor _ _)
        intro suffix
        split
        · exact Progress.atState _ _
        · exact nodeResult_progress _ _ _ _ _ _
    · exact Progress.atState _ _

/-- A rejected root visit charges one tick. Every later error returns the
arena prefix and counter produced by the completed child visits. -/
theorem runWith_progress (visitor : ∀ depth state refs, Progress limit state (visit depth state refs))
    (depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runWith visit limit depth state root) := by
  let entered := {state with steps := state.steps + 1}
  have rejected (reason : Error) : Progress limit state (⟨entered, .error reason⟩ : Outcome Nat) :=
    ⟨.refl _, Nat.le_succ _, fun room => Nat.succ_le_succ room, fun _ _ success => by cases success⟩
  by_cases exhausted : limit < state.steps + 1
  · simpa only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, ite_true, entered] using
      rejected (.tick (.stepLimit root))
  by_cases nesting : depth = 0
  · simpa only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, nesting, ite_false, ite_true, entered] using
      rejected (.tick (.depthLimit root))
  by_cases invalid : state.arena.size ≤ root
  · simpa only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, ite_false, ite_true, entered] using
      rejected (.tick (.invalidReference root))
  cases found : state.arena[root]? with
  | none =>
      simpa only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, found, ite_false, entered] using
        rejected (.outsideFragment root)
  | some row =>
      cases row with
      | var index =>
          simpa only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, found, ite_false, entered] using
            rejected (.outsideFragment root)
      | node op refs =>
          simp only [runWith, NativeCoreUnsignedCancellation.tick, exhausted, nesting, invalid, found, ite_false]
          have walked := walk_progress (state := entered) (root := root) (op := op) (before := refs)
            (allowZero := true) (visit (depth - 1)) (visitor (depth - 1))
          have room := Nat.le_of_not_gt exhausted
          exact ⟨walked.kept, Nat.le_trans (Nat.le_succ _) walked.monotone,
            fun _ => walked.bounded room, fun _ => walked.accepted room⟩

theorem run_progress (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run limit depth state root) :=
  runWith_progress (normalizeOperands_progress limit) depth state root

/-- A typed step either visits retained children under the same iteration
constructor, or applies the existing zero-count value equation afterward. -/
inductive Change (env : Environment) : Term → Term → Prop where
  | retained : GhostNormalization env input output → Change env input output
  | zero : GhostNormalization env input midpoint → ValueReduction.Root midpoint output → Change env input output

theorem Change.preserves (step : Change env input output)
    (typed : LoanTyping.HasType env loans ctx mode input type) :
    LoanTyping.HasType env [] ctx true output type := by
  cases step with
  | retained converted => exact converted.raw.typed typed
  | zero converted contract => exact LoanTyping.value_root_ghost_preservation contract (converted.raw.typed typed)

private theorem expanded_value_root (step : ValueReduction.Root input output) :
    ValueReduction.Root (EnvironmentDelta.expand env input) (EnvironmentDelta.expand env output) := by
  cases step <;> simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs, EnvironmentDelta.expand]
  · exact .arithmetic _ _ _ (by assumption)
  · exact .strict _ _
  · exact .free _ _
  · exact .foldZero _ _
  · exact .loopZero _ _ _

theorem Change.preservesExpanded (step : Change env input output)
    (typed : LoanTyping.HasType env loans ctx mode (EnvironmentDelta.expand env input) type) :
    LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env output) type := by
  cases step with
  | retained converted => exact converted.expanded.typed typed
  | zero converted contract =>
      exact LoanTyping.value_root_ghost_preservation (expanded_value_root contract) (converted.expanded.typed typed)

structure Refines (env : Environment) (start : State) (term : Term) (output : Outcome Nat) (selected : Nat)
    (allowZero : Bool := true) : Prop where
  kept : Prefix start.arena output.state.arena
  backward : Backward start.arena → Backward output.state.arena
  value : ∃ value, Represents output.state.arena selected value ∧
    (if allowZero then Change env term value else GhostNormalization env term value)

abbrev VisitSound (env : Environment) (visit : Visit) : Prop :=
  ∀ {before refs terms selected}, RepresentsList before.arena refs terms →
    (visit before refs).result = .ok selected →
    let result := visit before refs
    Prefix before.arena result.state.arena ∧ (Backward before.arena → Backward result.state.arena) ∧
      selected.length = refs.length ∧
      ∃ values, RepresentsList result.state.arena selected values ∧ ListRel (GhostNormalization env) terms values

private theorem unchanged_changes (terms : List Term) : ListRel (GhostNormalization env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (.refl _) ih

private theorem finish_refines (wf : UnifiedProgram.EnvWellFormed env)
    (visitor : VisitSound env visit) (layout : Layout Term op terms oldCount oldInit oldTail)
    (sourceRow : state.arena[root]? = some (.node op before))
    (countRep : Represents state.arena n count) (initRep : Represents state.arena init initial)
    (tailRep : RepresentsList state.arena later oldTail)
    (countChange : GhostNormalization env oldCount count) (initChange : GhostNormalization env oldInit initial)
    (success : (finish visit state root op before n init later allowZero).result = .ok selected) :
    Refines env state (.node op terms) (finish visit state root op before n init later allowZero) selected allowZero := by
  by_cases zero : state.arena[n]? = some (.node (.natural 0) [])
  · cases allowZero
    · simp [finish, zero] at success
    · rw [finish_zero zero] at success ⊢
      cases success
      have zeroRep : Represents state.arena n (.natural 0) := .node zero rfl .nil
      have countIsZero := countRep.unique zeroRep
      subst count
      obtain ⟨_, middle, reduction⟩ := layout.atZero initial
      exact ⟨.refl _, id, _, initRep, Change.zero (layout.normalization wf middle countChange initChange
        (unchanged_changes _)) reduction⟩
  · simp only [finish, ite_eq_right zero] at success ⊢
    cases suffix : (visit state later).result with
    | error reason => simp [next, suffix] at success
    | ok refs =>
        simp only [next, suffix] at success ⊢
        cases recorded : arrange op n init refs with
        | none => simp [recorded] at success
        | some rebuilt =>
            simp only [recorded] at success ⊢
            obtain ⟨kept, backward, _, actual, represented, changes⟩ := visitor tailRep suffix
            obtain ⟨terms, normalized, allChildren, arity⟩ :=
              (arrange_sound recorded).arranged (countRep.frame kept) (initRep.frame kept) represented
            obtain ⟨laterFrame, laterBackward, residual, residualRep, reduced⟩ :=
              nodeResult_refines (kept.lookup sourceRow) allChildren arity success
            have changed := (layout.normalization wf normalized countChange initChange changes).trans reduced
            refine ⟨kept.trans laterFrame, fun valid => laterBackward (backward valid), residual, residualRep, ?_⟩
            cases allowZero
            · exact changed
            · exact Change.retained changed

private theorem prefix_result
    (children : RepresentsList arena [countRef, initRef] terms)
    (norms : ListRel (GhostNormalization env) [oldCount, oldInit] terms) :
    ∃ n init, Represents arena countRef n ∧ Represents arena initRef init ∧
      GhostNormalization env oldCount n ∧ GhostNormalization env oldInit init := by
  cases children with
  | cons count tail =>
      cases tail with
      | cons init empty =>
          cases empty
          cases norms with
          | cons countChange tail =>
              cases tail with
              | cons initChange _ => exact ⟨_, _, count, init, countChange, initChange⟩

/-- Exact typed reductions for the ordered root walk with any child visitor
that refines the represented inputs. -/
theorem walk_refines (wf : UnifiedProgram.EnvWellFormed env) (visitor : VisitSound env visit)
    (sourceRow : state.arena[root]? = some (.node op before))
    (represented : RepresentsList state.arena before terms)
    (success : (walk visit state root op before allowZero).result = .ok selected) :
    Refines env state (.node op terms) (walk visit state root op before allowZero) selected allowZero := by
  cases layout : splitOperands op before with
  | none => simp [walk, layout] at success
  | some triple =>
      obtain ⟨count, initial, later⟩ := triple
      simp only [walk, layout] at success ⊢
      obtain ⟨n, init, tail, termLayout, prefixRep, tailRep⟩ := (splitOperands_sound layout).represented represented
      cases first : (visit state [count, initial]).result with
      | error reason => simp [next, first] at success
      | ok prefixRefs =>
          simp only [next, first] at success ⊢
          obtain ⟨kept, backward, length, values, valuesRep, changes⟩ := visitor prefixRep first
          obtain ⟨countRef, initRef, rfl⟩ : ∃ a b, prefixRefs = [a,b] := by
            cases prefixRefs with
            | nil => contradiction
            | cons a rest =>
                cases rest with
                | nil => contradiction
                | cons b rest =>
                    cases rest with
                    | nil => exact ⟨a, b, rfl⟩
                    | cons => simp at length
          obtain ⟨newCount, newInit, countRep, initRep, countChange, initChange⟩ :=
            prefix_result valuesRep changes
          obtain ⟨more, moreBack, value⟩ := finish_refines wf visitor termLayout (kept.lookup sourceRow)
            countRep initRep (tailRep.frame kept) countChange initChange success
          exact ⟨kept.trans more, fun valid => moreBack (backward valid), value⟩

/-- Every successful pure Fold or Loop root visit has the exact original
Loan64 type, including the unmodified original motive application. -/
theorem runWith_refines (wf : UnifiedProgram.EnvWellFormed env) (visitor : ∀ depth, VisitSound env (visit depth))
    (represented : Represents state.arena root term)
    (success : (runWith visit limit depth state root).result = .ok selected) :
    Refines env state term (runWith visit limit depth state root) selected := by
  cases paid : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with
  | mk result clock =>
      cases result with
      | error reason => simp [runWith, paid] at success
      | ok charged =>
          cases charged
          cases represented with
          | var read => simp [runWith, paid, read] at success
          | node read _ children =>
              simp only [runWith, paid, read] at success ⊢
              obtain ⟨kept, backward, value⟩ := walk_refines
                (state := {state with steps := clock}) (visit := visit (depth - 1))
                (allowZero := true) wf (visitor (depth - 1)) read children success
              exact ⟨kept, backward, value⟩

theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (represented : Represents state.arena root term)
    (success : (run limit depth state root).result = .ok selected) :
    Refines env state term (run limit depth state root) selected :=
  runWith_refines (visit := normalizeOperands limit) wf
    (fun _ {_ _ _ _} source solved => normalizeOperands_refines wf source solved) represented success

theorem run_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (represented : Represents state.arena root term) (typed : LoanTyping.HasType env loans ctx mode term type)
    (success : (run limit depth state root).result = .ok selected) :
    ∃ residual, Represents (run limit depth state root).state.arena selected residual ∧
      LoanTyping.HasType env [] ctx true residual type := by
  obtain ⟨value, held, change⟩ := (run_refines wf represented success).value
  exact ⟨value, held, change.preserves typed⟩

open NativeProgramWire (Roots)

/-- Exact-byte mixed admission supplies the declaration type and the
backward graph for any successful iteration-root run of a stored value. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, valid⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, raw, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, change⟩ := run_refines valid source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, change.preservesExpanded typed⟩

namespace Examples

private def count : Term := .app (.lam false .u64 (.var 0)) (.natural 3)
private def initial : Term := .app (.lam false .i64 (.var 0)) (.integer 7)
private def motive : Term := .lam false .u64 .i64
private def body : Term := .lam false .u64
  (.lam true (.lt (.var 0) (.natural 3)) (.lam false .i64 (.var 0)))
private def loopSource : Term := .loop count motive initial body
private def foldSource : Term := .fold count initial body
private def loopResult : Term := .loop (.natural 3) motive (.integer 7) body
private def foldResult : Term := .fold (.natural 3) (.integer 7) body
private def originalType : Term := .app motive count

private def arena : Arena := #[.node .u64 [], .node .i64 [], .node (.natural 3) [], .var 0,
  .node (.lam false) [0, 3], .node .app [4, 2], .node (.integer 7) [], .node (.lam false) [1, 3],
  .node .app [7, 6], .node (.lam false) [0, 1], .node .lt [3, 2], .node (.lam true) [10, 7],
  .node (.lam false) [0, 11], .node .loop [5, 9, 8, 12], .node .fold [5, 8, 12],
  .node (.natural 0) [], .node .loop [15, 9, 6, 12]]
private def state : State := ⟨arena, 0⟩
private def env : Environment := Environment.empty
private theorem checkedEnvironment : UnifiedProgram.EnvWellFormed env :=
  UnifiedProgram.EnvWellFormed.empty

/-- Both beta redexes are normalized, but the counted iteration remains
in the graph. Loop retains its exact source motive application as its type. -/
theorem checked_loop_rebuilds_at_original_type :
    let output := run 64 20 state 13
    output = ⟨⟨arena.push (.node .loop [2, 9, 6, 12]), 29⟩, .ok 17⟩ ∧
      LoanTyping.HasType env [] [] true loopResult originalType := by
  have accepted : LoanTyping.Checker.check 56 env [] [] true loopSource originalType = true := by cbv
  have sourceRep : Represents arena 13 loopSource := decode_sound (fuel := 16) (by cbv)
  have executed : run 64 20 state 13 = ⟨⟨arena.push (.node .loop [2, 9, 6, 12]), 29⟩, .ok 17⟩ := by cbv
  obtain ⟨residual, outputRep, typed⟩ := run_preserves checkedEnvironment sourceRep
    (LoanTyping.Checker.check_sound accepted) (congrArg Outcome.result executed)
  rw [executed] at outputRep
  have expected : Represents (arena.push (.node .loop [2, 9, 6, 12])) 17 loopResult :=
    decode_sound (fuel := 16) (by cbv)
  exact ⟨executed, outputRep.unique expected ▸ typed⟩

/-- The same native schedule for Fold omits only the motive visit and
commits the smaller three-operand row at the unchanged scalar type. -/
theorem checked_fold_rebuilds_at_original_type :
    let output := run 64 20 state 14
    output = ⟨⟨arena.push (.node .fold [2, 6, 12]), 26⟩, .ok 17⟩ ∧
      LoanTyping.HasType env [] [] true foldResult .i64 := by
  have accepted : LoanTyping.Checker.check 56 env [] [] true foldSource .i64 = true := by cbv
  have sourceRep : Represents arena 14 foldSource := decode_sound (fuel := 16) (by cbv)
  have executed : run 64 20 state 14 = ⟨⟨arena.push (.node .fold [2, 6, 12]), 26⟩, .ok 17⟩ := by cbv
  obtain ⟨residual, outputRep, typed⟩ := run_preserves checkedEnvironment sourceRep
    (LoanTyping.Checker.check_sound accepted) (congrArg Outcome.result executed)
  rw [executed] at outputRep
  have expected : Represents (arena.push (.node .fold [2, 6, 12])) 17 foldResult :=
    decode_sound (fuel := 16) (by cbv)
  exact ⟨executed, outputRep.unique expected ▸ typed⟩

/-- Exhaustion next occurs at the motive, after the count and initializer.
The empty iteration succeeds before spelling out either remaining visit. -/
theorem shared_clock_keeps_native_visit_order :
    run 17 20 state 13 = ⟨⟨arena, 18⟩, .error (.tick (.stepLimit 9))⟩ ∧
      run 3 2 state 16 = ⟨⟨arena, 3⟩, .ok 6⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreIterationNormal
