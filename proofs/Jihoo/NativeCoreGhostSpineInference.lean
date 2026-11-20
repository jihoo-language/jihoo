import Jihoo.NativeCoreTypedEqual
import Jihoo.NativeLoanTypeUniqueness

/-! Ghost Core.infer on local and global heads, dependent application spines,
and primitive forms with fixed operand types. A successful checker records
which pairs of normalized type roots identity accepted. The trace has no
effect on graph allocation or work. -/
namespace Jihoo.NativeKernel.NativeCoreGhostSpineInference

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreCompare (FullyRetained)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand expandArgs)

structure GraphBinding where
  typeRoot : Nat
  erased : Bool
  deriving Repr

structure Inferred where
  typeRoot : Nat
  compared : List (Nat × Nat)
  deriving Repr

abbrev Visit := State → Nat → Outcome Nat
abbrev Infer := State → Nat → Outcome Inferred
abbrev NormalAt := Nat → Visit

private def liftTransform (result : NativeCoreTransformExact.Outcome Nat) : Outcome Nat :=
  ⟨result.state, result.result.mapError .substitution⟩

private theorem liftTransform_success (success : (liftTransform result).result = .ok selected) :
    result.result = .ok selected := by
  cases found : result.result <;> simp [liftTransform, found, Except.mapError] at success ⊢
  exact success

private theorem liftTransform_progress (progress : NativeCoreTransformExact.Progress limit state result) :
    Progress limit state (liftTransform result) :=
  ⟨progress.kept, progress.monotone, progress.bounded, fun room selected found =>
    progress.accepted room selected (liftTransform_success found)⟩

private def shiftType (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.run limit depth state root (.shift amount) 0)

private def instantiate (limit depth : Nat) (state : State) (result argument : Nat) : Outcome Nat :=
  liftTransform (NativeCoreTransformExact.substitute limit depth state result argument)

private theorem shiftType_progress (limit depth : Nat) (state : State) (root amount : Nat) :
    Progress limit state (shiftType limit depth state root amount) :=
  liftTransform_progress (NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0)

private theorem instantiate_progress (limit depth : Nat) (state : State) (result argument : Nat) :
    Progress limit state (instantiate limit depth state result argument) :=
  liftTransform_progress (NativeCoreTransformExact.substitute_progress limit depth state result argument)

private def plain (root : Nat) : Inferred := ⟨root, []⟩

private def discard (state : State) (root : Nat) : Outcome α :=
  ⟨state, .error (.outsideFragment root)⟩

private def emit (state : State) (op : Op) : Outcome Inferred :=
  let result := append state op []
  ⟨result.state, result.result.map plain⟩

private def shiftInferred (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Inferred :=
  let shifted := shiftType limit depth state root amount
  ⟨shifted.state, shifted.result.map plain⟩

private def tick (limit depth : Nat) (state : State) (root : Nat)
    (entered : State → Outcome Inferred) : Outcome Inferred :=
  let (paid, steps) := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let state := {state with steps}
  match paid with
  | .error reason => ⟨state, .error (.tick reason)⟩
  | .ok () => entered state

/-- Core.require normalizes the inferred argument type, then the expected
domain, and uses identity on their live roots. The original argument
reference, not either type root, is later substituted into the codomain. -/
def requireTypes (normal : Visit) (limit depth : Nat) (state : State)
    (actual expected argument : Nat) : Outcome (Nat × Nat) :=
  (normal state actual).next fun afterLeft left =>
    (normal afterLeft expected).next fun afterRight right =>
      (NativeCoreTypedEqual.identify limit depth afterRight left right).next fun afterIdentity same =>
        if same then ⟨afterIdentity, .ok (left, right)⟩ else discard afterIdentity argument

/-- Check each operand before visiting the next one. All operands share the
single expected type node just emitted by the native inference branch. -/
private def requireOperands (infer : Infer) (normal : Visit) (limit depth expected : Nat) :
    State → List Nat → Outcome (List (Nat × Nat))
  | state, [] => ⟨state, .ok []⟩
  | state, root :: rest =>
      (infer state root).next fun inferred type =>
        (requireTypes normal limit depth inferred type.typeRoot expected root).next fun checked pair =>
          (requireOperands infer normal limit depth expected checked rest).next fun after comparisons =>
            ⟨after, .ok (type.compared ++ pair :: comparisons)⟩

/-- Native primitive branches synthesize the expected operand type, check
operands at child depth, then append the raw result type. -/
private def inferFixed (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (operand : Op) (args : List Nat) (output : Op) (refs : List Nat) : Outcome Inferred :=
  (append state operand []).next fun emitted expected =>
    (requireOperands infer normal limit depth expected emitted args).next fun checked comparisons =>
      (append checked output refs).next fun after root => ⟨after, .ok ⟨root, comparisons⟩⟩

/-- Post-tick App inference in ghost mode. Every recursive call here uses
the same child depth. The inferred codomain is returned immediately. -/
def inferApp (infer : Infer) (normal : Visit) (limit childDepth : Nat) (state : State)
    (function argument : Nat) : Outcome Inferred :=
  (infer state function).next fun afterFunction functionType =>
    (normal afterFunction functionType.typeRoot).next fun afterExpose functionRoot =>
      match afterExpose.arena[functionRoot]? with
      | some (.node (.pi _) [domain, result]) =>
          (infer afterExpose argument).next fun afterArgument argumentType =>
            (requireTypes normal limit childDepth afterArgument argumentType.typeRoot domain argument).next
              fun afterCheck pair =>
                (instantiate limit childDepth afterCheck result argument).next fun afterSubstitution output =>
                  ⟨afterSubstitution, .ok ⟨output, functionType.compared ++ argumentType.compared ++ [pair]⟩⟩
      | _ => discard afterExpose function

/-- The list reverses the compiler's physical list of bindings so that
de Bruijn index zero looks up the newest binding. Visibility is shared
by inference and all type normalization visits. -/
def runWith (normal : NormalAt) (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer
  | 0, _, state, root => tick limit 0 state root (fun entered => discard entered root)
  | depth + 1, ctx, state, root =>
      tick limit (depth + 1) state root fun entered =>
        match entered.arena[root]? with
        | some (.var index) =>
            match ctx[index]? with
            | some binding => shiftInferred limit depth entered binding.typeRoot (index + 1)
            | none => discard entered root
        | some (.node (.global index) []) =>
            if index < visible then
              match roots[index]? with
              | some declaration => shiftInferred limit depth entered declaration.typeRoot ctx.length
              | none => discard entered root
            else ⟨entered, .error (.invisibleGlobal root)⟩
        | some (.node (.universe level) []) =>
            if level < 32 then emit entered (.universe (level + 1)) else discard entered root
        | some (.node .prop []) | some (.node .u64 []) | some (.node .i64 []) =>
            emit entered (.universe 0)
        | some (.node (.natural value) []) =>
            if value < 2^64 then emit entered .u64 else discard entered root
        | some (.node (.integer value) []) =>
            if -(2^63 : Int) ≤ value ∧ value < (2^63 : Int) then emit entered .i64 else discard entered root
        | some (.node .array [n]) | some (.node .buffer [n]) =>
            inferFixed (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered
              .u64 [n] (.universe 0) []
        | some (.node .eq [a, b]) | some (.node .lt [a, b]) =>
            inferFixed (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .prop []
        | some (.node .refl [a]) =>
            inferFixed (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered
              .u64 [a] .eq [a, a]
        | some (.node .uadd [a, b]) =>
            inferFixed (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered
              .u64 [a, b] .u64 []
        | some (.node (.arith _) [a, b]) =>
            inferFixed (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered
              .i64 [a, b] .i64 []
        | some (.node .app [f, a]) =>
            inferApp (runWith normal roots visible limit depth ctx) (normal depth) limit depth entered f a
        | _ => discard entered root

def run (roots : List Roots) (visible limit : Nat) : Nat → List GraphBinding → Infer :=
  runWith (NativeCoreNestedAliases.run roots visible limit) roots visible limit

private theorem next_progress {before : Outcome α} {later : State → α → Outcome β}
    (prior : Progress limit state before) (room : state.steps ≤ limit)
    (following : ∀ value, before.result = .ok value → before.state.steps ≤ limit →
      Progress limit before.state (later before.state value)) :
    Progress limit state (before.next later) := by
  cases found : before.result with
  | error reason =>
      simp only [Outcome.next, found]
      exact ⟨prior.kept, prior.monotone, prior.bounded, fun _ _ impossible => by cases impossible⟩
  | ok value =>
      have within := prior.accepted room value found
      have after := following value found within
      simp only [Outcome.next, found]
      exact ⟨prior.kept.trans after.kept, Nat.le_trans prior.monotone after.monotone,
        fun _ => after.bounded within, fun _ output done => after.accepted within output done⟩

private theorem identify_progress (room : state.steps ≤ limit) :
    Progress limit state (NativeCoreTypedEqual.identify limit depth state left right) := by
  have bounds := NativeCoreIdentical.runArena_step_bounds (arena := state.arena)
    (depth := depth) (a := left) (b := right) room
  generalize found : NativeCoreIdentical.runArena state.arena limit depth state.steps left right = outcome at bounds ⊢
  rcases outcome with ⟨result, spent⟩
  simp only [NativeCoreTypedEqual.identify, found]
  refine ⟨.refl _, bounds.1, fun _ => bounds.2.1, fun _ value success => ?_⟩
  cases result with
  | error reason => simp [Except.mapError] at success
  | ok answer =>
      have found : answer = value := Except.ok.inj (by simpa only [Except.mapError] using success)
      exact bounds.2.2 value (congrArg Except.ok found)

theorem requireTypes_progress
    (metered : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (requireTypes normal limit depth state actual expected argument) := by
  apply next_progress (metered _ _ room) room
  intro left _ leftRoom
  apply next_progress (metered _ _ leftRoom) leftRoom
  intro right _ rightRoom
  apply next_progress (identify_progress rightRoom) rightRoom
  intro same _ _
  cases same <;> exact Progress.atState _ _

private theorem requireOperands_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (requireOperands infer normal limit depth expected state args) := by
  induction args generalizing state with
  | nil => exact Progress.atState _ _
  | cons root rest ih =>
      apply next_progress (infers _ _ room) room
      intro type _ inferredRoom
      apply next_progress (requireTypes_progress normalizes inferredRoom) inferredRoom
      intro pair _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

private theorem inferFixed_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferFixed infer normal limit depth state operand args output refs) := by
  apply next_progress (append_progress _ _ _) room
  intro expected _ emittedRoom
  apply next_progress (requireOperands_progress infers normalizes emittedRoom) emittedRoom
  intro comparisons _ _
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

theorem inferApp_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, state.steps ≤ limit → Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferApp infer normal limit childDepth state function argument) := by
  apply next_progress (infers _ _ room) room
  intro functionType _ functionRoom
  apply next_progress (normalizes _ _ functionRoom) functionRoom
  intro functionRoot _ exposedRoom
  split
  · apply next_progress (infers _ _ exposedRoom) exposedRoom
    intro argumentType _ argumentRoom
    apply next_progress (requireTypes_progress normalizes argumentRoom) argumentRoom
    intro pair _ _
    exact (instantiate_progress _ _ _ _ _).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem tick_progress
    (after : ∀ entered, entered.steps ≤ limit → Progress limit entered (visit entered)) :
    Progress limit state (tick limit depth state root visit) := by
  have rejected (why : NativeCoreIdentical.Error) :
      Progress limit state (⟨{state with steps := state.steps + 1}, .error (.tick why)⟩ : Outcome Inferred) :=
    ⟨.refl _, Nat.le_succ _, Nat.succ_le_succ, fun _ _ impossible => by cases impossible⟩
  by_cases outside : limit < state.steps + 1
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_left outside] using rejected (.stepLimit root)
  by_cases tooDeep : depth = 0
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_left tooDeep] using
      rejected (.depthLimit root)
  by_cases missing : state.arena.size ≤ root
  · simpa only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_right tooDeep,
      ite_eq_left missing] using
      rejected (.invalidReference root)
  have room : state.steps + 1 ≤ limit := by omega
  have continued := after {state with steps := state.steps + 1} room
  simp only [tick, NativeCoreUnsignedCancellation.tick, ite_eq_right outside, ite_eq_right tooDeep, ite_eq_right missing]
  exact ⟨continued.kept, Nat.le_trans (Nat.le_succ _) continued.monotone,
    fun _ => continued.bounded room, fun _ => continued.accepted room⟩

/-- Progress is a statement about the executable graph path, including
rejected steps and failures before the eventual type has been instantiated. -/
theorem runWith_progress {normal : NormalAt} {roots : List Roots} {bindings : List GraphBinding}
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWith normal roots visible limit depth bindings state root) := by
  induction depth generalizing state root with
  | zero => exact tick_progress (fun _ _ => Progress.atState _ _)
  | succ depth ih =>
      simp only [runWith]
      apply tick_progress
      intro entered within
      split
      · split
        · exact (shiftType_progress _ _ _ _ _).map plain
        · exact Progress.atState _ _
      · split
        · split
          · exact (shiftType_progress _ _ _ _ _).map plain
          · exact Progress.atState _ _
        · exact Progress.atState _ _
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      · exact (append_progress _ _ _).map plain
      · exact (append_progress _ _ _).map plain
      · exact (append_progress _ _ _).map plain
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      · split
        · exact (append_progress _ _ _).map plain
        · exact Progress.atState _ _
      all_goals first
        | exact inferFixed_progress (fun _ _ room => ih room)
            (fun state ref _ => normalProgress depth state ref) within
        | exact inferApp_progress (fun _ _ room => ih room)
            (fun state ref _ => normalProgress depth state ref) within
        | exact Progress.atState _ _

theorem run_progress {roots : List Roots} {bindings : List GraphBinding}
    (room : state.steps ≤ limit) :
    Progress limit state (run roots visible limit depth bindings state root) :=
  runWith_progress (NativeCoreNestedAliases.run_progress roots visible limit) room

/-- Each graph row records the written domain in pre-binder scope. -/
def BindingRep (env : Environment) (arena : Arena) (row : GraphBinding) (binding : Binding) : Prop :=
  ∃ term, Represents arena row.typeRoot term ∧ binding.ty = expand env term ∧ binding.erased = row.erased

inductive ContextRep (env : Environment) (arena : Arena) : List GraphBinding → Context → Prop where
  | nil : ContextRep env arena [] []
  | cons : BindingRep env arena row binding → ContextRep env arena rows ctx →
      ContextRep env arena (row :: rows) (binding :: ctx)

theorem ContextRep.frame (represented : ContextRep env arena rows ctx) (kept : Prefix arena after) :
    ContextRep env after rows ctx := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih =>
      obtain ⟨term, source, ty, flag⟩ := head
      exact .cons ⟨term, source.frame kept, ty, flag⟩ ih

theorem ContextRep.lookup_type (represented : ContextRep env arena rows ctx)
    {index : Nat} (found : rows[index]? = some row) :
    ∃ term, Represents arena row.typeRoot term ∧
      lookup ctx index = some ⟨(expand env term).rename (fun x => x + (index + 1)), row.erased⟩ := by
  induction represented generalizing index with
  | nil => simp at found
  | cons headRep tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst row
          obtain ⟨term, source, ty, flag⟩ := headRep
          exact ⟨term, source, by simp only [lookup, ty, flag]⟩
      | succ k =>
          obtain ⟨term, source, atIndex⟩ := ih (by simpa using found)
          refine ⟨term, source, ?_⟩
          simp only [lookup, atIndex, Option.map_some, Term.rename_comp, Nat.succ_eq_add_one, Nat.add_assoc]

private theorem represented_at {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (found : roots[index]? = some row) :
    ∃ source, definitions[index]? = some source ∧ RepresentsDefinition arena row source := by
  induction aligned generalizing index with
  | nil => simp at found
  | @cons _ source _ _ head _ tail =>
      cases index with
      | zero => cases found; exact ⟨source, rfl, head⟩
      | succ index => exact tail found

private theorem type_expansion_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : definitions[index]? = some source) :
    ∃ entry, env.globals[index]? = some entry ∧ GlobalEnvironment.Expansion env.globals source.type entry.type := by
  induction history with
  | empty => simp at found
  | @definition definitions declarations env raw entry history checked ih =>
      by_cases earlier : index < definitions.length
      · rw [List.getElem?_append_left earlier] at found
        obtain ⟨previous, previousFound, expanded⟩ := ih found
        have inside : index < env.globals.size := history.globalLength.symm ▸ earlier
        refine ⟨previous, ?_, expanded.extend entry⟩
        rw [Array.getElem?_eq_getElem inside] at previousFound
        exact (Array.getElem?_push_lt (x := entry) inside).trans previousFound
      · have bound := (List.getElem?_eq_some_iff.mp found).1
        have atEnd : index = definitions.length := by simp only [List.length_append, List.length_singleton] at bound; omega
        subst index
        have same : raw = source := by simpa using found
        subst source
        exact ⟨entry, by rw [← history.globalLength, Array.getElem?_push_size], checked.typeExpansion.extend entry⟩
  | family _ _ ih => exact ih found

private theorem checked_type_at {index : Nat} (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions arena roots definitions) (found : roots[index]? = some row) :
    ∃ entry written, env.globals[index]? = some entry ∧ Represents arena row.typeRoot written ∧
      expand env written = entry.type := by
  obtain ⟨source, sourceFound, represented⟩ := represented_at aligned found
  obtain ⟨entry, recorded, expanded⟩ := type_expansion_at history sourceFound
  exact ⟨entry, source.type, recorded, represented.1, EnvironmentDelta.expansion_eq_expand expanded⟩

private theorem plain_success {original : Outcome Nat} (success : (original.result.map plain) = .ok answer) :
    ∃ selected, original.result = .ok selected ∧ answer = plain selected := by
  cases found : original.result with
  | error reason => simp [found, Except.map] at success
  | ok selected =>
      exact ⟨selected, rfl, (Except.ok.inj (by simpa only [found, Except.map] using success)).symm⟩

private theorem shiftType_refines (source : Represents state.arena root written)
    (success : (shiftType limit depth state root amount).result = .ok selected) :
    let output := shiftType limit depth state root amount
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected (written.rename (fun x => x + amount)) := by
  obtain ⟨kept, backward, residual, expected, held⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift amount) (binders := 0) (value := written)
      source trivial (liftTransform_success success)).1
  change PartialRenaming.shift amount 0 written = some residual at expected
  rw [PartialRenaming.shift_nonnegative (by omega)] at expected
  have shape : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun x => x + amount := by
    funext index
    simp [PartialRenaming.raiseIndex]
  rw [shape] at expected
  cases expected
  exact ⟨kept, backward, held⟩

private theorem tick_success (success : (tick limit depth state root visit).result = .ok selected) :
    tick limit depth state root visit = visit {state with steps := state.steps + 1} ∧ state.steps + 1 ≤ limit := by
  by_cases outside : limit < state.steps + 1
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside] at success
  by_cases tooDeep : depth = 0
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep] at success
  by_cases missing : state.arena.size ≤ root
  · simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep, missing] at success
  exact ⟨by simp [tick, NativeCoreUnsignedCancellation.tick, outside, tooDeep, missing], by omega⟩

def PairRetained (arena : Arena) (pair : Nat × Nat) : Prop :=
  ∃ first second, Represents arena pair.1 first ∧ Represents arena pair.2 second ∧
    FullyRetained first ∧ FullyRetained second

def RetainedComparisons (arena : Arena) (answer : Inferred) : Prop :=
  ∀ pair ∈ answer.compared, PairRetained arena pair

private theorem identify_true
    (left : Represents state.arena a first) (right : Represents state.arena b second)
    (success : (NativeCoreTypedEqual.identify limit depth state a b).result = .ok true) :
    (NativeCoreTypedEqual.identify limit depth state a b).state.arena = state.arena ∧
      NativeCoreCompare.project first = NativeCoreCompare.project second := by
  rcases compared : NativeCoreIdentical.runArena state.arena limit depth state.steps a b with ⟨result, steps⟩
  cases result with
  | error reason => simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
  | ok flag =>
      simp [NativeCoreTypedEqual.identify, compared, Except.mapError] at success
      subst flag
      exact ⟨by simp [NativeCoreTypedEqual.identify, compared],
        (NativeCoreIdentical.runArena_refines left right compared).mp rfl⟩

/-- Retention is evidence about the actual two comparison outcomes.
Full syntax equality reflects their projected identity, and the normalizer
supplies conversion from each original type to its corresponding outcome. -/
theorem requireTypes_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (leftRep : Represents state.arena actual actualType) (rightRep : Represents state.arena expected expectedType)
    (success : (requireTypes normal limit depth state actual expected argument).result = .ok pair)
    (ambient : Prefix (requireTypes normal limit depth state actual expected argument).state.arena final)
    (retained : PairRetained final pair) :
    let output := requireTypes normal limit depth state actual expected argument
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      LoanTyping.Conversion.Conv env (expand env actualType) (expand env expectedType) := by
  unfold requireTypes at success ambient ⊢
  obtain ⟨a, firstOk, firstNext⟩ := Outcome.next_success success
  obtain ⟨firstKept, firstBack, first, firstRep, firstChange⟩ := normalSound onBase leftRep firstOk
  rw [firstNext] at success ambient ⊢
  obtain ⟨b, secondOk, secondNext⟩ := Outcome.next_success success
  obtain ⟨secondKept, secondBack, second, secondRep, secondChange⟩ :=
    normalSound (onBase.trans firstKept) (rightRep.frame firstKept) secondOk
  rw [secondNext] at success ambient ⊢
  obtain ⟨flag, identical, identityNext⟩ := Outcome.next_success success
  rw [identityNext] at success ambient ⊢
  cases flag with
  | false => simp [discard] at success
  | true =>
      simp at success
      subst pair
      have firstFinal := firstRep.frame secondKept
      obtain ⟨unchanged, same⟩ := identify_true firstFinal secondRep identical
      simp [unchanged] at ambient ⊢
      obtain ⟨left, right, leftRep, rightRep, leftKept, rightKept⟩ := retained
      have sameLeft := (firstFinal.frame ambient).unique leftRep
      have sameRight := (secondRep.frame ambient).unique rightRep
      have syntactic : first = second := NativeCoreCompare.project_injective_of_fully_retained
        (sameLeft.symm ▸ leftKept) (sameRight.symm ▸ rightKept) same
      refine ⟨firstKept.trans secondKept, secondBack ∘ firstBack, ?_⟩
      have converted : LoanTyping.Conversion.Conv env (expand env actualType) (expand env first) :=
        firstChange.converted
      rw [syntactic] at converted
      exact converted.trans secondChange.converted.symm

private theorem binary_read
    (represented : Represents arena root term) (read : arena[root]? = some (.node op [a, b])) :
    ∃ first second, term = .node op [first, second] ∧ Represents arena a first ∧ Represents arena b second := by
  cases represented with
  | var variableRead => rw [read] at variableRead; cases variableRead
  | node found _ children =>
      rw [read] at found
      cases found
      cases children with
      | cons first tail =>
        cases tail with
        | cons second tail =>
          cases tail
          exact ⟨_, _, rfl, first, second⟩

structure Refines (env : Environment) (arena : Arena) (ctx : Context) (source : Term)
    (outcome : Outcome Inferred) (answer : Inferred) : Prop where
  kept : Prefix arena outcome.state.arena
  backward : Backward arena → Backward outcome.state.arena
  inferred : ∃ type, Represents outcome.state.arena answer.typeRoot type ∧
    LoanTyping.HasType env [] ctx true (expand env source) (expand env type)

def InferSound (env : Environment) (base : Arena) (ctx : Context) (limit : Nat) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final →
    RetainedComparisons final answer → Refines env state.arena ctx term (visit state root) answer

private theorem requireOperands_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (operands : RepresentsList state.arena args terms) (expectedRep : Represents state.arena expected type)
    (success : (requireOperands infer normal limit depth expected state args).result = .ok comparisons)
    (ambient : Prefix (requireOperands infer normal limit depth expected state args).state.arena final)
    (retained : ∀ pair ∈ comparisons, PairRetained final pair) :
    let outcome := requireOperands infer normal limit depth expected state args
    Prefix state.arena outcome.state.arena ∧ (Backward state.arena → Backward outcome.state.arena) ∧
      ∀ term ∈ terms, LoanTyping.HasType env [] ctx true (expand env term) (expand env type) := by
  induction args generalizing state terms comparisons with
  | nil =>
      cases operands
      exact ⟨.refl _, id, by simp⟩
  | cons root rest ih =>
      cases operands with
      | @cons _ term _ tail head tailRep =>
          simp only [requireOperands] at success ambient ⊢
          obtain ⟨inferred, inferredOk, inferredNext⟩ := Outcome.next_success success
          rw [inferredNext] at success ambient ⊢
          obtain ⟨pair, checkedOk, checkedNext⟩ := Outcome.next_success success
          rw [checkedNext] at success ambient ⊢
          obtain ⟨remaining, restOk, restNext⟩ := Outcome.next_success success
          rw [restNext] at success ambient ⊢
          simp only [Except.ok.injEq] at success
          subst comparisons
          have inferredProgress := childProgress state root room
          have inferredRoom := inferredProgress.accepted room inferred inferredOk
          let checked := requireTypes normal limit depth (infer state root).state inferred.typeRoot expected root
          have checkedProgress := requireTypes_progress (expected := expected) (actual := inferred.typeRoot)
            (argument := root) (depth := depth) (fun state ref _ => normalProgress state ref) inferredRoom
          have checkedRoom := checkedProgress.accepted inferredRoom pair checkedOk
          have restProgress := requireOperands_progress (expected := expected) (depth := depth) (args := rest)
            childProgress (fun state ref _ => normalProgress state ref) checkedRoom
          have checkedFinal := restProgress.kept.trans ambient
          have inferredFinal := checkedProgress.kept.trans checkedFinal
          obtain ⟨_, inferredBack, actualType, actualRep, typed⟩ := childSound onBase room head inferredOk
            inferredFinal (fun comparison found => retained comparison (List.mem_append_left _ found))
          obtain ⟨kept, checkedBack, conversion⟩ := requireTypes_refines normalSound
            (onBase.trans inferredProgress.kept) actualRep (expectedRep.frame inferredProgress.kept)
            checkedOk checkedFinal (retained pair (List.mem_append_right _ (List.mem_cons_self)))
          have throughCheck := inferredProgress.kept.trans kept
          obtain ⟨restKept, restBack, restTyped⟩ := ih (state := checked.state)
            (onBase.trans throughCheck) checkedRoom (tailRep.frame throughCheck) (expectedRep.frame throughCheck)
            restOk ambient (fun comparison found => retained comparison
              (List.mem_append_right _ (List.mem_cons_of_mem _ found)))
          refine ⟨throughCheck.trans restKept, restBack ∘ checkedBack ∘ inferredBack, ?_⟩
          intro operand member
          rcases List.mem_cons.mp member with rfl | previous
          · exact typed.convert conversion
          · exact restTyped operand previous

private theorem inferFixed_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (operands : RepresentsList state.arena args terms) (operandArity : operand.arity = 0)
    (resultRefs : RepresentsList state.arena refs resultTerms) (resultArity : refs.length = output.arity)
    (success : (inferFixed infer normal limit depth state operand args output refs).result = .ok answer)
    (ambient : Prefix (inferFixed infer normal limit depth state operand args output refs).state.arena final)
    (retained : RetainedComparisons final answer)
    (typing : (∀ term ∈ terms, LoanTyping.HasType env [] ctx true (expand env term) (expand env (.node operand []))) →
      LoanTyping.HasType env [] ctx true (expand env source) (expand env (.node output resultTerms))) :
    Refines env state.arena ctx source (inferFixed infer normal limit depth state operand args output refs) answer := by
  unfold inferFixed at success ambient ⊢
  obtain ⟨expected, emittedOk, emittedNext⟩ := Outcome.next_success success
  rw [emittedNext] at success ambient ⊢
  obtain ⟨comparisons, checkedOk, checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨root, resultOk, resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  obtain ⟨emittedKept, emittedBack, expectedRep⟩ := append_refines .nil operandArity.symm emittedOk
  have emittedRoom := (append_progress state operand []).accepted room expected emittedOk
  let checks := requireOperands infer normal limit depth expected (append state operand []).state args
  have resultProgress := append_progress (limit := limit) checks.state output refs
  obtain ⟨checkedKept, checkedBack, typedOperands⟩ := requireOperands_refines normalSound normalProgress childSound
    childProgress (onBase.trans emittedKept) emittedRoom (operands.frame emittedKept) expectedRep checkedOk
    (resultProgress.kept.trans ambient) retained
  have throughChecks := emittedKept.trans checkedKept
  obtain ⟨resultKept, resultBack, outputRep⟩ := append_refines (resultRefs.frame throughChecks) resultArity resultOk
  exact ⟨throughChecks.trans resultKept, resultBack ∘ checkedBack ∘ emittedBack, _, outputRep, typing typedOperands⟩

/-- A successful application returns the captured Pi body instantiated with
the original graph operand. The proof exposes a real function type and
reflects the accepted argument comparison under its retention evidence. -/
theorem inferApp_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fn : Represents state.arena function f) (arg : Represents state.arena argument a)
    (success : (inferApp infer normal limit depth state function argument).result = .ok answer)
    (ambient : Prefix (inferApp infer normal limit depth state function argument).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.app f a) (inferApp infer normal limit depth state function argument) answer := by
  unfold inferApp at success ambient ⊢
  obtain ⟨fType, fOk, fNext⟩ := Outcome.next_success success
  rw [fNext] at success ambient ⊢
  obtain ⟨exposed, exposedOk, exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  case h_2 => simp [discard] at success
  case h_1 erased domain result read =>
    simp only [read] at ambient
    obtain ⟨aType, argOk, argNext⟩ := Outcome.next_success success
    rw [argNext] at success ambient ⊢
    obtain ⟨pair, checkedOk, checkedNext⟩ := Outcome.next_success success
    rw [checkedNext] at success ambient ⊢
    obtain ⟨selected, substitutedOk, substitutedNext⟩ := Outcome.next_success success
    rw [substitutedNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    have progressF := childProgress state function room
    have fRoom := progressF.accepted room fType fOk
    have progressPi := normalProgress (infer state function).state fType.typeRoot
    have exposedRoom := progressPi.accepted fRoom exposed exposedOk
    let exposedState := (normal (infer state function).state fType.typeRoot).state
    have progressA := childProgress exposedState argument exposedRoom
    have argRoom := progressA.accepted exposedRoom aType argOk
    have progressCheck := requireTypes_progress (actual := aType.typeRoot) (expected := domain)
      (argument := argument) (depth := depth) (fun state ref _ => normalProgress state ref) argRoom
    let afterCheck := (requireTypes normal limit depth (infer exposedState argument).state
      aType.typeRoot domain argument).state
    have progressSub := instantiate_progress limit depth afterCheck result argument
    change Prefix (instantiate limit depth afterCheck result argument).state.arena final at ambient
    have checkFinal := progressSub.kept.trans ambient
    have argFinal := progressCheck.kept.trans checkFinal
    have funFinal := progressPi.kept.trans (progressA.kept.trans argFinal)
    have ⟨_, fBack, rawFunctionType, fRep, fTyped⟩ :=
      childSound onBase room fn fOk funFinal (fun check member =>
        retained check (List.mem_append_left _ (List.mem_append_left _ member)))
    obtain ⟨_, piBack, exposedType, piRef, converted⟩ := normalSound
      (onBase.trans progressF.kept) fRep exposedOk
    obtain ⟨dom, cod, sameType, domRep, codRep⟩ := binary_read piRef read
    have throughPi := progressF.kept.trans progressPi.kept
    obtain ⟨_, argBack, rawArgumentType, aRep, aTyped⟩ := childSound (onBase.trans throughPi) exposedRoom
      (arg.frame throughPi) argOk argFinal (fun check member =>
        retained check (List.mem_append_left _ (List.mem_append_right _ member)))
    have throughArgument := throughPi.trans progressA.kept
    obtain ⟨_, checkBack, compatible⟩ := requireTypes_refines normalSound (onBase.trans throughArgument)
      aRep (domRep.frame progressA.kept) checkedOk checkFinal (retained pair (by simp))
    have afterExpose := progressA.kept.trans progressCheck.kept
    have throughCheck := throughPi.trans afterExpose
    obtain ⟨_, subBack, resultRep⟩ := NativeCoreTransformExact.substitute_refines
      (codRep.frame afterExpose) (arg.frame throughCheck) (liftTransform_success substitutedOk)
    have calleeTyped : LoanTyping.HasType env [] ctx true (expand env f)
        (.pi erased (expand env dom) (expand env cod)) := by
      have exactType := fTyped.convert converted.converted
      rw [sameType] at exactType
      simpa only [Term.pi, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs] using exactType
    have argumentTyped := aTyped.convert compatible
    have appTyped := LoanTyping.HasType.app calleeTyped argumentTyped (Or.inl rfl)
    have instantiation : expand env (cod.subst (single a)) =
        (expand env cod).subst (single (expand env a)) := by
      rw [EnvironmentDelta.expand_substitution wf.admissible]
      congr 1
      funext index
      cases index <;> simp only [single, expand]
    refine ⟨throughCheck.trans progressSub.kept, subBack ∘ checkBack ∘ argBack ∘ piBack ∘ fBack,
      cod.subst (single a), resultRep, ?_⟩
    rw [instantiation]
    change LoanTyping.HasType env [] ctx true (.app (expand env f) (expand env a))
      ((expand env cod).subst (single (expand env a))) at appTyped
    simpa only [Term.app, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs] using appTyped

private theorem emit_refines
    (arity : op.arity = 0)
    (typed : LoanTyping.HasType env [] ctx true (expand env term) (expand env (.node op [])))
    (success : (emit state op).result = .ok answer) :
    Refines env state.arena ctx term (emit state op) answer := by
  obtain ⟨ref, added, shape⟩ := plain_success (original := append state op []) success
  subst answer
  obtain ⟨kept, backward, represented⟩ := append_refines .nil arity.symm added
  exact ⟨kept, backward, .node op [], represented, typed⟩

private theorem variable_refines (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env state.arena bindings ctx) {index : Nat} (found : bindings[index]? = some binding)
    (success : (shiftInferred limit depth state binding.typeRoot (index + 1)).result = .ok answer) :
    Refines env state.arena ctx (.var index) (shiftInferred limit depth state binding.typeRoot (index + 1)) answer := by
  obtain ⟨written, represented, typedLookup⟩ := context.lookup_type found
  obtain ⟨ref, shifted, shape⟩ := plain_success
    (original := shiftType limit depth state binding.typeRoot (index + 1)) success
  subst answer
  obtain ⟨kept, backward, shiftedType⟩ := shiftType_refines represented shifted
  refine ⟨kept, backward, _, shiftedType, ?_⟩
  rw [EnvironmentDelta.expand_renaming wf.admissible, expand]
  exact .var typedLookup (Or.inl rfl)

private theorem global_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions) {index : Nat} (found : roots[index]? = some row)
    (success : (shiftInferred limit depth state row.typeRoot amount).result = .ok answer) :
    Refines env state.arena ctx (.node (.global index) [])
      (shiftInferred limit depth state row.typeRoot amount) answer := by
  obtain ⟨entry, written, checked, represented, expanded⟩ := checked_type_at history aligned found
  obtain ⟨ref, shifted, shape⟩ := plain_success (original := shiftType limit depth state row.typeRoot amount) success
  subst answer
  obtain ⟨kept, backward, shiftedType⟩ := shiftType_refines represented shifted
  have closed := (history.wellFormed.globals index entry checked).1
  have original : LoanTyping.HasType env [] ctx true (.node (.global index) []) entry.type := by
    have direct := LoanTyping.HasType.global (loans := []) (ctx := ctx) (ghost := true) checked
    rwa [Environment.closed_rename closed] at direct
  refine ⟨kept, backward, _, shiftedType, ?_⟩
  rw [EnvironmentDelta.expand_global checked, EnvironmentDelta.expand_renaming history.wellFormed.admissible,
    expanded, Environment.closed_rename closed]
  exact history.delta_preserves checked original

/-- Every supported successful ghost inference derives the represented
result type in the original expanded context. -/
theorem runWith_sound {normal : NormalAt}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    InferSound env base ctx limit (runWith normal roots visible limit depth bindings) := by
  induction depth with
  | zero =>
      intro state root term answer final _ _ _ success _ _
      by_cases exhausted : limit < state.steps + 1 <;>
        simp [runWith, tick, NativeCoreUnsignedCancellation.tick, exhausted] at success
  | succ depth ih =>
      intro state root term answer final onBase room source success ambient retained
      simp only [runWith] at success ambient ⊢
      obtain ⟨entered, within⟩ := tick_success success
      rw [entered] at success ambient ⊢
      cases source with
      | var read =>
          simp only [read] at success ⊢
          split at success
          · exact variable_refines (state := {state with steps := state.steps + 1}) history.wellFormed
              (context.frame onBase) (by assumption) success
          · simp [discard] at success
      | @node _ op refs terms read arity children =>
          simp only [read] at success ambient ⊢
          cases op <;> simp only [Op.arity] at arity
          all_goals first | (simp [discard] at success; done) | skip
          all_goals try
            have empty := List.length_eq_zero_iff.mp arity
            subst refs
            cases children
          all_goals try dsimp only at success ambient ⊢
          case global.nil =>
            split at success
            · rename_i earlier
              simp only [ite_eq_left earlier]
              split at success
              · exact global_refines (state := {state with steps := state.steps + 1}) history
                  (NativeCoreNestedAliases.frame_definitions aligned onBase)
                  (by assumption) success
              · simp [discard] at success
            · simp at success
          case «universe».nil =>
            split at success
            · rename_i allowed
              simp only [ite_eq_left allowed]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              exact .univ allowed
            · simp [discard] at success
          case prop.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .prop) success
          case u64.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .u64) success
          case i64.nil =>
            exact emit_refines rfl (by simp only [expand, expandArgs]; exact .i64) success
          case natural.nil =>
            split at success
            · rename_i allowed
              simp only [ite_eq_left allowed]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              exact .natural allowed
            · simp [discard] at success
          case integer.nil =>
            split at success
            · rename_i bound
              simp only [ite_eq_left bound]
              apply emit_refines (by rfl) _ success
              simp only [expand, expandArgs]
              obtain ⟨lower, upper⟩ := bound
              exact .integer lower upper
            · simp [discard] at success
          case array | buffer =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons child tail =>
              cases tail
              dsimp only at success ambient ⊢
              apply inferFixed_refines (state := {state with steps := state.steps + 1})
                (operand := .u64) (output := .universe 0) (depth := depth)
                (normalSound depth) (normalProgress depth) ih
                (fun _ _ budget => runWith_progress normalProgress budget)
                onBase within (.cons child .nil) rfl .nil rfl success ambient retained
              intro typed
              simp only [expand, expandArgs] at typed ⊢
              first
              | exact .array (typed _ List.mem_cons_self)
              | exact .buffer (typed _ List.mem_cons_self)
          case refl =>
            have length : refs.length = 1 := arity
            obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp length
            cases children with
            | cons child tail =>
              cases tail
              dsimp only at success ambient ⊢
              apply inferFixed_refines (state := {state with steps := state.steps + 1})
                (operand := .u64) (output := .eq) (depth := depth)
                (normalSound depth) (normalProgress depth) ih
                (fun _ _ budget => runWith_progress normalProgress budget)
                onBase within (.cons child .nil) rfl (.cons child (.cons child .nil)) rfl success ambient retained
              intro typed
              simp only [expand, expandArgs] at typed ⊢
              exact .refl (typed _ List.mem_cons_self)
          case eq | lt | uadd | arith =>
            have length : refs.length = 2 := arity
            rcases refs with _ | ⟨left, _ | ⟨right, _ | ⟨_, _⟩⟩⟩ <;> simp at length
            cases children with
            | cons first rest =>
              cases rest with
              | cons second tail =>
                cases tail
                dsimp only at success ambient ⊢
                apply inferFixed_refines (state := {state with steps := state.steps + 1})
                  (depth := depth)
                  (normalSound depth) (normalProgress depth) ih
                  (fun _ _ budget => runWith_progress normalProgress budget)
                  onBase within (.cons first (.cons second .nil)) rfl .nil rfl success ambient retained
                intro typed
                simp only [expand, expandArgs] at typed ⊢
                have left := typed _ List.mem_cons_self
                have right := typed _ (List.mem_cons_of_mem _ List.mem_cons_self)
                first | exact .eq left right | exact .lt left right | exact .uadd left right | exact .arith left right
          case app =>
            have refsLength : refs.length = 2 := arity
            rcases refs with _ | ⟨function, _ | ⟨argument, _ | ⟨_, _⟩⟩⟩ <;> simp at refsLength
            case _ =>
              cases children with
              | cons fn tail =>
                cases tail with
                | cons arg tail =>
                  cases tail
                  exact inferApp_refines (state := {state with steps := state.steps + 1})
                    history.wellFormed (normalSound depth) (normalProgress depth) ih
                    (fun _ _ budget => runWith_progress normalProgress budget)
                    onBase within fn arg success ambient retained

private theorem nested_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    VisitsFrom base (ExpandedNormalization env) (NativeCoreNestedAliases.run roots visible limit depth) := by
  intro state ref term selected onBase source success
  obtain ⟨kept, backward, result⟩ := NativeCoreNestedAliases.run_refines history aligned onBase source success
  exact ⟨kept, backward, result⟩

theorem run_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (context : ContextRep env base bindings ctx) :
    InferSound env base ctx limit (run roots visible limit depth bindings) :=
  runWith_sound history aligned context (NativeCoreNestedAliases.run_progress roots visible limit)
    (fun _ => nested_sound history aligned)

def CheckedInferences (snapshot : NativeFamilyWire.Snapshot) (env : Environment)
    (normalize : Nat → Nat → NormalAt) : Prop :=
  ∀ {index limit depth initial : Nat} {row : Roots},
    snapshot.definitions[index]? = some row →
    let start : State := ⟨snapshot.arena, initial⟩
    let output := runWith (normalize index limit) snapshot.definitions index limit depth [] start row.valueRoot
    initial ≤ limit →
      Progress limit start output ∧
      ∀ answer, output.result = .ok answer → RetainedComparisons output.state.arena answer →
        Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
        ∃ (entry : GlobalDeclaration) (source inferred : Term),
          env.globals[index]? = some entry ∧ Represents snapshot.arena row.valueRoot source ∧
          Represents output.state.arena answer.typeRoot inferred ∧
          LoanTyping.HasType env [] [] true (expand env source) (expand env inferred) ∧
          LoanTyping.Conversion.Conv env (expand env inferred) entry.type

/-- Exact-byte admission supplies both the original graph operand and its
checked declaration type. Successful inference in the covered fragment uses
the earlier visibility bound and computes a represented type convertible to
that original type by Loan64 uniqueness. -/
theorem admitted_program_infers_with
    (normalize : Environment → NativeFamilyWire.Snapshot → Nat → Nat → NormalAt)
    (metered : ∀ env snapshot visible limit depth state root,
      Progress limit state (normalize env snapshot visible limit depth state root))
    (sound : ∀ {env snapshot definitions declarations},
      LoanTyping.MixedProgram.History definitions declarations env →
      RepresentsDefinitions snapshot.arena snapshot.definitions definitions →
      ∀ visible limit depth, VisitsFrom snapshot.arena (ExpandedNormalization env)
        (normalize env snapshot visible limit depth))
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (normalize env snapshot) := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, valid, aligned, _, history, wf⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial row found start output room
  refine ⟨runWith_progress (metered env snapshot index limit) room, ?_⟩
  intro answer success retained
  obtain ⟨entry, raw, recorded, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, forwards, inferred, held, inferredTyped⟩ :=
    runWith_sound history aligned .nil (metered env snapshot index limit) (sound history aligned index limit)
      (.refl _) room source.2 success (.refl _) retained
  exact ⟨kept, forwards valid, entry, raw.value, inferred, recorded, source.2, held, inferredTyped,
    inferredTyped.unique wf typed⟩

theorem admitted_program_infers
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (NativeCoreNestedAliases.run snapshot.definitions) :=
  admitted_program_infers_with (fun _ snapshot => NativeCoreNestedAliases.run snapshot.definitions)
    (fun _ snapshot => NativeCoreNestedAliases.run_progress snapshot.definitions)
    (fun history aligned _ _ _ => nested_sound history aligned) admitted

/-- The same inference schedule uses recursive family normalization for
both Pi exposure and the argument-type comparison. -/
theorem admitted_family_program_infers
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      CheckedInferences snapshot env (NativeCoreExpandedFamilies.raw env snapshot.families snapshot.definitions) :=
  admitted_program_infers_with
    (fun env snapshot => NativeCoreExpandedFamilies.raw env snapshot.families snapshot.definitions)
    (fun env snapshot => NativeCoreExpandedFamilies.raw_progress env snapshot.families snapshot.definitions)
    (fun history aligned _ _ _ state ref term selected onBase source success => by
      obtain ⟨kept, backward, result⟩ := NativeCoreExpandedFamilies.raw_refines history aligned onBase source success
      exact ⟨kept, backward, result⟩) admitted

namespace Examples

private def proofOf (witness : Term) : Term := .eq witness witness
private def seven : Term := .natural 7
private def argument : Term := .node (.global 1) []
private def source : Term := .app (.app (.node (.global 0) []) seven) argument
private def familyType : Term :=
  .pi false .u64 (.pi true (proofOf (.var 0)) (proofOf (.var 1)))
private def familyValue : Term := .lam false .u64 (.lam true (proofOf (.var 0)) (.var 0))
private def definitions : List GlobalDeclaration :=
  [⟨familyType, familyValue⟩, ⟨proofOf seven, .refl seven⟩, ⟨proofOf seven, source⟩]
private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨6, 8⟩, ⟨10, 11⟩, ⟨10, 15⟩]
  families := []
  arena := #[.node .u64 [], .var 0, .var 1, .node .eq [1, 1], .node .eq [2, 2],
    .node (.pi true) [3, 4], .node (.pi false) [0, 5], .node (.lam true) [3, 1],
    .node (.lam false) [0, 7], .node (.natural 7) [], .node .eq [9, 9], .node .refl [9],
    .node (.global 0) [], .node (.global 1) [], .node .app [12, 9], .node .app [14, 13]]
private def start : State := ⟨snapshot.arena, 0⟩
private def finalArena : Arena :=
  snapshot.arena ++ #[.node .u64 [], .node .eq [9, 9], .node .eq [9, 9], .node (.pi true) [17, 18]]
private def answer : Inferred := ⟨18, [(16, 0), (10, 17)]⟩

/-- Inference exposes a dependent Pi, instantiates its outer word binder,
then checks the ghost proof against the resulting domain and returns the
instantiated codomain. The two checks use the live appended rows. -/
theorem admitted_dependent_spine_executes :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run snapshot.definitions 2 59 24 [] start 15 = ⟨⟨finalArena, 59⟩, .ok answer⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

private def env : Environment :=
  ⟨#[⟨familyType, familyValue⟩, ⟨proofOf seven, .refl seven⟩,
    ⟨proofOf seven, .app (.app familyValue seven) (.refl seven)⟩], #[]⟩

private theorem concrete_comparisons_retained : RetainedComparisons finalArena answer := by
  have literal : FullyRetained seven := .node (by decide) rfl rfl (by simp)
  have word : FullyRetained .u64 := .node (by decide) rfl rfl (by simp)
  have evidence : FullyRetained (proofOf seven) := .node (by decide) rfl rfl (by
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst child
    exact literal)
  intro pair member
  change pair ∈ [(16, 0), (10, 17)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  obtain (rfl | rfl) := member
  · exact ⟨.u64, .u64, decode_sound (fuel := 2) rfl, decode_sound (fuel := 2) rfl, word, word⟩
  · exact ⟨proofOf seven, proofOf seven, decode_sound (fuel := 3) rfl, decode_sound (fuel := 3) rfl,
      evidence, evidence⟩

/-- The result root of the admitted spine actually represents its checked
dependent proposition, and the inference proof types the original operand. -/
theorem admitted_dependent_spine_typed :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    Represents finalArena answer.typeRoot (proofOf seven) ∧
    LoanTyping.HasType env [] [] true (expand env source) (proofOf seven) := by
  have history : LoanTyping.MixedProgram.History definitions [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have represented : Represents start.arena 15 source := decode_sound (fuel := 6) rfl
  have computed := admitted_dependent_spine_executes.2
  have output : Represents finalArena answer.typeRoot (proofOf seven) := decode_sound (fuel := 3) rfl
  obtain ⟨_, _, inferred, supplied, typed⟩ :=
    run_sound (limit := 59) (depth := 24) (visible := 2) history aligned ContextRep.nil
      (.refl _) (by decide) represented (congrArg Outcome.result computed) (by rw [computed]; exact .refl _)
      concrete_comparisons_retained
  rw [computed] at supplied
  rw [supplied.unique output] at typed
  exact ⟨admitted_dependent_spine_executes.1, output,
    by simpa only [proofOf, Term.eq, seven, Term.natural, expand, expandArgs] using typed⟩

theorem last_substitution_exhaustion_keeps_inferred_pi :
    run snapshot.definitions 2 56 24 [] start 15 =
      ⟨⟨finalArena, 57⟩, .error (.substitution (.tick (.stepLimit 18)))⟩ := by cbv

/-- Looking up the older erased proof shifts its stored domain by two in
ghost mode, visiting both occurrences of the younger term's index. -/
theorem open_variable_weakening_appends_domain :
    run snapshot.definitions 2 4 8 [⟨0, false⟩, ⟨3, true⟩, ⟨0, false⟩] start 2 =
      ⟨⟨snapshot.arena ++ #[.var 2, .var 2, .node .eq [16, 17]], 4⟩, .ok ⟨18, []⟩⟩ := by cbv

private def sum : Term := .uadd (.natural 7) (.natural 1)
private def reflexive : GlobalDeclaration := ⟨.eq sum sum, .refl sum⟩
private def primitiveSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨3, 4⟩]
  families := []
  arena := #[.node (.natural 7) [], .node (.natural 1) [], .node .uadd [0, 1],
    .node .eq [2, 2], .node .refl [2], .node (.integer 1) [], .node .eq [5, 2]]
private def primitiveStart : State := ⟨primitiveSnapshot.arena, 0⟩
private def primitiveFinal : Arena := primitiveSnapshot.arena ++
  #[.node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [], .node .u64 [], .node .eq [2, 2]]
private def primitiveAnswer : Inferred := ⟨12, [(9, 8), (10, 8), (11, 7)]⟩

/-- Refl checks its compound word before emitting equality at the original
operand reference. Both checks inside UAdd reuse a single expected row. -/
theorem admitted_reflexive_sum_executes :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot primitiveSnapshot) = true ∧
    run primitiveSnapshot.definitions 0 13 16 [] primitiveStart 4 =
      ⟨⟨primitiveFinal, 13⟩, .ok primitiveAnswer⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

theorem admitted_reflexive_sum_typed :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot primitiveSnapshot) = true ∧
    Represents primitiveFinal primitiveAnswer.typeRoot reflexive.type ∧
    LoanTyping.HasType ⟨#[⟨reflexive.type, reflexive.value⟩], #[]⟩ [] [] true reflexive.value reflexive.type := by
  let env : Environment := ⟨#[⟨reflexive.type, reflexive.value⟩], #[]⟩
  have history : LoanTyping.MixedProgram.History [reflexive] [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions primitiveSnapshot.arena primitiveSnapshot.definitions [reflexive] :=
    decodeRoots_sound (by cbv)
  have source : Represents primitiveStart.arena 4 reflexive.value := decode_sound (fuel := 4) rfl
  have output : Represents primitiveFinal primitiveAnswer.typeRoot reflexive.type := decode_sound (fuel := 4) rfl
  have retained : RetainedComparisons primitiveFinal primitiveAnswer := by
    have word : FullyRetained .u64 := .node (by decide) rfl rfl (by simp)
    intro pair member
    change pair ∈ [(9, 8), (10, 8), (11, 7)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      exact ⟨.u64, .u64, decode_sound (fuel := 1) rfl, decode_sound (fuel := 1) rfl, word, word⟩
  have computed := admitted_reflexive_sum_executes.2
  obtain ⟨_, _, type, represented, typed⟩ := run_sound (limit := 13) (depth := 16) (visible := 0)
    history aligned ContextRep.nil (.refl _) (by decide) source (congrArg Outcome.result computed)
    (by rw [computed]; exact .refl _) retained
  rw [computed] at represented
  rw [represented.unique output] at typed
  exact ⟨admitted_reflexive_sum_executes.1, output,
    by
      change LoanTyping.HasType env [] [] true reflexive.value reflexive.type
      simpa only [reflexive, sum, Term.refl, Term.eq, Term.uadd, Term.natural, expand, expandArgs] using typed⟩

/-- Equality stops at the signed first operand's type comparison and retains
the two rows already appended. -/
theorem primitive_first_mismatch_keeps_checked_prefix :
    run primitiveSnapshot.definitions 0 13 16 [] primitiveStart 6 =
      ⟨⟨primitiveSnapshot.arena ++ #[.node .u64 [], .node .i64 []], 5⟩,
        .error (.outsideFragment 5)⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreGhostSpineInference
