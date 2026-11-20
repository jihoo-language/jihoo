import Jihoo.NativeCoreIdentical
import Jihoo.NativeEnvironmentDeltaBounded
import Jihoo.NativeLoanPureConversion
import Jihoo.NativeLoanDeltaPreservation

/-! The allocation-free fragment of Core.normal that follows transparent
global aliases to atomic heads. The original graph and raw definition roots
remain fixed. Visibility counts definitions, whereas recursion follows body
node references and charges a tick for each visit. -/
namespace Jihoo.NativeKernel.NativeCoreGlobalNormal

open NativeArena NativeCoreGraph NativeProgramWire
open Environment.LoanTyping.MixedProgram (History DeclarationChecked)

def atomicOp : Op → Bool
  | .universe _ | .prop | .u64 | .i64 | .natural _ | .integer _ => true
  | _ => false

def Atomic : Term → Prop
  | .var _ => True
  | .node op [] => atomicOp op = true
  | .node _ (_ :: _) => False

inductive Head where
  | alias (index : Nat)
  | atomic
  | outside
  deriving DecidableEq

def head : Node → Head
  | .var _ => .atomic
  | .node (.global index) [] => .alias index
  | .node op [] => if atomicOp op then .atomic else .outside
  | _ => .outside

inductive Error where
  | stepLimit (root : Nat)
  | depthLimit (root : Nat)
  | invalidReference (root : Nat)
  | invisibleGlobal (root index : Nat)
  | missingDefinition (root index : Nat)
  | outsideFragment (root : Nat)
  deriving Repr, DecidableEq

abbrev Result := Except Error Nat × Nat

/-- Global lookup follows the current raw definition root in the fixed
arena and returns a reference to its existing terminal node. -/
def run (arena : Arena) (roots : List Roots) (visible limit : Nat) :
    Nat → Nat → Nat → Result
  | 0, steps, root =>
      let next := steps + 1
      if limit < next then (.error (.stepLimit root), next)
      else (.error (.depthLimit root), next)
  | depth + 1, steps, root =>
      let next := steps + 1
      if limit < next then (.error (.stepLimit root), next) else
      match arena[root]? with
      | none => (.error (.invalidReference root), next)
      | some node =>
          match head node with
          | .atomic => (.ok root, next)
          | .outside => (.error (.outsideFragment root), next)
          | .alias index =>
              if visible ≤ index then (.error (.invisibleGlobal root index), next) else
              match roots[index]? with
              | none => (.error (.missingDefinition root index), next)
              | some definition => run arena roots visible limit depth next definition.valueRoot

/-- An independent ordered witness of every root visit, including the final
unchanged atom. A body reference can be newer than the Global node. -/
inductive Trace (arena : Arena) (roots : List Roots) (visible : Nat) :
    Nat → Nat → List Nat → Prop where
  | atomic (read : arena[root]? = some node) (leaf : head node = .atomic) :
      Trace arena roots visible root root [root]
  | alias (read : arena[root]? = some node) (kind : head node = .alias index)
      (before : index < visible) (lookup : roots[index]? = some definition)
      (rest : Trace arena roots visible definition.valueRoot selected visited) :
      Trace arena roots visible root selected (root :: visited)

theorem Trace.execute (path : Trace arena roots visible root selected visited)
    (height : visited.length ≤ depth) (space : steps + visited.length ≤ limit) :
    run arena roots visible limit depth steps root = (.ok selected, steps + visited.length) := by
  induction path generalizing depth steps with
  | atomic read leaf =>
      simp only [List.length_singleton] at height space ⊢
      cases depth with
      | zero => omega
      | succ depth => simp [run, Nat.not_lt.mpr space, read, leaf]
  | @alias root node index definition selected visited read kind before lookup _ ih =>
      cases depth with
      | zero => simp at height
      | succ depth =>
          have room : ¬limit < steps + 1 := by simp only [List.length_cons] at space; omega
          simp only [run, ite_eq_right room, read, kind, ite_eq_right (Nat.not_le.mpr before), lookup]
          have nextHeight : visited.length ≤ depth := by simp only [List.length_cons] at height; omega
          have nextSpace : steps + 1 + visited.length ≤ limit := by simp only [List.length_cons] at space; omega
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ih nextHeight nextSpace

theorem run_trace (computed : run arena roots visible limit depth steps root = (.ok selected, counter)) :
    ∃ visited, Trace arena roots visible root selected visited ∧ visited.length ≤ depth ∧
      counter = steps + visited.length ∧ counter ≤ limit := by
  induction depth generalizing steps root selected counter with
  | zero => simp only [run] at computed; split at computed <;> cases computed
  | succ depth ih =>
      simp only [run] at computed
      by_cases exceeded : limit < steps + 1
      · simp [exceeded] at computed
      · rw [ite_eq_right exceeded] at computed
        cases read : arena[root]? with
        | none => simp [read] at computed
        | some node =>
            rw [read] at computed
            cases kind : head node with
            | atomic =>
                simp only [kind, Prod.mk.injEq, Except.ok.injEq] at computed
                obtain ⟨rfl, rfl⟩ := computed
                exact ⟨[root], .atomic read kind, by simp, rfl, Nat.le_of_not_gt exceeded⟩
            | outside => simp [kind] at computed
            | alias index =>
                by_cases before : index < visible
                · cases lookup : roots[index]? with
                  | none => simp [kind, Nat.not_le.mpr before, lookup] at computed
                  | some definition =>
                      simp only [kind, ite_eq_right (Nat.not_le.mpr before), lookup] at computed
                      obtain ⟨visited, path, height, spent, cap⟩ := ih computed
                      exact ⟨root :: visited, .alias read kind before lookup path,
                        Nat.succ_le_succ height, by simp only [List.length_cons]; omega, cap⟩
                · simp [kind, Nat.le_of_not_gt before] at computed

theorem run_visibility (read : arena[root]? = some node) (kind : head node = .alias index)
    (budget : steps + 1 ≤ limit) (hidden : visible ≤ index) :
    run arena roots visible limit (depth + 1) steps root = (.error (.invisibleGlobal root index), steps + 1) := by
  simp [run, Nat.not_lt.mpr budget, read, kind, hidden]

theorem run_step_limit_first (exceeded : limit < steps + 1) :
    run arena roots visible limit depth steps root = (.error (.stepLimit root), steps + 1) := by
  cases depth <;> simp [run, exceeded]

private theorem alias_node (kind : head node = .alias index) :
    node = .node (.global index) [] := by
  cases node with
  | var => cases kind
  | node op args =>
      cases args
      · cases op <;> simp [head, atomicOp] at kind
        subst index
        rfl
      · cases op <;> simp [head] at kind

private theorem atomic_node (read : arena[root]? = some node) (kind : head node = .atomic) :
    ∃ term, Atomic term ∧ Represents arena root term := by
  cases node with
  | var index => exact ⟨.var index, True.intro, .var read⟩
  | node op args =>
      cases args with
      | cons => cases op <;> simp [head] at kind
      | nil =>
          have canBeLeaf : atomicOp op = true := by
            cases op <;> simp [head, atomicOp] at kind ⊢
          have arity : ([] : List Nat).length = op.arity := by
            cases op <;> simp [atomicOp, Op.arity] at canBeLeaf ⊢
          exact ⟨.node op [], canBeLeaf, .node read arity .nil⟩

private theorem atomic_read (rep : Represents arena root term) (leaf : Atomic term) :
    ∃ node, arena[root]? = some node ∧ head node = .atomic := by
  cases rep with
  | var read => exact ⟨_, read, rfl⟩
  | @node root op refs args read arity children =>
      cases children with
      | nil =>
          refine ⟨_, read, ?_⟩
          cases op <;> simp [Atomic, head, atomicOp] at leaf ⊢
      | cons => contradiction

private theorem atomic_expand (leaf : Atomic term) : EnvironmentDelta.expand env term = term := by
  cases term with
  | var => rw [EnvironmentDelta.expand]
  | node op args =>
      cases args with
      | cons => contradiction
      | nil =>
          have ordinary : GlobalEnvironment.ordinary op = true := by
            cases op <;> simp [Atomic, atomicOp, GlobalEnvironment.ordinary] at leaf ⊢
          rw [EnvironmentDelta.expand_ordinary ordinary, EnvironmentDelta.expandArgs]

private theorem represents_global
    (rep : Represents arena root (.node (.global index) [])) :
    arena[root]? = some (.node (.global index) []) := by
  cases rep with
  | node read _ children =>
      cases children
      exact read

private theorem represented_at {index : Nat}
    (aligned : RepresentsDefinitions arena roots definitions) (lookup : roots[index]? = some row) :
    ∃ raw, definitions[index]? = some raw ∧ RepresentsDefinition arena row raw := by
  induction aligned generalizing index with
  | nil => simp at lookup
  | @cons _ raw _ _ head _ ih =>
      cases index with
      | zero => cases lookup; exact ⟨raw, rfl, head⟩
      | succ index => exact ih lookup

private theorem raw_expansion_at {index : Nat}
    (history : History definitions families env) (lookup : definitions[index]? = some source) :
    ∃ expanded, env.globals[index]? = some expanded ∧
      GlobalEnvironment.Expansion env.globals source.value expanded.value ∧
      ∀ target, source.value = .node (.global target) [] → target < index := by
  induction history with
  | empty => simp at lookup
  | @definition definitions families env raw expanded history checked ih =>
      by_cases earlier : index < definitions.length
      · rw [List.getElem?_append_left earlier] at lookup
        obtain ⟨entry, found, expansion, decreases⟩ := ih lookup
        have inside : index < env.globals.size := history.globalLength.symm ▸ earlier
        have preserved := Array.getElem?_push_lt (x := expanded) inside
        rw [Array.getElem?_eq_getElem inside] at found
        exact ⟨entry, preserved.trans found, expansion.extend expanded, decreases⟩
      · have bound := (List.getElem?_eq_some_iff.mp lookup).1
        have atEnd : index = definitions.length := by simp only [List.length_append, List.length_singleton] at bound; omega
        subst index
        have same : raw = source := by simpa using lookup
        subst source
        refine ⟨expanded, ?_, checked.valueExpansion.extend expanded, ?_⟩
        · rw [← history.globalLength, Array.getElem?_push_size]
        · intro target alias
          have expansion := checked.valueExpansion
          rw [alias] at expansion
          generalize expanded.value = result at expansion
          cases expansion with
          | global present =>
              rw [← history.globalLength]
              exact (Array.getElem?_eq_some_iff.mp present).1
          | node _ ordinary _ => contradiction
  | family _ _ ih => exact ih lookup

/-- An admitted source alias strictly targets an earlier definition, even
though the raw alias and its destination body can have any arena IDs. -/
theorem admitted_alias_before {index : Nat}
    (history : History definitions families env) (lookup : definitions[index]? = some source)
    (alias : source.value = .node (.global target) []) : target < index :=
  (raw_expansion_at history lookup).choose_spec.2.2 target alias

/-- A completed raw graph walk returns the exact transparently expanded term
in the authentic mixed environment, at the original terminal reference. -/
theorem Trace.expansion
    (path : Trace arena roots visible root selected visited)
    (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (source : Represents arena root term) :
    Atomic (EnvironmentDelta.expand env term) ∧ Represents arena selected (EnvironmentDelta.expand env term) := by
  induction path generalizing term with
  | atomic read kind =>
      obtain ⟨terminal, leaf, represented⟩ := atomic_node read kind
      have same := source.unique represented
      subst term
      rw [atomic_expand leaf]
      exact ⟨leaf, represented⟩
  | alias read kind before lookup rest ih =>
      rw [alias_node kind] at read
      have same := source.unique (Represents.node read rfl .nil)
      subst term
      obtain ⟨raw, atRaw, rawRep⟩ := represented_at aligned lookup
      obtain ⟨expanded, found, expandedFrom, earlier⟩ := raw_expansion_at history atRaw
      have unfolded := EnvironmentDelta.expansion_eq_expand expandedFrom
      rw [EnvironmentDelta.expand_global found, ← unfolded]
      exact ih rawRep.2

/-- A successful raw arena run certifies forward delta computation at the
same terminal reference in the mixed environment. -/
theorem run_delta
    (aligned : RepresentsDefinitions arena roots definitions) (history : History definitions families env)
    (source : Represents arena root term)
    (computed : run arena roots visible limit depth initial root = (.ok selected, counter)) :
    Represents arena selected (EnvironmentDelta.expand env term) ∧
      EnvironmentDelta.Forward env term (EnvironmentDelta.expand env term) := by
  obtain ⟨_, path, _, _, _⟩ := run_trace computed
  exact ⟨(path.expansion aligned history source).2, EnvironmentDelta.expand_forward env term⟩

private theorem atomic_or_alias (leaf : Atomic (EnvironmentDelta.expand env term)) :
    Atomic term ∨ ∃ index definition, term = .node (.global index) [] ∧
      env.globals[index]? = some definition ∧ Atomic definition.value := by
  cases term with
  | var => exact .inl True.intro
  | node op args =>
      cases args with
      | cons => rw [EnvironmentDelta.expand_node_cons] at leaf; contradiction
      | nil =>
          cases op <;> simp only [EnvironmentDelta.expand, EnvironmentDelta.expandArgs] at leaf
          all_goals first | exact .inl leaf | skip
          case global index =>
            cases found : env.globals[index]? with
            | none => simp [found, Atomic, atomicOp] at leaf
            | some definition => exact .inr ⟨index, definition, rfl, found, by simpa [found] using leaf⟩

/-- For a visible admitted declaration whose expanded value is atomic, its
actual raw body has a terminating path of at most its table index plus one
visits. Each alias encountered in that path points to a strictly earlier
declaration. -/
theorem definition_trace {index : Nat}
    (aligned : RepresentsDefinitions arena roots definitions) (history : History definitions families env)
    (found : env.globals[index]? = some entry) (leaf : Atomic entry.value) (shown : index < visible) :
    ∃ row selected visited, roots[index]? = some row ∧
      Trace arena roots visible row.valueRoot selected visited ∧
      Represents arena selected entry.value ∧ visited.length ≤ index + 1 := by
  induction index using Nat.strongRecOn generalizing entry with
  | ind index ih =>
      have inside : index < roots.length := by
        rw [aligned.length_eq, ← history.globalLength]
        exact (Array.getElem?_eq_some_iff.mp found).1
      let row := roots[index]
      have lookup : roots[index]? = some row := List.getElem?_eq_getElem inside
      obtain ⟨raw, atRaw, _, rawValue⟩ := represented_at aligned lookup
      obtain ⟨expanded, foundExpanded, expandedFrom, decreases⟩ := raw_expansion_at history atRaw
      have same := Option.some.inj (foundExpanded.symm.trans found)
      subst expanded
      have unfolded := EnvironmentDelta.expansion_eq_expand expandedFrom
      have expandedAtomic : Atomic (EnvironmentDelta.expand env raw.value) := unfolded.symm ▸ leaf
      rcases atomic_or_alias expandedAtomic with atomic | ⟨target, targetEntry, alias, atTarget, atomic⟩
      · obtain ⟨node, read, kind⟩ := atomic_read rawValue atomic
        have same : entry.value = raw.value := unfolded.symm.trans (atomic_expand atomic)
        exact ⟨row, row.valueRoot, [row.valueRoot], lookup, .atomic read kind,
          same.symm ▸ rawValue, by simp⟩
      · have earlier := decreases target alias
        have visibleTarget := Nat.lt_trans earlier shown
        obtain ⟨targetRow, selected, visited, targetRead, rest, represented, visits⟩ :=
          ih target earlier atTarget atomic visibleTarget
        have source : Represents arena row.valueRoot (.node (.global target) []) := alias ▸ rawValue
        have same : entry.value = targetEntry.value := by
          rw [← unfolded, alias, EnvironmentDelta.expand_global atTarget]
        refine ⟨row, selected, row.valueRoot :: visited, lookup, ?_, same ▸ represented, ?_⟩
        · exact .alias (represents_global source) rfl visibleTarget targetRead rest
        · simp only [List.length_cons]
          omega

/-- With the whole admitted prefix visible, any represented source whose
expanded head is atomic reaches its exact arena root within at most one more
tick than the number of definitions. -/
theorem admitted_trace
    (aligned : RepresentsDefinitions arena roots definitions) (history : History definitions families env)
    (visibility : env.globals.size ≤ visible) (source : Represents arena root term)
    (leaf : Atomic (EnvironmentDelta.expand env term)) :
    ∃ selected visited, Trace arena roots visible root selected visited ∧
      Represents arena selected (EnvironmentDelta.expand env term) ∧ visited.length ≤ env.globals.size + 1 := by
  rcases atomic_or_alias leaf with atomic | ⟨index, definition, rfl, found, atomic⟩
  · obtain ⟨node, read, kind⟩ := atomic_read source atomic
    rw [atomic_expand atomic]
    exact ⟨root, [root], .atomic read kind, source, by simp⟩
  · have inTable := (Array.getElem?_eq_some_iff.mp found).1
    have shown := Nat.lt_of_lt_of_le inTable visibility
    obtain ⟨row, selected, visited, lookup, path, represented, visits⟩ :=
      definition_trace aligned history found atomic shown
    rw [EnvironmentDelta.expand_global found]
    exact ⟨selected, root :: visited, .alias (represents_global source) rfl shown lookup path,
      represented, by simp only [List.length_cons]; omega⟩

private theorem atomic_values (leaf : Atomic term) :
    (∃ index, term = .var index) ∨ ∃ op, atomicOp op = true ∧ term = .node op [] := by
  cases term with
  | var index => exact .inl ⟨index, rfl⟩
  | node op args =>
      cases args with
      | nil => exact .inr ⟨op, leaf, rfl⟩
      | cons => contradiction

private theorem atomic_project_node (leaf : atomicOp op = true) :
    NativeCoreCompare.project (.node op []) =
      .node (ACU.Canonical.rank op, ACU.Canonical.payload op) [] := by
  cases op <;> simp [atomicOp] at leaf
  all_goals rw [NativeCoreCompare.project, NativeCoreCompare.projectArgs]; rfl

theorem atomic_project_injective (first : Atomic left) (second : Atomic right)
    (matched : NativeCoreCompare.project left = NativeCoreCompare.project right) : left = right := by
  rcases atomic_values first with ⟨index, rfl⟩ | ⟨op, firstOp, rfl⟩ <;>
    rcases atomic_values second with ⟨other, rfl⟩ | ⟨other, secondOp, rfl⟩
  · have equal : (index : Int) = (other : Int) := by simpa [NativeCoreCompare.project] using matched
    have indices : index = other := by omega
    rw [indices]
  · rw [NativeCoreCompare.project, atomic_project_node secondOp] at matched
    have ranks := congrArg Prod.fst (NativeCoreCompare.Shape.node.inj matched).1
    cases other <;> simp [atomicOp] at secondOp
    all_goals simp [ACU.Canonical.rank] at ranks
  · rw [atomic_project_node firstOp, NativeCoreCompare.project] at matched
    have ranks := congrArg Prod.fst (NativeCoreCompare.Shape.node.inj matched).1
    cases op <;> simp [atomicOp] at firstOp
    all_goals simp [ACU.Canonical.rank] at ranks
  · rw [atomic_project_node firstOp, atomic_project_node secondOp] at matched
    have heads := (NativeCoreCompare.Shape.node.inj matched).1
    cases op <;> simp [atomicOp] at firstOp
    all_goals cases other <;> simp [atomicOp] at secondOp
    all_goals simp [ACU.Canonical.rank, ACU.Canonical.payload] at heads ⊢
    all_goals first | exact heads | omega

inductive EqualError where
  | left (reason : Error)
  | right (reason : Error)
  | identity (reason : NativeCoreIdentical.Error)
  deriving Repr, DecidableEq

/-- The allocation-free Core.equal fragment runs left normal, right normal,
and then the actual identity traversal, passing the same step counter through
all three calls. Each starts at the original requested depth. -/
def equal (snapshot : NativeFamilyWire.Snapshot) (words : List NodeWords)
    (visible limit depth initial a b : Nat) : Except EqualError Bool × Nat :=
  match run snapshot.arena snapshot.definitions visible limit depth initial a with
  | (.error reason, steps) => (.error (.left reason), steps)
  | (.ok left, steps) =>
      match run snapshot.arena snapshot.definitions visible limit depth steps b with
      | (.error reason, steps) => (.error (.right reason), steps)
      | (.ok right, steps) =>
          match NativeCoreIdentical.run words limit depth steps left right with
          | (.error reason, steps) => (.error (.identity reason), steps)
          | (.ok value, steps) => (.ok value, steps)

/-- Successful equality over the parsed writer graph decides equality of the
actual expanded atomic heads. Its intermediate roots still inhabit the same
arena and its declaration roots were not rebuilt. -/
theorem equal_refines
    (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram roots families words ++ tail) =
      some (snapshot, rest))
    (aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions)
    (history : History definitions declarations env)
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (computed : equal snapshot words visible limit depth initial a b = (.ok result, steps)) :
    result = true ↔ EnvironmentDelta.expand env first = EnvironmentDelta.expand env second := by
  rcases hLeft : run snapshot.arena snapshot.definitions visible limit depth initial a with ⟨leftAnswer, leftSteps⟩
  cases leftAnswer with
  | error reason => simp [equal, hLeft] at computed
  | ok leftRoot =>
      rcases hRight : run snapshot.arena snapshot.definitions visible limit depth leftSteps b with
        ⟨rightAnswer, rightSteps⟩
      cases rightAnswer with
      | error reason => simp [equal, hLeft, hRight] at computed
      | ok rightRoot =>
          rcases compared : NativeCoreIdentical.run words limit depth rightSteps leftRoot rightRoot with
            ⟨answer, finalSteps⟩
          cases answer with
          | error reason => simp [equal, hLeft, hRight, compared] at computed
          | ok value =>
              simp only [equal, hLeft, hRight, compared, Prod.mk.injEq, Except.ok.injEq] at computed
              obtain ⟨rfl, rfl⟩ := computed
              obtain ⟨_, leftTrace, _, _, _⟩ := run_trace hLeft
              obtain ⟨_, rightTrace, _, _, _⟩ := run_trace hRight
              obtain ⟨leftAtomic, leftRep⟩ := leftTrace.expansion aligned history left
              obtain ⟨rightAtomic, rightRep⟩ := rightTrace.expansion aligned history right
              rw [NativeCoreIdentical.run_refines fits parsed leftRep rightRep compared]
              exact ⟨atomic_project_injective leftAtomic rightAtomic, congrArg NativeCoreCompare.project⟩

/-- Exact-byte mixed admission supplies the declaration table and its
genuine expansion history for the equality theorem. -/
theorem equal_checkBytes_refines
    (fits : ∀ word ∈ words, word.fits)
    (writer : NativeFamilyWire.encodeSnapshotList snapshot = encodeObservedProgram roots families words)
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (computed : equal snapshot words visible limit depth initial a b = (.ok result, steps)) :
    ∃ definitions declarations env,
      History definitions declarations env ∧
        (result = true ↔ EnvironmentDelta.expand env first = EnvironmentDelta.expand env second) := by
  obtain ⟨decoded, definitions, families, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  have parsed := NativeFamilyWire.parseSnapshot_encode snapshot []
  rw [writer] at parsed
  exact ⟨definitions, _, env, history, equal_refines fits parsed aligned history left right computed⟩

/-- The alias walk can move to newer arena references while the declaration
indices decrease. Equality uses five ticks across both normalization calls
and the final identity check. Hiding the newer declaration rejects first. -/
theorem forward_arena_alias_example :
    let words : List NodeWords := [⟨1, [1], []⟩, ⟨1, [0], []⟩, ⟨47, [7], []⟩, ⟨4, [], []⟩]
    let snapshot : NativeFamilyWire.Snapshot := ⟨[⟨3, 2⟩, ⟨3, 1⟩], [],
      #[.node (.global 1) [], .node (.global 0) [], .node (.natural 7) [], .node .u64 []]⟩
    equal snapshot words 2 5 3 0 0 2 = (.ok true, 5) ∧
      equal snapshot words 2 4 3 0 0 2 = (.error (.identity (.stepLimit 2)), 5) ∧
      equal snapshot words 1 5 3 0 0 2 = (.error (.left (.invisibleGlobal 0 1)), 1) := by
  exact ⟨rfl, rfl, rfl⟩

def discardRest : Node → Option Nat
  | .node .free [_, rest] | .node (.drop _) [_, rest] => some rest
  | _ => none

/-- The allocation-free pure normalization fragment that discards Free and
Drop operands. The native pure branch enters the continuation directly and
applies its depth, reference, and work checks along the selected path. -/
def runPure (arena : Arena) (roots : List Roots) (visible limit : Nat) :
    Nat → Nat → Nat → Result
  | 0, steps, root => run arena roots visible limit 0 steps root
  | depth + 1, steps, root =>
      let next := steps + 1
      if limit < next then (.error (.stepLimit root), next) else
      match arena[root]? with
      | none => (.error (.invalidReference root), next)
      | some node =>
          match discardRest node with
          | some rest => runPure arena roots visible limit depth next rest
          | none =>
              match head node with
              | .atomic => (.ok root, next)
              | .outside => (.error (.outsideFragment root), next)
              | .alias index =>
                  if visible ≤ index then (.error (.invisibleGlobal root index), next) else
                  match roots[index]? with
                  | none => (.error (.missingDefinition root index), next)
                  | some definition => runPure arena roots visible limit depth next definition.valueRoot

private def StepBounds (initial limit : Nat) (computed : Result) : Prop :=
  initial < computed.2 ∧ (initial ≤ limit → computed.2 ≤ limit + 1) ∧
    ∀ selected, computed.1 = .ok selected → computed.2 ≤ limit

private theorem StepBounds.error (reason : Error) :
    StepBounds initial limit (.error reason, initial + 1) := by
  refine ⟨Nat.lt_succ_self _, Nat.succ_le_succ, ?_⟩
  intro _ impossible
  cases impossible

private theorem StepBounds.prepend (available : initial + 1 ≤ limit)
    (remaining : StepBounds (initial + 1) limit computed) : StepBounds initial limit computed :=
  ⟨Nat.lt_trans (Nat.lt_succ_self _) remaining.1, fun _ => remaining.2.1 available, remaining.2.2⟩

/-- Every request consumes a tick. Successful traversal stays within the
limit. A request starting within budget can overspend by at most the
rejecting tick, including on invalid references and hidden globals. -/
theorem runPure_step_bounds (arena : Arena) (roots : List Roots) (visible limit depth initial root : Nat) :
    let computed := runPure arena roots visible limit depth initial root
    initial < computed.2 ∧ (initial ≤ limit → computed.2 ≤ limit + 1) ∧
      ∀ selected, computed.1 = .ok selected → computed.2 ≤ limit := by
  change StepBounds initial limit (runPure arena roots visible limit depth initial root)
  induction depth generalizing initial root with
  | zero =>
      simp only [runPure, run]
      split <;> exact StepBounds.error _
  | succ depth ih =>
      by_cases over : limit < initial + 1
      · simp only [runPure, over, ite_true]
        exact StepBounds.error _
      have room := Nat.le_of_not_gt over
      simp only [runPure, ite_eq_right over]
      cases read : arena[root]? with
      | none => exact StepBounds.error _
      | some node =>
          simp only
          cases discard : discardRest node with
          | some rest =>
              simp only
              exact (ih (initial := initial + 1) (root := rest)).prepend room
          | none =>
              simp only
              cases kind : head node with
              | atomic =>
                  simp only
                  exact ⟨Nat.lt_succ_self _, Nat.succ_le_succ, fun _ _ => room⟩
              | outside => exact StepBounds.error _
              | alias index =>
                  simp only
                  by_cases hidden : visible ≤ index
                  · simp only [hidden, ite_true]
                    exact StepBounds.error _
                  simp only [ite_eq_right hidden]
                  cases lookup : roots[index]? with
                  | none => exact StepBounds.error _
                  | some definition =>
                      simp only
                      exact (ih (initial := initial + 1) (root := definition.valueRoot)).prepend room

private theorem discard_shape (found : discardRest node = some rest) :
    ∃ op owner, node = .node op [owner, rest] ∧ (op = .free ∨ ∃ family, op = .drop family) := by
  fun_cases discardRest node <;> simp_all [discardRest]

private theorem represented_pair (rep : Represents arena root term)
    (read : arena[root]? = some (.node op [first, second])) :
    ∃ x y, term = .node op [x, y] ∧ Represents arena first x ∧ Represents arena second y := by
  cases rep with
  | var lookup => simp [read] at lookup
  | node lookup _ children =>
      rw [read] at lookup
      cases lookup
      cases children with
      | cons left tail =>
          cases tail with
          | cons right tail =>
              cases tail
              exact ⟨_, _, rfl, left, right⟩

private theorem expanded_pair (env : Environment) (op : Op) (first second : Term) :
    EnvironmentDelta.expand env (.node op [first, second]) =
      .node op [EnvironmentDelta.expand env first, EnvironmentDelta.expand env second] := by
  rw [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs, EnvironmentDelta.expandArgs]

private theorem discarded (kind : op = .free ∨ ∃ family, op = .drop family)
    (owner result : Term) :
    Environment.RawValue.Forward env (.node op [owner, result]) result ∧
    (∀ {ctx type}, Environment.LoanTyping.HasType env [] ctx true (.node op [owner, result]) type →
      Environment.LoanTyping.HasType env [] ctx true result type) := by
  rcases kind with rfl | ⟨family, rfl⟩
  · refine ⟨.free owner result, ?_⟩
    intro ctx type typed
    have view := typed.principalView
    change ∃ R, Environment.LoanTyping.HasType env [] ctx true result R ∧ _ at view
    obtain ⟨_, value, converted⟩ := view
    exact value.convert converted
  · refine ⟨.old (.old (.iota (.drop family owner result))), ?_⟩
    intro ctx type typed
    have view := typed.principalView
    change ∃ R, Environment.LoanTyping.HasType env [] ctx true result R ∧ _ at view
    obtain ⟨_, value, converted⟩ := view
    exact value.convert converted

/-- A pure Free or Drop node selects the represented continuation. Its
expanded input reduces to that continuation at the original ghost type. -/
theorem discard_target (source : Represents arena root term) (read : arena[root]? = some node)
    (skip : discardRest node = some rest) :
    ∃ tail, Represents arena rest tail ∧
      Environment.RawValue.Forward env (EnvironmentDelta.expand env term) (EnvironmentDelta.expand env tail) ∧
      (∀ {ctx type}, Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type →
        Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env tail) type) := by
  obtain ⟨op, owner, rfl, kind⟩ := discard_shape skip
  obtain ⟨first, second, rfl, _, tail⟩ := represented_pair source read
  rw [expanded_pair]
  obtain ⟨change, preserved⟩ :=
    discarded (env := env) kind (EnvironmentDelta.expand env first) (EnvironmentDelta.expand env second)
  exact ⟨second, tail, change, preserved⟩

/-- A checked raw alias and the raw row it selects have the same transparent
expansion. The row remains usable even when its body is a composite term. -/
theorem alias_target (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (read : arena[root]? = some node) (kind : head node = .alias index)
    (lookup : roots[index]? = some definition) :
    ∃ body, Represents arena definition.valueRoot body ∧
      EnvironmentDelta.expand env term = EnvironmentDelta.expand env body := by
  rw [alias_node kind] at read
  have same := source.unique (Represents.node read rfl .nil)
  subst term
  obtain ⟨raw, atRaw, rawRep⟩ := represented_at aligned lookup
  obtain ⟨expanded, found, expansion, _⟩ := raw_expansion_at history atRaw
  exact ⟨raw.value, rawRep.2, (EnvironmentDelta.expand_global found).trans
    (EnvironmentDelta.expansion_eq_expand expansion).symm⟩

private theorem runPure_expansion (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env)
    (source : Represents arena root term)
    (computed : runPure arena roots visible limit depth initial root = (.ok selected, counter)) :
    ∃ output, Atomic output ∧ Represents arena selected output ∧
      Environment.RawValue.Forward env (EnvironmentDelta.expand env term) output ∧
      (∀ {ctx type}, Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type →
        Environment.LoanTyping.HasType env [] ctx true output type) ∧
      initial < counter ∧ counter ≤ limit := by
  induction depth generalizing root term initial with
  | zero =>
      simp only [runPure, run] at computed
      split at computed <;> cases computed
  | succ depth ih =>
      by_cases exceeded : limit < initial + 1
      · simp [runPure, exceeded] at computed
      simp only [runPure, ite_eq_right exceeded] at computed
      cases read : arena[root]? with
      | none => simp [read] at computed
      | some node =>
          simp only [read] at computed
          cases skip : discardRest node with
          | some rest =>
              simp only [skip] at computed
              obtain ⟨_, tail, discard, preserved⟩ := discard_target (env := env) source read skip
              obtain ⟨output, atom, represented, reduced, preserves, charged, budget⟩ := ih tail computed
              exact ⟨output, atom, represented, discard.trans reduced,
                fun typed => preserves (preserved typed), by omega, budget⟩
          | none =>
              simp only [skip] at computed
              cases kind : head node with
              | outside => simp [kind] at computed
              | atomic =>
                  simp only [kind, Prod.mk.injEq, Except.ok.injEq] at computed
                  obtain ⟨rfl, rfl⟩ := computed
                  obtain ⟨atom, leaf, represented⟩ := atomic_node read kind
                  have same := source.unique represented
                  subst term
                  rw [atomic_expand leaf]
                  exact ⟨atom, leaf, represented, .refl, fun typed => typed,
                    Nat.lt_succ_self initial, Nat.le_of_not_gt exceeded⟩
              | alias index =>
                  by_cases hidden : visible ≤ index
                  · simp [kind, hidden] at computed
                  simp only [kind, ite_eq_right hidden] at computed
                  cases lookup : roots[index]? with
                  | none => simp [lookup] at computed
                  | some definition =>
                      rw [lookup] at computed
                      obtain ⟨_, body, same⟩ := alias_target aligned history source read kind lookup
                      rw [same]
                      obtain ⟨output, atom, represented, reduced, preserves, charged, budget⟩ :=
                        ih body computed
                      exact ⟨output, atom, represented, reduced, preserves, by omega, budget⟩

/-- Following actual arena rows and the authentic declaration history gives a
pure conversion witness and preserves the exact Loan64 ghost type of the
expanded input. Successful execution returns a pre-existing atomic row. -/
theorem runPure_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (typed : Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env term) type)
    (computed : runPure arena roots visible limit depth initial root = (.ok selected, counter)) :
    ∃ output, Atomic output ∧ Represents arena selected output ∧
      Environment.RawValue.Forward env term output ∧
      Environment.LoanTyping.HasType env [] ctx true output type ∧ initial < counter ∧ counter ≤ limit := by
  obtain ⟨output, atom, represented, reduced, preserves, charged, budget⟩ :=
    runPure_expansion aligned history source computed
  have delta : Environment.RawValue.Forward env term (EnvironmentDelta.expand env term) :=
    .old (.old (.old (EnvironmentDelta.expand_forward env term)))
  exact ⟨output, atom, represented, delta.trans reduced, preserves typed, charged, budget⟩

/-- A successful allocation-free walk ends at a represented atom. -/
theorem runPure_expanded_atom (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (computed : runPure arena roots visible limit depth initial root = (.ok selected, counter)) :
    ∃ output, Atomic output ∧ Represents arena selected output ∧
      Environment.RawValue.Forward env (EnvironmentDelta.expand env term) output := by
  obtain ⟨output, atom, represented, reduced, _, _, _⟩ :=
    runPure_expansion aligned history source computed
  exact ⟨output, atom, represented, reduced⟩

/-- The graph path supplies conversion before a typing derivation is
available, as in the native normalization of constructor annotations. -/
theorem runPure_expanded_conversion (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (computed : runPure arena roots visible limit depth initial root = (.ok selected, counter)) :
    ∃ output, Represents arena selected output ∧
      Environment.RawValue.Forward env (EnvironmentDelta.expand env term) output := by
  obtain ⟨output, _, represented, reduced⟩ := runPure_expanded_atom aligned history source computed
  exact ⟨output, represented, reduced⟩

theorem runPure_conversion (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root term)
    (computed : runPure arena roots visible limit depth initial root = (.ok selected, counter)) :
    ∃ output, Represents arena selected output ∧ Environment.RawValue.Forward env term output := by
  obtain ⟨output, represented, reduced⟩ := runPure_expanded_conversion aligned history source computed
  have delta : Environment.RawValue.Forward env term (EnvironmentDelta.expand env term) :=
    .old (.old (.old (EnvironmentDelta.expand_forward env term)))
  exact ⟨output, represented, delta.trans reduced⟩

/-- A raw definition root in the arena carries the type of its actual
admitted expanded declaration. -/
theorem checked_definition_at {index : Nat} (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions declarations env) (row : roots[index]? = some definition) :
    ∃ entry raw, env.globals[index]? = some entry ∧ RepresentsDefinition arena definition raw ∧
      Environment.LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env raw.value) entry.type := by
  obtain ⟨raw, atRaw, represented⟩ := represented_at aligned row
  obtain ⟨entry, found, expanded, _⟩ := raw_expansion_at history atRaw
  obtain ⟨_, _, body⟩ := history.global_typing found
  have typed := body.ghost []
  rw [← EnvironmentDelta.expansion_eq_expand expanded] at typed
  exact ⟨entry, raw, found, represented, typed⟩

/-- With exact-byte admission, the original result type comes from the
checked declaration corresponding to the requested row. -/
theorem runPure_admitted_definition_refines {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some roots)
    (computed : runPure snapshot.arena snapshot.definitions visible limit depth initial roots.valueRoot =
      (.ok selected, counter)) :
    ∃ definitions declarations env entry raw output,
      History definitions declarations env ∧ env.globals[index]? = some entry ∧
      RepresentsDefinition snapshot.arena roots raw ∧
      Atomic output ∧ Represents snapshot.arena selected output ∧
      Environment.RawValue.Forward env raw.value output ∧
      Environment.LoanTyping.HasType env [] [] true output entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := checked_definition_at aligned history row
  obtain ⟨output, atom, selectedRep, reduced, preserved, _, _⟩ :=
    runPure_refines aligned history represented.2 typed computed
  exact ⟨definitions, _, env, entry, raw, output, history, found, represented,
    atom, selectedRep, reduced, preserved⟩

/-- A transparent global can return a Drop containing a Free. The skipped
owner roots never consume a tick. The four visits share one work counter. -/
theorem pure_discard_alias_example :
    let arena : Arena := #[.node (.natural 7) [], .node .free [0, 0], .node (.drop 0) [0, 1],
      .node (.global 0) []]
    runPure arena [⟨0, 2⟩] 1 4 4 0 3 = (.ok 0, 4) ∧
      runPure arena [⟨0, 2⟩] 1 3 4 0 3 = (.error (.stepLimit 0), 4) ∧
      runPure arena [⟨0, 2⟩] 1 4 3 0 3 = (.error (.depthLimit 0), 4) := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreGlobalNormal
