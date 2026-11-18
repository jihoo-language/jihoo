import Jihoo.NativeLoanMixedAdmission

/-! The arena operations at the start of `Core.add` and `Core.extend` in
`compiler/core.jh`. Arena positions and child references are the integers
observed in the native snapshot. The scan follows the native suffix and child
order, including its first-error behavior. Name, span, typing, and operation
semantics of the Jihoo source are separate from this graph phase. -/
namespace Jihoo.NativeKernel.NativeCoreGraph
open NativeArena

def entryLimit : Nat := 200000

structure BadReference where
  node : Nat
  child : Nat
  deriving DecidableEq, Repr

inductive Error where
  | termLimit
  | reference (failure : BadReference)
  deriving DecidableEq, Repr

private def scanNode (arena : Arena) (id : Nat) : Option BadReference := do
  let node ← arena[id]?
  let child ← node.references.find? (fun ref => decide (id ≤ ref))
  some ⟨id, child⟩

def scanSuffix (arena : Arena) (start : Nat) : Option BadReference :=
  (List.range' start (arena.size - start)).findSome? (scanNode arena)

def checkGraph (arena : Arena) (checkedNodes : Nat) : Except Error Unit :=
  if entryLimit < arena.size then .error .termLimit else
    match scanSuffix arena checkedNodes with
    | none => .ok ()
    | some failure => .error (.reference failure)

def addNode (arena : Arena) (node : Node) : Except Error (Arena × Nat) :=
  if arena.size < entryLimit then .ok (allocate arena node) else .error .termLimit

variable {arena old after : Arena} {node : Node} {id start : Nat} {failure : BadReference}

/-- The exact graph result, including the first bad reference, depends only
on the ordered list of child references at every position. -/
theorem checkGraph_references {left right : Arena}
    (same : left.map Node.references = right.map Node.references) (checkedNodes : Nat) :
    checkGraph left checkedNodes = checkGraph right checkedNodes := by
  have sizes : left.size = right.size := by
    simpa only [Array.size_map] using congrArg Array.size same
  have scans : scanNode left = scanNode right := by
    funext i
    have refs : left[i]?.map Node.references = right[i]?.map Node.references := by
      simpa only [Array.getElem?_map] using congrArg (fun refs : Array (List Nat) => refs[i]?) same
    cases h₁ : left[i]? <;> cases h₂ : right[i]? <;> simp [h₁, h₂] at refs
    · simp [scanNode, h₁, h₂]
    · simp [scanNode, h₁, h₂, refs]
  simp only [checkGraph, scanSuffix, sizes, scans]

private theorem scanNode_clear (arena : Arena) (id : Nat) :
    scanNode arena id = none ↔
      ∀ node, arena[id]? = some node → ∀ child ∈ node.references, child < id := by
  cases lookup : arena[id]? with
  | none => simp [scanNode, lookup]
  | some node =>
      have clear : scanNode arena id = none ↔
          node.references.find? (fun ref => decide (id ≤ ref)) = none := by
        cases h : node.references.find? (fun ref => decide (id ≤ ref)) <;>
          simp [scanNode, lookup, h]
      rw [clear, List.find?_eq_none]
      simp [Nat.not_le]

private theorem mem_suffix {arena : Arena} {start id : Nat} :
    id ∈ List.range' start (arena.size - start) ↔ start ≤ id ∧ id < arena.size := by
  rw [List.mem_range']
  constructor
  · rintro ⟨offset, bound, matchId⟩
    simp only [Nat.one_mul] at matchId
    omega
  · rintro ⟨before, bound⟩
    exact ⟨id - start, by omega, by simp; omega⟩

theorem scanSuffix_clear (arena : Arena) (start : Nat) :
    scanSuffix arena start = none ↔
      ∀ id node, start ≤ id → arena[id]? = some node →
        ∀ child ∈ node.references, child < id := by
  rw [scanSuffix, List.findSome?_eq_none_iff]
  constructor
  · intro clean id node startBound lookup child member
    have valid := (Array.getElem?_eq_some_iff.mp lookup).1
    exact (scanNode_clear _ _).mp (clean id (mem_suffix.mpr ⟨startBound, valid⟩))
      node lookup child member
  · intro clean id member
    exact (scanNode_clear _ _).mpr (clean id · (mem_suffix.mp member).1 ·)

/-- The error identifies the earliest failing node in the suffix and its first
non-backward child in the original reference order. -/
theorem scanSuffix_first_failure (failed : scanSuffix arena start = some failure) :
    ∃ checked later node earlierRefs laterRefs,
      List.range' start (arena.size - start) = checked ++ failure.node :: later ∧
      (∀ id ∈ checked, ∀ known, arena[id]? = some known →
        ∀ child ∈ known.references, child < id) ∧
      arena[failure.node]? = some node ∧
      node.references = earlierRefs ++ failure.child :: laterRefs ∧
      (∀ child ∈ earlierRefs, child < failure.node) ∧ failure.node ≤ failure.child := by
  obtain ⟨checked, id, later, rows, hit, preceding⟩ := List.findSome?_eq_some_iff.mp failed
  cases lookup : arena[id]? with
  | none => simp [scanNode, lookup] at hit
  | some node =>
      cases bad : node.references.find? (fun ref => decide (id ≤ ref)) with
      | none => simp [scanNode, lookup, bad] at hit
      | some child =>
          simp [scanNode, lookup, bad] at hit
          subst failure
          obtain ⟨outOfRange, earlierRefs, laterRefs, refs, good⟩ :=
            List.find?_eq_some_iff_append.mp bad
          exact ⟨checked, later, node, earlierRefs, laterRefs, rows,
            fun j member => (scanNode_clear _ _).mp (preceding j member), lookup, refs,
            fun ref member => by simpa [Nat.not_le] using good ref member,
            of_decide_eq_true outOfRange⟩

theorem checkGraph_ok_iff (arena : Arena) (checkedNodes : Nat) :
    checkGraph arena checkedNodes = .ok () ↔
      arena.size ≤ entryLimit ∧
      ∀ id node, checkedNodes ≤ id → arena[id]? = some node →
        ∀ child ∈ node.references, child < id := by
  rw [← scanSuffix_clear]
  by_cases over : entryLimit < arena.size
  · simp [checkGraph, over, Nat.not_le.mpr over]
  · have cap := Nat.le_of_not_gt over
    cases h : scanSuffix arena checkedNodes <;> simp [checkGraph, over, h, cap]

/-- `Core.check` resets `checked_nodes`, so its graph phase examines all nodes. -/
theorem checkGraph_full (arena : Arena) :
    checkGraph arena 0 = .ok () ↔ arena.size ≤ entryLimit ∧ Backward arena := by
  simp [checkGraph_ok_iff, Backward]

/-- The cached prefix has to be immutable. The suffix scan then establishes
the same full graph property as a scan from zero. -/
theorem checkGraph_extend (preserved : Prefix old arena) (checked : Backward old) :
    checkGraph arena old.size = .ok () ↔ arena.size ≤ entryLimit ∧ Backward arena := by
  rw [checkGraph_ok_iff]
  constructor
  · rintro ⟨cap, suffix⟩
    refine ⟨cap, ?_⟩
    intro id node lookup child member
    by_cases before : id < old.size
    · have original : old[id]? = some (old[id]'before) := Array.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
      have same := Option.some.inj ((preserved.lookup original).symm.trans lookup)
      subst node
      exact checked id _ original child member
    · exact suffix id node (by omega) lookup child member
  · rintro ⟨cap, backward⟩
    exact ⟨cap, fun id node _ => backward id node⟩

/-- A successful `Core.add` appends at the old length and keeps all old nodes.
The result fits the native u32 reference space. -/
theorem addNode_commits (added : addNode arena node = .ok (after, id)) :
    Prefix arena after ∧ id = arena.size ∧ id < 2 ^ 32 ∧ after.size = arena.size + 1 ∧
      after.size ≤ entryLimit ∧ after[id]? = some node := by
  unfold addNode at added
  split at added
  · rename_i cap
    cases added
    exact ⟨Prefix.push _ _, rfl, by unfold entryLimit at cap; omega,
      by simp, by simp; omega, by simp⟩
  · contradiction

/-- One append passes the actual incremental scan precisely when all its
children existed before the append. The old prefix is checked separately. -/
theorem checkGraph_new_node (added : addNode arena node = .ok (after, id)) :
    checkGraph after arena.size = .ok () ↔ ∀ child ∈ node.references, child < id := by
  obtain ⟨_, sameId, _, grows, cap, selected⟩ := addNode_commits added
  rw [checkGraph_ok_iff]
  constructor
  · rintro ⟨_, suffix⟩
    exact suffix id node (by omega) selected
  · intro children
    refine ⟨cap, ?_⟩
    intro root result lower lookup
    have upper := (Array.getElem?_eq_some_iff.mp lookup).1
    have same : root = id := by omega
    subst root
    have resultEq := Option.some.inj (lookup.symm.trans selected)
    subst result
    exact children

theorem addNode_preserves_backward (checked : Backward arena)
    (added : addNode arena node = .ok (after, id))
    (known : ∀ child ∈ node.references, child < id) : Backward after := by
  have preserved := (addNode_commits added).1
  exact ((checkGraph_extend preserved checked).mp ((checkGraph_new_node added).mpr known)).2

private theorem mapM_some {f : α → Option β} {xs : List α}
    (each : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨y, head⟩ := each x (by simp)
      obtain ⟨ys, tail⟩ := ih (fun a member => each a (List.mem_cons_of_mem _ member))
      exact ⟨y :: ys, by simp [List.mapM_cons, head, tail]⟩

/-- When the source constructor projection also has the native arities, all
checked nodes have a tree interpretation. Descending indices give the explicit
fuel bound without an additional well-foundedness assumption. -/
theorem checkedGraph_decode {root fuel : Nat} (checked : checkGraph arena 0 = .ok ())
    (shaped : ∀ (id : Nat) (op : Op) (refs : List Nat),
      arena[id]? = some (.node op refs) → refs.length = op.arity)
    (selected : root < arena.size) (budget : root < fuel) :
    ∃ term, decode fuel arena root = some term := by
  have backward := ((checkGraph_full _).mp checked).2
  induction fuel generalizing root with
  | zero => omega
  | succ fuel ih =>
      cases lookup : arena[root]'selected with
      | var index =>
          have found := Array.getElem?_eq_some_iff.mpr ⟨selected, lookup⟩
          exact ⟨.var index, by simp [decode, found]⟩
      | node op refs =>
          have found := Array.getElem?_eq_some_iff.mpr ⟨selected, lookup⟩
          have arity := shaped root op refs found
          obtain ⟨args, decoded⟩ : ∃ args, refs.mapM (decode fuel arena) = some args :=
            mapM_some fun child member => by
              have earlier := backward root (.node op refs) found child member
              exact ih (by omega) (by omega)
          exact ⟨.node op args, by simp [decode, found, arity, decoded]⟩

/-- Exact-byte Loan64 admission supplies a snapshot satisfying the separate
production graph-phase limits and reference checks. -/
theorem checkBytes_core_graph
    (accepted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ snapshot, NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      checkGraph snapshot.arena 0 = .ok () := by
  obtain ⟨snapshot, _, _, _, encoded, valid, backward, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound accepted
  refine ⟨snapshot, encoded, (checkGraph_full _).mpr ⟨?_, backward⟩⟩
  have capacity := NativeWire.graphValid_size valid
  unfold entryLimit
  omega

end Jihoo.NativeKernel.NativeCoreGraph
