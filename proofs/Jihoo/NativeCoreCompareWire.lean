import Jihoo.NativeCoreGraphWire
import Jihoo.NativeACUNormalizer

/-! Structural comparison at the v6 writer boundary. The constructor rank is
the production ordering, the payload is the signed widened scalar vector,
and only the conversion children are followed. -/
namespace Jihoo.NativeKernel.NativeCoreCompare

open NativeArena NativeCoreGraph GraphCertificates.Canonical
open ACU.Canonical (rank payload)

abbrev Header := Nat × List Int

inductive View (α : Type) where
  | strict (result : α)
  | plain (head : Header) (children : List α)

/-- The writer preserves its stable tags even where the production sorting
rank inserted later constructors elsewhere in the ordering. -/
def wireRank : Nat → Nat
  | 32 => 43
  | 33 => 44
  | 34 => 45
  | 35 => 51
  | 36 => 52
  | 37 => 53
  | 38 => 47
  | 39 => 48
  | 40 => 46
  | 41 => 50
  | 42 => 49
  | 43 => 32
  | 44 => 33
  | 45 => 34
  | 46 => 35
  | 47 => 36
  | 48 => 37
  | 49 => 38
  | 50 => 39
  | 51 => 40
  | 52 => 41
  | 53 => 42
  | tag => tag

theorem wireRank_schema (op : Op) : wireRank (NativeSchema.tag op) = rank op := by
  cases op <;> rfl

/-- For comparison, vector length is handled after the common children.
The integer sign and magnitude are interpreted as one widened signed value. -/
def wirePayload : Nat → List Nat → List Int
  | 48, [0, magnitude] => [(magnitude : Int)]
  | 48, [1, magnitude] => [-(magnitude : Int)]
  | 11, fields | 13, fields | 43, fields => (fields.take 1).map (fun n : Nat => (n : Int))
  | 12, fields | 40, fields => (fields.take 2).map (fun n : Nat => (n : Int))
  | 49, _ => []
  | _, fields => fields.map (fun n : Nat => (n : Int))

theorem wirePayload_schema (op : Op) :
    wirePayload (NativeSchema.tag op) (NativeSchema.payload op) = payload op := by
  cases op
  all_goals first | rfl | skip
  case arith op => cases op <;> rfl
  case pi erased => cases erased <;> rfl
  case lam erased => cases erased <;> rfl
  case back erased => cases erased <;> rfl
  case give erased => cases erased <;> rfl
  case view recursive family count => cases recursive <;> rfl
  case integer value => cases value <;> rfl

def conversionChildren (op : Op) (children : List α) : List α :=
  match op with
  | .usub | .pack | .give true => children.take 2
  | _ => children

def wireChildren (tag : Nat) (fields : List Nat) (children : List α) : List α :=
  if tag = 21 ∨ tag = 24 ∨ (tag = 36 ∧ fields = [1]) then children.take 2 else children

theorem wireChildren_schema (op : Op) (children : List α) :
    wireChildren (NativeSchema.tag op) (NativeSchema.payload op) children =
      conversionChildren op children := by
  cases op
  all_goals first | rfl | skip
  case give erased => cases erased <;> rfl

def syntaxView (op : Op) (children : List α) : View α :=
  if op = .strict then
    match children with
    | [_, result] => .strict result
    | _ => .plain (rank op, payload op) (conversionChildren op children)
  else .plain (rank op, payload op) (conversionChildren op children)

def wireView (word : NodeWords) : View Nat :=
  let tag := word.tag.toNat
  let fields := word.fields.map UInt64.toNat
  let children := word.children.map UInt32.toNat
  match tag, children with
  | 16, [_, result] => .strict result
  | _, _ => .plain (wireRank tag, wirePayload tag fields) (wireChildren tag fields children)

def nodeView : Node → View Nat
  | .var index => .plain (0, [Int.ofNat index]) []
  | .node op children => syntaxView op children

private theorem ofCode_exact (decoded : NativeSchema.ofCode tag fields = some op) :
    tag = NativeSchema.tag op ∧ fields = NativeSchema.payload op := by
  -- Compute tags 0 through 53 separately and reject every larger tag.
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first
    | cases decoded <;> exact ⟨rfl, rfl⟩
    | rcases fields with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
      all_goals first
        | cases decoded <;> exact ⟨rfl, rfl⟩
        | rcases a with _ | _ | _ | _ <;> cases decoded <;> exact ⟨rfl, rfl⟩
        | rcases a with _ | _ | _ | _ <;>
            rcases b with _ | _ <;> cases decoded <;> exact ⟨rfl, rfl⟩

private theorem op_view (op : Op) (children : List Nat) :
    (match NativeSchema.tag op, children with
    | 16, [_, result] => View.strict result
    | _, _ => .plain (wireRank (NativeSchema.tag op), wirePayload (NativeSchema.tag op) (NativeSchema.payload op))
        (wireChildren (NativeSchema.tag op) (NativeSchema.payload op) children)) =
      nodeView (.node op children) := by
  simp only [nodeView, wireRank_schema, wirePayload_schema, wireChildren_schema]
  cases op <;> try rfl
  all_goals rcases children with _ | ⟨first, _ | ⟨result, _ | ⟨extra, rest⟩⟩⟩ <;> rfl

/-- Successful decoding retains exactly the comparison header and ordered
references, including the four exceptional child views. -/
theorem wireView_refines {words : NodeWords} {node : Node} (decoded : words.toNode = some node) :
    wireView words = nodeView node := by
  unfold NodeWords.toNode at decoded
  split at decoded
  · rename_i tag
    dsimp only at decoded
    split at decoded
    · rename_i index _ _ fields children
      cases decoded
      simp [wireView, tag, fields, children, wireRank, wirePayload, wireChildren, nodeView]
    · contradiction
  · cases code : NativeSchema.ofCode words.tag.toNat (words.fields.map UInt64.toNat) with
    | none => simp [code] at decoded
    | some op =>
        obtain ⟨tag, fields⟩ := ofCode_exact code
        simp only [code, Option.map_some, Option.some.injEq] at decoded
        subst node
        unfold wireView
        rw [tag, fields]
        exact op_view _ _

/-- Parse the exact observed row bytes and recover its production comparison
view, before consulting any referenced child. -/
theorem parse_comparison_view (words : NodeWords) (fits : words.fits)
    (parsed : NativeWire.parseNode (words.encode ++ tail) = some (node, rest)) :
    tail = rest ∧ wireView words = nodeView node := by
  rw [parseNodeWords words fits tail] at parsed
  cases decoded : words.toNode with
  | none => simp [decoded] at parsed
  | some selected =>
      simp only [decoded, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      exact ⟨rfl, wireView_refines decoded⟩

/-- The signed production payload has an exact i128 interpretation even for
a full-range unsigned field or the signed minimum. -/
theorem wirePayload_fits (word : NodeWords) (value : Int)
    (member : value ∈ wirePayload word.tag.toNat (word.fields.map UInt64.toNat)) :
    -(2 ^ 127 : Int) ≤ value ∧ value < 2 ^ 127 := by
  have inWord : ∀ n ∈ word.fields.map UInt64.toNat, n < 2 ^ 64 := by
    intro n present
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp present
    exact field.toNat_lt
  generalize tagEq : word.tag.toNat = tag at member
  generalize fieldsEq : word.fields.map UInt64.toNat = fields at member inWord
  clear tagEq fieldsEq
  unfold wirePayload at member
  split at member
  all_goals try simp only [List.mem_singleton, List.not_mem_nil] at member
  all_goals first
    | rename_i magnitude
      subst value
      have bounded := inWord magnitude (by simp)
      omega
    | obtain ⟨n, present, rfl⟩ := List.mem_map.mp member
      have bounded := inWord n (by first | exact present | exact List.mem_of_mem_take present)
      omega

/-- A source Integer's signed cast and its v6 sign/magnitude representation
give the same comparison scalar, including Int64.minValue. -/
theorem writtenInteger_payload (value : Int64) :
    wirePayload 48 ((NativeWire.integerPayloadWords value).map UInt64.toNat) = [value.toInt] := by
  rw [NativeWire.integerPayloadWords_refines]
  exact wirePayload_schema (.integer value.toInt)

inductive Shape where
  | node (head : Header) (children : List Shape)

private def View.map (f : α → β) : View α → View β
  | .strict result => .strict (f result)
  | .plain head children => .plain head (children.map f)

private def View.finish : View Shape → Shape
  | .strict result => result
  | .plain head children => .node head children

mutual
  /-- An independent structural identity on trees, following precisely the
  result of Strict and the conversion children of every other operator. -/
  def project : Term → Shape
    | .var index => .node (0, [index]) []
    | .node op children => (syntaxView op (projectArgs children)).finish
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf; all_goals omega

  def projectArgs : List Term → List Shape
    | [] => []
    | term :: terms => project term :: projectArgs terms
  termination_by terms => sizeOf terms
  decreasing_by all_goals simp_wf; all_goals omega
end

private theorem projectArgs_map (args : List Term) : projectArgs args = args.map project := by
  induction args with
  | nil => simp only [projectArgs, List.map_nil]
  | cons term terms ih => simp only [projectArgs, List.map_cons, ih]

private theorem conversionChildren_map (op : Op) (args : List α) (f : α → β) :
    conversionChildren op (args.map f) = (conversionChildren op args).map f := by
  cases op <;> try rfl
  case usub => exact List.map_take.symm
  case pack => exact List.map_take.symm
  case give erased =>
    cases erased
    · rfl
    · exact List.map_take.symm

private theorem syntaxView_map (op : Op) (args : List α) (f : α → β) :
    syntaxView op (args.map f) = (syntaxView op args).map f := by
  by_cases strict : op = .strict
  · subst op
    rcases args with _ | ⟨first, _ | ⟨result, _ | ⟨extra, rest⟩⟩⟩ <;> rfl
  · simp only [syntaxView, ite_eq_right strict, View.map, conversionChildren_map]

private theorem project_node (op : Op) (args : List Term) :
    project (.node op args) = ((syntaxView op args).map project).finish := by
  rw [project, projectArgs_map, syntaxView_map]

private def tagForRank (order : Nat) : Nat :=
  ((List.range 54).find? fun candidate => wireRank candidate == order).getD order

private theorem tagForRank_schema (op : Op) : tagForRank (rank op) = NativeSchema.tag op := by
  cases op <;> rfl

private def payloadForArity (tag arity : Nat) (fields : List Int) : List Nat :=
  match tag, fields with
  | 48, [.ofNat value] => [0, value]
  | 48, [.negSucc value] => [1, value + 1]
  | 11, fields | 12, fields => fields.map Int.toNat ++ [arity]
  | 13, fields | 40, fields | 43, fields => fields.map Int.toNat ++ [arity - 2]
  | 49, _ => [arity]
  | _, fields => fields.map Int.toNat

private theorem payloadForArity_schema (op : Op) :
    payloadForArity (NativeSchema.tag op) op.arity (payload op) = NativeSchema.payload op := by
  cases op
  all_goals first | rfl | skip
  case arith operation => cases operation <;> rfl
  case back erased => cases erased <;> rfl
  case give erased => cases erased <;> rfl
  case view recursive family count => cases recursive <;> rfl
  case pi erased => cases erased <;> rfl
  case lam erased => cases erased <;> rfl
  case integer value => cases value <;> rfl

/-- The comparison header and full child arity determine the constructor.
For vector constructors, the arity recovers the length omitted by the
comparison payload. -/
theorem header_injective (same : (rank first, payload first) = (rank second, payload second))
    (arity : first.arity = second.arity) : first = second := by
  have tags : NativeSchema.tag first = NativeSchema.tag second := by
    simpa only [tagForRank_schema] using congrArg (fun header : Header => tagForRank header.1) same
  have fields : NativeSchema.payload first = NativeSchema.payload second := by
    rw [← payloadForArity_schema first, ← payloadForArity_schema second, tags, arity, (Prod.mk.inj same).2]
  apply Option.some.inj
  rw [← NativeSchema.ofCode_payload first, ← NativeSchema.ofCode_payload second, tags, fields]

/-- A tree on which identity retains every constructor and every child. -/
inductive FullyRetained : Term → Prop where
  | var (index : Nat) : FullyRetained (.var index)
  | node (ordinary : op ≠ .strict) (kept : conversionChildren op args = args)
      (arity : args.length = op.arity) (children : ∀ child ∈ args, FullyRetained child) :
      FullyRetained (.node op args)

private theorem take_kept_of_length {before after : List Term} (length : before.length = after.length)
    (kept : before.take 2 = before) : after.take 2 = after := by
  apply List.take_of_length_le
  rw [← length, ← kept]
  exact List.length_take_le _ _

/-- Retention selects positions by constructor and child count. Replacing
the children without changing their count preserves full retention. -/
theorem children_kept_of_length {before after : List Term}
    (length : before.length = after.length) (kept : conversionChildren op before = before) :
    conversionChildren op after = after := by
  cases op <;> try rfl
  case usub => exact take_kept_of_length length kept
  case pack => exact take_kept_of_length length kept
  case give erased => cases erased <;> first | rfl | exact take_kept_of_length length kept

private theorem retained_node (ordinary : op ≠ .strict) (kept : conversionChildren op args = args) :
    project (.node op args) = .node (rank op, payload op) (args.map project) := by
  rw [project_node]
  simp only [syntaxView, ite_eq_right ordinary, kept, View.map, View.finish]

private theorem rank_positive (op : Op) : rank op ≠ 0 := by
  cases op <;> simp [rank]

private theorem project_children_injective {inputs outputs : List Term}
    (mapped : inputs.map project = outputs.map project)
    (right : ∀ child ∈ outputs, FullyRetained child)
    (use : ∀ child ∈ inputs, ∀ other, FullyRetained other → project child = project other → child = other) :
    inputs = outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp_all
  | cons child rest ih =>
      cases outputs with
      | nil => simp at mapped
      | cons other later =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          have head := use child List.mem_cons_self other (right other List.mem_cons_self) mapped.1
          have tail := ih mapped.2 (fun term member => right term (List.mem_cons_of_mem _ member))
            (fun term member => use term (List.mem_cons_of_mem _ member))
          rw [head, tail]

/-- Equality of the retained shapes reflects equality of the entire source
trees when the comparison retained every field. -/
theorem project_injective_of_fully_retained (left : FullyRetained first) (right : FullyRetained second)
    (matched : project first = project second) : first = second := by
  induction left generalizing second with
  | var index =>
      cases right with
      | var other =>
          simp only [project, Shape.node.injEq, Prod.mk.injEq, List.cons.injEq] at matched
          have same : index = other := by omega
          rw [same]
      | @node op args ordinary kept _ _ =>
          rw [project, retained_node ordinary kept] at matched
          exact False.elim (rank_positive op ((Prod.mk.inj (Shape.node.inj matched).1).1.symm))
  | @node op inputs ordinary kept arity _ ih =>
      cases right with
      | var index =>
          rw [retained_node ordinary kept, project] at matched
          exact False.elim (rank_positive op (Prod.mk.inj (Shape.node.inj matched).1).1)
      | @node other outputs otherOrdinary otherKept otherArity otherChildren =>
          rw [retained_node ordinary kept, retained_node otherOrdinary otherKept] at matched
          obtain ⟨header, children⟩ := Shape.node.inj matched
          have same := project_children_injective children otherChildren
            (fun child member _ fully same => ih child member fully same)
          have sameArity : op.arity = other.arity := arity.symm.trans
            ((congrArg List.length same).trans otherArity)
          rw [header_injective header sameArity, same]

def compareHeader (left right : Header) : Ordering :=
  (compare left.1 right.1).then (compare left.2 right.2)

private theorem compareHeader_eq (left right : Header) : compareHeader left right = .eq ↔ left = right := by
  simp [compareHeader, Ordering.then_eq_eq, Prod.ext_iff]

mutual
  /-- Lexicographic constructor, scalar and recursive child ordering. -/
  def compareShape : Shape → Shape → Ordering
    | .node left xs, .node right ys => (compareHeader left right).then (compareShapes xs ys)
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

  def compareShapes : List Shape → List Shape → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys => (compareShape x y).then (compareShapes xs ys)
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem compareShape_eq (left right : Shape) : compareShape left right = .eq ↔ left = right := by
  induction left using Shape.rec (motive_2 := fun xs => ∀ ys, compareShapes xs ys = .eq ↔ xs = ys)
      generalizing right with
  | node head children ih =>
      cases right
      simp [compareShape, Ordering.then_eq_eq, compareHeader_eq, ih]
  | nil =>
      rename_i ys
      cases ys <;> simp [compareShapes]
  | cons head tail ihHead ihTail =>
      rename_i ys
      cases ys <;> simp [compareShapes, Ordering.then_eq_eq, ihHead, ihTail]

private def compareRefs (step : Nat → Nat → Nat → Option (Ordering × Nat)) :
    Nat → List Nat → List Nat → Option (Ordering × Nat)
  | work, [], [] => some (.eq, work)
  | work, [], _ :: _ => some (.lt, work)
  | work, _ :: _, [] => some (.gt, work)
  | work, x :: xs, y :: ys => do
      let (result, remaining) ← step work x y
      match result with
      | .eq => compareRefs step remaining xs ys
      | other => some (other, remaining)

/-- Each call consumes one tick. A shared root can return immediately after
the tick, and each recursive child or Strict descent uses one less depth. -/
private def compareViews (read : Nat → Option (View Nat)) : Nat → Nat → Nat → Nat → Option (Ordering × Nat)
  | 0, _, _, _ => none
  | _ + 1, 0, _, _ => none
  | depth + 1, work + 1, a, b => do
      let left ← read a
      if a = b then some (.eq, work) else
        match left with
        | .strict result => compareViews read depth work result b
        | .plain x xs => do
            let right ← read b
            match right with
            | .strict result => compareViews read depth work a result
            | .plain y ys =>
                match compareHeader x y with
                | .eq => compareRefs (compareViews read depth) work xs ys
                | other => some (other, work)

def compareGraph (words : List NodeWords) : Nat → Nat → Nat → Nat → Option (Ordering × Nat) :=
  compareViews (fun ref => words[ref]?.map wireView)

/-- Compare live rows, including atoms appended earlier in normalization. -/
def compareArena (arena : Arena) : Nat → Nat → Nat → Nat → Option (Ordering × Nat) :=
  compareViews (fun ref => arena[ref]?.map nodeView)

private theorem represented_take (count : Nat) (children : RepresentsList arena refs terms) :
    RepresentsList arena (refs.take count) (terms.take count) := by
  induction count generalizing refs terms with
  | zero => exact .nil
  | succ count ih =>
      cases children with
      | nil => exact .nil
      | cons head rest => exact .cons head (ih rest)

private theorem conversionChildren_represented (op : Op) (children : RepresentsList arena refs terms) :
    RepresentsList arena (conversionChildren op refs) (conversionChildren op terms) := by
  cases op <;> try exact children
  case usub => exact represented_take 2 children
  case pack => exact represented_take 2 children
  case give erased => cases erased <;> first | exact children | exact represented_take 2 children

def ViewMatches (arena : Arena) (view : View Nat) (term : Term) : Prop :=
  match view with
  | .strict root => ∃ inner, Represents arena root inner ∧ project term = project inner
  | .plain head refs => ∃ children, RepresentsList arena refs children ∧
      project term = Shape.node head (children.map project)

private theorem syntaxView_matches (op : Op) (children : RepresentsList arena refs terms) :
    ViewMatches arena (syntaxView op refs) (.node op terms) := by
  unfold ViewMatches
  rw [project_node]
  by_cases strict : op = .strict
  · subst op
    cases children with
    | nil => exact ⟨[], .nil, rfl⟩
    | cons first tail =>
        cases tail with
        | nil => exact ⟨_, .cons first .nil, rfl⟩
        | cons result rest =>
            cases rest with
            | nil => exact ⟨_, result, rfl⟩
            | cons extra rest => exact ⟨_, .cons first (.cons result (.cons extra rest)), rfl⟩
  · simp only [syntaxView, ite_eq_right strict, View.map, View.finish]
    exact ⟨_, conversionChildren_represented op children, rfl⟩

private theorem mapM_read {index : Nat} {words : List NodeWords} {nodes : List Node}
    (aligned : words.mapM NodeWords.toNode = some nodes) (read : nodes[index]? = some node) :
    ∃ word, words[index]? = some word ∧ word.toNode = some node := by
  induction words generalizing index nodes with
  | nil => simp at aligned; subst nodes; simp at read
  | cons word words ih =>
      simp only [List.mapM_cons] at aligned
      obtain ⟨first, head, aligned⟩ := Option.bind_eq_some_iff.mp aligned
      obtain ⟨rest, tail, aligned⟩ := Option.bind_eq_some_iff.mp aligned
      cases aligned
      cases index with
      | zero =>
          cases read
          exact ⟨word, rfl, head⟩
      | succ index => exact ih tail read

/-- Every represented node supplies the comparison view of its actual arena
row, including the ordered children retained by conversion. -/
theorem arena_view_matches (represented : Represents arena root term) :
    ∃ node, arena[root]? = some node ∧ ViewMatches arena (nodeView node) term := by
  cases represented with
  | var read => exact ⟨_, read, [], .nil, by simp [project]⟩
  | node read _ children => exact ⟨_, read, syntaxView_matches _ children⟩

/-- Decoded rows and their original snapshot words supply the same
comparison lookup at every reference, including missing rows. -/
theorem comparison_rows_agree {words : List NodeWords} {nodes : List Node}
    (aligned : words.mapM NodeWords.toNode = some nodes) :
    words.map wireView = nodes.map nodeView := by
  induction words generalizing nodes with
  | nil =>
      simp at aligned
      subst nodes
      rfl
  | cons word words ih =>
      simp only [List.mapM_cons] at aligned
      obtain ⟨first, decoded, aligned⟩ := Option.bind_eq_some_iff.mp aligned
      obtain ⟨later, rest, aligned⟩ := Option.bind_eq_some_iff.mp aligned
      cases aligned
      simp only [List.map_cons, wireView_refines decoded, ih rest]

theorem compareArena_agrees_wire (aligned : words.mapM NodeWords.toNode = some arena.toList) :
    compareArena arena depth work a b = compareGraph words depth work a b := by
  have views := comparison_rows_agree aligned
  have reads : (fun ref : Nat => arena[ref]?.map nodeView) = fun ref => words[ref]?.map wireView := by
    funext ref
    have corresponding := congrArg (fun rows : List (View Nat) => rows[ref]?) views
    simpa using corresponding.symm
  unfold compareArena compareGraph
  rw [reads]

/-- An observed row at a represented root is related to the same projected
subtree or to the exact ordered list of retained child terms. -/
theorem wire_matches {words : List NodeWords} {arena : Arena}
    (aligned : words.mapM NodeWords.toNode = some arena.toList)
    (represented : Represents arena root term) :
    ∃ word, words[root]? = some word ∧ ViewMatches arena (wireView word) term := by
  obtain ⟨node, read, matched⟩ := arena_view_matches represented
  obtain ⟨word, found, decoded⟩ := mapM_read aligned (by simpa using read)
  exact ⟨word, found, by rw [wireView_refines decoded]; exact matched⟩

private theorem compareRefs_sound {step : Nat → Nat → Nat → Option (Ordering × Nat)}
    (stepSound : ∀ work a b first second result remaining,
      Represents arena a first → Represents arena b second →
      step work a b = some (result, remaining) → result = compareShape (project first) (project second))
    (left : RepresentsList arena xs firsts) (right : RepresentsList arena ys seconds)
    (computed : compareRefs step work xs ys = some (result, remaining)) :
    result = compareShapes (firsts.map project) (seconds.map project) := by
  induction left using RepresentsList.rec (motive_1 := fun _ _ _ => True)
      generalizing work ys seconds with
  | var | node => trivial
  | nil =>
      cases right <;> cases computed <;> simp [compareShapes]
  | @cons a first xs firsts head rest _ ih =>
      cases right with
      | nil => cases computed; simp [compareShapes]
      | @cons b second ys seconds rightHead rightRest =>
          simp only [compareRefs] at computed
          obtain ⟨⟨order, budget⟩, firstResult, computed⟩ := Option.bind_eq_some_iff.mp computed
          have firstOrder := stepSound work a b first second order budget head rightHead firstResult
          simp only [List.map_cons, compareShapes, ← firstOrder]
          cases order with
          | lt => cases computed; rfl
          | eq => exact ih rightRest computed
          | gt => cases computed; rfl

private theorem compareViews_sound {read : Nat → Option (View Nat)}
    (observes : ∀ {root term}, Represents arena root term →
      ∃ observed, read root = some observed ∧ ViewMatches arena observed term)
    (left : Represents arena a first) (right : Represents arena b second)
    (computed : compareViews read depth work a b = some (result, remaining)) :
    result = compareShape (project first) (project second) := by
  induction depth generalizing work a b first second result remaining with
  | zero => simp [compareViews] at computed
  | succ depth ih =>
      cases work with
      | zero => simp [compareViews] at computed
      | succ work =>
          obtain ⟨leftObserved, atLeft, leftView⟩ := observes left
          simp only [compareViews, atLeft, Bind.bind, Option.bind] at computed
          by_cases same : a = b
          · subst b
            simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at computed
            have equal := Represents.unique left right
            subst second
            exact computed.1.symm.trans ((compareShape_eq _ _).mpr rfl).symm
          · rw [ite_eq_right same] at computed
            cases leftObserved with
            | strict next =>
                obtain ⟨child, childRep, eq⟩ := leftView
                rw [eq]
                exact ih childRep right computed
            | plain x xs =>
                obtain ⟨childrenLeft, kidsLeft, eqLeft⟩ := leftView
                obtain ⟨rightObserved, atRight, rightView⟩ := observes right
                simp only [atRight] at computed
                cases rightObserved with
                | strict next =>
                    obtain ⟨child, childRep, eq⟩ := rightView
                    rw [eq]
                    exact ih left childRep computed
                | plain y ys =>
                    obtain ⟨childrenRight, kidsRight, eqRight⟩ := rightView
                    rw [eqLeft, eqRight, compareShape]
                    dsimp only at computed
                    cases heads : compareHeader x y <;> rw [heads] at computed
                    · cases computed; rfl
                    · exact compareRefs_sound (fun _ _ _ _ _ _ _ => ih) kidsLeft kidsRight computed
                    · cases computed; rfl

/-- On represented live terms the sorted ordering uses the same projection
as identity, with the exact simulated comparison budget. -/
theorem compareArena_refines (left : Represents arena a first) (right : Represents arena b second)
    (computed : compareArena arena depth work a b = some (result, remaining)) :
    result = compareShape (project first) (project second) := by
  apply compareViews_sound _ left right computed
  intro _ _ represented
  obtain ⟨node, read, matched⟩ := arena_view_matches represented
  exact ⟨nodeView node, by simp [read], matched⟩

/-- Successful direct graph comparison agrees with the independent tree
projection throughout the decoded version-6 arena. -/
theorem compareGraph_refines (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ tail) =
      some (snapshot, rest))
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (computed : compareGraph words depth work a b = some (result, remaining)) :
    result = compareShape (project first) (project second) := by
  rw [parseObservedProgram _ _ _ fits] at parsed
  cases aligned : words.mapM NodeWords.toNode with
  | none => simp [aligned] at parsed
  | some nodes =>
      simp only [aligned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      rw [← compareArena_agrees_wire (by simpa using aligned)] at computed
      exact compareArena_refines left right computed

theorem compareGraph_zero_iff (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ tail) =
      some (snapshot, rest))
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (computed : compareGraph words depth work a b = some (result, remaining)) :
    result = .eq ↔ project first = project second := by
  rw [compareGraph_refines fits parsed left right computed]
  exact compareShape_eq _ _

end Jihoo.NativeKernel.NativeCoreCompare
