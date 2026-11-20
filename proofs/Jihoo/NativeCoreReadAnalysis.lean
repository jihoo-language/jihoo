import Jihoo.NativeCoreTrapAnalysis

/-! Core.reads conservatively recognizes borrowed reads and loop work.
The result of a View and the head of an application are inspected using
the same live rows that the normalizer will use. -/
namespace Jihoo.NativeKernel.NativeCoreReadAnalysis

open NativeArena
open NativeCoreTrapAnalysis (CallHead graphHead graphHead_refines termHead)

private def nodeRow : Node → Option (Op × List Nat)
  | .var _ => none
  | .node op children => some (op, children)

private def termRow : Term → Option (Op × List Term)
  | .var _ => none
  | .node op children => some (op, children)

private def isPi (row : Option (Op × List α)) : Bool :=
  match row with
  | some (.pi _, _) => true
  | _ => false

private def motiveYieldsFunction (read : α → Option (Op × List α)) (motive : α) : Bool :=
  match read motive with
  | some (.lam _, [_, body]) => isPi (read body)
  | row => isPi row

private def graphRow (arena : Arena) (ref : Nat) : Option (Op × List Nat) :=
  (arena[ref]?).bind nodeRow

private theorem isPi_refines (represented : Represents arena ref term) :
    isPi (graphRow arena ref) = isPi (termRow term) := by
  cases represented with
  | var lookup => simp [graphRow, lookup, nodeRow, termRow, isPi]
  | @node _ op refs terms lookup arity children =>
      cases op <;> simp [graphRow, lookup, nodeRow, termRow, isPi]

private theorem motive_refines (represented : Represents arena ref term) :
    motiveYieldsFunction (graphRow arena) ref = motiveYieldsFunction termRow term := by
  cases represented with
  | var lookup => simp [motiveYieldsFunction, graphRow, lookup, nodeRow, termRow, isPi]
  | @node _ op refs terms lookup arity children =>
      cases op
      all_goals try solve | simp [motiveYieldsFunction, graphRow, lookup, nodeRow, termRow, isPi]
      case lam =>
        cases children with
        | nil => cases arity
        | cons first rest =>
            cases rest with
            | nil => cases arity
            | cons body leftover =>
                cases leftover with
                | cons => cases arity
                | nil =>
                    simpa [motiveYieldsFunction, graphRow, lookup, nodeRow, termRow] using isPi_refines body

private def scan (head : Unit → CallHead) (motive visit : α → Bool) (op : Op) (children : List α) : Bool :=
  match op, children with
  | .view .., first :: _ => !motive first
  | .app, _ =>
      match head () with
      | .variableHead | .viewHead => true
      | .other => children.any visit
  | .lam _, _ | .absurd, _ => false
  | .fold, _ | .loop, _ => true
  | _, _ => children.any visit

def graphReads (arena : Arena) : Nat → Nat → Bool
  | 0, _ => true
  | depth + 1, root =>
      match arena[root]? with
      | none => true
      | some (.var _) => false
      | some (.node op refs) =>
          scan (fun () => graphHead arena (root+1) root) (motiveYieldsFunction (graphRow arena))
            (graphReads arena depth) op refs

def termReads : Nat → Term → Bool
  | 0, _ => true
  | _ + 1, .var _ => false
  | depth + 1, .node op terms =>
      scan (fun () => termHead (.node op terms)) (motiveYieldsFunction termRow) (termReads depth) op terms

private theorem any_refines {readRef : Nat → Bool} {readTerm : Term → Bool}
    (represented : RepresentsList arena refs terms)
    (agrees : ∀ {ref term}, Represents arena ref term → readRef ref = readTerm term) :
    refs.any readRef = terms.any readTerm := by
  induction refs generalizing terms with
  | nil => cases represented; rfl
  | cons ref refs ih =>
      cases represented with
      | cons first rest => simp only [List.any_cons, agrees first, ih rest]

private theorem scan_refines (represented : RepresentsList arena refs terms)
    (agrees : ∀ {ref term}, Represents arena ref term → readRef ref = readTerm term)
    (head : CallHead) (op : Op) :
    scan (fun () => head) (motiveYieldsFunction (graphRow arena)) readRef op refs =
      scan (fun () => head) (motiveYieldsFunction termRow) readTerm op terms := by
  have ordinary := any_refines represented agrees
  cases op
  all_goals try solve | exact ordinary | rfl
  case app => cases head <;> first | exact ordinary | rfl
  case view =>
    cases represented with
    | nil => rfl
    | cons motive rest => simp only [scan, motive_refines motive]

/-- The graph read analysis agrees with its syntax interpretation,
including the App spine and the erased function-result test of View. -/
theorem graphReads_refines (backward : Backward arena) (represented : Represents arena root term) :
    graphReads arena depth root = termReads depth term := by
  induction depth generalizing root term with
  | zero => rfl
  | succ depth ih =>
      cases represented with
      | var read => simp only [graphReads, read, termReads]
      | node read arity children =>
          have head := graphHead_refines backward (.node read arity children) (Nat.lt_succ_self _)
          simp only [graphReads, read, termReads, head]
          exact scan_refines children (fun represented => ih represented) _ _

/-- Two Views of the same scrutinee have distinct analysis outcomes when
one motive returns a function and the other reads a scalar. -/
theorem function_and_scalar_views :
    let arena : Arena := #[.node .u64 [], .node (.pi false) [0, 0], .node (.lam false) [0, 1],
      .node (.view false 0 0) [2, 0], .node (.view false 0 0) [0, 0]]
    graphReads arena 1 3 = false ∧ graphReads arena 1 4 = true :=
  ⟨rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreReadAnalysis
