import Jihoo.NativeCoreEffectAnalysis

/-! The depth-limited Core.may_trap analysis uses the entire application
spine and only visits the runtime positions of selected constructors. -/
namespace Jihoo.NativeKernel.NativeCoreTrapAnalysis

open NativeArena Environment

inductive CallHead where
  | variableHead
  | viewHead
  | other
  deriving DecidableEq, Repr

def termHead : Term → CallHead
  | .var _ => .variableHead
  | .node (.view ..) _ => .viewHead
  | .node .app [fn, _] => termHead fn
  | _ => .other
termination_by term => sizeOf term
decreasing_by simp_wf; omega

def graphHead (arena : Arena) : Nat → Nat → CallHead
  | 0, _ => .other
  | fuel + 1, root =>
      match arena[root]? with
      | some (.var _) => .variableHead
      | some (.node (.view ..) _) => .viewHead
      | some (.node .app [fn, _]) => graphHead arena fuel fn
      | _ => .other

/-- Backward edges bound the unmetered application-spine walk by its root
index, so no additional termination certificate is required. -/
theorem graphHead_refines (backward : Backward arena) (represented : Represents arena root term)
    (enough : root < fuel) :
    graphHead arena fuel root = termHead term := by
  induction fuel generalizing root term with
  | zero => omega
  | succ fuel ih =>
      cases represented with
      | var read => simp [graphHead, read, termHead]
      | @node _ op refs children read arity kids =>
          cases op
          all_goals try solve | simp only [graphHead, read, termHead]
          case app =>
            cases kids with
            | nil => cases arity
            | @cons fn _ _ _ function rest =>
                cases rest with
                | nil => cases arity
                | cons argument tail =>
                    cases tail with
                    | cons => cases arity
                    | nil =>
                        simp only [graphHead, read, termHead]
                        apply ih function
                        have earlier := backward root _ read fn (by simp [Node.references])
                        omega

def trapEdge : Op → Nat → Bool
  | .refine, _ | .proof, _ | .absurd, _ | .back _, _ => false
  | .pack, i => i == 1
  | .give erased, i => i == 1 || (!erased && i == 2)
  | .loop, i => i != 1
  | _, _ => true

private def anyChild (visit : α → Bool) (op : Op) : Nat → List α → Bool
  | _, [] => false
  | index, first :: rest =>
      (trapEdge op index && visit first) || anyChild visit op (index+1) rest

private def boxed (env : Environment) (family : Nat) : Bool :=
  (env.families[family]?.map (·.boxed)).getD false

private def trapRoot (env : Environment) (runtime : Bool) (head : Unit → CallHead) : Op → Bool
  | .arith _ | .strict | .uadd | .alloc | .load | .store | .free | .drop _ | .caseOf .. => true
  | .con family .. | .elim family .. => boxed env family
  | .app => runtime && decide (head () = .variableHead)
  | _ => false

def graphMayTrap (env : Environment) (runtime : Bool) (arena : Arena) : Nat → Nat → Bool
  | 0, _ => true
  | depth+1, root =>
      match arena[root]? with
      | none => true
      | some (.var _) => false
      | some (.node op refs) =>
          trapRoot env runtime (fun _ => graphHead arena (root+1) root) op ||
            anyChild (graphMayTrap env runtime arena depth) op 0 refs

def termMayTrap (env : Environment) (runtime : Bool) : Nat → Term → Bool
  | 0, _ => true
  | _+1, .var _ => false
  | depth+1, .node op terms =>
      trapRoot env runtime (fun _ => termHead (.node op terms)) op ||
        anyChild (termMayTrap env runtime depth) op 0 terms

private theorem anyChild_refines {visitRef : Nat → Bool} {visitTerm : Term → Bool}
    (children : RepresentsList arena refs terms)
    (seen : ∀ {ref term}, Represents arena ref term → visitRef ref = visitTerm term)
    (op : Op) (index : Nat) :
    anyChild visitRef op index refs = anyChild visitTerm op index terms := by
  induction refs generalizing terms index with
  | nil => cases children; rfl
  | cons ref rest ih =>
      cases children with
      | cons first rest => simp only [anyChild, seen first, ih rest]

/-- The live analysis agrees with its syntax interpretation at every depth,
including depth exhaustion and calls through a runtime variable. -/
theorem graphMayTrap_refines (backward : Backward arena) (represented : Represents arena root term) :
    graphMayTrap env runtime arena depth root = termMayTrap env runtime depth term := by
  induction depth generalizing root term with
  | zero => rfl
  | succ depth ih =>
      cases represented with
      | var read => simp only [graphMayTrap, read, termMayTrap]
      | node read arity children =>
          have head := graphHead_refines backward (.node read arity children) (Nat.lt_succ_self _)
          simp only [graphMayTrap, read, termMayTrap, head]
          rw [anyChild_refines children (fun represented => ih represented)]

theorem graph_unsigned_add_traps (represented : Represents arena root (.uadd a b)) :
    graphMayTrap env runtime arena depth root = true := by
  cases depth with
  | zero => rfl
  | succ depth =>
      cases represented with
      | node read _ _ => simp [graphMayTrap, read, trapRoot]

/-- A trap in a Pack predicate and an erased Give result is excluded by the
traversal, while a call through a variable is a runtime trap candidate. -/
theorem graph_analysis_example :
    let arena : Arena := #[.node (.natural 1) [], .node .uadd [0, 0], .var 0, .node .app [2, 0],
      .node .pack [1, 0, 1], .node (.give true) [1, 0, 1]]
    graphMayTrap Environment.empty true arena 4 3 = true ∧
      graphMayTrap Environment.empty false arena 4 3 = false ∧
      graphMayTrap Environment.empty true arena 4 4 = false ∧
      graphMayTrap Environment.empty true arena 4 5 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreTrapAnalysis
