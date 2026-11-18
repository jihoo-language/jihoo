import Jihoo.NativeCoreGraphWire
import Jihoo.NativeIterationMemory

/-! The bounded graph traversal behind Core.effectful. The Boolean here is
its negation. Missing references and absent family metadata are rejected,
as they cannot occur in the corresponding checked family environment. -/
namespace Jihoo.NativeKernel.Environment.CoreEffectAnalysis

open NativeArena NativeCoreGraph

private def skipsChildren : Op → Bool
  | .absurd | .back _ => true
  | _ => false

private def visitChildren (visit : α → Bool) (op : Op) : Nat → List α → Bool
  | _, [] => true
  | offset, child :: rest =>
      (!iterationEffectEdge op offset || visit child) && visitChildren visit op (offset+1) rest

private def memoryNode (env : Environment) (visit : α → Bool) (op : Op) (children : List α) : Bool :=
  iterationMemoryFree env (.node op []) && (skipsChildren op || visitChildren visit op 0 children)

def graphMemoryFree (env : Environment) (arena : Arena) : Nat → Nat → Bool
  | 0, _ => false
  | depth+1, root =>
      match arena[root]? with
      | none => false
      | some (.var _) => true
      | some (.node op children) => memoryNode env (graphMemoryFree env arena depth) op children

def termMemoryFree (env : Environment) : Nat → Term → Bool
  | 0, _ => false
  | _+1, .var _ => true
  | depth+1, .node op children => memoryNode env (termMemoryFree env depth) op children

private theorem represented_children (children : RepresentsList arena refs terms)
    (aligned : ∀ {root term}, Represents arena root term → visitRef root = visitTerm term)
    (op : Op) (offset : Nat) : visitChildren visitRef op offset refs = visitChildren visitTerm op offset terms := by
  induction refs generalizing terms offset with
  | nil => cases children; rfl
  | cons ref refs ih =>
      cases children with
      | cons one rest => simp only [visitChildren,aligned one,ih rest]

/-- Traversing the shared graph implements the same depth-limited effect check
as traversing the represented syntax, including the skipped operand positions. -/
theorem graphMemoryFree_refines (represented : Represents arena root term) (depth : Nat) :
    graphMemoryFree env arena depth root = termMemoryFree env depth term := by
  induction depth generalizing root term with
  | zero => rfl
  | succ depth ih =>
      cases represented with
      | var lookup => simp only [graphMemoryFree,lookup,termMemoryFree]
      | node lookup _ children =>
          simp only [graphMemoryFree,lookup,termMemoryFree,memoryNode]
          rw [represented_children children (fun represented => ih represented)]

private theorem unbounded_children (env : Environment) (op : Op) (offset : Nat) (children : List Term) :
    visitChildren (iterationMemoryFree env) op offset children = iterationMemoryFreeArgs env op offset children := by
  induction children generalizing offset with
  | nil => simp only [visitChildren,iterationMemoryFreeArgs]
  | cons first rest ih => simp only [visitChildren,iterationMemoryFreeArgs,ih]

private theorem unbounded_node (env : Environment) (op : Op) (children : List Term) :
    memoryNode env (iterationMemoryFree env) op children = iterationMemoryFree env (.node op children) := by
  unfold memoryNode
  rw [unbounded_children]
  cases op <;> simp only [iterationMemoryFree,iterationMemoryFreeArgs,skipsChildren,Bool.false_or,
    Bool.true_or,Bool.true_and,Bool.false_and]
  all_goals split <;> simp

private theorem visitChildren_implies (step : ∀ t ∈ children, first t = true → second t = true)
    (accepted : visitChildren first op offset children = true) : visitChildren second op offset children = true := by
  induction children generalizing offset with
  | nil => rfl
  | cons child children ih =>
      simp only [visitChildren,Bool.and_eq_true,Bool.or_eq_true] at accepted ⊢
      refine ⟨accepted.1.elim Or.inl (fun seen => Or.inr (step child List.mem_cons_self seen)),?_⟩
      exact ih (fun t member => step t (List.mem_cons_of_mem _ member)) accepted.2

theorem termMemoryFree_sound (accepted : termMemoryFree env depth term = true) :
    iterationMemoryFree env term = true := by
  induction depth generalizing term with
  | zero => simp [termMemoryFree] at accepted
  | succ depth ih =>
      cases term with
      | var => simp only [iterationMemoryFree]
      | node op children =>
          simp only [termMemoryFree,memoryNode,Bool.and_eq_true,Bool.or_eq_true] at accepted
          rw [← unbounded_node]
          simp only [memoryNode,Bool.and_eq_true,Bool.or_eq_true]
          exact ⟨accepted.1,accepted.2.elim Or.inl (fun seen => Or.inr
            (visitChildren_implies (fun _ _ visited => ih visited) seen))⟩

private theorem foldl_max_lower (xs : List Nat) (initial : Nat) : initial ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem treeDepth_member (child : Term) (children : List Term) (member : child ∈ children)
    (initial : Nat) : NativeKernel.Conversion.treeDepth child ≤
      (children.map NativeKernel.Conversion.treeDepth).foldl max initial := by
  induction children generalizing initial with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_lower _ _)
      · exact ih member _

theorem termMemoryFree_complete (depthEnough : NativeKernel.Conversion.treeDepth term ≤ depth)
    (unbounded : iterationMemoryFree env term = true) : termMemoryFree env depth term = true := by
  induction depth generalizing term with
  | zero => cases term <;> simp [NativeKernel.Conversion.treeDepth] at depthEnough
  | succ depth ih =>
      cases term with
      | var => rfl
      | node op children =>
          simp only [NativeKernel.Conversion.treeDepth] at depthEnough
          rw [← unbounded_node] at unbounded
          simp only [termMemoryFree,memoryNode,Bool.and_eq_true,Bool.or_eq_true] at unbounded ⊢
          refine ⟨unbounded.1,unbounded.2.elim Or.inl (fun seen => Or.inr ?_)⟩
          apply visitChildren_implies (first := iterationMemoryFree env) ?_ seen
          intro child member free
          have inside := treeDepth_member child children member 0
          exact ih (term := child) (by omega) free

theorem graphMemoryFree_iff (represented : Represents arena root term)
    (depthEnough : NativeKernel.Conversion.treeDepth term ≤ depth) :
    graphMemoryFree env arena depth root = true ↔ iterationMemoryFree env term = true := by
  rw [graphMemoryFree_refines represented depth]
  exact ⟨termMemoryFree_sound,termMemoryFree_complete depthEnough⟩

def observedMemoryFree (env : Environment) (words : List NodeWords) (depth root : Nat) : Option Bool := do
  let nodes ← words.mapM NodeWords.toNode
  pure (graphMemoryFree env nodes.toArray depth root)

theorem parsedGraphMemoryFree_sound
    (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions familyRoots words ++ rest) =
      some (snapshot, tail))
    (represented : Represents snapshot.arena root term)
    (accepted : observedMemoryFree env words depth root = some true) :
    iterationMemoryFree env term = true := by
  unfold observedMemoryFree at accepted
  obtain ⟨nodes,decoded,result⟩ := Option.bind_eq_some_iff.mp accepted
  rw [parseObservedProgram definitions familyRoots words fits rest] at parsed
  simp only [decoded,Option.map_some,Option.some.injEq,Prod.mk.injEq] at parsed
  obtain ⟨rfl,rfl⟩ := parsed
  have free := Option.some.inj result
  rw [graphMemoryFree_refines represented depth] at free
  exact termMemoryFree_sound free

end Jihoo.NativeKernel.Environment.CoreEffectAnalysis
