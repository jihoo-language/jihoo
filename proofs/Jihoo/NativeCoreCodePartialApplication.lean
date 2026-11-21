import Jihoo.NativeCoreCodeLinearity
import Jihoo.NativeCoreGhostTypeRequirement

/-! The ownership scan of a partial application revisits each original
callee from the outside of the spine toward its head. Erased arguments
skip the linearity classification. -/
namespace Jihoo.NativeKernel.NativeCoreCodePartialApplication

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreGhostSpineInference (Infer Visit Inferred next_progress)

private def outside (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

def spineHead (arena : Arena) : Nat → Nat → Nat
  | 0,root => root
  | fuel+1,root =>
    match arena[root]? with
    | some (.node .app [callee,_]) => spineHead arena fuel callee
    | _ => root

def scan (ghost : Infer) (normal : Visit) (boxed : Nat → Bool) (source : Nat) :
    Nat → State → Nat → Outcome (List (Nat × Nat))
  | 0,state,_ => outside state source
  | fuel+1,state,root =>
    match state.arena[root]? with
    | some (.node .app [callee,_]) =>
      (ghost state callee).next fun inferred ty =>
        (normal inferred ty.typeRoot).next fun exposed product =>
          let remaining := fun after =>
            (scan ghost normal boxed source fuel after callee).next fun final compared =>
              ⟨final,.ok (ty.compared ++ compared)⟩
          match exposed.arena[product]? with
          | some (.node (.pi true) [_,_]) => remaining exposed
          | some (.node (.pi false) [domain,_]) =>
            (NativeCoreCodeLinearity.run normal boxed exposed domain).next fun tested linear =>
              if linear then outside tested source else remaining tested
          | _ => ⟨exposed,.ok ty.compared⟩
    | _ => ⟨state,.ok []⟩

def run (ghost : Infer) (normal : Visit) (boxed : Nat → Bool) (state : State) (root : Nat) :
    Outcome (List (Nat × Nat)) :=
  match state.arena[spineHead state.arena (state.arena.size+1) root]? with
  | some (.node (.caseOf _ _) _) => outside state root
  | _ => scan ghost normal boxed root (state.arena.size+1) state root

theorem scan_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (scan ghost normal boxed source fuel state root) := by
  induction fuel generalizing state root with
  | zero => exact Progress.atState _ _
  | succ fuel ih =>
    unfold scan
    split
    · apply next_progress (ghostProgress _ _ room) room
      intro ty _ inferredRoom
      apply next_progress (normalProgress _ _) inferredRoom
      intro selected _ exposedRoom
      split
      · exact (ih exposedRoom).next (fun _ => Progress.atState _ _)
      · apply next_progress (NativeCoreCodeLinearity.run_progress normalProgress) exposedRoom
        intro linear _ testedRoom
        split
        · exact Progress.atState _ _
        · exact (ih testedRoom).next (fun _ => Progress.atState _ _)
      · exact Progress.atState _ _
    · exact Progress.atState _ _

theorem run_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run ghost normal boxed state root) := by
  unfold run
  split
  · exact Progress.atState _ _
  · exact scan_progress ghostProgress normalProgress room

/-- A successful scan witnesses the original callee list and, for every
relevant argument at an exposed product, the actual negative ownership
test at that product's domain. -/
inductive Visits (ghost : Infer) (normal : Visit) (boxed : Nat → Bool) (source : Nat) :
    State → Nat → State → List (Nat × Nat) → Prop where
  | head (read : ∀ callee argument, state.arena[root]? ≠ some (.node .app [callee,argument])) :
      Visits ghost normal boxed source state root state []
  | stops (read : state.arena[root]? = some (.node .app [callee,argument]))
      (inferOk : (ghost state callee).result = .ok inferred)
      (normalOk : (normal (ghost state callee).state inferred.typeRoot).result = .ok selected)
      (head : ∀ erased domain body,
        (normal (ghost state callee).state inferred.typeRoot).state.arena[selected]? ≠ some (.node (.pi erased) [domain,body])) :
      Visits ghost normal boxed source state root
        (normal (ghost state callee).state inferred.typeRoot).state inferred.compared
  | erased (read : state.arena[root]? = some (.node .app [callee,argument]))
      (inferOk : (ghost state callee).result = .ok inferred)
      (normalOk : (normal (ghost state callee).state inferred.typeRoot).result = .ok selected)
      (product : (normal (ghost state callee).state inferred.typeRoot).state.arena[selected]? =
        some (.node (.pi true) [domain,body]))
      (tail : Visits ghost normal boxed source (normal (ghost state callee).state inferred.typeRoot).state callee final compared) :
      Visits ghost normal boxed source state root final (inferred.compared ++ compared)
  | relevant (read : state.arena[root]? = some (.node .app [callee,argument]))
      (inferOk : (ghost state callee).result = .ok inferred)
      (normalOk : (normal (ghost state callee).state inferred.typeRoot).result = .ok selected)
      (product : (normal (ghost state callee).state inferred.typeRoot).state.arena[selected]? =
        some (.node (.pi false) [domain,body]))
      (plain : (NativeCoreCodeLinearity.run normal boxed (normal (ghost state callee).state inferred.typeRoot).state domain).result =
        .ok false)
      (tail : Visits ghost normal boxed source
        (NativeCoreCodeLinearity.run normal boxed (normal (ghost state callee).state inferred.typeRoot).state domain).state
        callee final compared) :
      Visits ghost normal boxed source state root final (inferred.compared ++ compared)

theorem scan_visits
    (success : (scan ghost normal boxed source fuel state root).result = .ok compared) :
    Visits ghost normal boxed source state root (scan ghost normal boxed source fuel state root).state compared := by
  induction fuel generalizing state root compared with
  | zero => cases success
  | succ fuel ih =>
    unfold scan at success ⊢
    split at success
    · rename_i callee argument read
      obtain ⟨inferred,inferredOk,nextInfer⟩ := Outcome.next_success success
      rw [nextInfer] at success ⊢
      obtain ⟨selected,selectedOk,nextNormal⟩ := Outcome.next_success success
      rw [nextNormal] at success ⊢
      split at success
      · rename_i domain body product
        dsimp only at success ⊢
        obtain ⟨more,rest,nextRest⟩ := Outcome.next_success success
        rw [nextRest] at success ⊢
        cases success
        exact .erased read inferredOk selectedOk product (ih rest)
      · rename_i domain body product
        dsimp only at success ⊢
        obtain ⟨linear,linearOk,nextLinear⟩ := Outcome.next_success success
        rw [nextLinear] at success ⊢
        cases linear with
        | true => cases success
        | false =>
          simp only [Bool.false_eq_true,ite_false] at success ⊢
          obtain ⟨more,rest,nextRest⟩ := Outcome.next_success success
          rw [nextRest] at success ⊢
          cases success
          exact .relevant read inferredOk selectedOk product linearOk (ih rest)
      · rename_i excluded missingErased missingRelevant
        cases success
        exact .stops read inferredOk selectedOk (by intro erased; cases erased <;> assumption)
    · rename_i excluded notApplication
      cases success
      exact .head notApplication

theorem run_visits (success : (run ghost normal boxed state root).result = .ok compared) :
    (∀ family count refs, state.arena[spineHead state.arena (state.arena.size+1) root]? ≠
      some (.node (.caseOf family count) refs)) ∧ Visits ghost normal boxed root state root
        (run ghost normal boxed state root).state compared := by
  unfold run at success ⊢
  split at success
  · cases success
  · rename_i excluded notCase
    exact ⟨notCase,scan_visits success⟩

end Jihoo.NativeKernel.NativeCoreCodePartialApplication
