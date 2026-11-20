import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreGhostLiteralAddition

/-! Runtime application classifies its normalized domain once. A type
argument then enters a second pass, which normalizes the whole kind again
and each word-domain and codomain at the successively smaller depth. -/
namespace Jihoo.NativeKernel.NativeCoreCodeKind

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand expandArgs)

def sortAt (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node (.universe _) []) => true
  | some (.node (.pi _) [_,body]) => if body < root then sortAt arena body else false
  | _ => false
termination_by root

/-- Following the codomain edges of the checked arena adds no meter charges.
Backward references make the bounded representation of the native loop exact. -/
theorem sortAt_represents (represented : Represents arena root term) (backward : Backward arena) :
    sortAt arena root = kindOf term := by
  cases represented with
  | var read =>
    rw [sortAt,read]
    simp only [kindOf]
  | @node _ op refs terms read arity children =>
    rw [sortAt,read]
    cases op
    case pi erased =>
      have width : refs.length = 2 := arity
      rcases refs with _ | ⟨_,_ | ⟨body,_ | ⟨_,_⟩⟩⟩ <;> simp at width
      cases children with
      | cons domain tail =>
        cases tail with
        | cons codomain tail =>
          cases tail
          have smaller : body < root := backward _ _ read _ (by simp [Node.references])
          simp only [ite_eq_left smaller,kindOf]
          exact sortAt_represents codomain backward
    case «universe» level =>
      have width := List.length_eq_zero_iff.mp (show refs.length = 0 from arity)
      subst refs
      cases children
      rfl
    all_goals rfl
termination_by root

def classify (normal : State → Nat → Outcome Nat) (state : State) (domain : Nat) : Outcome Bool :=
  (normal state domain).next fun after root => ⟨after,.ok (sortAt after.arena root)⟩

theorem classify_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (classify normal state domain) :=
  (normalProgress _ _).next fun _ => Progress.atState _ _

theorem classify_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (backward : Backward state.arena)
    (source : Represents state.arena domain D) (success : (classify normal state domain).result = .ok typeArgument) :
    let after := (classify normal state domain).state.arena
    Prefix state.arena after ∧ Backward after ∧
      ∃ residual, RawLend.Conv env (expand env D) (expand env residual) ∧ kindOf residual = typeArgument := by
  unfold classify at success ⊢
  obtain ⟨root,rootOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,safe,residual,represented,converted⟩ := normalSound onBase source rootOk
  simp only [Except.ok.injEq] at success
  rw [sortAt_represents represented (safe backward)] at success
  exact ⟨kept,safe backward,residual,converted.converted,success⟩

/-- The expected kind must end in a universe and every domain inspected by
the walk must normalize to U64. After failure the last state is retained. -/
def firstOrder (normal : Nat → State → Nat → Outcome Nat) : Nat → State → Nat → Outcome Bool
  | 0,state,root =>
    (normal 0 state root).next fun after selected =>
      match after.arena[selected]? with
      | some (.node (.universe _) []) => ⟨after,.ok true⟩
      | _ => ⟨after,.ok false⟩
  | depth+1,state,root =>
    (normal (depth+1) state root).next fun after selected =>
      match after.arena[selected]? with
      | some (.node (.universe _) []) => ⟨after,.ok true⟩
      | some (.node (.pi _) [domain,body]) =>
        (normal depth after domain).next fun checked indexType =>
          if checked.arena[indexType]? = some (.node .u64 []) then firstOrder normal depth checked body
          else ⟨checked,.ok false⟩
      | _ => ⟨after,.ok false⟩

theorem firstOrder_progress (normalProgress : ∀ depth state root, Progress limit state (normal depth state root)) :
    Progress limit state (firstOrder normal depth state root) := by
  induction depth generalizing state root with
  | zero =>
    unfold firstOrder
    exact (normalProgress _ _ _).next (fun _ => by split <;> exact Progress.atState _ _)
  | succ depth ih =>
    unfold firstOrder
    apply (normalProgress _ _ _).next
    intro selected
    split
    · exact Progress.atState _ _
    · exact (normalProgress _ _ _).next (fun _ => by split; exact ih; exact Progress.atState _ _)
    · exact Progress.atState _ _

private theorem shaped (represented : Represents arena root term) (read : arena[root]? = some (.node op refs)) :
    ∃ args, term = .node op args ∧ RepresentsList arena refs args := by
  cases represented with
  | var found => rw [read] at found; cases found
  | node found _ children => rw [read] at found; cases found; exact ⟨_,rfl,children⟩

private theorem accepted_universe {normal : Nat → State → Nat → Outcome Nat} {state : State}
    (normalSound : VisitsFrom base (ExpandedNormalization env) (normal depth))
    (onBase : Prefix base state.arena) (written : Represents state.arena root D)
    (success : (normal depth state root).result = .ok selected)
    (read : (normal depth state root).state.arena[selected]? = some (.node (.universe level) [])) :
    RawLend.Conv env (expand env D) (.univ level) := by
  obtain ⟨_,_,residual,represented,converted⟩ := normalSound onBase written success
  obtain ⟨args,rfl,children⟩ := shaped represented read
  cases children
  simpa only [Term.univ,expand,expandArgs] using converted.converted

/-- Each success yields a convertible kind made entirely of relevant or
erased U64 domains and a universe. This permits different graph rows to
represent the same kind after repeated native normalization. -/
theorem firstOrder_refines
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (onBase : Prefix base state.arena) (written : Represents state.arena root D)
    (success : (firstOrder normal depth state root).result = .ok true) :
    let after := (firstOrder normal depth state root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ kind, RawLend.Conv env (expand env D) kind ∧ firstOrderKind kind = true ∧ globalFree kind = true := by
  induction depth generalizing state root D with
  | zero =>
    unfold firstOrder at success ⊢
    obtain ⟨selected,ran,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    split at success
    · rename_i level read
      obtain ⟨kept,safe,_,_,_⟩ := normalSound 0 onBase written ran
      exact ⟨kept,safe,.univ level,accepted_universe (normalSound 0) onBase written ran read,rfl,by simp [Term.univ,globalFree,globalFreeArgs]⟩
    · cases success
  | succ depth ih =>
    unfold firstOrder at success ⊢
    obtain ⟨selected,ran,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨kept,safe,residual,represented,converted⟩ := normalSound (depth+1) onBase written ran
    split at success
    · rename_i level read
      exact ⟨kept,safe,.univ level,accepted_universe (normalSound (depth+1)) onBase written ran read,rfl,by simp [Term.univ,globalFree,globalFreeArgs]⟩
    · rename_i erased domain body read
      obtain ⟨parts,shape,children⟩ := shaped represented read
      obtain ⟨indexType,indexOk,indexNext⟩ := Outcome.next_success success
      rw [indexNext] at success ⊢
      split at success
      · rename_i word
        simp only [ite_eq_left word]
        cases children with
        | @cons _ domainTerm _ _ domainRep tail =>
          cases tail with
          | @cons _ bodyTerm _ _ bodyRep tail =>
            cases tail
            obtain ⟨indexKept,indexSafe,indexNorm,indexRep,indexConverted⟩ :=
              normalSound depth (onBase.trans kept) domainRep indexOk
            obtain ⟨_,indexShape,empty⟩ := shaped indexRep word
            cases empty
            obtain ⟨bodyKept,bodySafe,kind,bodyConverted,firstOrder,free⟩ :=
              ih (onBase.trans (kept.trans indexKept)) (bodyRep.frame indexKept) success
            have code : RawLend.Conv env (expand env domainTerm) .u64 := by
              simpa only [indexShape,expand,expandArgs,Term.u64] using indexConverted.converted
            have product : RawLend.Conv env (.pi erased (expand env domainTerm) (expand env bodyTerm)) (.pi erased .u64 kind) :=
              .node _ (.cons code (.cons bodyConverted .nil))
            refine ⟨kept.trans (indexKept.trans bodyKept),bodySafe ∘ indexSafe ∘ safe,
              .pi erased .u64 kind,converted.converted.trans (by simpa only [shape,expand,expandArgs] using product),?_⟩
            exact ⟨by simp only [firstOrderKind,firstOrder], by simp only [Term.pi,Term.u64,globalFree,globalFreeArgs,free]; rfl⟩
      · cases success
    · cases success

private def fixture : Arena := #[.node .u64 [],.node .i64 [],.node (.universe 0) [],
  .node (.pi true) [0,2],.node (.pi false) [0,3],.node (.pi false) [1,2]]

/-- Classification walks the already-normalized codomain without charging
ticks. The kind gate revisits the word domains and rejects a signed binder. -/
theorem kind_gates_revisit_domains_in_order :
    let normal := NativeCoreGhostLiteralAddition.run [] 0 16
    classify (normal 8) ⟨fixture,0⟩ 4 = ⟨⟨fixture,5⟩,.ok true⟩ ∧
    firstOrder normal 8 ⟨fixture,0⟩ 4 = ⟨⟨fixture,11⟩,.ok true⟩ ∧
    firstOrder normal 8 ⟨fixture,0⟩ 5 = ⟨⟨fixture,4⟩,.ok false⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeKind
