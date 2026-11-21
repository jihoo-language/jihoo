import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreGhostSort

/-! Native View distinguishes an ordinary result type from a lambda
motive. It checks the latter's borrow domain before checking the result
sort, then visits the original motive again for its representation. -/
namespace Jihoo.NativeKernel.NativeCoreViewMotiveGate

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Visit PairRetained next_progress requireTypes requireTypes_progress requireTypes_refines)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def lowerArray (limit depth : Nat) (state : State) (length binders : Nat) : Outcome Unit :=
  let shifted := NativeCoreTransformExact.run limit depth state length (.shift (-(Int.ofNat binders))) 0
  match shifted.result with
  | .ok _ => ⟨shifted.state,.ok ()⟩
  | .error _ => reject shifted.state length

private theorem lowerArray_progress : Progress limit state (lowerArray limit depth state length binders) := by
  unfold lowerArray
  let shifted := NativeCoreTransformExact.run limit depth state length (.shift (-(Int.ofNat binders))) 0
  have held := NativeCoreTransformExact.run_progress limit depth state length (.shift (-(Int.ofNat binders))) 0
  change Progress limit state (match shifted.result with
    | .ok _ => ⟨shifted.state,.ok ()⟩
    | .error _ => reject shifted.state length)
  cases ran : shifted.result with
  | ok selected =>
    exact ⟨held.kept,held.monotone,held.bounded,fun room _ _ => held.accepted room selected ran⟩
  | error reason =>
    exact ⟨held.kept,held.monotone,held.bounded,fun _ _ impossible => by cases impossible⟩

def runtimeResult (limit depth : Nat) (state : State) : Nat → Nat → Nat → Outcome Unit
  | 0,_,root => reject state root
  | fuel+1,binders,root =>
    match state.arena[root]? with
    | some (.node (.pi _) [_,rest]) => runtimeResult limit depth state fuel (binders+1) rest
    | some (.node .array [length]) => lowerArray limit depth state length binders
    | some (.node .i64 []) | some (.node .u64 []) | some (.node .refine [_])
    | some (.node .buffer [_]) | some (.node (.ind _ _) _) => ⟨state,.ok ()⟩
    | _ => reject state root

theorem runtimeResult_progress : Progress limit state (runtimeResult limit depth state fuel binders root) := by
  induction fuel generalizing root binders with
  | zero => exact Progress.atState _ _
  | succ fuel ih =>
    unfold runtimeResult
    split
    · exact ih
    · exact lowerArray_progress
    all_goals exact Progress.atState _ _

private theorem lowerArray_refines (source : Represents state.arena length size)
    (success : (lowerArray limit depth state length binders).result = .ok ()) :
    let after := (lowerArray limit depth state length binders).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      (PartialRenaming.shift (-(Int.ofNat binders)) 0 size).isSome = true := by
  unfold lowerArray at success ⊢
  dsimp only at success ⊢
  split at success
  · rename_i selected ran
    obtain ⟨kept,safe,output,expected,_⟩ :=
      (NativeCoreTransformExact.run_refines (mode := .shift (-(Int.ofNat binders)))
        (binders := 0) (value := .var 0) source True.intro ran).1
    change PartialRenaming.shift (-(Int.ofNat binders)) 0 size = some output at expected
    exact ⟨kept,safe,by simp only [expected,Option.isSome_some]⟩
  · cases success

theorem runtimeResult_refines (source : Represents state.arena root term)
    (success : (runtimeResult limit depth state fuel binders root).result = .ok ()) :
    let after := (runtimeResult limit depth state fuel binders root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      viewRepresentation fuel binders term = true := by
  induction fuel generalizing root binders term with
  | zero => cases success
  | succ fuel ih =>
    cases source with
    | var read => simp [runtimeResult,read,reject] at success
    | @node _ op refs terms read width children =>
      rw [runtimeResult,read] at success ⊢
      cases op
      case pi erased =>
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp [Op.arity] at width
        cases children with
        | cons domain tail =>
          cases tail with
          | cons body rest =>
            cases rest
            obtain ⟨kept,safe,accepted⟩ := ih body success
            exact ⟨kept,safe,by simpa only [viewRepresentation] using accepted⟩
      case array =>
        rcases refs with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp [Op.arity] at width
        cases children with
        | cons length tail =>
          cases tail
          obtain ⟨kept,safe,accepted⟩ := lowerArray_refines length success
          exact ⟨kept,safe,by simpa only [viewRepresentation] using accepted⟩
      case u64 | i64 =>
        have nil : refs = [] := List.length_eq_zero_iff.mp width
        subst refs
        cases children
        exact ⟨.refl _,id,rfl⟩
      case refine | buffer =>
        rcases refs with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp [Op.arity] at width
        cases children with
        | cons first rest =>
          cases rest
          exact ⟨.refl _,id,rfl⟩
      case ind =>
        exact ⟨.refl _,id,rfl⟩
      all_goals cases success

private def representation (normal : Visit) (limit depth : Nat) (state : State) (motive : Nat) : Outcome Unit :=
  (normal state motive).next fun after selected =>
    match after.arena[selected]? with
    | some (.node (.lam _) [_,body]) => runtimeResult limit depth after (after.arena.size+1) 1 body
    | _ => reject after motive

private theorem representation_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (representation normal limit depth state motive) :=
  (normalProgress _ _).next (fun _ => by split; exact runtimeResult_progress; exact Progress.atState _ _)

structure Checked where
  dependent : Bool
  compared : List (Nat × Nat)

private def isLambda (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node (.lam _) [_,_]) => true
  | _ => false

private def universeZero (normal : Visit) (state : State) (root motive : Nat) : Outcome Unit :=
  (NativeCoreGhostSort.sort normal state root).next fun after sort =>
    if sort = .type 0 then ⟨after,.ok ()⟩ else reject after motive

private theorem universeZero_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (universeZero normal state root motive) :=
  (NativeCoreGhostSort.sort_progress normalProgress).next (fun _ => by split <;> exact Progress.atState _ _)

def run (normal : Visit) (limit depth : Nat) (state : State) (motive inferred referenceType : Nat) : Outcome Checked :=
  (normal state motive).next fun classified selected =>
    if isLambda classified.arena selected then
      (normal classified inferred).next fun afterSort product =>
        match afterSort.arena[product]? with
        | some (.node (.pi false) [domain,level]) =>
          (requireTypes normal limit depth afterSort domain referenceType motive).next fun matched compared =>
            (universeZero normal matched level motive).next fun checked _ =>
              (representation normal limit depth checked motive).next fun after _ =>
                ⟨after,.ok ⟨true,[compared]⟩⟩
        | _ => reject afterSort motive
    else
      (universeZero normal classified inferred motive).next fun after _ => ⟨after,.ok ⟨false,[]⟩⟩

theorem run_progress (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run normal limit depth state motive inferred referenceType) := by
  unfold run
  apply next_progress (normalProgress _ _) room
  intro selected _ classifiedRoom
  split
  · apply next_progress (normalProgress _ _) classifiedRoom
    intro product _ sortRoom
    split
    · apply next_progress (requireTypes_progress (fun state root _ => normalProgress state root) sortRoom) sortRoom
      intro compared _ matchedRoom
      exact (universeZero_progress normalProgress).next fun _ =>
        (representation_progress normalProgress).next (fun _ => Progress.atState _ _)
    · exact Progress.atState _ _
  · exact (universeZero_progress normalProgress).next (fun _ => Progress.atState _ _)


private theorem universeZero_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (source : Represents state.arena root original)
    (success : (universeZero normal state root motive).result = .ok ()) :
    let after := (universeZero normal state root motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RawLend.Conv env (expand env original) (.univ 0) := by
  unfold universeZero at success ⊢
  obtain ⟨sort,sortOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  by_cases zero : sort = .type 0
  · subst sort
    simpa only [ite_true,SortTag.term] using NativeCoreGhostSort.sort_refines normalSound onBase source sortOk
  · simp [zero,reject] at success

private theorem binary_parts (represented : Represents arena product type)
    (read : arena[product]? = some (.node op [domain,level])) :
    ∃ D L, type = .node op [D,L] ∧ Represents arena domain D ∧ Represents arena level L := by
  cases represented with
  | var found => rw [read] at found; cases found
  | node found width children =>
    rw [read] at found
    cases found
    cases children with
    | cons head rest =>
      cases rest with
      | cons tail empty =>
        cases empty
        exact ⟨_,_,rfl,head,tail⟩

/-- Successful motive inspection justifies its Type0 result and, for a
dependent motive, the original scrutinee's borrow as its domain. -/
theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena)
    (motiveRep : Represents state.arena motive M) (sortRep : Represents state.arena inferred original)
    (borrowRep : Represents state.arena referenceType (.ref T))
    (success : (run normal limit depth state motive inferred referenceType).result = .ok answer)
    (ambient : Prefix (run normal limit depth state motive inferred referenceType).state.arena final)
    (retained : ∀ pair ∈ answer.compared, PairRetained final pair) :
    let after := (run normal limit depth state motive inferred referenceType).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RawLend.Conv env (expand env original) (viewMotiveType answer.dependent (expand env T)) := by
  unfold run at success ambient ⊢
  obtain ⟨selected,classified,nextClass⟩ := Outcome.next_success success
  rw [nextClass] at success ambient ⊢
  obtain ⟨classKept,classBack,_,_,_⟩ := normalSound onBase motiveRep classified
  split at success
  · rename_i dependent
    simp only [ite_eq_left dependent] at ambient ⊢
    obtain ⟨product,productOk,nextProduct⟩ := Outcome.next_success success
    rw [nextProduct] at success ambient ⊢
    obtain ⟨productKept,productBack,_,productRep,sortChanged⟩ := normalSound (onBase.trans classKept)
      (sortRep.frame classKept) productOk
    let classifiedState := (normal state motive).state
    let productState := (normal classifiedState inferred).state
    split at success
    · rename_i domain level read
      simp only [read] at ambient ⊢
      obtain ⟨compared,comparison,comparedNext⟩ := Outcome.next_success success
      rw [comparedNext] at success ambient ⊢
      obtain ⟨⟨⟩,sortOk,sortNext⟩ := Outcome.next_success success
      rw [sortNext] at success ambient ⊢
      obtain ⟨⟨⟩,represented,representationNext⟩ := Outcome.next_success success
      rw [representationNext] at success ambient ⊢
      cases success
      obtain ⟨D,L,shape,domainRep,levelRep⟩ := binary_parts productRep read
      have beforeCompare := classKept.trans productKept
      let comparisonRun := requireTypes normal limit depth productState domain referenceType motive
      let sortRun := universeZero normal comparisonRun.state level motive
      have sortCost := universeZero_progress (state := comparisonRun.state) (root := level) (motive := motive) normalProgress
      have representationCost := representation_progress (state := sortRun.state) (motive := motive)
        (depth := depth) normalProgress
      have afterComparison := sortCost.kept.trans (representationCost.kept.trans ambient)
      obtain ⟨compareKept,compareBack,domainChanged⟩ := requireTypes_refines normalSound
        (onBase.trans beforeCompare) domainRep (borrowRep.frame beforeCompare) comparison afterComparison
        (retained compared (by simp))
      have beforeSort := beforeCompare.trans compareKept
      obtain ⟨sortKept,sortBack,levelChanged⟩ := universeZero_refines normalSound
        (onBase.trans beforeSort) (levelRep.frame compareKept) sortOk
      have productChanged : RawLend.Conv env (expand env original) (.pi false (expand env D) (expand env L)) := by
        simpa only [shape,Term.pi,expand,expandArgs] using sortChanged.converted
      refine ⟨beforeSort.trans (sortKept.trans representationCost.kept),?_,?_⟩
      · intro back
        have beforeRepresentation := sortBack (compareBack (productBack (classBack back)))
        have retainedSource := motiveRep.frame (beforeSort.trans sortKept)
        -- The final visit preserves its normalized result and every appended row.
        unfold representation at represented ⊢
        obtain ⟨motiveHead,normalOk,normalNext⟩ := Outcome.next_success represented
        rw [normalNext] at represented ⊢
        obtain ⟨_,normalBack,_,motiveRep,_⟩ := normalSound (onBase.trans (beforeSort.trans sortKept)) retainedSource normalOk
        split at represented
        · rename_i erased domain body read
          obtain ⟨_,_,_,_,bodyRep⟩ := binary_parts motiveRep read
          exact (runtimeResult_refines bodyRep represented).2.1 (normalBack beforeRepresentation)
        · cases represented
      · simp only [viewMotiveType,ite_true]
        exact productChanged.trans (.node (.pi false) (.cons
          (by simpa only [Term.ref,expand,expandArgs] using domainChanged) (.cons levelChanged .nil)))
    · cases success
  · rename_i notDependent
    simp only [ite_eq_right notDependent] at ambient ⊢
    obtain ⟨⟨⟩,sortOk,sortNext⟩ := Outcome.next_success success
    rw [sortNext] at success ambient ⊢
    cases success
    obtain ⟨kept,back,converter⟩ := universeZero_refines normalSound (onBase.trans classKept)
      (sortRep.frame classKept) sortOk
    exact ⟨classKept.trans kept,back ∘ classBack,by simpa only [viewMotiveType,Bool.false_eq_true,ite_false] using converter⟩

end Jihoo.NativeKernel.NativeCoreViewMotiveGate
