import Jihoo.NativeLoanComparisonPathLookup
import Jihoo.NativeCoreCodeArgumentPolicy

/-! Type requirements normalize both original annotations in the same live
arena before native identity. Successful identity recovers typed erased
occurrences from the normalized comparison, with their original contexts. -/
namespace Jihoo.NativeKernel.NativeCoreComparisonTypedRequirements

open Environment NativeArena
open EnvironmentDelta (expand)
open NativeCorePureComputationNormal (Outcome ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (requireTypes)
open NativeCoreCodeArgumentPolicy (GlobalFreeOutputs)
open NativeCoreCompare (FullyRetained)
open LoanTyping.ComparisonEvidence (follow IgnoredProposition HasEvidence)

private theorem identity_retains_layout
    (accepted : (NativeCoreTypedEqual.identify limit depth state left right).result = .ok true) :
    (NativeCoreTypedEqual.identify limit depth state left right).state.arena = state.arena ∧
      NativeCoreIdentical.runArena state.arena limit depth state.steps left right =
        (.ok true,(NativeCoreTypedEqual.identify limit depth state left right).state.steps) := by
  rcases seen : NativeCoreIdentical.runArena state.arena limit depth state.steps left right with ⟨result,steps⟩
  cases result with
  | error reason => simp [NativeCoreTypedEqual.identify,seen,Except.mapError] at accepted
  | ok answer =>
    have checked : answer = true := by simpa only [NativeCoreTypedEqual.identify,seen,Except.mapError,Except.ok.injEq] using accepted
    subst answer
    simp [NativeCoreTypedEqual.identify,seen]

/-- The normalizations preserve each original formation. The returned pair
locates the two native identity operands and the live comparison receipt. -/
theorem requireTypes_checked_comparison
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalFree : GlobalFreeOutputs base (fun _ => normal))
    (onBase : Prefix base state.arena)
    (actualRep : Represents state.arena actual A) (expectedRep : Represents state.arena expected B)
    (actualTyped : LoanTyping.HasType env [] ctx true (expand env A) firstSort)
    (expectedTyped : LoanTyping.HasType env [] ctx true (expand env B) secondSort)
    (accepted : (requireTypes normal limit depth state actual expected argument).result = .ok pair) :
    let output := requireTypes normal limit depth state actual expected argument
    let compared := (normal (normal state actual).state expected).state
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ first second,
        Represents output.state.arena pair.1 first ∧ Represents output.state.arena pair.2 second ∧
        LoanTyping.HasType env [] ctx true first firstSort ∧ LoanTyping.HasType env [] ctx true second secondSort ∧
        NativeCoreIdentical.runArena output.state.arena limit depth compared.steps pair.1 pair.2 = (.ok true,output.state.steps) := by
  unfold requireTypes at accepted ⊢
  obtain ⟨left,firstOk,firstNext⟩ := Outcome.next_success accepted
  rw [firstNext] at accepted ⊢
  obtain ⟨right,secondOk,secondNext⟩ := Outcome.next_success accepted
  rw [secondNext] at accepted ⊢
  obtain ⟨matched,identityOk,identityNext⟩ := Outcome.next_success accepted
  rw [identityNext] at accepted ⊢
  cases matched
  · cases accepted
  · change Except.ok (left,right) = .ok pair at accepted
    simp only [Except.ok.injEq] at accepted
    subst pair
    obtain ⟨firstKept,firstBack,first,firstRep,firstChange⟩ := normalSound onBase actualRep firstOk
    obtain ⟨secondKept,secondBack,second,secondRep,secondChange⟩ := normalSound
      (onBase.trans firstKept) (expectedRep.frame firstKept) secondOk
    have firstFree := normalFree (depth := depth) onBase actualRep firstOk firstRep
    have secondFree := normalFree (depth := depth) (onBase.trans firstKept) (expectedRep.frame firstKept) secondOk secondRep
    have firstPreserved := firstChange.preserves actualTyped
    have secondPreserved := secondChange.preserves expectedTyped
    rw [EnvironmentDelta.expand_globalFree ((globalFree_correct _).mp firstFree)] at firstPreserved
    rw [EnvironmentDelta.expand_globalFree ((globalFree_correct _).mp secondFree)] at secondPreserved
    obtain ⟨unchanged,receipt⟩ := identity_retains_layout identityOk
    let beforeCompare := (normal (normal state actual).state expected).state
    let finalState := (NativeCoreTypedEqual.identify limit depth beforeCompare left right).state
    change Prefix state.arena finalState.arena ∧ (Backward state.arena → Backward finalState.arena) ∧
      ∃ first second, Represents finalState.arena left first ∧ Represents finalState.arena right second ∧
        LoanTyping.HasType env [] ctx true first firstSort ∧ LoanTyping.HasType env [] ctx true second secondSort ∧
        NativeCoreIdentical.runArena finalState.arena limit depth beforeCompare.steps left right = (.ok true,finalState.steps)
    have sameArena : finalState.arena = beforeCompare.arena := unchanged
    rw [sameArena]
    exact ⟨firstKept.trans secondKept,secondBack ∘ firstBack,first,second,firstRep.frame secondKept,
      secondRep,firstPreserved,secondPreserved,receipt⟩

/-- The compared pair can omit different evidence at a retained path.
The automatically aligned contexts and retained operands recover both
proofs at the same proposition. -/
theorem requireTypes_path_common_proposition
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalFree : GlobalFreeOutputs base (fun _ => normal))
    (wf : UnifiedProgram.EnvWellFormed env) (onBase : Prefix base state.arena)
    (actualRep : Represents state.arena actual A) (expectedRep : Represents state.arena expected B)
    (actualTyped : LoanTyping.HasType env [] ctx true (expand env A) firstSort)
    (expectedTyped : LoanTyping.HasType env [] ctx true (expand env B) secondSort)
    (accepted : (requireTypes normal limit depth state actual expected argument).result = .ok pair)
    (firstOperand : Represents (requireTypes normal limit depth state actual expected argument).state.arena pair.1 first)
    (secondOperand : Represents (requireTypes normal limit depth state actual expected argument).state.arena pair.2 second)
    (firstPath : follow firstFuel first path = some (firstBinders,.node firstOp [a,b,firstProof]))
    (secondPath : follow secondFuel second path = some (secondBinders,.node secondOp [a',b',secondProof]))
    (firstDomains : ∀ binding ∈ firstBinders,FullyRetained binding.ty)
    (secondDomains : ∀ binding ∈ secondBinders,FullyRetained binding.ty)
    (firstField : IgnoredProposition firstOp a b original) (secondField : IgnoredProposition secondOp a' b' other)
    (firstKept : FullyRetained a ∧ FullyRetained b) (secondKept : FullyRetained a' ∧ FullyRetained b') :
    original = other ∧ HasEvidence env (firstBinders ++ ctx) original firstProof ∧
      LoanTyping.HasType env [] (firstBinders ++ ctx) true secondProof original := by
  obtain ⟨_,_,left,right,leftRep,rightRep,leftTyped,rightTyped,receipt⟩ := requireTypes_checked_comparison
    (depth := depth) (limit := limit) normalSound (@normalFree) onBase actualRep expectedRep actualTyped expectedTyped accepted
  cases leftRep.unique firstOperand
  cases rightRep.unique secondOperand
  exact LoanTyping.ComparisonEvidence.live_identity_path_common_proposition_in_context wf leftRep rightRep receipt
    firstPath secondPath leftTyped rightTyped firstDomains secondDomains firstField secondField firstKept secondKept

end Jihoo.NativeKernel.NativeCoreComparisonTypedRequirements

namespace Jihoo.NativeKernel.NativeCoreComparisonTypedRequirements.Examples

open Environment NativeArena
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (requireTypes)
open NativeCoreCompare (FullyRetained)
open LoanTyping.ComparisonEvidence (HasEvidence IgnoredProposition follow)

private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))
private def point : Term := .natural 0
private def checkedType (proof : Nat) : Term := .app (.var 2) (.pack predicate point (.var proof))
private def scope : Context := [⟨.eq point point,true⟩,⟨.eq point point,true⟩,⟨.pi false (.refine predicate) (.univ 0),false⟩]
private def arena : Arena := #[.node .u64 [],.var 0,.node .eq [1,1],.node (.lam false) [0,2],.node .refine [3],
  .node (.universe 0) [],.node (.pi false) [4,5],.node (.natural 0) [],.node .eq [7,7],.var 1,.var 2,
  .node .pack [3,7,1],.node .pack [3,7,9],.node .app [10,11],.node .app [10,12]]
private def state : State := ⟨arena,0⟩
private def normal (limit : Nat) := NativeCoreGhostLiteralAddition.run [] 0 limit

set_option maxRecDepth 4096

private theorem formed (proof : Bool) : LoanTyping.HasType empty [] scope true
    (checkedType (if proof then 1 else 0)) (.univ 0) := by
  cases proof <;> exact LoanTyping.Checker.infer_sound (fuel := 128) (by cbv)

private theorem retained_point : FullyRetained point :=
  .node (by decide) rfl rfl (by simp)

private theorem retained_predicate : FullyRetained predicate := by
  refine .node (by decide) rfl rfl ?_
  intro term member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact .node (by decide) rfl rfl (by simp)
  · refine .node (by decide) rfl rfl ?_
    intro child included
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at included
    subst child
    exact .var 0

private theorem fixture_left : normal 29 8 state 13 = ⟨⟨arena,10⟩,.ok 13⟩ := by cbv

private theorem fixture_right : normal 29 8 ⟨arena,10⟩ 14 = ⟨⟨arena,20⟩,.ok 14⟩ := by cbv

private theorem fixture_identity : NativeCoreTypedEqual.identify 29 8 ⟨arena,20⟩ 13 14 =
    ⟨⟨arena,29⟩,.ok true⟩ := by cbv

/-- Both typed source annotations compare in 29 ticks without allocating any graph rows. -/
theorem pack_type_comparison_schedule : requireTypes (normal 29 8) 29 8 state 13 14 13 =
    ⟨⟨arena,29⟩,.ok (13,14)⟩ := by
  simp [requireTypes,fixture_left,Outcome.next,fixture_right,fixture_identity]

/-- The identity pass of the measured type requirement consults two
separately checked erased variables at the original Pack predicate. -/
theorem compared_pack_proofs_share_the_original_predicate :
    HasEvidence empty scope (.app predicate point) (.var 0) ∧
      LoanTyping.HasType empty [] scope true (.var 1) (.app predicate point) := by
  have compared : NativeCoreIdentical.runArena arena 29 8 20 13 14 = (.ok true,29) := by cbv
  have left : Represents arena 13 (checkedType 0) := decode_sound (fuel := 16) rfl
  have right : Represents arena 14 (checkedType 1) := decode_sound (fuel := 16) rfl
  have firstPath : follow 3 (checkedType 0) [1] = some ([],.pack predicate point (.var 0)) := by cbv
  have secondPath : follow 3 (checkedType 1) [1] = some ([],.pack predicate point (.var 1)) := by cbv
  have firstTyped : LoanTyping.HasType empty [] scope true (checkedType 0) (.univ 0) := formed false
  have secondTyped : LoanTyping.HasType empty [] scope true (checkedType 1) (.univ 0) := formed true
  exact (LoanTyping.ComparisonEvidence.live_identity_path_common_proposition_in_context
    (initial := 20) (path := [1]) (leftBinders := []) (rightBinders := [])
    UnifiedProgram.EnvWellFormed.empty left right compared firstPath secondPath firstTyped secondTyped
    (by simp) (by simp) IgnoredProposition.pack IgnoredProposition.pack
    ⟨retained_predicate,retained_point⟩ ⟨retained_predicate,retained_point⟩).2

end Jihoo.NativeKernel.NativeCoreComparisonTypedRequirements.Examples
