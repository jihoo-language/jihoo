import Jihoo.NativeCoreCodeApplicationFinalization
import Jihoo.NativeCoreCodeLambda
import Jihoo.NativeCoreCodeScalarInference

/-! Scalar operands, runtime function bodies and both application
positions call the same recursive code visitor. The ghost visitor is
used only where the source checker selects a ghost premise. -/
namespace Jihoo.NativeKernel.NativeCoreCodeInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (GraphBinding ContextRep Infer Visit Inferred InferSound RetainedComparisons
  conditionOp inferConditional inferConditional_progress inferConditional_modeRefines
  inferSubtractWithProof inferSubtractWithProof_progress inferSubtractWithProof_modeRefines)
open NativeCoreCodeScalarInference (enter enter_progress enter_success arithmetic arithmetic_progress
  arithmetic_refines strict strict_progress strict_refines)
open NativeCoreBufferRelease (inferFree inferFree_progress)

abbrev GhostAt := Nat → List GraphBinding → Infer

def run (normal : Nat → Visit) (ghost : GhostAt) (env : Environment)
    (isData boxed : Nat → Bool) (limit : Nat) : Nat → List GraphBinding → Bool → Infer
  | 0,bindings,_,state,root => NativeCoreCodeHeadInference.run limit 0 bindings state root
  | depth+1,bindings,head,state,root =>
    let recur := run normal ghost env isData boxed limit depth bindings false
    match state.arena[root]? with
    | some (.node (.arith _) [left,right]) => enter limit (depth+1) state root fun entered =>
        arithmetic recur (normal depth) limit depth entered .i64 left right
    | some (.node .uadd [left,right]) => enter limit (depth+1) state root fun entered =>
        arithmetic recur (normal depth) limit depth entered .u64 left right
    | some (.node .usub [left,right,proof]) => enter limit (depth+1) state root fun entered =>
        inferSubtractWithProof recur (ghost depth bindings) (normal depth) limit depth entered left right proof
    | some (.node .strict [first,last]) => enter limit (depth+1) state root fun entered =>
        strict recur entered first last
    | some (.node .ifLt [left,right,yes,no]) => enter limit (depth+1) state root fun entered =>
        inferConditional recur (fun assumption => run normal ghost env isData boxed limit depth
          (⟨assumption,true⟩ :: bindings) false) (normal depth) limit depth entered false left right yes no
    | some (.node .ifEq [left,right,yes,no]) => enter limit (depth+1) state root fun entered =>
        inferConditional recur (fun assumption => run normal ghost env isData boxed limit depth
          (⟨assumption,true⟩ :: bindings) false) (normal depth) limit depth entered true left right yes no
    | some (.node .free [buffer,tail]) => enter limit (depth+1) state root fun entered =>
        inferFree recur (normal depth) entered buffer tail
    | some (.node (.lam erased) [domain,body]) => enter limit (depth+1) state root fun entered =>
        NativeCoreCodeLambda.run (ghost depth bindings)
          (fun binding => run normal ghost env isData boxed limit depth (binding :: bindings) false)
          (normal depth) isData boxed limit depth entered root domain body erased
    | some (.node .app [function,argument]) => enter limit (depth+1) state root fun entered =>
        let callee := run normal ghost env isData boxed limit depth bindings true
        let erased := ghost depth bindings
        let argumentInfer := fun flag => if flag then erased else recur
        NativeCoreCodeApplicationFinalization.run callee argumentInfer erased normal env boxed
          limit depth entered root function argument head
    | _ => NativeCoreCodeHeadInference.run limit (depth+1) bindings state root

theorem run_progress
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run normal ghost env isData boxed limit depth bindings head state root) := by
  induction depth generalizing bindings head state root with
  | zero => exact NativeCoreCodeHeadInference.run_progress
  | succ depth ih =>
    unfold run
    split
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferSubtractWithProof_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => strict_progress (fun _ _ => ih) inside)
    · exact enter_progress (fun _ inside => inferConditional_progress (fun _ _ => ih)
        (fun _ _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferConditional_progress (fun _ _ => ih)
        (fun _ _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferFree_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside =>
        NativeCoreCodeLambda.run_progress (ghostProgress depth bindings) (fun _ _ => ih) (normalProgress depth) inside)
    · apply enter_progress
      intro _ inside
      apply NativeCoreCodeApplicationFinalization.run_progress (fun _ _ => ih) _ (ghostProgress depth bindings) normalProgress inside
      intro mode
      cases mode
      · exact fun _ _ => ih
      · exact ghostProgress depth bindings
    · exact NativeCoreCodeHeadInference.run_progress

/-- All recursive code branches share the original local annotations.
The ghost callback handles annotations, erased arguments and ownership
inspection. The application policy uses a normalizer that resolves
transparent globals before inspecting their representation. -/
theorem run_sound (wf : UnifiedProgram.EnvWellFormed env)
    (metadata : NativeCoreGhostSort.DataFamilies env isData)
    (boxedMetadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalFree : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs base normal)
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (ghostSound : ∀ {arena bindings ctx}, Prefix base arena → ContextRep env arena bindings ctx →
      ∀ depth, InferSound env arena ctx limit (ghost depth bindings))
    (onStart : Prefix base start) (context : ContextRep env start bindings ctx) :
    NativeCoreCodeHeadInference.Sound env start ctx limit (run normal ghost env isData boxed limit depth bindings head) := by
  induction depth generalizing head start bindings ctx with
  | zero => exact NativeCoreCodeHeadInference.run_sound wf context
  | succ depth ih =>
    intro state root term answer final onBase room source success ambient retained
    let recur := run normal ghost env isData boxed limit depth bindings false
    have normalLocal (depth : Nat) : VisitsFrom start (ExpandedNormalization env) (normal depth) := by
      intro _ _ _ _ later represented succeeded
      exact normalSound depth (onStart.trans later) represented succeeded
    have normalLocalFree : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs start normal := by
      intro _ _ _ _ _ _ onBase input succeeded output
      exact normalFree (onStart.trans onBase) input succeeded output
    have childSound : NativeCoreCodeHeadInference.Sound env start ctx limit recur := ih onStart context
    have childCost : ∀ state root, state.steps ≤ limit → Progress limit state (recur state root) :=
      fun _ _ inside => run_progress ghostProgress normalProgress inside
    have modeSound : NativeCoreBufferRelease.ModeSound env [] start ctx limit false recur := by
      intro _ _ _ _ _ withinBase room source found after retained
      obtain ⟨kept,safe,typed⟩ := childSound withinBase room source found after retained
      exact ⟨kept,safe,typed⟩
    unfold run at success ambient ⊢
    cases source with
    | var read =>
      simp only [read] at success ambient ⊢
      exact NativeCoreCodeHeadInference.run_sound wf context onBase room (.var read) success ambient retained
    | @node _ op refs terms read arity children =>
      simp only [read] at success ambient ⊢
      cases op
      case arith | uadd | strict | free | app =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons first rest =>
          cases rest with
          | cons second tail =>
            cases tail
            dsimp only at success ambient ⊢
            obtain ⟨entered,inside⟩ := enter_success success
            rw [entered] at success ambient ⊢
            first
            | exact strict_refines (state := {state with steps := state.steps+1})
                childSound childCost onBase inside first second success ambient retained
            | obtain ⟨kept,backward,typed⟩ := NativeCoreBufferRelease.inferFree_refines
                (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                modeSound childCost onBase inside first second success ambient retained
              exact ⟨kept,backward,typed⟩
            | apply arithmetic_refines (state := {state with steps := state.steps+1}) (depth := depth)
                (normalLocal depth) (normalProgress depth) childSound childCost
                onBase inside first second rfl _ success ambient retained
              intro left right
              simp only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] at left right ⊢
              first | exact .arith left right | exact .uadd left right
            | let callee := run normal ghost env isData boxed limit depth bindings true
              let erased := ghost depth bindings
              have calleeTyped : NativeCoreCodeApplication.Sound env [] start ctx limit false callee := by
                intro _ _ _ _ _ held cost represented succeeded finalPrefix comparisons
                obtain ⟨kept,safe,typed⟩ := ih onStart context held cost
                  represented succeeded finalPrefix comparisons
                exact ⟨kept,safe,typed⟩
              have operandTyped : ∀ mode, NativeCoreCodeApplication.Sound env [] start ctx limit mode
                  (if mode then erased else recur) := by
                intro mode
                cases mode
                · exact modeSound
                · intro _ _ _ _ _ held cost represented succeeded finalPrefix comparisons
                  obtain ⟨kept,safe,typed⟩ := ghostSound onStart context depth held cost
                    represented succeeded finalPrefix comparisons
                  exact ⟨kept,safe,typed⟩
              have operandProgress : ∀ (mode : Bool) state root, state.steps ≤ limit →
                  Progress limit state ((if mode then erased else recur) state root) := by
                intro mode
                cases mode
                · exact childCost
                · exact ghostProgress depth bindings
              obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreCodeApplicationFinalization.run_refines
                (state := {state with steps := state.steps+1}) wf normalLocalFree normalLocal normalProgress
                calleeTyped operandTyped (fun _ _ inside => run_progress ghostProgress normalProgress inside)
                operandProgress (ghostProgress depth bindings) (ghostSound onStart context depth) boxedMetadata onBase inside
                (.node read arity (.cons first (.cons second .nil))) first second success ambient retained
              exact ⟨kept,safe,type,represented,by simpa only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      case usub =>
        have length : refs.length = 3 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩⟩ <;> simp at length
        cases children with
        | cons left rest =>
          cases rest with
          | cons right rest =>
            cases rest with
            | cons proof rest =>
              cases rest
              dsimp only at success ambient ⊢
              obtain ⟨entered,inside⟩ := enter_success success
              rw [entered] at success ambient ⊢
              obtain ⟨kept,safe,typed⟩ := inferSubtractWithProof_modeRefines
                (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                onBase inside left right proof success ambient retained
              exact ⟨kept,safe,typed⟩
      case ifLt | ifEq =>
        have length : refs.length = 4 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩⟩⟩ <;> simp at length
        cases children with
        | @cons _ a _ _ leftRep rest =>
          cases rest with
          | @cons _ b _ _ rightRep rest =>
            cases rest with
            | cons yesRep rest =>
              cases rest with
              | cons noRep rest =>
                cases rest
                dsimp only at success ambient ⊢
                obtain ⟨entered,inside⟩ := enter_success success
                rw [entered] at success ambient ⊢
                let next := fun assumption => run normal ghost env isData boxed limit depth
                  (⟨assumption,true⟩ :: bindings) false
                have branchSound (equality : Bool) : ∀ {opened assumption}, Prefix state.arena opened →
                    Represents opened assumption (.node (conditionOp equality) [a,b]) →
                    NativeCoreBufferRelease.ModeSound env [] opened
                      (⟨EnvironmentDelta.expand env (.node (conditionOp equality) [a,b]),true⟩ :: ctx) limit false
                      (next assumption) := by
                  intro opened assumption kept represented _ _ _ _ _ current currentRoom branch checked future tape
                  have baseHere := onBase.trans kept
                  have extended : ContextRep env opened (⟨assumption,true⟩ :: bindings)
                      (⟨EnvironmentDelta.expand env (.node (conditionOp equality) [a,b]),true⟩ :: ctx) :=
                    .cons ⟨_,represented,rfl,rfl⟩ (context.frame baseHere)
                  obtain ⟨kept,safe,typed⟩ := ih (head := false) (onStart.trans baseHere) extended
                    current currentRoom branch checked future tape
                  exact ⟨kept,safe,typed⟩
                have enteredNormal : VisitsFrom state.arena (ExpandedNormalization env) (normal depth) := by
                  intro _ _ _ _ later represented succeeded
                  exact normalLocal depth (onBase.trans later) represented succeeded
                have enteredMode : NativeCoreBufferRelease.ModeSound env [] state.arena ctx limit false recur := by
                  intro _ _ _ _ _ later room represented succeeded after tape
                  exact modeSound (onBase.trans later) room represented succeeded after tape
                first
                | obtain ⟨kept,safe,typed⟩ := inferConditional_modeRefines
                    (state := {state with steps := state.steps+1}) (inferThen := next) wf enteredNormal (normalProgress depth)
                    enteredMode childCost (branchSound false) (fun _ _ _ room => run_progress ghostProgress normalProgress room)
                    (.refl _) inside leftRep rightRep yesRep noRep success ambient retained
                  exact ⟨kept,safe,typed⟩
                | obtain ⟨kept,safe,typed⟩ := inferConditional_modeRefines
                    (state := {state with steps := state.steps+1}) (inferThen := next) wf enteredNormal (normalProgress depth)
                    enteredMode childCost (branchSound true) (fun _ _ _ room => run_progress ghostProgress normalProgress room)
                    (.refl _) inside leftRep rightRep yesRep noRep success ambient retained
                  exact ⟨kept,safe,typed⟩
      case lam flag =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨domain,_ | ⟨body,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | @cons _ D _ _ domainRep rest =>
          cases rest with
          | cons bodyRep tail =>
            cases tail
            dsimp only at success ambient ⊢
            obtain ⟨entered,inside⟩ := enter_success success
            rw [entered] at success ambient ⊢
            have enteredBase := onStart.trans onBase
            have enteredContext := context.frame onBase
            have extended : ContextRep env state.arena (⟨domain,flag⟩ :: bindings)
                (⟨EnvironmentDelta.expand env D,flag⟩ :: ctx) :=
              .cons ⟨D,domainRep,rfl,rfl⟩ enteredContext
            have enteredNormal : VisitsFrom state.arena (ExpandedNormalization env) (normal depth) := by
              intro _ _ _ _ later represented succeeded
              exact normalLocal depth (onBase.trans later) represented succeeded
            let visitBody := fun binding => run normal ghost env isData boxed limit depth (binding :: bindings) false
            have bodySound : NativeCoreCodeApplication.Sound env [] state.arena
                (⟨EnvironmentDelta.expand env D,flag⟩ :: ctx) limit false (visitBody ⟨domain,flag⟩) := by
              intro _ _ _ _ _ localBase cost represented succeeded finalPrefix comparisons
              obtain ⟨kept,safe,typed⟩ := ih (head := false) enteredBase extended localBase cost
                represented succeeded finalPrefix comparisons
              exact ⟨kept,safe,typed⟩
            obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreCodeLambda.run_refines
              (state := {state with steps := state.steps+1}) (visitBody := visitBody) (depth := depth)
              metadata boxedMetadata enteredNormal (normalProgress depth) (ghostSound enteredBase enteredContext depth)
              bodySound (ghostProgress depth bindings) (fun _ _ inside => run_progress ghostProgress normalProgress inside)
              (.refl _) inside domainRep bodyRep success ambient retained
            exact ⟨kept,safe,_,represented,by simpa only [Term.lam,EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      all_goals
        exact NativeCoreCodeHeadInference.run_sound wf context onBase room (.node read arity children)
          success ambient retained

end Jihoo.NativeKernel.NativeCoreCodeInference

namespace Jihoo.NativeKernel.NativeCoreCodeInference.Examples

open NativeArena Environment
open NativeCoreGhostSpineInference (Inferred)
open NativeCorePureComputationNormal (Outcome)
open NativeCoreTransformExact (State)

private def fixture : Arena :=
  #[.node (.natural 2) [],.node .u64 [],.var 0,.node .uadd [2,0],.node (.lam false) [1,3],
    .node .app [4,0],.node (.integer (-1)) [],.node .strict [6,5],.node .i64 [],.var 1,
    .node (.lam false) [8,9],.node (.lam false) [1,10],.node .app [11,0]]

private def checked (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreGhostLiteralAddition.run [] 0 limit
  let ghost := NativeCoreGhostSpineInference.runWith normal [] 0 limit
  run normal ghost empty (fun _ => false) (fun _ => false) limit 32 [] false ⟨fixture,0⟩ root

/-- The recursive visitor checks a code lambda inside an application,
then the same application inside Strict, and a function-valued result. -/
theorem nested_runtime_calls_match_native :
    let direct := checked 26 5
    let strict := checked 28 7
    let underApplied := checked 44 12
    direct.state.steps = 26 ∧ direct.state.arena.size = 19 ∧ direct.result.map Inferred.typeRoot = .ok 16 ∧
    strict.state.steps = 28 ∧ strict.state.arena.size = 20 ∧ strict.result.map Inferred.typeRoot = .ok 17 ∧
    underApplied.state.steps = 44 ∧ underApplied.state.arena.size = 22 ∧ underApplied.result.map Inferred.typeRoot = .ok 15 := by
  cbv


private def conditionalArena (equality invalid : Bool) : Arena := #[
  .node .u64 [],.node (.natural 0) [],.node (.natural 1) [],.var 1,.var 0,
  .node (if equality then .ifEq else .ifLt) [1,2,if invalid then 4 else 3,4]]

private def conditionalExtra (equality : Bool) : Arena := #[
  .node .u64 [],.node .u64 [],.node .u64 [],.node (if equality then .eq else .lt) [1,2]]

/-- Both runtime conditionals keep the pre-existing word slot and deny
runtime access to the new proof slot. The exhausted remaining budgets and
committed rows match the native paths. -/
theorem conditionals_match_native_erased_scope (equality : Bool) :
    let runAt := fun limit invalid =>
      run (NativeCoreGhostLiteralAddition.run [] 0 limit) (fun _ _ state root => ⟨state,.error (.outsideFragment root)⟩)
        empty (fun _ => false) (fun _ => false) limit 16 [⟨0,false⟩] false ⟨conditionalArena equality invalid,0⟩ 5
    let accepted := runAt 18 false
    let rejected := runAt 10 true
    accepted.state = ⟨conditionalArena equality false ++ conditionalExtra equality,18⟩ ∧
      accepted.result.map Inferred.typeRoot = .ok 0 ∧
      rejected.state = ⟨conditionalArena equality true ++ conditionalExtra equality,10⟩ ∧
      rejected.result = .error (.outsideFragment 4) := by
  cases equality <;> cbv


private def subtractionArena (invalid : Bool) : Arena := #[
  .node (.natural 0) [],.node (.natural 1) [],.node .uadd [0,1],.node .lt [0,2],.var 0,
  .node .usub [if invalid then 4 else 0,0,4]]

private def subtractionRows : Arena := #[
  .node .u64 [],.node .u64 [],.node .u64 [],.node (.natural 1) [],.node .uadd [0,9],.node .lt [0,10],
  .node (.natural 1) [],.node .lt [0,12],.node (.natural 1) [],.node .lt [0,14],.node .u64 []]

/-- A runtime subtraction reads its erased proof slot in ghost mode.
Using the same slot for the first runtime operand is rejected after
creating only the shared U64 annotation. -/
theorem subtraction_proof_mode_matches_native :
    let runAt := fun limit invalid =>
      run (NativeCoreGhostLiteralAddition.run [] 0 limit) (NativeCoreGhostSpineInference.run [] 0 limit)
        empty (fun _ => false) (fun _ => false) limit 16 [⟨3,true⟩] false ⟨subtractionArena invalid,0⟩ 5
    let accepted := runAt 32 false
    let rejected := runAt 2 true
    accepted.state = ⟨subtractionArena false ++ subtractionRows,32⟩ ∧
      accepted.result.map Inferred.typeRoot = .ok 16 ∧
      rejected.state = ⟨subtractionArena true ++ #[.node .u64 []],2⟩ ∧
      rejected.result = .error (.outsideFragment 4) := by cbv

end Jihoo.NativeKernel.NativeCoreCodeInference.Examples
