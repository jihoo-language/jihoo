import Jihoo.NativeCoreCodeBorrow
import Jihoo.NativeCoreGhostConstructorInference
import Jihoo.NativeCoreDependentLendCallbacks
import Jihoo.NativeCoreGhostLendInference
import Jihoo.NativeCoreCodeApplicationFinalization
import Jihoo.NativeCoreCodeLambda
import Jihoo.NativeCoreCodeScalarInference
import Jihoo.NativeLoanGhostInputMode
import Jihoo.NativeCoreGhostOwnerReturns
import Jihoo.NativeCoreGhostTakeInference

/-! Scalar operands, runtime function bodies and both application
positions call the same recursive code visitor. The ghost visitor is
used only where the source checker selects a ghost premise. -/
namespace Jihoo.NativeKernel.NativeCoreCodeInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (GraphBinding ContextRep Infer Visit Inferred InferSound RetainedComparisons
  inferAbsurdInMode inferAbsurdInMode_progress inferAbsurdInMode_modeRefines
  inferLoadWithProof inferLoadWithProof_progress inferLoadWithProof_modeRefines
  inferDrop inferDrop_progress inferDrop_modeRefines
  inferPackWithEvidence inferPackWithEvidence_progress inferPackWithEvidence_modeRefines
  inferRefinementProjection inferRefinementProjection_progress inferRefinementProjection_modeRefines
  conditionOp inferConditional inferConditional_progress inferConditional_modeRefines
  inferSubtractWithProof inferSubtractWithProof_progress inferSubtractWithProof_modeRefines
  inferAlloc inferAlloc_progress inferAlloc_modeRefines
  inferElements inferElements_progress inferElements_modeRefines
  inferStoreWithProof inferStoreWithProof_progress inferStoreWithProof_modeRefines
  inferIndexWithProof inferIndexWithProof_progress inferIndexWithProof_modeRefines)
open NativeCoreCodeScalarInference (enter enter_progress enter_success arithmetic arithmetic_progress
  arithmetic_refinesMode strict strict_progress strict_refinesMode)
open NativeCoreBufferRelease (ModeSound inferFree inferFree_progress)
open NativeCoreCodeLeaseLookup (Snapshot FramesRep)

private def familyShape (env : Environment) (family : Nat) : Option (Nat × Bool) :=
  env.families[family]?.map fun entry => (entry.declaration.arity,entry.declaration.data)

abbrev GhostAt := Nat → List GraphBinding → Infer

private def runtimeHead (visitGhost : Infer) (env : Environment) (limit depth : Nat)
    (bindings : List GraphBinding) (op : Op) : Infer :=
  if LoanTyping.GhostInputMode.eligibleWithFamilies env op then visitGhost
  else NativeCoreCodeHeadInference.run limit depth bindings

def runWithConstructors (normal : Nat → Visit) (ghost : GhostAt) (env : Environment)
    (isData boxed : Nat → Bool) (constructorRoots : Nat → Nat → Option Nat) (limit : Nat) (snapshots : List Snapshot) : Nat → List GraphBinding → Bool → Infer
  | 0,bindings,_,state,root => NativeCoreCodeHeadInference.run limit 0 bindings state root
  | depth+1,bindings,head,state,root =>
    let recur := runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings false
    match state.arena[root]? with
    | some (.node (.arith _) [left,right]) => enter limit (depth+1) state root fun entered =>
        arithmetic recur (normal depth) limit depth entered .i64 left right
    | some (.node .uadd [left,right]) => enter limit (depth+1) state root fun entered =>
        arithmetic recur (normal depth) limit depth entered .u64 left right
    | some (.node .usub [left,right,proof]) => enter limit (depth+1) state root fun entered =>
        inferSubtractWithProof recur (ghost depth bindings) (normal depth) limit depth entered left right proof
    | some (.node .absurd [target,proof]) => enter limit (depth+1) state root fun entered =>
        inferAbsurdInMode (ghost depth bindings) (normal depth) false entered target proof
    | some (.node .alloc [length,fill]) => enter limit (depth+1) state root fun entered =>
        inferAlloc recur (normal depth) limit depth entered length fill
    | some (.node (.elements length) elements) => enter limit (depth+1) state root fun entered =>
        inferElements recur (normal depth) limit depth entered root length elements
    | some (.node .load [buffer,index,proof,continuation]) => enter limit (depth+1) state root fun entered =>
        inferLoadWithProof recur (ghost depth bindings) (normal depth) false limit depth entered buffer index proof continuation
    | some (.node .store [buffer,index,value,proof]) => enter limit (depth+1) state root fun entered =>
        inferStoreWithProof recur (ghost depth bindings) (normal depth) limit depth entered buffer index value proof
    | some (.node .index [subject,index,proof]) => enter limit (depth+1) state root fun entered =>
        inferIndexWithProof recur (ghost depth bindings) (normal depth) limit depth entered subject index proof
    | some (.node (.back erased) [owner,motive]) => enter limit (depth+1) state root fun entered =>
        NativeCoreGhostOwnerReturns.runBack (ghost depth bindings) (normal depth) boxed limit depth entered erased owner motive
    | some (.node (.give erased) [motive,owner,result]) => enter limit (depth+1) state root fun entered =>
        NativeCoreGhostOwnerReturns.runGiveWithModes recur (ghost depth bindings)
          (if erased then ghost depth bindings else recur) (normal depth) boxed limit depth entered erased motive owner result
    | some (.node .take [owner,continuation]) => enter limit (depth+1) state root fun entered =>
        NativeCoreGhostTakeInference.runInMode recur (normal depth) false limit depth entered owner continuation
    | some (.node .pack [predicate,word,proof]) => enter limit (depth+1) state root fun entered =>
        inferPackWithEvidence recur (ghost depth bindings) (normal depth) limit depth entered predicate word proof
    | some (.node .witness [subject]) => enter limit (depth+1) state root fun entered =>
        inferRefinementProjection recur (normal depth) entered false subject
    | some (.node .proof [subject]) => enter limit (depth+1) state root fun entered =>
        inferRefinementProjection (ghost depth bindings) (normal depth) entered true subject
    | some (.node .borrow [owner]) => enter limit (depth+1) state root fun entered =>
        NativeCoreCodeBorrow.run boxed (ghost depth bindings) (normal depth)
          limit depth bindings.length entered snapshots root owner
    | some (.node .lend [owner,reader,continuation]) => enter limit (depth+1) state root fun entered =>
        NativeCoreGhostLendInference.runCode (ghost depth bindings)
          (fun saved => runWithConstructors normal ghost env isData boxed constructorRoots limit saved depth bindings false)
          (normal depth) isData boxed limit depth bindings.length entered snapshots owner reader continuation
    | some (.node .strict [first,last]) => enter limit (depth+1) state root fun entered =>
        strict recur entered first last
    | some (.node .ifLt [left,right,yes,no]) => enter limit (depth+1) state root fun entered =>
        inferConditional recur (fun assumption => runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth
          (⟨assumption,true⟩ :: bindings) false) (normal depth) limit depth entered false left right yes no
    | some (.node .ifEq [left,right,yes,no]) => enter limit (depth+1) state root fun entered =>
        inferConditional recur (fun assumption => runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth
          (⟨assumption,true⟩ :: bindings) false) (normal depth) limit depth entered true left right yes no
    | some (.node (.drop family) [owner,tail]) => enter limit (depth+1) state root fun entered =>
        inferDrop recur (normal depth) boxed (familyShape env) entered root family owner tail
    | some (.node .free [buffer,tail]) => enter limit (depth+1) state root fun entered =>
        inferFree recur (normal depth) entered buffer tail
    | some (.node (.lam erased) [domain,body]) => enter limit (depth+1) state root fun entered =>
        NativeCoreCodeLambda.run (ghost depth bindings)
          (fun binding => runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth (binding :: bindings) false)
          (normal depth) isData boxed limit depth entered root domain body erased
    | some (.node .app [function,argument]) => enter limit (depth+1) state root fun entered =>
        let callee := runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings true
        let erased := ghost depth bindings
        let argumentInfer := fun flag => if flag then erased else recur
        NativeCoreCodeApplicationFinalization.run callee argumentInfer erased normal env boxed
          limit depth entered root function argument head
    | some (.node (.con family constructor _) fields) => enter limit (depth+1) state root fun entered =>
        NativeCoreGhostConstructorInference.runSelectedByMode env false
          (fun flag => if flag then ghost depth bindings else recur) (normal depth)
          limit depth root bindings.length constructorRoots entered family constructor fields
    | some (.node op _) => runtimeHead (ghost (depth+1) bindings) env limit (depth+1) bindings op state root
    | _ => NativeCoreCodeHeadInference.run limit (depth+1) bindings state root

theorem runWithConstructors_progress
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings head state root) := by
  induction depth generalizing snapshots bindings head state root with
  | zero => exact NativeCoreCodeHeadInference.run_progress
  | succ depth ih =>
    unfold runWithConstructors
    split
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferSubtractWithProof_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferAbsurdInMode_progress (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferAlloc_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferElements_progress (fun _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferLoadWithProof_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferStoreWithProof_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferIndexWithProof_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => NativeCoreGhostOwnerReturns.runBack_progress
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => NativeCoreGhostOwnerReturns.runGiveWithModes_progress
        (fun _ _ room => ih room) (ghostProgress depth bindings)
        (by
          intro current root room
          split
          · exact ghostProgress depth bindings current root room
          · exact ih room)
        (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => NativeCoreGhostTakeInference.runInMode_progress
        (fun _ _ room => ih room) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferPackWithEvidence_progress (fun _ _ => ih)
        (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferRefinementProjection_progress (fun _ _ => ih)
        (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferRefinementProjection_progress (ghostProgress depth bindings)
        (normalProgress depth) inside)
    · exact enter_progress (fun _ inside =>
        NativeCoreCodeBorrow.run_progress (ghostProgress depth bindings) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => NativeCoreGhostLendInference.runCode_progress
        (ghostProgress depth bindings) (fun _ _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => strict_progress (fun _ _ => ih) inside)
    · exact enter_progress (fun _ inside => inferConditional_progress (fun _ _ => ih)
        (fun _ _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferConditional_progress (fun _ _ => ih)
        (fun _ _ _ => ih) (normalProgress depth) inside)
    · exact enter_progress (fun _ inside => inferDrop_progress (fun _ _ => ih) (normalProgress depth) inside)
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
    · exact enter_progress fun _ inside => NativeCoreGhostConstructorInference.runSelectedByMode_progress
        (fun mode => by cases mode
                        · exact fun _ _ => ih
                        · exact ghostProgress depth bindings)
        (normalProgress depth) inside
    · unfold runtimeHead
      split
      · exact ghostProgress (depth+1) bindings _ _ room
      · exact NativeCoreCodeHeadInference.run_progress
    · exact NativeCoreCodeHeadInference.run_progress

private theorem headSound (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env base bindings ctx) :
    ModeSound env loans base ctx limit false (NativeCoreCodeHeadInference.run limit depth bindings) := by
  intro _ _ _ _ _ onBase room source success ambient retained
  obtain ⟨kept,safe,type,represented,typed⟩ :=
    NativeCoreCodeHeadInference.run_sound wf context onBase room source success ambient retained
  exact ⟨kept,safe,type,represented,typed.withAmbientLoans wf⟩

private theorem runtimeHead_sound (wf : UnifiedProgram.EnvWellFormed env)
    (context : ContextRep env base bindings ctx) (ghostSound : InferSound env base ctx limit visitGhost)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena root (.node op terms))
    (success : (runtimeHead visitGhost env limit depth bindings op state root).result = .ok answer)
    (ambient : Prefix (runtimeHead visitGhost env limit depth bindings op state root).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (runtimeHead visitGhost env limit depth bindings op state root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env loans ctx false (EnvironmentDelta.expand env (.node op terms))
          (EnvironmentDelta.expand env type) := by
  by_cases selected : LoanTyping.GhostInputMode.eligibleWithFamilies env op = true
  · simp only [runtimeHead,selected,ite_true] at success ambient ⊢
    obtain ⟨kept,safe,type,annotation,typed⟩ := ghostSound onBase room source success ambient retained
    exact ⟨kept,safe,type,annotation,
      LoanTyping.GhostInputMode.recheckWithFamilies typed (LoanTyping.GhostInputMode.HeadWithFamilies.expanded selected)⟩
  · simp only [runtimeHead,ite_eq_right selected] at success ambient ⊢
    exact headSound wf context onBase room source success ambient retained

set_option maxHeartbeats 360000 in
/-- All recursive code branches share the original local annotations.
The ghost callback handles annotations, erased arguments and ownership
inspection. The application policy uses a normalizer that resolves
transparent globals before inspecting their representation. -/
theorem runWithConstructors_sound (wf : UnifiedProgram.EnvWellFormed env)
    (metadata : NativeCoreGhostSort.DataFamilies env isData)
    (boxedMetadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (constructorsSound : NativeCoreGhostConstructorInference.ConstructorTable env base constructorRoots)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalFree : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs base normal)
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (ghostSound : ∀ {arena bindings ctx}, Prefix base arena → ContextRep env arena bindings ctx →
      ∀ depth, InferSound env arena ctx limit (ghost depth bindings))
    (onStart : Prefix base start) (context : ContextRep env start bindings ctx)
    (frames : FramesRep start snapshots loans) :
    ModeSound env loans start ctx limit false (runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings head) := by
  induction depth generalizing snapshots loans head start bindings ctx with
  | zero => exact headSound wf context
  | succ depth ih =>
    intro state root term answer final onBase room source success ambient retained
    let recur := runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings false
    have normalLocal (depth : Nat) : VisitsFrom start (ExpandedNormalization env) (normal depth) := by
      intro _ _ _ _ later represented succeeded
      exact normalSound depth (onStart.trans later) represented succeeded
    have normalLocalFree : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs start normal := by
      intro _ _ _ _ _ _ onBase input succeeded output
      exact normalFree (onStart.trans onBase) input succeeded output
    have childCost : ∀ state root, state.steps ≤ limit → Progress limit state (recur state root) :=
      fun _ _ inside => runWithConstructors_progress ghostProgress normalProgress inside
    have modeSound : ModeSound env loans start ctx limit false recur := ih onStart context frames
    have erasedSound : ModeSound env loans start ctx limit true (ghost depth bindings) := by
      intro _ _ _ _ _ held cost represented succeeded finalPrefix comparisons
      obtain ⟨kept,safe,type,annotation,typed⟩ := ghostSound onStart context depth held cost
        represented succeeded finalPrefix comparisons
      exact ⟨kept,safe,type,annotation,typed.ghost loans⟩
    unfold runWithConstructors at success ambient ⊢
    cases source with
    | var read =>
      simp only [read] at success ambient ⊢
      exact headSound wf context onBase room (.var read) success ambient retained
    | @node _ op refs terms read arity children =>
      simp only [read] at success ambient ⊢
      cases op
      case back erased =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons owner rest =>
          cases rest with
          | cons motive rest =>
            cases rest
            dsimp only at success ambient ⊢
            obtain ⟨entered,inside⟩ := enter_success success
            rw [entered] at success ambient ⊢
            obtain ⟨kept,safe,typed⟩ := NativeCoreGhostOwnerReturns.runBack_modeRefines
              (state := {state with steps := state.steps+1}) boxedMetadata (normalLocal depth) (normalProgress depth)
              (ghostSound onStart context depth) (ghostProgress depth bindings)
              onBase inside owner motive success ambient retained
            exact ⟨kept,safe,typed⟩
      case take =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons owner rest =>
          cases rest with
          | cons continuation rest =>
            cases rest
            dsimp only at success ambient ⊢
            obtain ⟨entered,inside⟩ := enter_success success
            rw [entered] at success ambient ⊢
            obtain ⟨kept,safe,typed⟩ := NativeCoreGhostTakeInference.runInMode_refines
              (state := {state with steps := state.steps+1}) wf (normalLocal depth) (normalProgress depth)
              modeSound childCost onBase inside owner continuation success ambient retained
            exact ⟨kept,safe,typed⟩
      case give erased =>
        have length : refs.length = 3 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩⟩ <;> simp at length
        cases children with
        | cons motive rest =>
          cases rest with
          | cons owner rest =>
            cases rest with
            | cons result rest =>
              cases rest
              dsimp only at success ambient ⊢
              obtain ⟨entered,inside⟩ := enter_success success
              rw [entered] at success ambient ⊢
              let visitResult : Infer := if erased then ghost depth bindings else recur
              have resultSound : ModeSound env loans start ctx limit (false || erased) visitResult := by
                cases erased
                · exact modeSound
                · exact erasedSound
              have resultCost : ∀ state root, state.steps ≤ limit → Progress limit state (visitResult state root) := by
                cases erased
                · exact childCost
                · exact ghostProgress depth bindings
              obtain ⟨kept,safe,typed⟩ := NativeCoreGhostOwnerReturns.runGiveWithModes_refines
                (state := {state with steps := state.steps+1}) boxedMetadata (normalLocal depth) (normalProgress depth)
                modeSound (ghostSound onStart context depth) resultSound
                childCost (ghostProgress depth bindings) resultCost onBase inside motive owner result success ambient retained
              exact ⟨kept,safe,typed⟩
      case arith | uadd | alloc | strict | drop | free | app | absurd =>
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
            | obtain ⟨kept,safe,typed⟩ := strict_refinesMode (state := {state with steps := state.steps+1})
                modeSound childCost onBase inside first second success ambient retained
              exact ⟨kept,safe,typed⟩
            | obtain ⟨kept,backward,typed⟩ := inferDrop_modeRefines (state := {state with steps := state.steps+1})
                boxedMetadata (normalLocal depth) (normalProgress depth) modeSound childCost onBase inside
                first second success ambient retained
              exact ⟨kept,backward,typed⟩
            | obtain ⟨kept,backward,typed⟩ := NativeCoreBufferRelease.inferFree_refines
                (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                modeSound childCost onBase inside first second success ambient retained
              exact ⟨kept,backward,typed⟩
            | obtain ⟨kept,backward,typed⟩ := inferAlloc_modeRefines (state := {state with steps := state.steps+1})
                (normalLocal depth) (normalProgress depth) modeSound childCost onBase inside first second success ambient retained
              exact ⟨kept,backward,typed⟩
            | obtain ⟨kept,safe,typed⟩ := inferAbsurdInMode_modeRefines (state := {state with steps := state.steps+1})
                (normalLocal depth) (normalProgress depth) (ghostSound onStart context depth) (ghostProgress depth bindings)
                onBase inside first second success ambient retained
              exact ⟨kept,safe,typed⟩
            | apply arithmetic_refinesMode (state := {state with steps := state.steps+1}) (depth := depth)
                (normalLocal depth) (normalProgress depth) modeSound childCost
                onBase inside first second rfl _ success ambient retained
              intro left right
              simp only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] at left right ⊢
              first | exact .arith left right | exact .uadd left right
            | let callee := runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth bindings true
              let erased := ghost depth bindings
              have calleeTyped : NativeCoreCodeApplication.Sound env loans start ctx limit false callee := by
                intro _ _ _ _ _ held cost represented succeeded finalPrefix comparisons
                obtain ⟨kept,safe,typed⟩ := ih onStart context frames held cost
                  represented succeeded finalPrefix comparisons
                exact ⟨kept,safe,typed⟩
              have operandTyped : ∀ mode, NativeCoreCodeApplication.Sound env loans start ctx limit mode
                  (if mode then erased else recur) := by
                intro mode
                cases mode
                · exact modeSound
                · exact erasedSound
              have operandProgress : ∀ (mode : Bool) state root, state.steps ≤ limit →
                  Progress limit state ((if mode then erased else recur) state root) := by
                intro mode
                cases mode
                · exact childCost
                · exact ghostProgress depth bindings
              obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreCodeApplicationFinalization.run_refines
                (state := {state with steps := state.steps+1}) wf normalLocalFree normalLocal normalProgress
                calleeTyped operandTyped (fun _ _ inside => runWithConstructors_progress ghostProgress normalProgress inside)
                operandProgress (ghostProgress depth bindings) (ghostSound onStart context depth) boxedMetadata onBase inside
                (.node read arity (.cons first (.cons second .nil))) first second success ambient retained
              exact ⟨kept,safe,type,represented,by simpa only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      case usub | index | pack | lend =>
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
              first
              | obtain ⟨kept,safe,typed⟩ := inferSubtractWithProof_modeRefines
                  (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                  modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                  onBase inside left right proof success ambient retained
                exact ⟨kept,safe,typed⟩
              | obtain ⟨kept,safe,typed⟩ := inferIndexWithProof_modeRefines
                  (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                  modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                  onBase inside left right proof success ambient retained
                exact ⟨kept,safe,typed⟩
              | obtain ⟨kept,safe,typed⟩ := inferPackWithEvidence_modeRefines
                  (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                  modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                  onBase inside left right proof success ambient retained
                exact ⟨kept,safe,typed⟩
              | let entered := {state with steps := state.steps+1}
                let visitCode := fun saved => runWithConstructors normal ghost env isData boxed constructorRoots limit saved depth bindings false
                have codeSound : ∀ {arena saved active}, Prefix start arena →
                    FramesRep arena saved active → ModeSound env active arena ctx limit false (visitCode saved) := by
                  intro arena saved active later stack
                  exact ih (onStart.trans later) (context.frame later) stack
                rw [context.length_eq] at success ambient ⊢
                obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreGhostLendInference.runCode_refines
                  (state := entered) wf metadata boxedMetadata (normalLocal depth) (normalProgress depth)
                  (ghostSound onStart context depth) (ghostProgress depth bindings) codeSound
                  (fun _ _ _ room => runWithConstructors_progress ghostProgress normalProgress room)
                  onBase inside (frames.frame onBase) left right proof success ambient retained
                exact ⟨kept,safe,type,represented,by
                  simpa only [Term.lend,EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      case witness | proof =>
        have length : refs.length = 1 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp at length
        cases children with
        | cons subject rest =>
          cases rest
          dsimp only at success ambient ⊢
          obtain ⟨entered,inside⟩ := enter_success success
          rw [entered] at success ambient ⊢
          first
          | obtain ⟨kept,safe,type,represented,typed⟩ := inferRefinementProjection_modeRefines
              (state := {state with steps := state.steps+1}) (mode := false) (evidence := false)
              (normalLocal depth) (normalProgress depth) modeSound childCost onBase inside subject success ambient retained
            exact ⟨kept,safe,type,represented,typed⟩
          | obtain ⟨kept,safe,type,represented,typed⟩ := inferRefinementProjection_modeRefines
              (state := {state with steps := state.steps+1}) (mode := false) (evidence := true)
              (normalLocal depth) (normalProgress depth) erasedSound (ghostProgress depth bindings)
              onBase inside subject success ambient retained
            exact ⟨kept,safe,type,represented,typed⟩
      case borrow =>
        have length : refs.length = 1 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp at length
        cases children with
        | cons ownerRep rest =>
          cases rest
          dsimp only at success ambient ⊢
          obtain ⟨entered,inside⟩ := enter_success success
          rw [entered] at success ambient ⊢
          obtain ⟨index,rfl⟩ := NativeCoreCodeBorrow.accepted_owner_named
            (state := {state with steps := state.steps+1}) ownerRep success
          rw [context.length_eq] at success ambient ⊢
          obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreCodeBorrow.run_refines
            (state := {state with steps := state.steps+1}) wf boxedMetadata (frames.frame onBase)
            (ghostSound onStart context depth) (normalLocal depth) (normalProgress depth)
            onBase inside ownerRep success ambient retained
          exact ⟨kept,safe,.ref type,represented,by
            simpa only [Term.borrow,Term.ref,EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      case con family constructor count =>
        dsimp only at success ambient ⊢
        obtain ⟨entered,inside⟩ := enter_success success
        rw [entered] at success ambient ⊢
        rw [context.length_eq] at success ambient ⊢
        let inferField : Bool → Infer := fun flag => if flag then ghost depth bindings else recur
        have fieldsSound : ∀ flag, ModeSound env loans start ctx limit flag (inferField flag) := by
          intro flag
          cases flag
          · exact modeSound
          · exact erasedSound
        have fieldsCost : ∀ flag state root, state.steps ≤ limit → Progress limit state (inferField flag state root) := by
          intro flag
          cases flag
          · exact childCost
          · exact ghostProgress depth bindings
        obtain ⟨kept,safe,typed⟩ := NativeCoreGhostConstructorInference.runSelectedByMode_refines
          (state := {state with steps := state.steps+1}) wf (constructorsSound.frame onStart)
          (normalLocal depth) (normalProgress depth) fieldsSound fieldsCost onBase inside
          children arity success ambient retained
        exact ⟨kept,safe,typed⟩
      case elements count =>
        dsimp only at success ambient ⊢
        obtain ⟨entered,inside⟩ := enter_success success
        rw [entered] at success ambient ⊢
        obtain ⟨kept,safe,typed⟩ := inferElements_modeRefines (state := {state with steps := state.steps+1})
          (normalLocal depth) (normalProgress depth) modeSound childCost onBase inside children success ambient retained
        exact ⟨kept,safe,typed⟩
      case store =>
        have length : refs.length = 4 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩⟩⟩ <;> simp at length
        cases children with
        | cons buffer rest =>
          cases rest with
          | cons index rest =>
            cases rest with
            | cons value rest =>
              cases rest with
              | cons proof rest =>
                cases rest
                dsimp only at success ambient ⊢
                obtain ⟨entered,inside⟩ := enter_success success
                rw [entered] at success ambient ⊢
                obtain ⟨kept,safe,typed⟩ := inferStoreWithProof_modeRefines
                  (state := {state with steps := state.steps+1}) (normalLocal depth) (normalProgress depth)
                  modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                  onBase inside buffer index value proof success ambient retained
                exact ⟨kept,safe,typed⟩
      case load =>
        have length : refs.length = 4 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩⟩⟩ <;> simp at length
        cases children with
        | cons buffer rest =>
          cases rest with
          | cons index rest =>
            cases rest with
            | cons value rest =>
              cases rest with
              | cons proof rest =>
                cases rest
                dsimp only at success ambient ⊢
                obtain ⟨entered,inside⟩ := enter_success success
                rw [entered] at success ambient ⊢
                obtain ⟨kept,safe,typed⟩ := inferLoadWithProof_modeRefines
                  (state := {state with steps := state.steps+1}) wf (normalLocal depth) (normalProgress depth)
                  modeSound childCost (ghostSound onStart context depth) (ghostProgress depth bindings)
                  onBase inside buffer index value proof success ambient retained
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
                let next := fun assumption => runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth
                  (⟨assumption,true⟩ :: bindings) false
                have branchSound (equality : Bool) : ∀ {opened assumption}, Prefix state.arena opened →
                    Represents opened assumption (.node (conditionOp equality) [a,b]) →
                    ModeSound env loans opened
                      (⟨EnvironmentDelta.expand env (.node (conditionOp equality) [a,b]),true⟩ :: ctx) limit false
                      (next assumption) := by
                  intro opened assumption kept represented _ _ _ _ _ current currentRoom branch checked future tape
                  have baseHere := onBase.trans kept
                  have extended : ContextRep env opened (⟨assumption,true⟩ :: bindings)
                      (⟨EnvironmentDelta.expand env (.node (conditionOp equality) [a,b]),true⟩ :: ctx) :=
                    .cons ⟨_,represented,rfl,rfl⟩ (context.frame baseHere)
                  obtain ⟨kept,safe,typed⟩ := ih (head := false) (onStart.trans baseHere) extended (frames.frame baseHere)
                    current currentRoom branch checked future tape
                  exact ⟨kept,safe,typed⟩
                have enteredNormal : VisitsFrom state.arena (ExpandedNormalization env) (normal depth) := by
                  intro _ _ _ _ later represented succeeded
                  exact normalLocal depth (onBase.trans later) represented succeeded
                have enteredMode : ModeSound env loans state.arena ctx limit false recur := by
                  intro _ _ _ _ _ later room represented succeeded after tape
                  exact modeSound (onBase.trans later) room represented succeeded after tape
                first
                | obtain ⟨kept,safe,typed⟩ := inferConditional_modeRefines
                    (state := {state with steps := state.steps+1}) (inferThen := next) wf enteredNormal (normalProgress depth)
                    enteredMode childCost (branchSound false) (fun _ _ _ room => runWithConstructors_progress ghostProgress normalProgress room)
                    (.refl _) inside leftRep rightRep yesRep noRep success ambient retained
                  exact ⟨kept,safe,typed⟩
                | obtain ⟨kept,safe,typed⟩ := inferConditional_modeRefines
                    (state := {state with steps := state.steps+1}) (inferThen := next) wf enteredNormal (normalProgress depth)
                    enteredMode childCost (branchSound true) (fun _ _ _ room => runWithConstructors_progress ghostProgress normalProgress room)
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
            let visitBody := fun binding => runWithConstructors normal ghost env isData boxed constructorRoots limit snapshots depth (binding :: bindings) false
            have bodySound : NativeCoreCodeApplication.Sound env loans state.arena
                (⟨EnvironmentDelta.expand env D,flag⟩ :: ctx) limit false (visitBody ⟨domain,flag⟩) := by
              intro _ _ _ _ _ localBase cost represented succeeded finalPrefix comparisons
              obtain ⟨kept,safe,typed⟩ := ih (head := false) enteredBase extended (frames.frame onBase) localBase cost
                represented succeeded finalPrefix comparisons
              exact ⟨kept,safe,typed⟩
            obtain ⟨kept,safe,type,represented,typed⟩ := NativeCoreCodeLambda.run_refines
              (state := {state with steps := state.steps+1}) (visitBody := visitBody) (depth := depth)
              metadata boxedMetadata enteredNormal (normalProgress depth) (ghostSound enteredBase enteredContext depth)
              bodySound (ghostProgress depth bindings) (fun _ _ inside => runWithConstructors_progress ghostProgress normalProgress inside)
              (.refl _) inside domainRep bodyRep success ambient retained
            exact ⟨kept,safe,_,represented,by simpa only [Term.lam,EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using typed⟩
      all_goals
        exact runtimeHead_sound wf context (ghostSound onStart context (depth+1))
          onBase room (.node read arity children) success ambient retained

abbrev runWithLoans (normal : Nat → Visit) (ghost : GhostAt) (env : Environment)
    (isData boxed : Nat → Bool) (limit : Nat) (snapshots : List Snapshot) : Nat → List GraphBinding → Bool → Infer :=
  runWithConstructors normal ghost env isData boxed (fun _ _ => none) limit snapshots

theorem runWithLoans_progress
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runWithLoans normal ghost env isData boxed limit snapshots depth bindings head state root) :=
  runWithConstructors_progress ghostProgress normalProgress room

theorem runWithLoans_sound (wf : UnifiedProgram.EnvWellFormed env)
    (metadata : NativeCoreGhostSort.DataFamilies env isData)
    (boxedMetadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalFree : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs base normal)
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (ghostSound : ∀ {arena bindings ctx}, Prefix base arena → ContextRep env arena bindings ctx →
      ∀ depth, InferSound env arena ctx limit (ghost depth bindings))
    (onStart : Prefix base start) (context : ContextRep env start bindings ctx)
    (frames : FramesRep start snapshots loans) :
    ModeSound env loans start ctx limit false (runWithLoans normal ghost env isData boxed limit snapshots depth bindings head) :=
  runWithConstructors_sound wf metadata boxedMetadata (by intro _ _ _ impossible; cases impossible)
    normalProgress normalSound normalFree ghostProgress ghostSound onStart context frames

abbrev run (normal : Nat → Visit) (ghost : GhostAt) (env : Environment)
    (isData boxed : Nat → Bool) (limit : Nat) : Nat → List GraphBinding → Bool → Infer :=
  runWithLoans normal ghost env isData boxed limit []

theorem run_progress
    (ghostProgress : ∀ depth bindings state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run normal ghost env isData boxed limit depth bindings head state root) :=
  runWithLoans_progress ghostProgress normalProgress room

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
  intro _ _ _ _ _ onBase room source success ambient retained
  obtain ⟨kept,safe,typed⟩ := runWithLoans_sound wf metadata boxedMetadata normalProgress normalSound normalFree
    ghostProgress ghostSound onStart context (loans := []) FamilyEnvironment.RelList.nil
    onBase room source success ambient retained
  exact ⟨kept,safe,typed⟩

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

private def runtimeArraySnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨4,2⟩]
  families := []
  arena := #[.node (.integer 3) [],.node (.integer (-4)) [],.node (.elements 2) [0,1],
    .node (.natural 2) [],.node .array [3]]

private def runtimeAllocationSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨3,2⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.integer (-7)) [],.node .alloc [0,1],.node .buffer [0]]

private def runtimeBufferOperationsSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨8,5⟩,⟨9,7⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.natural 0) [],.node (.integer (-7)) [],.node .alloc [0,2],
    .node .decide [1,0],.node .store [3,1,2,4],.node (.natural 9) [],.node .free [5,6],
    .node .buffer [0],.node .u64 []]

private def runtimeIndexSnapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨11,6⟩,⟨13,12⟩]
  families := []
  arena := #[.node (.natural 2) [],.node (.natural 1) [],.node (.integer 3) [],.node (.integer (-4)) [],
    .node (.elements 2) [2,3],.node .decide [1,0],.node .index [4,1,5],.node .buffer [0],.node .ref [7],
    .var 0,.node .index [9,1,5],.node .i64 [],.node (.lam false) [8,10],.node (.pi false) [8,11]]

private def runtimeMemoryProbe (arena : Arena) (limit depth : Nat)
    (bindings : List NativeCoreGhostSpineInference.GraphBinding) (root : Nat) :=
  run (NativeCoreGhostLiteralAddition.run [] 0 limit) (NativeCoreGhostSpineInference.run [] 0 limit)
    empty (fun _ => false) (fun _ => false) limit depth bindings false ⟨arena,0⟩ root

set_option maxRecDepth 4096 in
/-- Allocation, materialized arrays, owner stores and both forms of
indexing use the original operands and the native result rows in CODE. -/
theorem memory_visits_match_native_code :
    let array := runtimeMemoryProbe runtimeArraySnapshot.arena 9 20 [] 2
    let allocation := runtimeMemoryProbe runtimeAllocationSnapshot.arena 9 20 [] 2
    let store := runtimeMemoryProbe runtimeBufferOperationsSnapshot.arena 40 32 [] 5
    let plain := runtimeMemoryProbe runtimeIndexSnapshot.arena 36 32 [] 6
    let borrowed := runtimeMemoryProbe runtimeIndexSnapshot.arena 34 32 [⟨8,false⟩] 10
    array.state.steps = 9 ∧ array.result.map Inferred.typeRoot = .ok 9 ∧
      array.state.arena[9]? = some (.node .array [8]) ∧
    allocation.state.steps = 9 ∧ allocation.result.map Inferred.typeRoot = .ok 8 ∧
      allocation.state.arena[8]? = some (.node .buffer [0]) ∧
    store.state.steps = 40 ∧ store.result.map Inferred.typeRoot = .ok 24 ∧
      store.state.arena[24]? = some (.node .buffer [0]) ∧
    plain.state.steps = 36 ∧ plain.result.map Inferred.typeRoot = .ok 26 ∧
      plain.state.arena[21]? = some (.node .lt [1,17]) ∧ plain.state.arena[26]? = some (.node .i64 []) ∧
    borrowed.state.steps = 34 ∧ borrowed.result.map Inferred.typeRoot = .ok 21 ∧
      borrowed.state.arena[16]? = some (.node .lt [1,0]) ∧ borrowed.state.arena[21]? = some (.node .i64 []) := by
  cbv


private def lendCallbackInput : Arena := #[
  .var 0,.node (.natural 1) [],.node .buffer [1],.node .ref [2],
  .node (.natural 0) [],.node .decide [4,1],.node .index [0,4,5],.node (.lam false) [3,6],
  .node .i64 [],.var 1,.node .free [0,9],.node (.lam false) [2,10],
  .node (.lam false) [8,11],.node .lend [0,7,12],.node .ref [2]]

private def preparedReaderArena : Arena :=
  (NativeCoreDependentLendCallbacks.run 13 31 ⟨lendCallbackInput,0⟩ 0 7 12).state.arena

private def checkReader (limit : Nat) (snapshots : List NativeCoreCodeLeaseLookup.Snapshot) :=
  runWithLoans (NativeCoreGhostLiteralAddition.run [] 0 limit) (NativeCoreGhostSpineInference.run [] 0 limit)
    empty (fun _ => false) (fun _ => false) limit snapshots 31 [⟨2,false⟩] false ⟨preparedReaderArena,0⟩ 16

set_option maxRecDepth 4096 in
/-- The actual specialized Index reader gains its borrowed reference from
the saved owner. The same reader without that snapshot stops after two
entries with the original arena. -/
theorem prepared_reader_borrow_matches_native :
    let active := checkReader 38 [⟨1,0⟩]
    let outside := checkReader 2 []
    active.state = ⟨preparedReaderArena ++ #[.node .ref [2],.node .u64 [],.node .u64 [],.node .lt [4,1],
      .node .u64 [],.node .u64 [],.node .u64 [],.node .lt [4,1],.node .i64 []],38⟩ ∧
      active.result.map Inferred.typeRoot = .ok 29 ∧
      outside = ⟨⟨preparedReaderArena,2⟩,.error (.outsideFragment 15)⟩ := by
  cbv

private def checkLend (arena : Arena) (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  run normal (NativeCoreGhostSpineInference.runWith normal [] 0 limit)
    empty (fun _ => false) (fun _ => false) limit 32 [⟨2,false⟩] false
    ⟨arena,0⟩ root

set_option maxRecDepth 4096 in
/-- Recursive CODE Lend retains the signed result through the final
native continuation gate. Exhaustion there retains every earlier row. -/
theorem dependent_lend_matches_native_code :
    let source := lendCallbackInput.extract 0 14
    let full := checkLend source 112 13
    let short := checkLend source 111 13
    full.state.steps = 112 ∧ full.state.arena.size = 37 ∧
      full.result.map Inferred.typeRoot = .ok 8 ∧ full.state.arena[8]? = some (.node .i64 []) ∧
      short.state.steps = 112 ∧ short.state.arena = full.state.arena ∧
      short.result = .error (.tick (.stepLimit 8)) := by
  cbv

private def genericLendInput : Arena :=
  lendCallbackInput.extract 0 14 ++ #[.node (.integer 6) [],.node .alloc [1,14],.node .lend [15,7,12]]

set_option maxRecDepth 4096 in
/-- The generic CODE path checks the concrete allocation and both
original callbacks, then retains the lowered result across the last visit. -/
theorem generic_lend_matches_native_code :
    let full := checkLend genericLendInput 126 16
    let short := checkLend genericLendInput 125 16
    full.state.steps = 126 ∧ full.state.arena.size = 42 ∧
      full.result.map Inferred.typeRoot = .ok 8 ∧ full.state.arena[8]? = some (.node .i64 []) ∧
      short.state.steps = 126 ∧ short.state.arena = full.state.arena ∧
      short.result = .error (.tick (.stepLimit 8)) := by
  cbv

private def refinementInput : Arena := #[.node .u64 [],.var 0,.node .eq [1,1],
  .node (.lam false) [0,2],.node .refine [3],.node (.natural 7) [],.node .refl [5],.node .pack [3,5,6],.var 0]

private def checkCodeProbe (arena : Arena) (limit root : Nat)
    (bindings : List NativeCoreGhostSpineInference.GraphBinding) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  run normal (NativeCoreGhostSpineInference.runWith normal [] 0 limit)
    empty (fun _ => false) (fun _ => false) limit 24 bindings false ⟨arena,0⟩ root

set_option maxRecDepth 4096 in
/-- CODE Pack visits the word, and the two projections select different
modes for the same written subject. -/
theorem runtime_refinement_modes_match_native :
    let packed := checkCodeProbe refinementInput 54 7 [⟨4,false⟩]
    let read := checkCodeProbe (refinementInput.push (.node .witness [7])) 61 9 [⟨4,false⟩]
    let witness := refinementInput.push (.node .witness [8])
    let denied := checkCodeProbe witness 2 9 [⟨4,true⟩]
    let inspected := checkCodeProbe (refinementInput.push (.node .proof [8])) 14 9 [⟨4,true⟩]
    packed.state.steps = 54 ∧ packed.state.arena.size = 24 ∧
      packed.result.map Inferred.typeRoot = .ok 23 ∧ packed.state.arena[23]? = some (.node .refine [3]) ∧
    read.state.steps = 61 ∧ read.state.arena.size = 26 ∧
      read.result.map Inferred.typeRoot = .ok 25 ∧ read.state.arena[25]? = some (.node .u64 []) ∧
    denied = ⟨⟨witness,2⟩,.error (.outsideFragment 8)⟩ ∧
    inspected.state.steps = 14 ∧ inspected.state.arena.size = 12 ∧
      inspected.result.map Inferred.typeRoot = .ok 11 ∧ inspected.state.arena[10]? = some (.node .witness [8]) ∧
      inspected.state.arena[11]? = some (.node .app [3,10]) := by cbv

private def dropInput (recursive : Bool) : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨true,0,0,0,[1,3]⟩]
  arena := #[.node (.natural 0) [],.node (.ind 0 0) [],.node .u64 [],
    .node (.pi false) [if recursive then 1 else 2,1],.var 0,.node .borrow [4],.node .deref [5],
    .node .u64 [],.node .u64 [],.node .u64 [],.node (.integer (-3)) [],.node (.drop 0) [4,10]]

private def checkDrop (recursive : Bool) (limit : Nat) : Outcome Inferred :=
  let snapshot := dropInput recursive
  let checked : Option Environment := do
    let (definitions,families) ← NativeFamilyWire.decodeProgram snapshot
    LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)
  let env := checked.getD empty
  let normal := NativeCoreExpandedFamilies.raw env snapshot.families [] 0 limit
  run normal (NativeCoreGhostSpineInference.runWith normal [] 0 limit) env
    (NativeCoreGhostSort.isDataAt env) (NativeCoreGhostReferenceTypes.isBoxedAt env)
    limit 32 [⟨1,false⟩] false ⟨snapshot.arena,0⟩ 11

/-- Boxed Drop visits the original owner and code tail. A flat family is
rejected at the first visit, before the owner can allocate any rows. -/
theorem boxed_drop_matches_native_code :
    (let released := checkDrop true 5
     released.state.steps = 5 ∧ released.result.map Inferred.typeRoot = .ok 12 ∧
       released.state.arena[12]? = some (.node .i64 [])) ∧
    checkDrop false 1 = ⟨⟨(dropInput false).arena,1⟩,.error (.outsideFragment 11)⟩ := by cbv

private def formationInput : Arena :=
  (refinementInput.extract 0 5).push (.node (.universe 0) [])

private def transportInput : Arena := (refinementInput.extract 0 4) ++
  #[.node (.natural 7) [],.node .refl [4],.node .transport [3,5,5],.node .eq [4,4]]

set_option maxRecDepth 4096 in
/-- Formation and Transport start their ordinary ghost entry once, with
the same native tick and graph append order in CODE. -/
theorem formation_and_transport_share_ghost_visits :
    let formed := checkCodeProbe formationInput 24 4 []
    let stopped := checkCodeProbe transportInput 32 6 []
    formed.state.steps = 24 ∧ formed.state.arena.size = 14 ∧
      formed.result.map Inferred.typeRoot = .ok 13 ∧ formed.state.arena[13]? = some (.node (.universe 0) []) ∧
    stopped.state.steps = 33 ∧ stopped.state.arena.size = 19 ∧
      stopped.state.arena[17]? = some (.node .eq [4,4]) ∧ stopped.state.arena[18]? = some (.node .app [3,4]) ∧
      stopped.result = .error (.tick (.stepLimit 5)) := by cbv

private def localConstructorInput (data : Bool) : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨data,0,1,0,[7]⟩]
  arena := #[.node (.natural 3) [],.node .u64 [],.var 0,.var 1,.node .eq [2,2],
    .node (.ind 0 1) [3],.node (.pi true) [4,5],.node (.pi false) [1,6],.node .refl [0],
    .node (.con 0 0 1) [0],.node (.con 0 0 2) [0,8],.node (.universe 0) [],.node .u64 [],
    .node .prop [],.node .u64 [],.node (.con 0 0 2) [3,2]]

private def checkLocalConstructor (data erased ghost : Bool) (limit : Nat) : Outcome Inferred :=
  let snapshot := localConstructorInput data
  let checked : Option Environment := do
    let (definitions,families) ← NativeFamilyWire.decodeProgram snapshot
    LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)
  let env := checked.getD empty
  let normal := NativeCoreExpandedFamilies.raw env snapshot.families [] 0 limit
  let kind := NativeCoreGhostSort.isDataAt env
  let boxed := NativeCoreGhostReferenceTypes.isBoxedAt env
  let table := NativeCoreGhostConstructorInference.constructorAt snapshot.families 0
  let inferGhost := NativeCoreGhostSpineInference.runWithConstructors normal [] 0 limit kind boxed
    (NativeCoreGhostSpineInference.visibleFamilyShape env 0) table
  let state : State := ⟨snapshot.arena,0⟩
  let bindings : List NativeCoreGhostSpineInference.GraphBinding := [⟨4,true⟩,⟨1,erased⟩]
  if ghost then inferGhost 32 bindings state 15
  else runWithConstructors normal inferGhost env kind boxed table limit [] 32 bindings false state 15

private def completeLocalField (output : Outcome Inferred) : Prop :=
  output.state.steps = 54 ∧ output.state.arena.size = 25 ∧ output.result.map Inferred.typeRoot = .ok 24 ∧
    NativeArena.decode 4 output.state.arena 24 = some (.node (.ind 0 1) [.var 1])

set_option maxRecDepth 4096 in
/-- Constructor field mode comes from the actual admitted family kind and
each instantiated binder. The completed result keeps the original local index. -/
theorem constructor_modes_preserve_actual_field_indices :
    completeLocalField (checkLocalConstructor true false false 54) ∧
    completeLocalField (checkLocalConstructor true true true 54) ∧
    completeLocalField (checkLocalConstructor false true false 54) ∧
    checkLocalConstructor true true false 18 =
      ⟨⟨(localConstructorInput true).arena,18⟩,.error (.outsideFragment 3)⟩ := by cbv

/-- Even in CODE, ZeroLe checks its operand in ghost mode and retains the
original word reference in the mathematical successor. -/
theorem zero_bound_uses_ghost_operand :
    let wide : Arena := #[.node (.natural (2^64-1)) [],.node .zeroLe [0],.node (.natural 0) [],
      .node (.natural 1) [],.node .uadd [0,3],.node .lt [2,4]]
    let accepted := checkCodeProbe wide 5 1 []
    let erased : Arena := #[.node .u64 [],.var 0,.node .zeroLe [1]]
    let throughErasure := checkCodeProbe erased 6 2 [⟨0,true⟩]
    accepted.state.steps = 5 ∧ accepted.state.arena.size = 12 ∧
      accepted.result.map Inferred.typeRoot = .ok 11 ∧ accepted.state.arena[10]? = some (.node .uadd [0,9]) ∧
      accepted.state.arena[11]? = some (.node .lt [8,10]) ∧
      throughErasure.state.steps = 6 ∧ throughErasure.state.arena.size = 8 ∧
      throughErasure.result.map Inferred.typeRoot = .ok 7 ∧
      throughErasure.state.arena[6]? = some (.node .uadd [1,5]) := by cbv

private def loadInput : Arena := #[.node (.natural 0) [],.node .u64 [],.node .i64 [],
  .var 0,.node .lt [0,3],.var 1,.node (.integer (-7)) [],.node .alloc [5,6],.var 2,.node .buffer [8],
  .node .free [3,5],.node (.lam false) [9,10],.node (.lam false) [2,11],.node .load [7,0,3,12],
  .node (.lam true) [4,13],.node (.lam false) [1,14],.node (.pi true) [4,2],.node (.pi false) [1,16]]

set_option maxRecDepth 4096 in
/-- CODE Load checks the erased bound and both live callback binders. The
last normalization keeps the result and the previously compared owner rows. -/
theorem load_retains_lowered_code_callback_result :
    let bindings : List NativeCoreGhostSpineInference.GraphBinding := [⟨4,true⟩,⟨1,false⟩]
    let full := checkCodeProbe loadInput 77 13 bindings
    let short := checkCodeProbe loadInput 76 13 bindings
    full.state.steps = 77 ∧ full.state.arena.size = 37 ∧ full.result.map Inferred.typeRoot = .ok 2 ∧
      full.state.arena[24]? = some (.node .lt [0,5]) ∧ full.state.arena[36]? = some (.node .buffer [35]) ∧
      short.state = full.state ∧ short.result = .error (.tick (.stepLimit 2)) := by cbv

/-- CODE Absurd obtains its premise from a ghost slot after certifying the
original target type's result head. -/
theorem absurd_preserves_code_target_root :
    let arena : Arena := #[.node (.natural 0) [],.node .lt [0,0],.node .u64 [],.var 0,.node .absurd [2,3]]
    let checked := checkCodeProbe arena 12 4 [⟨1,true⟩]
    checked.state.steps = 12 ∧ checked.result.map Inferred.typeRoot = .ok 2 := by cbv

end Jihoo.NativeKernel.NativeCoreCodeInference.Examples
