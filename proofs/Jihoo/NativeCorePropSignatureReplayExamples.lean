import Jihoo.NativeCorePropSignatureReplay
import Jihoo.NativeCoreGhostSpineInference

namespace Jihoo.NativeKernel.NativeCorePropSignatureReplay.Examples

open Environment NativeArena
open NativeCoreTransformExact (State)
open NativeCoreGhostSpineInference (Infer Visit)
open NativeCorePureComputationNormal (Outcome)
open NativeCorePropCaseType (SignatureRoots)
open NativeCoreCaseStrict (append)

private def fixture : Arena :=
  #[.node (.natural 0) [],.node .u64 [],.var 0,.var 1,.var 2,.node (.ind 0 1) [0],.node (.ind 0 1) [2],
    .node (.ind 0 1) [3],.node (.ind 0 1) [4],.node (.pi true) [7,8],.node (.pi true) [6,9],
    .node (.pi false) [1,10]]

private def checkIndices (infer : Infer) (normal : Visit) (limit : Nat) (depth : Nat)
    (expected : Nat) : State → List Nat → Outcome Unit
  | state,[] => ⟨state,.ok ()⟩
  | state,index :: indices =>
    (NativeCoreGhostFoldInference.checkAgainst infer normal limit depth state expected index).next fun after _ =>
      checkIndices infer normal limit depth expected after indices

private def replay (limit : Nat) : Outcome (List SignatureRoots) :=
  let depth := 128
  let normalAt := NativeCoreGhostLiteralAddition.run [] 0 limit
  let normal := normalAt depth
  let visit : Bindings → Infer := fun ctx =>
    NativeCoreGhostSpineInference.runWith normalAt [] 0 limit depth
      (ctx.map fun (erased,typeRoot) => ⟨typeRoot,erased⟩)
  let binder : CheckBinder := fun ctx state root erased =>
    (NativeCoreGhostBinderCheck.inferBinder (visit ctx) normal (fun _ => false) state root erased).next
      fun after _ => ⟨after,.ok ()⟩
  let indices : CheckIndices := fun ctx state root refs =>
    if refs.length = 1 then
      (append state .u64 []).next fun after expected =>
        checkIndices (visit ctx) normal limit depth expected after refs
    else ⟨state,.error (.outsideFragment root)⟩
  runTable binder indices normal 0 13 [5,11] ⟨fixture,0⟩

/-- The native declaration normalizes two recursive fields in their
original binder scopes and stores their separate index lists. -/
theorem two_recursive_fields_match_native_declaration :
    let checked := replay 30
    let expected := fixture ++ #[.node .u64 [],.node .u64 [],.node (.universe 0) [],
      .node .u64 [],.node .u64 [],.node .u64 []]
    checked.state.arena = expected ∧ checked.state.steps = 30 ∧
      ∃ base step, checked.result = .ok [base,step] ∧
        base.fields = [] ∧ base.recursive = [] ∧ base.result = [0] ∧
        step.fields = [(false,1),(true,6),(true,7)] ∧
        step.recursive = [(1,[2]),(2,[3])] ∧ step.result = [4] := by
  exact ⟨by cbv,by cbv,_,_,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCorePropSignatureReplay.Examples
