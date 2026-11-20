import Jihoo.NativeCoreGhostLoopInference
import Jihoo.NativeCoreGhostSpineInference

/-! Two native fixtures exercise both accumulator erasure modes. The
proposition case uses the real successor expression in its proof fiber. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLoopExamples

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome PostExtension)
open NativeCoreGhostSpineInference (Inferred)

private def input : Arena := #[.node (.natural 3) [],.node .u64 [],.node .i64 [],.var 0,.node .lt [3,0],
  .node (.lam false) [1,2],.node (.integer 7) [],.node (.lam false) [2,3],.node (.lam true) [4,7],
  .node (.lam false) [1,8],.node .loop [0,5,6,9],.var 1,.var 2,.node (.natural 1) [],
  .node .uadd [12,13],.node .refl [14],.node .eq [11,11],.node (.lam true) [16,15],
  .node (.lam true) [4,17],.node (.lam false) [1,18],.node .eq [3,3],.node (.lam false) [1,20],
  .node (.natural 0) [],.node .refl [22],.node .loop [0,21,23,19]]

-- The measured fixture uses the native post-operand unsigned sum traversal.
private def postSum : PostExtension where
  accepts op := op == .uadd
  finish _ limit depth root state _ _ refs :=
    match refs with
    | [left,right] =>
      let summed := NativeCoreUnsignedSum.run empty false state.arena limit depth state.steps left right
      ⟨⟨summed.arena,summed.steps.getD state.steps⟩,summed.result.mapError fun _ => .outsideFragment root⟩
    | _ => ⟨state,.error (.outsideFragment root)⟩

private def loop (limit motive initial body : Nat) : Outcome Inferred :=
  let normal := NativeCorePureComputationNormal.runWithExtensions postSum (NativeCoreNestedAliases.extension [] 0) limit
  let infer := NativeCoreGhostSpineInference.runWith normal [] 0 limit 31 []
  NativeCoreGhostLoopInference.run (fun _ => false) (CoreEffectAnalysis.graphMemoryFree empty)
    infer (normal 31) limit 31 ⟨input,1⟩ 0 motive initial body

/-- The graph retains the original motive and applied count in both
modes. The native proof path checks the successor fiber under its original
three-binder scope. -/
theorem loop_checks_data_and_successor_proof :
    (let data := loop 99 5 6 9
     data.state.steps = 99 ∧ data.result.map Inferred.typeRoot = .ok 58 ∧
       data.state.arena[58]? = some (.node .app [5,0]) ∧ data.state.arena.size = 59) ∧
    (let proof := loop 196 21 23 19
     proof.state.steps = 196 ∧ proof.result.map Inferred.typeRoot = .ok 83 ∧
       proof.state.arena[83]? = some (.node .app [21,0]) ∧ proof.state.arena.size = 84) := by cbv

end Jihoo.NativeKernel.NativeCoreGhostLoopExamples
