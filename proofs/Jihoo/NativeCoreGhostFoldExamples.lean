import Jihoo.NativeCoreGhostFoldInference
import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreCodeInference

/-! Native Fold keeps the first normalized accumulator root. A dependent
body uses an erased bound at the intermediate binder in each case. -/
namespace Jihoo.NativeKernel.NativeCoreGhostFoldExamples

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (Inferred)

private def input : Arena := #[.node (.natural 3) [],.node .i64 [],.node .u64 [],.var 0,
  .node .lt [3,0],.node (.integer 7) [],.node (.lam false) [1,3],.node (.lam true) [4,6],
  .node (.lam false) [2,7],.node .fold [0,5,8],.node .alloc [0,5],.node .buffer [0],
  .node (.lam false) [11,3],.node (.lam true) [4,12],.node (.lam false) [2,13],.node .fold [0,10,14],
  .node .fold [0,0,14]]

private def fold (limit initial body : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWith normal [] 0 limit 31 []
  NativeCoreGhostFoldInference.run empty infer (normal 31) limit 31 ⟨input,1⟩ 0 initial body

/-- With a signed or a Buffer accumulator the branch checks the original
callback and returns the original normalized accumulator type, exactly at
the native budget. An unsigned accumulator fails before callback formation. -/
theorem signed_and_owned_fold_schedule :
    (let signed := fold 58 5 8
     signed.state.steps = 58 ∧ signed.result.map Inferred.typeRoot = .ok 19 ∧
       signed.state.arena.size = 34 ∧ signed.state.arena[19]? = some (.node .i64 [])) ∧
    (let owned := fold 81 10 14
     owned.state.steps = 81 ∧ owned.result.map Inferred.typeRoot = .ok 23 ∧
       owned.state.arena.size = 40 ∧ owned.state.arena[23]? = some (.node .buffer [0])) ∧
    (fold 128 0 14).result = .error (.outsideFragment 0) := by cbv

private def recursive (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  NativeCoreGhostSpineInference.runWith normal [] 0 limit 32 [] ⟨input,0⟩ root

/-- Dispatch from the written root, including its native entry tick, keeps
all of the standalone checking schedule and rejection state. -/
theorem recursive_dispatch_checks_schedule :
    recursive 58 9 = fold 58 5 8 ∧ recursive 81 15 = fold 81 10 14 ∧ recursive 128 16 = fold 128 0 14 := by cbv

private def codeFold (limit initial body : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let ghost := NativeCoreGhostSpineInference.runWith normal [] 0 limit
  let infer := NativeCoreCodeInference.run normal ghost empty (fun _ => false) (fun _ => false) limit 31 [] false
  NativeCoreGhostFoldInference.run empty infer (normal 31) limit 31 ⟨input,1⟩ 0 initial body

set_option maxRecDepth 4096 in
/-- The runtime callback checks its actual linear accumulator binder. The
signed and owned results retain the first normalized annotation. -/
theorem code_fold_checks_runtime_callback :
    (let signed := codeFold 62 5 8
     signed.state.steps = 62 ∧ signed.result.map Inferred.typeRoot = .ok 19 ∧
       signed.state.arena.size = 34 ∧ signed.state.arena[19]? = some (.node .i64 [])) ∧
    (let owned := codeFold 88 10 14
     owned.state.steps = 88 ∧ owned.result.map Inferred.typeRoot = .ok 23 ∧
       owned.state.arena.size = 40 ∧ owned.state.arena[23]? = some (.node .buffer [0])) := by
  exact ⟨by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCoreGhostFoldExamples
