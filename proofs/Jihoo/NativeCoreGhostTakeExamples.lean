import Jihoo.NativeCoreGhostTakeInference
import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreCodeInference

/-! The fixture uses the full ghost driver for Give and for both binders of
the written Take callback. The branch starts just after the entry tick. -/
namespace Jihoo.NativeKernel.NativeCoreGhostTakeExamples

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome Error)
open NativeCoreGhostSpineInference (Inferred)

private def input : Arena := #[.node (.natural 2) [],.node .buffer [0],.node .u64 [],.node (.lam false) [1,2],
  .node (.back false) [1,3],.node (.integer 0) [],.node .alloc [0,5],.node (.give false) [3,6,0],
  .node .ref [1],.node (.lam false) [1,8],.node (.back false) [1,9],.node .eq [0,0],
  .node (.lam false) [1,11],.node (.back true) [1,12],
  .node (.lam false) [2,5],.node (.lam false) [1,14],.node .take [7,15],
  .var 0,.node .alloc [17,5],.node (.lam false) [2,18],.node (.lam false) [1,19],.node .take [7,20],
  .node (.lam true) [2,5],.node (.lam false) [1,22],.node .take [7,23]]

private def take (limit continuation : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWith normal [] 0 limit 31 []
  NativeCoreGhostTakeInference.run infer (normal 31) limit 31 ⟨input,1⟩ 7 continuation

private def escaped : Except Error Inferred → Bool
  | .error (.substitution (.escapes _)) => true
  | _ => false

/-- The dependent result annotation fits the original owner and yields an
I64 at the original caller depth. A callback with an escaping length or a
changed erasure flag is rejected at its respective check. -/
theorem take_checks_original_binders_and_result :
    (let checked := take 95 15
     checked.state.steps = 95 ∧ checked.result.map Inferred.typeRoot = .ok 44 ∧
       checked.state.arena.size = 47 ∧ checked.state.arena[44]? = some (.node .i64 [])) ∧
    escaped (take 256 20).result = true ∧
    (take 256 23).result = .error (.outsideFragment 23) := by cbv

private def recursive (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  NativeCoreGhostSpineInference.runWith normal [] 0 limit 32 [] ⟨input,0⟩ root

/-- Dispatch from the written root, including its native entry tick, keeps
all of the standalone checking schedule and rejection state. -/
theorem recursive_dispatch_checks_schedule :
    recursive 95 16 = take 95 15 ∧ recursive 256 21 = take 256 20 ∧ recursive 256 24 = take 256 23 := by cbv

private def codeInput : Arena := (input.extract 0 14) ++ #[.var 1,.node .free [14,5],
  .node (.lam false) [2,15],.node (.lam false) [1,16],.node .take [7,17]]

private def takeInCode (limit : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let ghost := NativeCoreGhostSpineInference.runWith normal [] 0 limit
  NativeCoreCodeInference.run normal ghost empty (fun _ => false) (fun _ => false) limit 32 [] false ⟨codeInput,0⟩ 18

set_option maxRecDepth 4096 in
/-- Both native callback binders are visited in CODE. The callback really
frees the original owner and the last tick checks the lowered I64 result. -/
theorem runtime_take_keeps_returned_result :
    let full := takeInCode 111
    let short := takeInCode 110
    full.state.steps = 111 ∧ full.state.arena.size = 41 ∧ full.result.map Inferred.typeRoot = .ok 38 ∧
      full.state.arena[38]? = some (.node .i64 []) ∧ short.state = full.state ∧
      short.result = .error (.tick (.stepLimit 38)) := by cbv

end Jihoo.NativeKernel.NativeCoreGhostTakeExamples
