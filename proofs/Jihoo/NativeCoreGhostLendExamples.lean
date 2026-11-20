import Jihoo.NativeCoreGhostLendInference
import Jihoo.NativeCoreGhostSpineInference

namespace Jihoo.NativeKernel.NativeCoreGhostLendExamples

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (Inferred)

private def input : Arena := #[.var 0,.node (.natural 1) [],.node .buffer [1],.node .ref [2],
  .node (.natural 0) [],.node .decide [4,1],.node .index [0,4,5],.node (.lam false) [3,6],
  .node .i64 [],.var 1,.node .free [0,9],.node (.lam false) [2,10],.node (.lam false) [8,11],
  .node .lend [0,7,12]]

private def inferred (arena : Arena) (owner limit : Nat) : Outcome Inferred :=
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let visit := NativeCoreGhostSpineInference.runWith normal [] 0 limit depth [⟨2,false⟩]
  NativeCoreGhostLendInference.run visit (normal depth) (fun _ => false) (fun _ => false)
    limit depth ⟨arena,1⟩ owner 7 12

/-- The native specialized and generic readers return the original signed
type, with different graph allocations and shared checking costs. -/
theorem two_lend_paths_keep_the_outer_result :
    (let dependent := inferred input 0 104
     dependent.state.steps = 104 ∧ dependent.result.map Inferred.typeRoot = .ok 8 ∧
       dependent.state.arena.size = 37) ∧
    (let ordinary := inferred (input ++ #[.node (.integer 6) [],.node .alloc [1,14],.node .lend [15,7,12]]) 15 110
     ordinary.state.steps = 110 ∧ ordinary.result.map Inferred.typeRoot = .ok 8 ∧
       ordinary.state.arena.size = 42) := by cbv

/-- Recursive ghost inference preserves every row, receipt, and tick of
both standalone routes after paying the original Lend entry tick. -/
theorem recursive_lend_uses_shared_counter :
    let genericArena := input ++ #[.node (.integer 6) [],.node .alloc [1,14],.node .lend [15,7,12]]
    let normal := fun limit => NativeCoreExpandedFamilies.raw empty [] [] 0 limit
    NativeCoreGhostSpineInference.runWith (normal 104) [] 0 104 32 [⟨2,false⟩] ⟨input,0⟩ 13 = inferred input 0 104 ∧
      NativeCoreGhostSpineInference.runWith (normal 110) [] 0 110 32 [⟨2,false⟩] ⟨genericArena,0⟩ 16 =
        inferred genericArena 15 110 := by cbv

end Jihoo.NativeKernel.NativeCoreGhostLendExamples
