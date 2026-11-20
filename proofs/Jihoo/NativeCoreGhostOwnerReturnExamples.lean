import Jihoo.NativeCoreGhostOwnerReturns
import Jihoo.NativeCoreGhostSpineInference

/-! The owner-return cases share the live recursive operand visitors. -/
namespace Jihoo.NativeKernel.NativeCoreGhostOwnerReturnExamples

open NativeArena NativeProgramWire Environment
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (Inferred)

private def input : Arena := #[.node (.natural 2) [],.node .buffer [0],.node .u64 [],.node (.lam false) [1,2],
  .node (.back false) [1,3],.node (.integer 0) [],.node .alloc [0,5],.node (.give false) [3,6,0],
  .node .ref [1],.node (.lam false) [1,8],.node (.back false) [1,9],.node .eq [0,0],
  .node (.lam false) [1,11],.node (.back true) [1,12]]

private def form (limit : Nat) (erased : Bool) (motive : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWith normal [] 0 limit 31 []
  NativeCoreGhostOwnerReturns.runBack infer (normal 31) (fun _ => false) limit 31 ⟨input,1⟩ erased 1 motive

private def give (limit : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWith normal [] 0 limit 31 []
  NativeCoreGhostOwnerReturns.runGive infer (normal 31) (fun _ => false) limit 31 ⟨input,1⟩ false 3 6 0

/-- Each clock starts at one to account for the enclosing native inference
tick. Back forms Type0 in both cases. Give retains its original motive and
the buffer's original length in the type that it appends last. -/
theorem owner_return_motive_and_result_schedule :
    (let formed := form 32 false 3
     formed.state.steps = 32 ∧ formed.result.map Inferred.typeRoot = .ok 22 ∧
       formed.state.arena[22]? = some (.node (.universe 0) [])) ∧
    (let formed := form 36 true 12
     formed.state.steps = 36 ∧ formed.result.map Inferred.typeRoot = .ok 25 ∧
       formed.state.arena[25]? = some (.node (.universe 0) [])) ∧
    (let formed := form 128 false 9
     formed.result = .error (.outsideFragment 9)) ∧
    (let given := give 48
     given.state.steps = 48 ∧ given.result.map Inferred.typeRoot = .ok 26 ∧
       ∃ owner, given.state.arena[26]? = some (.node (.back false) [owner,3]) ∧
         given.state.arena[owner]? = some (.node .buffer [0])) := by
  refine ⟨by cbv,by cbv,by cbv,?_⟩
  exact ⟨by cbv,by cbv,⟨18,by cbv,by cbv⟩⟩

private def recursive (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  NativeCoreGhostSpineInference.runWith normal [] 0 limit 32 [] ⟨input,0⟩ root

/-- Dispatch at the original written root follows the same exact graph and
meter as the checked Back and Give branches after their entry tick. -/
theorem recursive_owner_return_schedule :
    recursive 32 4 = form 32 false 3 ∧ recursive 36 13 = form 36 true 12 ∧
      recursive 128 10 = form 128 false 9 ∧ recursive 48 7 = give 48 := by cbv

end Jihoo.NativeKernel.NativeCoreGhostOwnerReturnExamples
