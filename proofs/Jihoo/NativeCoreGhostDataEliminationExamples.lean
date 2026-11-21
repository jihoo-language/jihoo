import Jihoo.NativeCoreGhostDataElimination
import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreExpandedFamilies

namespace Jihoo.NativeKernel.NativeCoreGhostDataElimination.Examples

open Environment NativeArena NativeFamilyWire
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (Inferred)

private def row : FamilyRoots := ⟨true,1,2,0,[7]⟩

private def fixture (proof : Bool) : Arena :=
  #[.node (.natural 2) [],.node .u64 [],.node .i64 [],.var 0,.var 1,
    .node (.ind 0 2) [4,0],.node (.pi false) [2,5],.node (.pi true) [1,6],
    .node (.integer 0) [],.node (.con 0 0 2) [0,8],.node (.ind 0 2) [0,3],.node .eq [4,0],
    .node (.lam false) [10,if proof then 11 else 2],.node (.lam false) [1,12],.node .refl [0],
    .node (.lam false) [2,if proof then 14 else 3],.node (.elim 0 1) [13,15,9],.node (.elim 0 0) [13,9],
    .node (.universe 0) [],.node (.universe 0) [],.node .u64 [],.node .u64 []]

private def runFixture (limit : Nat) (proof : Bool) (branches : List Nat) : Outcome Inferred :=
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw empty [row] [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWithConstructors normal [] 0 limit (· == 0)
    (fun _ => false) (fun family => if family = 0 then some (2,true) else none)
    (NativeCoreGhostConstructorInference.constructorAt [row] 1) depth []
  let root := if branches.isEmpty then 17 else 16
  run infer (normal depth) limit depth ⟨fixture proof,1⟩ 0 13 9 root row branches

theorem indexed_motives_match_native :
    (let data := runFixture 171 false [15]
     data.state.steps = 171 ∧ data.state.arena.size = 53 ∧ data.result.map Inferred.typeRoot = .ok 52 ∧
       data.state.arena[51]? = some (.node .app [13,0]) ∧ data.state.arena[52]? = some (.node .app [51,9])) ∧
    (let proof := runFixture 200 true [15]
     proof.state.steps = 200 ∧ proof.state.arena.size = 59 ∧ proof.result.map Inferred.typeRoot = .ok 58 ∧
       proof.state.arena[57]? = some (.node .app [13,0]) ∧ proof.state.arena[58]? = some (.node .app [57,9])) ∧
    runFixture 200 false [] = ⟨⟨fixture false,1⟩,.error (.outsideFragment 17)⟩ := by
  exact ⟨by cbv,by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCoreGhostDataElimination.Examples
