import Jihoo.NativeCoreGhostDataElimination
import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreExpandedFamilies
import Jihoo.NativeCoreCodeInference

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
  let visible : NativeCoreGhostFamilyElimination.FamilyTable := fun family =>
    if family = 0 then some ⟨row,false,[]⟩ else none
  let infer := NativeCoreGhostSpineInference.runWithFamilyElimination normal [] 0 limit (· == 0)
    (fun _ => false) (fun family => if family = 0 then some (2,true) else none)
    (NativeCoreGhostConstructorInference.constructorAt [row] 1) visible (depth+1) []
  let root := if branches.isEmpty then 17 else 16
  infer ⟨fixture proof,0⟩ root

theorem indexed_motives_match_native :
    (let data := runFixture 171 false [15]
     data.state.steps = 171 ∧ data.state.arena.size = 53 ∧ data.result.map Inferred.typeRoot = .ok 52 ∧
       data.state.arena[51]? = some (.node .app [13,0]) ∧ data.state.arena[52]? = some (.node .app [51,9])) ∧
    (let proof := runFixture 200 true [15]
     proof.state.steps = 200 ∧ proof.state.arena.size = 59 ∧ proof.result.map Inferred.typeRoot = .ok 58 ∧
       proof.state.arena[57]? = some (.node .app [13,0]) ∧ proof.state.arena[58]? = some (.node .app [57,9])) ∧
    runFixture 200 false [] = ⟨⟨fixture false,1⟩,.error (.outsideFragment 17)⟩ := by
  exact ⟨by cbv,by cbv,by cbv⟩


private def boxedRow : FamilyRoots := ⟨true,0,1,0,[3,4]⟩

private def boxedFixture : Arena :=
  #[.node (.natural 2) [],.node .u64 [],.var 0,.node (.ind 0 1) [0],.node (.pi false) [3,3],
    .node (.con 0 0 0) [],.node (.ind 0 1) [2],.node (.lam false) [6,1],.node (.lam false) [1,7],
    .node (.natural 0) [],.node (.lam false) [1,9],.node (.lam true) [3,10],
    .node (.lam false) [3,9],.node (.elim 0 2) [8,9,11,5],.node (.caseOf 0 2) [8,9,12,5],
    .node .u64 [],.node .u64 [],.node .u64 [],.node .u64 [],.node .u64 [],.node .u64 []]

private def boxedRun (limit root : Nat) : Outcome Inferred :=
  let normal := NativeCoreExpandedFamilies.raw empty [boxedRow] [] 0 limit
  let visible : NativeCoreGhostFamilyElimination.FamilyTable := fun family =>
    if family = 0 then some ⟨boxedRow,true,[]⟩ else none
  let infer := NativeCoreGhostSpineInference.runWithFamilyElimination normal [] 0 limit (· == 0) (· == 0)
    (fun family => if family = 0 then some (1,true) else none)
    (NativeCoreGhostConstructorInference.constructorAt [boxedRow] 1) visible 32 []
  infer ⟨boxedFixture,0⟩ root

/-- Boxed induction checks a recursive field and its hypothesis, while
one-level analysis checks only the original field. Both uses return the
motive applied to the first scrutinee type's index and the original value. -/
theorem boxed_induction_and_case_match_native :
    (let induction := boxedRun 174 13
     induction.state.steps = 174 ∧ induction.state.arena.size = 63 ∧
       induction.result.map Inferred.typeRoot = .ok 62 ∧
       induction.state.arena[61]? = some (.node .app [8,0]) ∧
       induction.state.arena[62]? = some (.node .app [61,5])) ∧
    (let analysis := boxedRun 115 14
     analysis.state.steps = 115 ∧ analysis.state.arena.size = 50 ∧
       analysis.result.map Inferred.typeRoot = .ok 49 ∧
       analysis.state.arena[48]? = some (.node .app [8,0]) ∧
       analysis.state.arena[49]? = some (.node .app [48,5])) := by
  exact ⟨by cbv,by cbv⟩

private def runCodeFixture (limit : Nat) (proof : Bool) : Outcome Inferred :=
  let arena := fixture proof
  let snapshot : Snapshot := { definitions := [], families := [row], arena := arena }
  let audited : Option Environment := do
    let (definitions,families) ← decodeProgram snapshot
    LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)
  let env := audited.getD empty
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw env [row] [] 0 limit
  let visible : NativeCoreGhostFamilyElimination.FamilyTable := fun family =>
    if family = 0 then some ⟨row,false,[]⟩ else none
  let kind := NativeCoreGhostSort.isDataAt env
  let boxed := NativeCoreGhostReferenceTypes.isBoxedAt env
  let constructors := NativeCoreGhostConstructorInference.constructorAt [row] 1
  let ghost := NativeCoreGhostSpineInference.runWithFamilyElimination normal [] 0 limit kind boxed
    (NativeCoreGhostSpineInference.visibleFamilyShape env 1) constructors visible
  let children := fun erased =>
    if erased then ghost depth []
    else NativeCoreCodeInference.runWithConstructors normal ghost env kind boxed constructors limit [] depth [] false
  runInMode (ghost depth []) children (normal depth) false limit depth ⟨arena,1⟩ 0 13 9 16 row [15] false

set_option maxRecDepth 4096 in
/-- The actual motive sort controls CODE branch and subject checks. A data
result takes the final native normalization while the proof result keeps
its ghost schedule. Both preserve the original applications. -/
theorem indexed_code_elimination_matches_native :
    (let data := runCodeFixture 199 false
     data.state.steps = 199 ∧ data.state.arena.size = 55 ∧ data.result.map Inferred.typeRoot = .ok 52 ∧
       data.state.arena[51]? = some (.node .app [13,0]) ∧ data.state.arena[52]? = some (.node .app [51,9])) ∧
    runCodeFixture 200 true = runFixture 200 true [15] := by
  exact ⟨by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCoreGhostDataElimination.Examples
