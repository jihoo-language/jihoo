import Jihoo.NativeCoreGhostPropElimination
import Jihoo.NativeCoreGhostSpineInference
import Jihoo.NativeCoreCodeInference

namespace Jihoo.NativeKernel.NativeCoreGhostPropEliminationExamples

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome)
open NativeCorePropCaseType (SignatureRoots)
open NativeCoreGhostSpineInference (Inferred)

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨false,0,1,0,[6]⟩]
  arena := #[.node (.natural 2) [],.node .u64 [],.var 0,.node .eq [2,2],.node (.lam false) [1,3],
    .node .refl [0],.node (.ind 0 1) [0],.node (.con 0 0 0) [],.node (.elim 0 1) [4,5,7],
    .node (.elim 0 0) [4,7],.node .u64 [],.node .u64 []]

private def historyEnvironment : Option Environment := do
  let (definitions,families) ← NativeFamilyWire.decodeProgram snapshot
  LoanTyping.MixedProgram.checkProgram 64 128 definitions (families.map NativeLoanMixedAdmission.declaration)

private def inferred (ghost : Bool) (branches : List Nat) : Outcome Inferred :=
  let env := historyEnvironment.getD empty
  let limit := 63
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw env snapshot.families [] 0 limit
  let constructor : SignatureRoots := ⟨[],[],[0]⟩
  let visible : NativeCoreGhostFamilyElimination.FamilyTable := fun family =>
    (snapshot.families[family]?).map (fun row => ⟨row,false,[constructor]⟩)
  let kind := NativeCoreGhostSort.isDataAt env
  let boxed := NativeCoreGhostReferenceTypes.isBoxedAt env
  let constructors := NativeCoreGhostConstructorInference.constructorAt snapshot.families 0
  let visitGhost := NativeCoreGhostSpineInference.runWithFamilyElimination normal [] 0 limit kind boxed
    (NativeCoreGhostSpineInference.visibleFamilyShape env 0) constructors visible
  let root := if branches.isEmpty then 9 else 8
  if ghost then visitGhost (depth+1) [] ⟨snapshot.arena,0⟩ root
  else NativeCoreCodeInference.runWithConstructors normal visitGhost env kind boxed constructors limit [] (depth+1)
    [] false ⟨snapshot.arena,0⟩ root

/-- The live checked signature supplies the original index. The motive,
branch and evidence are all visited before the result is appended. -/
theorem indexed_proposition_checks_motive_branch_and_evidence :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    (let accepted := inferred true [5]
     accepted.state.steps = 63 ∧ accepted.state.arena.size = 25 ∧
       accepted.result.map Inferred.typeRoot = .ok 24 ∧ accepted.state.arena[24]? = some (.node .app [4,0])) ∧
    inferred true [] = ⟨⟨snapshot.arena,1⟩,.error (.outsideFragment 9)⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

/-- CODE proposition elimination executes the same visits to the original
motive, proof branch, and evidence. -/
theorem code_elimination_keeps_ghost_operands :
    inferred false [5] = inferred true [5] ∧ inferred false [] = inferred true [] := by cbv

end Jihoo.NativeKernel.NativeCoreGhostPropEliminationExamples
