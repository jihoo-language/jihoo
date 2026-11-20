import Jihoo.NativeCoreGhostPropElimination
import Jihoo.NativeCoreGhostSpineInference

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

private def inferred (branches : List Nat) : Outcome Inferred :=
  let env := historyEnvironment.getD empty
  let limit := 63
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw env snapshot.families [] 0 limit
  let visit := NativeCoreGhostSpineInference.runWithConstructors normal [] 0 limit
    (NativeCoreGhostSort.isDataAt env) (NativeCoreGhostReferenceTypes.isBoxedAt env)
    (NativeCoreGhostSpineInference.visibleFamilyShape env 0)
    (NativeCoreGhostConstructorInference.constructorAt snapshot.families 0) depth []
  let constructor : SignatureRoots := ⟨[],[],[0]⟩
  NativeCoreGhostPropElimination.run visit (normal depth) limit depth ⟨snapshot.arena,1⟩ 0 1 4 7 9 [constructor] branches

/-- The live checked signature supplies the original index. The motive,
branch and evidence are all visited before the result is appended. -/
theorem indexed_proposition_checks_motive_branch_and_evidence :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    (let accepted := inferred [5]
     accepted.state.steps = 63 ∧ accepted.state.arena.size = 25 ∧
       accepted.result.map Inferred.typeRoot = .ok 24 ∧ accepted.state.arena[24]? = some (.node .app [4,0])) ∧
    inferred [] = ⟨⟨snapshot.arena,1⟩,.error (.outsideFragment 9)⟩ := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeCoreGhostPropEliminationExamples
