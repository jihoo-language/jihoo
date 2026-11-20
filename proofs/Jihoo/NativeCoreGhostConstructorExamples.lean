import Jihoo.NativeCoreGhostConstructorInference
import Jihoo.NativeCoreGhostSpineInference

namespace Jihoo.NativeKernel.NativeCoreGhostConstructorInference

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome)
open NativeCoreGhostSpineInference (Inferred)

open NativeProgramWire

private def constructorSnapshot : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨false,0,1,0,[7]⟩]
  arena := #[.node (.natural 3) [],.node .u64 [],.var 0,.var 1,.node .eq [2,2],
    .node (.ind 0 1) [3],.node (.pi true) [4,5],.node (.pi false) [1,6],.node .refl [0],
    .node (.con 0 0 1) [0],.node (.con 0 0 2) [0,8],.node (.universe 0) [],.node .u64 [],
    .node .prop [],.node .u64 []]

private def constructorEnvironment : Option Environment := do
  let (defs,families) ← NativeFamilyWire.decodeProgram constructorSnapshot
  LoanTyping.MixedProgram.checkProgram 64 128 defs (families.map NativeLoanMixedAdmission.declaration)

private def constructorVisit (limit root : Nat) (fields : List Nat) : Outcome Inferred :=
  let env := constructorEnvironment.getD empty
  let normal := NativeCoreExpandedFamilies.raw env constructorSnapshot.families [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWithFamilyShapes normal [] 0 limit
    (NativeCoreGhostSort.isDataAt env) (NativeCoreGhostReferenceTypes.isBoxedAt env)
    (NativeCoreGhostSpineInference.visibleFamilyShape env 0) 31 []
  run infer (normal 31) limit 31 root 0 ⟨constructorSnapshot.arena,1⟩ 7 fields

/-- The initial graph is the checked native family arena. Its dependent
evidence field sees the first argument and the final result contains the
same index root. The outer inference visit has already spent one tick. -/
theorem admitted_dependent_constructor_meters_fields :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot constructorSnapshot) = true ∧
    (let complete := constructorVisit 54 10 [0,8]
     complete.state.steps = 54 ∧ complete.state.arena.size = 22 ∧
       complete.state.arena[16]? = some (.node .eq [0,0]) ∧
       complete.state.arena[17]? = some (.node (.ind 0 1) [0]) ∧
       complete.result.map Inferred.typeRoot = .ok 17) ∧
    (constructorVisit 54 9 [0]).result = .error (.outsideFragment 9) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

/-- Recursive inference selects the same authenticated constructor root and
reproduces its entire native checking schedule, including the entry tick. -/
theorem recursive_dispatch_checks_dependent_constructor :
    let env := constructorEnvironment.getD empty
    let normal := NativeCoreExpandedFamilies.raw env constructorSnapshot.families [] 0 54
    let checked := NativeCoreGhostSpineInference.runWithConstructors normal [] 0 54
      (NativeCoreGhostSort.isDataAt env) (NativeCoreGhostReferenceTypes.isBoxedAt env)
      (NativeCoreGhostSpineInference.visibleFamilyShape env 0) (constructorAt constructorSnapshot.families 0)
      32 [] ⟨constructorSnapshot.arena,0⟩ 10
    constructorEnvironment = some env ∧ checked.state.steps = 54 ∧
      checked.state.arena.size = 22 ∧ checked.result.map Inferred.typeRoot = .ok 17 ∧
      checked.state.arena[17]? = some (.node (.ind 0 1) [0]) := by
  cbv

end Jihoo.NativeKernel.NativeCoreGhostConstructorInference
