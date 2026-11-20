import Jihoo.NativeCoreCodeScalarInference
import Jihoo.NativeCoreGhostDefinitionChecking

/-! A complete declaration check may select recursively inferred runtime
scalar expressions while keeping the original annotation's ghost mode. -/
namespace Jihoo.NativeKernel.NativeCoreCodeScalarDeclarations

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound)
open NativeCoreGhostDefinitionChecking (BodySound runWithModes)

/-- The annotation chooses the branch before the original body is visited. -/
def bodies (ghost : Infer) (normal : NativeCoreCodeScalarInference.NormalAt) (limit depth : Nat) : Bool → Infer
  | true => ghost
  | false => NativeCoreCodeScalarInference.run normal limit [] depth

theorem bodies_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root)) :
    ∀ mode state root, state.steps ≤ limit → Progress limit state (bodies ghost normal limit depth mode state root) := by
  intro mode state root room
  cases mode
  · exact NativeCoreCodeScalarInference.run_progress normalProgress room
  · exact ghostProgress _ _ room

theorem bodies_sound (wf : UnifiedProgram.EnvWellFormed env) (ghostSound : InferSound env base [] limit ghost)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    BodySound env base limit (bodies ghost normal limit depth) := by
  intro mode state root term answer final onBase room represented success ambient retained
  cases mode
  · obtain ⟨kept,backward,typed⟩ := NativeCoreCodeScalarInference.run_sound wf .nil normalProgress normalSound
      onBase room represented success ambient retained
    exact ⟨kept,backward,typed⟩
  · obtain ⟨kept,backward,typed⟩ := ghostSound onBase room represented success ambient retained
    exact ⟨kept,backward,typed⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨7,6⟩]
  families := []
  arena := #[.node (.integer (-2)) [],.node (.integer 3) [],.node (.arith .add) [0,1],.node (.natural 2) [],
    .node (.natural 3) [],.node .uadd [3,4],.node .strict [2,5],.node .u64 []]

/-- A written U64 annotation selects code for the signed effect and
unsigned result. Formation and all five comparisons share one meter. -/
theorem admitted_recursive_scalar_body_uses_code :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    (let limit := 24
     let normal := NativeCoreGhostLiteralAddition.run snapshot.definitions 0 limit
     let ghost := NativeCoreGhostSpineInference.run snapshot.definitions 0 limit 128 []
     let checked := runWithModes ghost (bodies ghost normal limit 128) (normal 128) limit 128 ⟨snapshot.arena,0⟩ 7 6
     checked.state.steps = 24 ∧ checked.result.map List.length = .ok 5) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeCoreCodeScalarDeclarations
