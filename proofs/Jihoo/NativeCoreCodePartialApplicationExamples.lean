import Jihoo.NativeCoreCodePartialApplication
import Jihoo.NativeCoreCodeApplication

namespace Jihoo.NativeKernel.NativeCoreCodePartialApplication.Examples

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome)

private def fixture : Arena :=
  #[.node (.natural 2) [],.node .u64 [],.node .i64 [],.node .buffer [0],.node (.pi false) [2,2],
    .node (.pi false) [1,4],.node (.pi true) [1,4],.node (.pi false) [3,4],.var 1,.var 0,.node .app [8,9]]

private def runFixture (limit functionType argumentType : Nat) (erased : Bool) : Outcome (List (Nat × Nat)) :=
  let rows := [⟨argumentType,erased⟩,⟨functionType,false⟩]
  let depth := 31
  let normal := NativeCoreGhostLiteralAddition.run [] 0 limit
  let code := NativeCoreCodeHeadInference.run limit depth rows
  let ghost := NativeCoreGhostSpineInference.runWith normal [] 0 limit depth rows
  let arg := fun erased => if erased then ghost else code
  let stopped := NativeCoreCodeApplication.run code arg normal empty limit depth ⟨fixture,1⟩ 10 8 9 false
  run ghost (normal depth) (fun _ => false) stopped.state 10

/-- The native query normalizes an ordinary captured domain twice. An
erased argument skips both visits. A buffer domain is rejected. -/
theorem partial_application_matches_native_meter :
    runFixture 37 5 1 false = ⟨⟨fixture,37⟩,.ok []⟩ ∧
      runFixture 35 6 1 true = ⟨⟨fixture,35⟩,.ok []⟩ ∧
      runFixture 48 7 3 false = ⟨⟨fixture,48⟩,.error (.outsideFragment 10)⟩ := by
  exact ⟨by cbv,by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCoreCodePartialApplication.Examples
