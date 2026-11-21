import Jihoo.NativeCoreViewSubject
import Jihoo.NativeCoreViewMotiveGate
import Jihoo.NativeCoreViewCaseType
import Jihoo.NativeCoreGhostFoldInference
import Jihoo.NativeCoreGhostFamilyElimination

/-! Ghost View first inspects the original borrow, then checks its motive
and each branch in constructor order. The dependent result applies the
original motive to the original scrutinee. -/
namespace Jihoo.NativeKernel.NativeCoreGhostViewInference

open NativeArena NativeFamilyWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines PairRetained RetainedComparisons next_progress)
open NativeCoreGhostFoldInference (checkAgainst checkAgainst_progress checkAgainst_refines)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

def checkCases (infer : Infer) (normal : Visit) (env : Environment) (limit depth family motive rejected : Nat)
    (row : FamilyRoots) (parameters : List Nat) (recursive : Bool) :
    Nat → State → List Nat → Outcome (List (Nat × Nat))
  | _,state,[] => ⟨state,.ok []⟩
  | constructor,state,branch :: rest =>
    match row.constructors[constructor]? with
    | none => reject state rejected
    | some written =>
      (NativeCoreViewCaseType.run normal env limit depth state family constructor row.params motive written parameters
        recursive).next fun generated expected =>
        (checkAgainst infer normal limit depth generated expected branch).next fun checked compared =>
          (checkCases infer normal env limit depth family motive rejected row parameters recursive
            (constructor+1) checked rest).next fun after suffix =>
              ⟨after,.ok (compared ++ suffix)⟩

theorem checkCases_progress
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (checkCases infer normal env limit depth family motive rejected row parameters recursive constructor state branches) := by
  induction branches generalizing constructor state with
  | nil => exact Progress.atState _ _
  | cons branch rest ih =>
    unfold checkCases
    split
    · exact Progress.atState _ _
    · apply next_progress (NativeCoreViewCaseType.run_progress normalProgress) room
      intro expected _ generatedRoom
      apply next_progress (checkAgainst_progress inferProgress normalProgress generatedRoom) generatedRoom
      intro _ _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

private def finish (state : State) (motive subject : Nat) (dependent : Bool) : Outcome Nat :=
  if dependent then append state .app [motive,subject] else ⟨state,.ok motive⟩

private theorem finish_progress : Progress limit state (finish state motive subject dependent) := by
  unfold finish
  split
  · exact append_progress _ _ _
  · exact Progress.atState _ _

def run (infer : Infer) (normal : Visit) (env : Environment) (limit depth : Nat)
    (state : State) (family motive subject root : Nat) (row : FamilyRoots)
    (boxed recursive : Bool) (branches : List Nat) : Outcome Inferred :=
  if boxed && row.arity == row.params then
    if branches.length = row.constructors.length then
      (NativeCoreViewSubject.run infer normal state family subject).next fun exposed source =>
        (infer exposed motive).next fun inferred sort =>
          (NativeCoreViewMotiveGate.run normal limit depth inferred motive sort.typeRoot source.referenceType).next
            fun formed chosen =>
              (checkCases infer normal env limit depth family motive root row source.parameters recursive 0 formed
                branches).next fun checked compared =>
                (finish checked motive subject chosen.dependent).next fun after output =>
                  ⟨after,.ok ⟨output,source.inferred.compared ++ (sort.compared ++ (chosen.compared ++ compared))⟩⟩
    else reject state root
  else reject state root

theorem run_progress
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal env limit depth state family motive subject root row boxed recursive branches) := by
  unfold run
  split
  · split
    · apply next_progress (NativeCoreViewSubject.run_progress inferProgress normalProgress room) room
      intro source _ exposedRoom
      apply next_progress (inferProgress _ _ exposedRoom) exposedRoom
      intro sort _ motiveRoom
      apply next_progress (NativeCoreViewMotiveGate.run_progress normalProgress motiveRoom) motiveRoom
      intro chosen _ formedRoom
      apply next_progress (checkCases_progress inferProgress normalProgress formedRoom) formedRoom
      intro _ _ _
      exact finish_progress.next (fun _ => Progress.atState _ _)
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem finish_refines (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (success : (finish state motive subject dependent).result = .ok output) :
    let after := (finish state motive subject dependent).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after output (viewResult dependent M X) := by
  cases dependent
  · cases success
    exact ⟨.refl _,id,motiveRep⟩
  · exact append_refines (.cons motiveRep (.cons subjectRep .nil)) rfl success

open NativeCoreGhostFamilyElimination (FamilyTable)

def runNode (environment : Option Environment) (visibleTable : FamilyTable)
    (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (recursive : Bool) (root family : Nat) (arguments : List Nat) : Outcome Inferred :=
  match environment, visibleTable family, arguments with
  | some env, some entry, motive :: tail =>
    match tail.getLast? with
    | some subject => run infer normal env limit depth state family motive subject root entry.source entry.boxed recursive tail.dropLast
    | none => reject state root
  | _,_,_ => reject state root

theorem runNode_progress
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runNode environment visibleTable infer normal limit depth state recursive root family arguments) := by
  unfold runNode
  split
  · split
    · exact run_progress inferProgress normalProgress room
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem runNode_disabled : runNode none visibleTable infer normal limit depth state recursive root family arguments =
    ⟨state,.error (.outsideFragment root)⟩ := rfl

end Jihoo.NativeKernel.NativeCoreGhostViewInference
