import Jihoo.NativeCorePropCaseType
import Jihoo.NativeCorePropSignatureConversion
import Jihoo.NativeCoreGhostFoldInference

/-! Proposition Elim checks each written branch against its own generated
constructor telescope. The observed graph signature may use convertible
normal forms of the independently checked domains and indices. -/
namespace Jihoo.NativeKernel.NativeCoreGhostPropCases

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained next_progress)
open NativeCoreGhostFoldInference (checkAgainst checkAgainst_progress checkAgainst_refines)
open NativeCorePropCaseType (SignatureRoots SignatureRep)
open FamilyEnvironment (RelList)
open EnvironmentDelta (expand expandArgs)

/-- Native roots denote the observed signature, which may use a different
normal form from the same checked constructor in the earlier history. -/
structure CheckedSignature (env : Environment) (arena : Arena) (roots : SignatureRoots) (checked : Signature) : Prop where
  represented : ∃ observed, SignatureRep arena roots observed ∧ SignatureConversion env (expandSignature env observed) checked

def run (infer : Infer) (normal : Visit) (limit depth motive rejected : Nat) :
    List SignatureRoots → List Nat → State → Outcome (List (Nat × Nat))
  | [], [], state => ⟨state,.ok []⟩
  | shape :: remaining, branch :: rest, state =>
    (NativeCorePropCaseType.run limit depth state motive shape).next fun generated expected =>
      (checkAgainst infer normal limit depth generated expected branch).next fun checked compared =>
        (run infer normal limit depth motive rejected remaining rest checked).next fun after suffix =>
          ⟨after,.ok (compared ++ suffix)⟩
  | _, _, state => ⟨state,.error (.outsideFragment rejected)⟩

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth motive rejected roots branches state) := by
  induction roots generalizing branches state with
  | nil => cases branches <;> exact Progress.atState _ _
  | cons shape rest ih =>
    cases branches with
    | nil => exact Progress.atState _ _
    | cons branch branches =>
      unfold run
      apply next_progress NativeCorePropCaseType.run_progress room
      intro expected _ expectedRoom
      apply next_progress (checkAgainst_progress childProgress normalProgress expectedRoom) expectedRoom
      intro _ _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

theorem table_frame (table : RelList (CheckedSignature env arena) roots signatures) (kept : Prefix arena after) :
    RelList (CheckedSignature env after) roots signatures := by
  induction table with
  | nil => exact .nil
  | cons first _ ih =>
    obtain ⟨observed,represented,converted⟩ := first.represented
    exact .cons ⟨⟨observed,represented.frame kept,converted⟩⟩ ih

/-- Each accepted branch is typed at the case telescope of its authentic
checked signature. No proposed body typing or output index is needed. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (motiveRep : Represents state.arena motive M)
    (caseReps : RepresentsList state.arena branches cases)
    (table : RelList (CheckedSignature env state.arena) roots signatures)
    (success : (run infer normal limit depth motive rejected roots branches state).result = .ok compared)
    (ambient : Prefix (run infer normal limit depth motive rejected roots branches state).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (run infer normal limit depth motive rejected roots branches state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Cases env [] ctx (expand env M) signatures (expandArgs env cases) := by
  induction roots generalizing state branches cases signatures compared with
  | nil =>
    cases table
    cases caseReps with
    | nil => exact ⟨.refl _,id,by simp only [expandArgs]; exact .nil⟩
    | cons _ _ => cases success
  | cons shape shapes ih =>
    cases table with
    | cons header others =>
      cases caseReps with
      | nil => cases success
      | @cons branch _ remaining _ branchRep rest =>
        unfold run at success ambient ⊢
        obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
        rw [expectedNext] at success ambient ⊢
        obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
        rw [firstNext] at success ambient ⊢
        obtain ⟨othersPairs,othersOk,othersNext⟩ := Outcome.next_success success
        rw [othersNext] at success ambient ⊢
        simp only [Except.ok.injEq] at success
        subst compared
        let formed := NativeCorePropCaseType.run limit depth state motive shape
        have expectedCost := NativeCorePropCaseType.run_progress (limit := limit) (depth := depth) (state := state)
          (motive := motive) (roots := shape)
        have expectedRoom := expectedCost.accepted room expected expectedOk
        have branchCost := checkAgainst_progress (state := formed.state) (depth := depth) (expected := expected) (argument := branch)
          childProgress normalProgress expectedRoom
        have restRoom := branchCost.accepted expectedRoom first firstOk
        have restCost := run_progress (roots := shapes) (branches := remaining) (motive := motive) (rejected := rejected)
          (depth := depth) childProgress normalProgress restRoom
        obtain ⟨observed,headerRep,convertedHeader⟩ := header.represented
        obtain ⟨typeKept,typeBack,expectedRep⟩ := NativeCorePropCaseType.run_refines motiveRep headerRep expectedOk
        obtain ⟨branchKept,branchBack,typed⟩ := checkAgainst_refines normalSound normalProgress childSound childProgress
          (onBase.trans typeKept) expectedRoom (branchRep.frame typeKept) expectedRep firstOk (restCost.kept.trans ambient)
          (fun pair member => retained pair (List.mem_append_left _ member))
        have throughHead := typeKept.trans branchKept
        obtain ⟨restKept,restBack,typedRest⟩ := ih (onBase.trans throughHead) restRoom (motiveRep.frame throughHead)
          (rest.frame throughHead) (table_frame others throughHead) othersOk ambient
          (fun pair member => retained pair (List.mem_append_right _ member))
        rw [expand_prop_case_type wf.admissible] at typed
        exact ⟨throughHead.trans restKept,restBack ∘ branchBack ∘ typeBack,
          by simpa only [expandArgs] using LoanTyping.Cases.cons (typed.convert (convertedHeader.prop_case wf.closed (.refl _))) typedRest⟩

end Jihoo.NativeKernel.NativeCoreGhostPropCases
