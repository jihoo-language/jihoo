import Jihoo.NativeCoreDataCaseAlignment
import Jihoo.NativeCoreGhostFoldInference

/-! The native nonrecursive data eliminator builds each expected branch
from its own written constructor and checks branches in declaration
order. The checked family prefix authenticates every result. -/
namespace Jihoo.NativeKernel.NativeCoreGhostDataCases

open NativeArena NativeFamilyWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained next_progress)
open NativeCoreGhostFoldInference (checkAgainst checkAgainst_progress checkAgainst_refines)
open EnvironmentDelta (expand expandArgs)

def run (infer : Infer) (normal : Visit) (limit depth family motive root : Nat) (row : FamilyRoots)
    (parameters : List Nat) : List Nat → Nat → State → Outcome (List (Nat × Nat))
  | [],_,state => ⟨state,.ok []⟩
  | branch :: branches,constructor,state =>
    match row.constructors[constructor]? with
    | none => ⟨state,.error (.outsideFragment root)⟩
    | some source =>
      (NativeCoreDataCaseTelescope.run limit depth state family constructor row.params motive source parameters).next
        fun expected type =>
          (checkAgainst infer normal limit depth expected type branch).next fun checked comparisons =>
            (run infer normal limit depth family motive root row parameters branches (constructor+1) checked).next
              fun after tail => ⟨after,.ok (comparisons ++ tail)⟩

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth family motive root row parameters branches constructor state) := by
  induction branches generalizing constructor state with
  | nil => exact Progress.atState _ _
  | cons branch branches ih =>
    unfold run
    split
    · exact Progress.atState _ _
    · apply next_progress NativeCoreDataCaseTelescope.run_progress room
      intro _ _ builtRoom
      apply next_progress (checkAgainst_progress childProgress normalProgress builtRoom) builtRoom
      intro _ _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

theorem families_frame (rows : RepresentsFamilies arena roots terms) (kept : Prefix arena after) :
    RepresentsFamilies after roots terms := by
  induction rows with
  | nil => exact .nil
  | cons first _ ih =>
    exact .cons ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,first.2.2.2.2.frame kept⟩ ih

private theorem remaining_constructor {entry : CheckedFamily}
    (rest : entry.signatures.drop constructor = signature :: signatures) :
    entry.signatures[constructor]? = some signature ∧
      entry.signatures.drop (constructor+1) = signatures := by
  constructor
  · have read := congrArg (fun (items : List Signature) => items[0]?) rest
    simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] using read
  · have dropped := congrArg (List.drop 1) rest
    simpa only [List.drop_drop,List.drop_succ_cons,List.drop_zero,Nat.add_comm 1] using dropped

theorem run_refines
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (rowFound : familyRows[family]? = some row) (data : row.data = true)
    (entryFound : env.families[family]? = some entry) (params : entry.declaration.params = row.params)
    (motiveRep : Represents state.arena motive M) (parametersRep : RepresentsList state.arena parameters values)
    (branchesRep : RepresentsList state.arena branches cases)
    (remaining : entry.signatures.drop constructor = signatures)
    (width : branches.length = signatures.length)
    (success : (run infer normal limit depth family motive root row parameters branches constructor state).result = .ok compared)
    (ambient : Prefix (run infer normal limit depth family motive root row parameters branches constructor state).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (run infer normal limit depth family motive root row parameters branches constructor state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ types, (signatures.zipIdx constructor).mapM (fun (signature,index) =>
        dataCaseType family index entry.declaration.params ctx.length signature (expandArgs env values)
          (expand env M) false proof) = some types ∧
        LoanTyping.BranchTypes env [] ctx true types (expandArgs env cases) := by
  induction signatures generalizing branches cases state constructor compared with
  | nil =>
    have noCases := List.length_eq_zero_iff.mp width
    subst branches
    cases branchesRep
    exact ⟨.refl _,id,[],rfl,by simp only [expandArgs]; exact .nil⟩
  | cons signature signatures ih =>
    cases branchesRep with
    | nil => simp at width
    | @cons branch _ branches _ branchRep tail =>
      unfold run at success ambient ⊢
      split at success
      · cases success
      · rename_i source sourceFound
        simp only [sourceFound] at ambient ⊢
        obtain ⟨type,typeOk,nextType⟩ := Outcome.next_success success
        rw [nextType] at success ambient ⊢
        obtain ⟨first,firstOk,nextBranch⟩ := Outcome.next_success success
        rw [nextBranch] at success ambient ⊢
        obtain ⟨others,othersOk,nextRest⟩ := Outcome.next_success success
        rw [nextRest] at success ambient ⊢
        simp only [Except.ok.injEq] at success
        subst compared
        obtain ⟨atIndex,remainingNext⟩ := remaining_constructor remaining
        let expected := NativeCoreDataCaseTelescope.run limit depth state family constructor row.params motive source parameters
        have typeCost := NativeCoreDataCaseTelescope.run_progress (limit := limit) (depth := depth) (state := state)
          (family := family) (constructor := constructor) (params := row.params) (motive := motive) (written := source)
          (arguments := parameters)
        have typeRoom := typeCost.accepted room type typeOk
        have branchCost := checkAgainst_progress (state := expected.state) (depth := depth) (expected := type)
          (argument := branch) childProgress normalProgress typeRoom
        have nextRoom := branchCost.accepted typeRoom first firstOk
        have tailCost := run_progress (depth := depth) (family := family) (motive := motive) (root := root)
          (row := row) (parameters := parameters) (branches := branches) (constructor := constructor+1)
          childProgress normalProgress nextRoom
        obtain ⟨actualEntry,actualSignature,wanted,observed,foundEntry,_,_,foundSignature,built,typeKept,typeBack,typeRep,related⟩ :=
          NativeCoreDataCaseAlignment.run_matches_checked_case (contextDepth := ctx.length) (proof := proof)
            history rows rowFound sourceFound data parametersRep motiveRep typeOk
        have sameEntry := Option.some.inj (foundEntry.symm.trans entryFound)
        subst actualEntry
        have sameSignature := Option.some.inj (foundSignature.symm.trans atIndex)
        subst actualSignature
        obtain ⟨branchKept,branchBack,typed⟩ := checkAgainst_refines normalSound normalProgress childSound childProgress
          (onBase.trans typeKept) typeRoom (branchRep.frame typeKept) typeRep firstOk (tailCost.kept.trans ambient)
          (fun pair member => retained pair (List.mem_append_left _ member))
        have throughBranch := typeKept.trans branchKept
        have tailWidth : branches.length = signatures.length := Nat.succ.inj width
        obtain ⟨tailKept,tailBack,tailTypes,generated,typedTail⟩ := ih
          (onBase.trans throughBranch) nextRoom (families_frame rows throughBranch) (motiveRep.frame throughBranch)
          (parametersRep.frame throughBranch) (tail.frame throughBranch) remainingNext tailWidth othersOk ambient
          (fun pair member => retained pair (List.mem_append_right _ member))
        have generatedFirst : dataCaseType family constructor entry.declaration.params ctx.length signature
            (expandArgs env values) (expand env M) false proof = some wanted := by rw [params]; exact built
        refine ⟨throughBranch.trans tailKept,tailBack ∘ branchBack ∘ typeBack,wanted :: tailTypes,?_,?_⟩
        · simp [List.zipIdx_cons,generatedFirst,generated]
        · simp only [expandArgs]
          exact .cons (typed.convert related) typedTail

end Jihoo.NativeKernel.NativeCoreGhostDataCases
