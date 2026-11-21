import Jihoo.NativeCoreDataRecursiveCaseLink
import Jihoo.NativeCoreDataCaseAlignment
import Jihoo.NativeCoreGhostFoldInference

/-! The native data eliminator builds each expected branch
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

private def branchType (limit depth : Nat) (state : State)
    (family constructor params motive source : Nat) (parameters : List Nat) (recursive proof : Bool) : Outcome Nat :=
  if recursive then
    NativeCoreDataRecursionCase.run limit depth state family constructor params motive source parameters proof
  else
    NativeCoreDataCaseTelescope.run limit depth state family constructor params motive source parameters

private theorem branchType_progress :
    Progress limit state (branchType limit depth state family constructor params motive source parameters recursive proof) := by
  unfold branchType
  split
  · exact NativeCoreDataRecursionCase.run_progress
  · exact NativeCoreDataCaseTelescope.run_progress

private theorem branchType_refines
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (familyRep : RepresentsFamilies state.arena familyRows familyTerms)
    (selectedFamily : familyRows[family]? = some row)
    (selectedConstructor : row.constructors[constructor]? = some written) (data : row.data = true)
    (independentParameters : recursive = true →
      ∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64)
    (paramRep : RepresentsList state.arena argumentRefs values) (motiveRep : Represents state.arena motiveRef motive)
    (success : (branchType limit depth state family constructor row.params motiveRef written argumentRefs recursive proof).result =
      .ok selected) :
    let after := (branchType limit depth state family constructor row.params motiveRef written argumentRefs recursive proof).state.arena
    ∃ entry signature expected observed,
      env.families[family]? = some entry ∧ entry.declaration.data = true ∧ entry.declaration.params = row.params ∧
      entry.signatures[constructor]? = some signature ∧
      dataCaseType family constructor row.params ctx.length signature (expandArgs env values) (expand env motive) recursive proof = some expected ∧
      Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected observed ∧ RawLend.Conv env (expand env observed) expected := by
  cases recursive with
  | false =>
    exact NativeCoreDataCaseAlignment.run_matches_checked_case history familyRep selectedFamily selectedConstructor
      data paramRep motiveRep success
  | true =>
    exact NativeCoreDataRecursiveFieldAlignment.run_matches_checked_case history familyRep selectedFamily selectedConstructor
      data paramRep (independentParameters rfl) motiveRep success

def runWithMode (infer : Infer) (normal : Visit) (limit depth family motive root : Nat) (row : FamilyRoots)
    (parameters : List Nat) (recursive proof : Bool) : List Nat → Nat → State → Outcome (List (Nat × Nat))
  | [],_,state => ⟨state,.ok []⟩
  | branch :: branches,constructor,state =>
    match row.constructors[constructor]? with
    | none => ⟨state,.error (.outsideFragment root)⟩
    | some source =>
      (branchType limit depth state family constructor row.params motive source parameters recursive proof).next
        fun expected type =>
          (checkAgainst infer normal limit depth expected type branch).next fun checked comparisons =>
            (runWithMode infer normal limit depth family motive root row parameters recursive proof branches (constructor+1) checked).next
              fun after tail => ⟨after,.ok (comparisons ++ tail)⟩

theorem runWithMode_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runWithMode infer normal limit depth family motive root row parameters recursive proof branches constructor state) := by
  induction branches generalizing constructor state with
  | nil => exact Progress.atState _ _
  | cons branch branches ih =>
    unfold runWithMode
    split
    · exact Progress.atState _ _
    · apply next_progress branchType_progress room
      intro _ _ builtRoom
      apply next_progress (checkAgainst_progress childProgress normalProgress builtRoom) builtRoom
      intro _ _ checkedRoom
      exact (ih checkedRoom).next (fun _ => Progress.atState _ _)

def run (infer : Infer) (normal : Visit) (limit depth family motive root : Nat) (row : FamilyRoots)
    (parameters : List Nat) : List Nat → Nat → State → Outcome (List (Nat × Nat)) :=
  runWithMode infer normal limit depth family motive root row parameters false false

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth family motive root row parameters branches constructor state) :=
  runWithMode_progress childProgress normalProgress room

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

theorem runWithMode_refines
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
    (independentParameters : recursive = true →
      ∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64)
    (branchesRep : RepresentsList state.arena branches cases)
    (remaining : entry.signatures.drop constructor = signatures)
    (width : branches.length = signatures.length)
    (success : (runWithMode infer normal limit depth family motive root row parameters recursive proof branches constructor state).result = .ok compared)
    (ambient : Prefix (runWithMode infer normal limit depth family motive root row parameters recursive proof branches constructor state).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (runWithMode infer normal limit depth family motive root row parameters recursive proof branches constructor state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ types, (signatures.zipIdx constructor).mapM (fun (signature,index) =>
        dataCaseType family index entry.declaration.params ctx.length signature (expandArgs env values)
          (expand env M) recursive proof) = some types ∧
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
      unfold runWithMode at success ambient ⊢
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
        let expected := branchType limit depth state family constructor row.params motive source parameters recursive proof
        have typeCost := branchType_progress (limit := limit) (depth := depth) (state := state)
          (family := family) (constructor := constructor) (params := row.params) (motive := motive) (source := source)
          (parameters := parameters) (recursive := recursive) (proof := proof)
        have typeRoom := typeCost.accepted room type typeOk
        have branchCost := checkAgainst_progress (state := expected.state) (depth := depth) (expected := type)
          (argument := branch) childProgress normalProgress typeRoom
        have nextRoom := branchCost.accepted typeRoom first firstOk
        have tailCost := runWithMode_progress (depth := depth) (family := family) (motive := motive) (root := root)
          (row := row) (parameters := parameters) (branches := branches) (constructor := constructor+1)
          (recursive := recursive) (proof := proof)
          childProgress normalProgress nextRoom
        obtain ⟨actualEntry,actualSignature,wanted,observed,foundEntry,_,_,foundSignature,built,typeKept,typeBack,typeRep,related⟩ :=
          branchType_refines (proof := proof) history rows rowFound sourceFound data independentParameters parametersRep motiveRep typeOk
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
            (expandArgs env values) (expand env M) recursive proof = some wanted := by rw [params]; exact built
        refine ⟨throughBranch.trans tailKept,tailBack ∘ branchBack ∘ typeBack,wanted :: tailTypes,?_,?_⟩
        · simp [List.zipIdx_cons,generatedFirst,generated]
        · simp only [expandArgs]
          exact .cons (typed.convert related) typedTail

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
  have unchanged (signature : Signature) (index : Nat) :
      dataCaseType family index entry.declaration.params ctx.length signature (expandArgs env values)
        (expand env M) false proof =
      dataCaseType family index entry.declaration.params ctx.length signature (expandArgs env values)
        (expand env M) false false := by
    unfold dataCaseType
    split <;> rfl
  simp only [unchanged]
  exact runWithMode_refines (recursive := false) (proof := false) history normalSound normalProgress childSound
    childProgress onBase room rows rowFound data entryFound params motiveRep parametersRep
    (by intro impossible; cases impossible) branchesRep remaining width success ambient retained

end Jihoo.NativeKernel.NativeCoreGhostDataCases
