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

/-- The constructor check relates a successful live build to its original
stored signature, after parameter opening and conversion of the field types. -/
def CaseReplay (env : Environment) (base : Arena) (ctx : Context) (normal : Visit) (limit depth family motive : Nat)
    (row : FamilyRoots) (entry : CheckedFamily) (parameters : List Nat) (values : List Term)
    (M : Term) (recursive dependent : Bool) : Prop :=
  ∀ {state constructor written selected}, Prefix base state.arena → row.constructors[constructor]? = some written →
    (NativeCoreViewCaseType.run normal env limit depth state family constructor row.params motive written parameters recursive).result =
      .ok selected →
    let after := (NativeCoreViewCaseType.run normal env limit depth state family constructor row.params motive written parameters recursive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ signature expected observed, entry.signatures[constructor]? = some signature ∧
        viewCaseType env family constructor entry.declaration.params ctx.length signature (expandArgs env values)
          (expand env M) recursive dependent = some expected ∧
        Represents after selected observed ∧ RawLend.Conv env (expand env observed) expected

/-- The case loop checks the branches in declaration order, and keeps
one shared comparison tape for the actual types inspected by the checker. -/
theorem checkCases_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (caseReplay : CaseReplay env base ctx normal limit depth family motive row entry parameters values M recursive dependent)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (branchReps : RepresentsList state.arena branches cases)
    (remaining : entry.signatures.drop constructor = signatures) (width : branches.length = signatures.length)
    (success : (checkCases infer normal env limit depth family motive rejected row parameters recursive constructor state branches).result =
      .ok compared)
    (ambient : Prefix (checkCases infer normal env limit depth family motive rejected row parameters recursive
      constructor state branches).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (checkCases infer normal env limit depth family motive rejected row parameters recursive constructor state branches).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ types, (signatures.zipIdx constructor).mapM (fun (signature,index) =>
        viewCaseType env family index entry.declaration.params ctx.length signature (expandArgs env values)
          (expand env M) recursive dependent) = some types ∧
        LoanTyping.BranchTypes env [] ctx true types (expandArgs env cases) := by
  induction signatures generalizing branches cases state constructor compared with
  | nil =>
    have none := List.length_eq_zero_iff.mp width
    subst branches
    cases branchReps
    exact ⟨.refl _,id,[],rfl,by simp only [expandArgs]; exact .nil⟩
  | cons signature signatures ih =>
    cases branchReps with
    | nil => simp at width
    | @cons branch _ branches _ branchRep tail =>
      unfold checkCases at success ambient ⊢
      split at success
      · cases success
      · rename_i written found
        simp only [found] at ambient ⊢
        obtain ⟨selected,built,builtNext⟩ := Outcome.next_success success
        rw [builtNext] at success ambient ⊢
        obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
        rw [firstNext] at success ambient ⊢
        obtain ⟨rest,restOk,restNext⟩ := Outcome.next_success success
        rw [restNext] at success ambient ⊢
        simp only [Except.ok.injEq] at success
        subst compared
        let generated := NativeCoreViewCaseType.run normal env limit depth state family constructor row.params motive written parameters recursive
        have buildCost : Progress limit state generated := NativeCoreViewCaseType.run_progress normalProgress
        have buildRoom := buildCost.accepted room selected built
        have branchCost := checkAgainst_progress (state := generated.state) (depth := depth) (expected := selected)
          (argument := branch) inferProgress normalProgress buildRoom
        have restRoom := branchCost.accepted buildRoom first firstOk
        have restCost  := checkCases_progress (env := env) (depth := depth) (family := family) (motive := motive)
          (rejected := rejected) (row := row) (parameters := parameters) (branches := branches)
          (constructor := constructor+1) (recursive := recursive) inferProgress normalProgress restRoom
        obtain ⟨buildKept,buildBack,actual,expected,observed,selectedSignature,writtenType,typeRep,converted⟩ :=
          caseReplay onBase found built
        have aligned : entry.signatures[constructor]? = some signature := by
          have lookup := congrArg (fun items : List Signature => items[0]?) remaining
          change (entry.signatures.drop constructor)[0]? = some signature at lookup
          rw [List.getElem?_drop,Nat.add_zero] at lookup
          exact lookup
        have same := Option.some.inj (selectedSignature.symm.trans aligned)
        subst actual
        have remainingNext : entry.signatures.drop (constructor+1) = signatures := by
          simpa only [List.drop_drop,List.drop_succ_cons,List.drop_zero,Nat.add_comm 1] using congrArg (List.drop 1) remaining
        obtain ⟨firstKept,firstBack,typed⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
          (onBase.trans buildKept) buildRoom (branchRep.frame buildKept) typeRep firstOk (restCost.kept.trans ambient)
          (fun pair member => retained pair (List.mem_append_left _ member))
        have through := buildKept.trans firstKept
        obtain ⟨restKept,restBack,types,tailTypes,typedTail⟩ := ih (onBase.trans through) restRoom
          (tail.frame through) remainingNext (Nat.succ.inj width) restOk ambient
          (fun pair member => retained pair (List.mem_append_right _ member))
        refine ⟨through.trans restKept,restBack ∘ firstBack ∘ buildBack,expected :: types,?_,?_⟩
        · simp [List.zipIdx_cons,writtenType,tailTypes]
        · simp only [expandArgs]
          exact .cons (typed.convert converted) typedTail


open NativeCoreGhostSpineInference (Refines RetainedComparisons)

/-- With constructor types linked to the checked family signature, the
actual View visit derives its original source typing. The subject proof
ensures that the selected reference really has the family's declared arity. -/
theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (entryFound : env.families[family]? = some entry) (data : entry.declaration.data = true)
    (shape : row.arity = entry.declaration.arity) (parameterCount : row.params = entry.declaration.params)
    (availability : boxed = entry.boxed) (constructors : row.constructors.length = entry.signatures.length)
    (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (branchReps : RepresentsList state.arena branches cases)
    (subjectFormation : ∀ {input original}, (infer state subject).result = .ok input →
      Represents (infer state subject).state.arena input.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term)
    (caseReplay : ∀ {start parameters values dependent},
      Prefix base start → Represents start motive M → RepresentsList start parameters values →
      values.length = entry.declaration.params →
      (∀ value ∈ values, LoanTyping.HasType env [] ctx true (expand env value) .u64) →
      LoanTyping.HasType env [] ctx true (expand env X)
        (.ref (.node (.ind family entry.declaration.arity) (expandArgs env values))) →
      LoanTyping.HasType env [] ctx true (expand env M)
        (viewMotiveType dependent (.node (.ind family entry.declaration.arity) (expandArgs env values))) →
      CaseReplay env start ctx normal limit depth family motive row entry parameters values M recursive dependent)
    (success : (run infer normal env limit depth state family motive subject root row boxed recursive branches).result = .ok answer)
    (ambient : Prefix (run infer normal env limit depth state family motive subject root row boxed recursive branches).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.view recursive family cases.length) (M :: (cases ++ [X])))
      (run infer normal env limit depth state family motive subject root row boxed recursive branches) answer := by
  unfold run at success ambient ⊢
  split at success
  · rename_i allowed
    simp only [ite_eq_left allowed] at ambient ⊢
    have flags := Bool.and_eq_true_iff.mp allowed
    have boxedActual : entry.boxed = true := availability.symm.trans flags.1
    have unindexed : entry.declaration.arity = entry.declaration.params :=
      shape.symm.trans ((beq_iff_eq.mp flags.2).trans parameterCount)
    split at success
    · rename_i branchCount
      simp only [ite_eq_left branchCount] at ambient ⊢
      obtain ⟨exposed,exposedOk,exposedNext⟩ := Outcome.next_success success
      rw [exposedNext] at success ambient ⊢
      obtain ⟨sort,sortOk,sortNext⟩ := Outcome.next_success success
      rw [sortNext] at success ambient ⊢
      obtain ⟨choice,choiceOk,choiceNext⟩ := Outcome.next_success success
      rw [choiceNext] at success ambient ⊢
      obtain ⟨compared,comparedOk,comparedNext⟩ := Outcome.next_success success
      rw [comparedNext] at success ambient ⊢
      obtain ⟨selected,selectedOk,selectedNext⟩ := Outcome.next_success success
      rw [selectedNext] at success ambient ⊢
      cases success
      have subjectCost := NativeCoreViewSubject.run_progress (state := state) (family := family) (subject := subject)
        inferProgress normalProgress room
      have motiveRoom := subjectCost.accepted room exposed exposedOk
      let scrub := NativeCoreViewSubject.run infer normal state family subject
      have motiveCost := inferProgress scrub.state motive motiveRoom
      have gateRoom := motiveCost.accepted motiveRoom sort sortOk
      let inferred := infer scrub.state motive
      have gateCost := NativeCoreViewMotiveGate.run_progress (state := inferred.state) (limit := limit) (depth := depth)
        (motive := motive) (inferred := sort.typeRoot) (referenceType := exposed.referenceType) normalProgress gateRoom
      have casesRoom := gateCost.accepted gateRoom choice choiceOk
      let gate := NativeCoreViewMotiveGate.run normal limit depth inferred.state motive sort.typeRoot exposed.referenceType
      have caseCost := checkCases_progress (env := env) (state := gate.state) (depth := depth) (family := family) (motive := motive)
        (rejected := root) (row := row) (parameters := exposed.parameters) (branches := branches)
        (constructor := 0) (recursive := recursive) inferProgress normalProgress casesRoom
      let checked := checkCases infer normal env limit depth family motive root row exposed.parameters recursive 0 gate.state branches
      have outputCost := finish_progress (state := checked.state) (motive := motive) (subject := subject)
        (dependent := choice.dependent) (limit := limit)
      have afterCases := outputCost.kept.trans ambient
      have afterGate := caseCost.kept.trans afterCases
      have afterMotive := gateCost.kept.trans afterGate
      have afterSubject := motiveCost.kept.trans afterMotive
      obtain ⟨subjectKept,subjectBack,actualEntry,inner,values,entryLookup,realArity,referenceRep,parametersRep,
        width,parametersTyped,innerConv,typedSubject⟩ :=
        NativeCoreViewSubject.run_refines_formed normalSound normalProgress inferSound onBase room subjectRep
          subjectFormation exposedOk afterSubject (fun pair member => retained pair (List.mem_append_left _ member))
      have sameEntry := Option.some.inj (entryLookup.symm.trans entryFound)
      subst actualEntry
      have parameterWidth := width.trans (realArity.trans unindexed)
      have subjectTyped : LoanTyping.HasType env [] ctx true (expand env X)
          (.ref (.node (.ind family entry.declaration.arity) (expandArgs env values))) :=
        realArity ▸ typedSubject
      obtain ⟨motiveKept,motiveBack,_,sortRep,motiveTyped⟩ := inferSound (onBase.trans subjectKept) motiveRoom
        (motiveRep.frame subjectKept) sortOk afterMotive
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
      have throughMotive := subjectKept.trans motiveKept
      obtain ⟨gateKept,gateBack,gateConv⟩ := NativeCoreViewMotiveGate.run_refines normalSound normalProgress
        (onBase.trans throughMotive) (motiveRep.frame throughMotive) sortRep (referenceRep.frame motiveKept)
        choiceOk afterGate (fun pair member => retained pair (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_left _ member))))
      have motiveConv : RawLend.Conv env (viewMotiveType choice.dependent (expand env inner))
          (viewMotiveType choice.dependent (.node (.ind family entry.declaration.arity) (expandArgs env values))) := by
        cases chosen : choice.dependent
        · exact .refl _
        · simp only [viewMotiveType,ite_true]
          rw [←realArity]
          exact .node (.pi false) (.cons (.node .ref (.cons innerConv .nil)) (.cons (.refl _) .nil))
      have checkedMotive := motiveTyped.convert (gateConv.trans motiveConv)
      have beforeCases := throughMotive.trans gateKept
      have parameterKept := motiveKept.trans gateKept
      have casesLocal : Prefix base gate.state.arena := onBase.trans beforeCases
      have localInfer : InferSound env gate.state.arena ctx limit infer := by
        intro _ _ _ _ _ baseHere otherRoom held done future comparisons
        exact inferSound (casesLocal.trans baseHere) otherRoom held done future comparisons
      have localNormal : VisitsFrom gate.state.arena (ExpandedNormalization env) normal := by
        intro _ _ _ _ baseHere held done
        exact normalSound (casesLocal.trans baseHere) held done
      obtain ⟨casesKept,casesBack,expectedTypes,typeRows,typedCases⟩ := checkCases_refines localNormal normalProgress
        localInfer inferProgress (caseReplay casesLocal (motiveRep.frame beforeCases) (parametersRep.frame parameterKept)
          parameterWidth parametersTyped subjectTyped checkedMotive) (.refl _) casesRoom (branchReps.frame beforeCases) List.drop_zero
        (branchCount.trans constructors) comparedOk afterCases (fun pair member => retained pair
          (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member))))
      have beforeOutput := beforeCases.trans casesKept
      obtain ⟨outKept,outBack,outRep⟩ := finish_refines (motiveRep.frame beforeOutput) (subjectRep.frame beforeOutput) selectedOk
      refine ⟨beforeOutput.trans outKept,outBack ∘ casesBack ∘ gateBack ∘ motiveBack ∘ subjectBack,_,outRep,?_⟩
      have indexCount : (expandArgs env values).length = entry.declaration.params := by
        simpa only [EnvironmentDelta.expandArgs_map,List.length_map] using parameterWidth
      have typed := LoanTyping.HasType.view (recursion := recursive) entryFound data boxedActual unindexed indexCount
        subjectTyped checkedMotive (.inl rfl) (by simpa only [viewCaseTypes] using typeRows) typedCases
      cases chosen : choice.dependent <;>
        simpa only [viewResult,chosen,Bool.false_eq_true,ite_false,ite_true,Term.app,EnvironmentDelta.expand_node_cons,
          expand,EnvironmentDelta.expandArgs_map,List.map_append,List.map_cons,List.map_nil,List.length_map] using typed
    · cases success
  · cases success

end Jihoo.NativeKernel.NativeCoreGhostViewInference
