import Jihoo.NativeCoreGhostDataCases
import Jihoo.NativeCoreDataMotiveInference
import Jihoo.NativeCoreGhostFamilyEvidence

/-! Data elimination obtains parameters from the first ghost visit of
the scrutinee. It checks the motive and cases, then revisits the original
scrutinee before building the final motive application. -/
namespace Jihoo.NativeKernel.NativeCoreGhostDataElimination

open NativeArena NativeFamilyWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines RetainedComparisons PairRetained next_progress)
open NativeCoreGhostFamilyEvidence (evidence evidence_progress evidence_refines expand_spine)
open NativeCoreCaseNormal (appendApplications appendApplications_progress appendApplications_refines)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

def run (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State) (family motive subject root : Nat)
    (row : FamilyRoots) (branches : List Nat) (recursive : Bool := false) : Outcome Inferred :=
  if branches.length = row.constructors.length then
    (evidence infer normal state family subject).next fun scrutinized original =>
      let indices := original.2.2
      let parameters := indices.take row.params
      (infer scrutinized motive).next fun inferred motiveType =>
        (NativeCoreDataMotiveInference.run normal limit depth inferred family row.params row.arity
          motive motiveType.typeRoot parameters).next fun checkedMotive chosen =>
          (NativeCoreGhostDataCases.runWithMode infer normal limit depth family motive root row parameters
            recursive chosen.proof branches 0 checkedMotive).next fun checkedCases compared =>
            (infer checkedCases subject).next fun checkedSubject checked =>
              (appendApplications checkedSubject motive (indices.drop row.params)).next fun applied body =>
                (append applied .app [body,subject]).next fun after selected =>
                  ⟨after,.ok ⟨selected,original.1.compared ++ (motiveType.compared ++
                    ([chosen.compared] ++ (compared ++ checked.compared)))⟩⟩
  else ⟨state,.error (.outsideFragment root)⟩

private theorem applications_progress : Progress limit state (appendApplications state motive indices) := by
  obtain ⟨kept,steps,_,_⟩ := appendApplications_progress state motive indices
  exact Progress.uncharged kept steps

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth state family motive subject root row branches recursive) := by
  unfold run
  split
  · apply next_progress (evidence_progress childProgress normalProgress room) room
    intro original _ scrutinizedRoom
    apply next_progress (childProgress _ _ scrutinizedRoom) scrutinizedRoom
    intro motiveType _ inferredRoom
    apply next_progress (NativeCoreDataMotiveInference.run_progress normalProgress inferredRoom) inferredRoom
    intro chosen _ motiveRoom
    apply next_progress (NativeCoreGhostDataCases.runWithMode_progress childProgress normalProgress motiveRoom) motiveRoom
    intro _ _ casesRoom
    apply next_progress (childProgress _ _ casesRoom) casesRoom
    intro _ _ _
    exact applications_progress.next (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))
  · exact Progress.atState _ _

private theorem represented_take (count : Nat) (held : RepresentsList arena refs terms) :
    RepresentsList arena (refs.take count) (terms.take count) := by
  induction count generalizing refs terms with
  | zero => exact .nil
  | succ count ih =>
    cases held with
    | nil => exact .nil
    | cons first rest => exact .cons first (ih rest)

private theorem represented_drop (count : Nat) (held : RepresentsList arena refs terms) :
    RepresentsList arena (refs.drop count) (terms.drop count) := by
  induction count generalizing refs terms with
  | zero => exact held
  | succ count ih =>
    cases held with
    | nil => exact .nil
    | cons _ rest => exact ih rest

private theorem expand_take (env : Environment) (xs : List Term) (count : Nat) :
    expandArgs env (xs.take count) = (expandArgs env xs).take count := by
  simp only [EnvironmentDelta.expandArgs_map,List.map_take]

private theorem expand_drop (env : Environment) (xs : List Term) (count : Nat) :
    expandArgs env (xs.drop count) = (expandArgs env xs).drop count := by
  simp only [EnvironmentDelta.expandArgs_map,List.map_drop]

/-- The nonrecursive ghost branch instantiates its motive at the first
scrutinee type's indices and the original scrutinee expression. -/
theorem run_refines
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (rows : RepresentsFamilies state.arena familyRows familyTerms) (rowFound : familyRows[family]? = some row)
    (data : row.data = true) (found : env.families[family]? = some entry)
    (analysisAllowed : analysis = true → entry.boxed = true)
    (recursionMatches : recursive = (entry.boxed && !analysis))
    (chosenWidth : ∀ {values count}, LoanTyping.HasType env [] ctx true (expand env X)
      (.node (.ind family count) values) → count = row.arity)
    (wordIndices : recursive = true → ∀ {values count}, LoanTyping.HasType env [] ctx true (expand env X)
      (.node (.ind family count) values) → ∀ value ∈ values, LoanTyping.HasType env [] ctx true value .u64)
    (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (branchesRep : RepresentsList state.arena branches cases)
    (success : (run infer normal limit depth state family motive subject root row branches recursive).result = .ok answer)
    (ambient : Prefix (run infer normal limit depth state family motive subject root row branches recursive).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx
      (.node (if analysis then .caseOf family cases.length else .elim family cases.length) (M :: (cases ++ [X])))
      (run infer normal limit depth state family motive subject root row branches recursive) answer := by
  obtain ⟨bound,width⟩ := NativeCoreConstructorTelescopeAlignment.checked_family_widths history rows rowFound found
  unfold run at success ambient ⊢
  split at success
  · rename_i correct
    simp only [ite_eq_left correct] at ambient ⊢
    obtain ⟨original,subjectOk,subjectNext⟩ := Outcome.next_success success
    rw [subjectNext] at success ambient ⊢
    obtain ⟨motiveType,motiveOk,motiveNext⟩ := Outcome.next_success success
    rw [motiveNext] at success ambient ⊢
    obtain ⟨chosen,motiveCheck,motiveCheckNext⟩ := Outcome.next_success success
    rw [motiveCheckNext] at success ambient ⊢
    obtain ⟨branchPairs,branchesOk,branchesNext⟩ := Outcome.next_success success
    rw [branchesNext] at success ambient ⊢
    obtain ⟨checkedAgain,againOk,againNext⟩ := Outcome.next_success success
    rw [againNext] at success ambient ⊢
    obtain ⟨body,applied,applicationNext⟩ := Outcome.next_success success
    rw [applicationNext] at success ambient ⊢
    obtain ⟨selected,selectedOk,selectedNext⟩ := Outcome.next_success success
    rw [selectedNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let indices := original.2.2
    let ps := indices.take row.params
    let first := evidence infer normal state family subject
    let inferredMotive := infer first.state motive
    let checkedMotive := NativeCoreDataMotiveInference.run normal limit depth inferredMotive.state
      family row.params row.arity motive motiveType.typeRoot ps
    let checkedCases := NativeCoreGhostDataCases.runWithMode infer normal limit depth family motive root row ps
      recursive chosen.proof branches 0 checkedMotive.state
    let checkedSubject := infer checkedCases.state subject
    let spine := appendApplications checkedSubject.state motive (indices.drop row.params)
    have firstCost := evidence_progress (state := state) (family := family) (subject := subject)
      childProgress normalProgress room
    have motiveRoom := firstCost.accepted room original subjectOk
    have motiveCost := childProgress first.state motive motiveRoom
    have inferredRoom := motiveCost.accepted motiveRoom motiveType motiveOk
    have motiveCheckCost := NativeCoreDataMotiveInference.run_progress (state := inferredMotive.state) (depth := depth)
      (family := family) (params := row.params) (arity := row.arity) (motive := motive) (inferred := motiveType.typeRoot)
      (values := ps) normalProgress inferredRoom
    have casesRoom := motiveCheckCost.accepted inferredRoom chosen motiveCheck
    have casesCost := NativeCoreGhostDataCases.runWithMode_progress (state := checkedMotive.state) (depth := depth)
      (family := family) (motive := motive) (root := root) (row := row) (parameters := ps) (branches := branches)
      (constructor := 0) (recursive := recursive) (proof := chosen.proof) childProgress normalProgress casesRoom
    have againRoom := casesCost.accepted casesRoom branchPairs branchesOk
    have againCost := childProgress checkedCases.state subject againRoom
    have spineCost := applications_progress (limit := limit) (state := checkedSubject.state)
      (motive := motive) (indices := indices.drop row.params)
    have afterSpine := (append_progress (limit := limit) spine.state .app [body,subject]).kept.trans ambient
    have afterAgain := spineCost.kept.trans afterSpine
    have afterCases := againCost.kept.trans afterAgain
    have afterMotiveCheck := casesCost.kept.trans afterCases
    have afterMotive := motiveCheckCost.kept.trans afterMotiveCheck
    have afterFirst := motiveCost.kept.trans afterMotive
    obtain ⟨firstKept,firstBack,values,valuesRep,representedWidth,typedSubject⟩ :=
      evidence_refines normalProgress inferSound normalSound onBase room subjectRep subjectOk afterFirst
        (fun pair member => retained pair (List.mem_append_left _ member))
    have arity := chosenWidth typedSubject
    have validIndices : indices.length = row.arity := representedWidth.trans arity
    have count : ps.length = row.params := by
      simp only [ps,List.length_take,validIndices,Nat.min_eq_left bound]
    obtain ⟨actualEntry,actualFound,dataFamily,paramWidth,arityWidth⟩ :=
      NativeCoreConstructorTelescopeAlignment.checked_family_layout history rows rowFound
    have same := Option.some.inj (actualFound.symm.trans found)
    subst actualEntry
    obtain ⟨motiveKept,motiveBack,_,motiveTypeRep,motiveTyped⟩ :=
      inferSound (onBase.trans firstKept) motiveRoom (motiveRep.frame firstKept) motiveOk afterMotive
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
    have beforeMotiveCheck := firstKept.trans motiveKept
    have parameterRep := (represented_take row.params valuesRep).frame motiveKept
    obtain ⟨motiveCheckKept,motiveCheckBack,motiveConv⟩ :=
      NativeCoreDataMotiveInference.run_refines history.wellFormed normalSound normalProgress (onBase.trans beforeMotiveCheck)
        motiveTypeRep parameterRep count bound motiveCheck afterMotiveCheck
        (retained chosen.compared (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]))
    have beforeCases := beforeMotiveCheck.trans motiveCheckKept
    have wordParameters (recursing : recursive = true) :
        ∀ parameter ∈ values.take row.params, LoanTyping.HasType env [] ctx true (expand env parameter) .u64 := by
      intro parameter member
      apply wordIndices recursing typedSubject
      rw [EnvironmentDelta.expandArgs_map]
      exact List.mem_map.mpr ⟨parameter,List.mem_of_mem_take member,rfl⟩
    obtain ⟨casesKept,casesBack,types,expectedTypes,typedCases⟩ :=
      NativeCoreGhostDataCases.runWithMode_refines (proof := chosen.proof) history normalSound normalProgress inferSound childProgress
        (onBase.trans beforeCases) casesRoom (NativeCoreGhostDataCases.families_frame rows beforeCases) rowFound data found paramWidth
        (motiveRep.frame beforeCases) (parameterRep.frame motiveCheckKept) wordParameters (branchesRep.frame beforeCases)
        List.drop_zero (correct.trans width) branchesOk afterCases
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_left _ member)))))
    have beforeAgain := beforeCases.trans casesKept
    obtain ⟨againKept,againBack,_,_,_⟩ :=
      inferSound (onBase.trans beforeAgain) againRoom (subjectRep.frame beforeAgain) againOk afterAgain
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_right _ member)))))
    have beforeSpine := beforeAgain.trans againKept
    have indicesThrough := motiveKept.trans (motiveCheckKept.trans (casesKept.trans againKept))
    obtain ⟨spineKept,spineBack,_,spineRep⟩ := appendApplications_refines (motiveRep.frame beforeSpine)
      (represented_drop row.params (valuesRep.frame indicesThrough)) applied
    have beforeOutput := beforeSpine.trans spineKept
    obtain ⟨outputKept,outputBack,outputRep⟩ := append_refines (.cons spineRep
      (.cons (subjectRep.frame beforeOutput) .nil)) rfl selectedOk
    refine ⟨beforeOutput.trans outputKept,
      outputBack ∘ spineBack ∘ againBack ∘ casesBack ∘ motiveCheckBack ∘ motiveBack ∘ firstBack,_,outputRep,?_⟩
    have typedMotive := motiveTyped.convert motiveConv
    rw [expand_take,←paramWidth,←arityWidth] at typedMotive
    rw [arity,←arityWidth] at typedSubject
    rw [expand_take,←paramWidth] at expectedTypes
    have indicesLength : (expandArgs env values).length = entry.declaration.arity := by
      simpa only [EnvironmentDelta.expandArgs_map,List.length_map,←NativeCoreIdentical.represented_length valuesRep,
        arityWidth] using validIndices
    have typed := LoanTyping.HasType.dataElim (analysis := analysis) (ghost := true)
      found (dataFamily.trans data) analysisAllowed indicesLength typedMotive
      (by simpa only [Bool.true_or] using typedSubject)
      (by simpa only [dataCaseTypes,←recursionMatches] using expectedTypes)
      (by simpa only [Bool.true_or] using typedCases) (.inl (by simp))
    cases analysis <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Term.app,EnvironmentDelta.expand_node_cons,
      expand,EnvironmentDelta.expandArgs_map,List.map_append,List.map_cons,List.map_nil,List.length_map,←paramWidth,
      expand_spine,List.map_drop] using typed
  · cases success

end Jihoo.NativeKernel.NativeCoreGhostDataElimination
