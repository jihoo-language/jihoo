import Jihoo.NativeCoreGhostFamilyElimination
import Jihoo.NativeCoreFamilyHeadFormation
import Jihoo.NativeCoreGhostSpineInference

/-! CODE data elimination reads the visible family row before visiting the
original scrutinee. A boxed recursive Elim and a one-level Case have separate
case telescopes. The authenticated original scrutinee annotation supplies the
indices used by both. -/
namespace Jihoo.NativeKernel.NativeCoreCodeDataDispatch

open Environment NativeArena NativeFamilyWire
open EnvironmentDelta (expand expandArgs)
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred RetainedComparisons GraphBinding ContextRep)
open NativeCoreGhostFamilyElimination (FamilyTable TableRep)
open NativeCoreBufferRelease (ModeSound)

private def reject (state : State) (root : Nat) : Outcome Inferred :=
  ⟨state,.error (.outsideFragment root)⟩

private def chooseData (visibleTable : FamilyTable) (analysis : Bool) (family : Nat) :
    Option NativeCoreGhostFamilyElimination.VisibleFamily := do
  let entry ← visibleTable family
  if entry.source.data && (!analysis || entry.boxed) then some entry else none

/-- Post-entry CODE data dispatch. A one-level Case needs boxed metadata.
Elim asks for recursive hypotheses exactly on boxed visibleTable. -/
def run (visibleTable : FamilyTable) (inferGhost : Infer) (inferMode : Bool → Infer)
    (normal : Visit) (limit depth : Nat) (state : State) (analysis : Bool)
    (root family motive subject : Nat) (branches : List Nat) : Outcome Inferred :=
  match chooseData visibleTable analysis family with
  | none => reject state root
  | some entry =>
    NativeCoreGhostDataElimination.runInMode inferGhost inferMode normal false limit depth state family motive subject root
      entry.source branches (entry.boxed && !analysis)

theorem run_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferGhost state root))
    (modeProgress : ∀ (mode : Bool) state root, state.steps ≤ limit → Progress limit state (inferMode mode state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run visibleTable inferGhost inferMode normal limit depth state analysis root family motive subject branches) := by
  unfold run
  split
  · exact Progress.atState _ _
  · exact NativeCoreGhostDataElimination.runInMode_progress ghostProgress modeProgress normalProgress room

private theorem chooseData_refines (chosen : chooseData visibleTable analysis family = some entry) :
    visibleTable family = some entry ∧ entry.source.data = true ∧ (analysis = true → entry.boxed = true) := by
  unfold chooseData at chosen
  obtain ⟨observed,found,selected⟩ := Option.bind_eq_some_iff.mp chosen
  split at selected
  · rename_i allowed
    cases selected
    obtain ⟨data,layout⟩ := Bool.and_eq_true_iff.mp allowed
    refine ⟨found,data,fun analyzing => ?_⟩
    simpa only [analyzing,Bool.not_true,Bool.false_or] using layout
  · cases selected

/-- Successful CODE dispatch types the original branches and repeated subject
at the motive's actual relevance. Formation belongs to the type node returned
by the first ghost subject visit. -/
theorem run_refines_formed
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (table : TableRep env state.arena familyRows visibleTable)
    (ghostSound : InferSound env base ctx limit inferGhost)
    (modeSound : ∀ (mode : Bool), ModeSound env loans base ctx limit mode (inferMode mode))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferGhost state root))
    (modeProgress : ∀ (mode : Bool) state root, state.steps ≤ limit → Progress limit state (inferMode mode state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (branchReps : RepresentsList state.arena branches sourceCases)
    (formation : ∀ {answer original}, (inferGhost state subject).result = .ok answer →
      Represents (inferGhost state subject).state.arena answer.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term)
    (success : (run visibleTable inferGhost inferMode normal limit depth state analysis root family motive subject branches).result = .ok answer)
    (ambient : Prefix (run visibleTable inferGhost inferMode normal limit depth state analysis root family motive subject branches).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (run visibleTable inferGhost inferMode normal limit depth state analysis root family motive subject branches).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ output, Represents after answer.typeRoot output ∧ LoanTyping.HasType env loans ctx false
        (expand env (.node (if analysis then .caseOf family sourceCases.length else .elim family sourceCases.length)
          (M :: (sourceCases ++ [X])))) (expand env output) := by
  unfold run at success ambient ⊢
  cases selected : chooseData visibleTable analysis family with
  | none => simp [selected,reject] at success
  | some facts =>
    simp only [selected] at success ambient ⊢
    obtain ⟨visible,data,analysisAllowed⟩ := chooseData_refines selected
    obtain ⟨entry,stored,found,boxed,_⟩ := table family facts visible
    obtain ⟨recorded,known,_,_,arity⟩ := NativeCoreConstructorTelescopeAlignment.checked_family_layout history rows stored
    have same := Option.some.inj (known.symm.trans found)
    subst recorded
    have allows : analysis = true → entry.boxed = true := fun analyzing => boxed.symm.trans (analysisAllowed analyzing)
    exact NativeCoreGhostDataElimination.runInMode_refines_using (mode := false)
      history ghostSound (fun proof => @modeSound proof)
      normalSound ghostProgress modeProgress normalProgress onBase room rows stored data found allows
      (by rw [boxed])
      (fun inferred represented reduced _ => NativeCoreGhostDataElimination.formed_subject_facts
        formation found arity inferred represented reduced)
      motiveRep subjectRep branchReps success ambient retained

def runNode (visibleTable : FamilyTable) (inferGhost : Infer) (inferMode : Bool → Infer)
    (normal : Visit) (limit depth : Nat) (state : State) (analysis : Bool)
    (root family : Nat) : List Nat → Outcome Inferred
  | motive :: tail =>
    match tail.getLast? with
    | some subject => run visibleTable inferGhost inferMode normal limit depth state analysis root family motive subject tail.dropLast
    | none => reject state root
  | [] => reject state root

theorem runNode_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferGhost state root))
    (modeProgress : ∀ (mode : Bool) state root, state.steps ≤ limit → Progress limit state (inferMode mode state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runNode visibleTable inferGhost inferMode normal limit depth state analysis root family arguments) := by
  cases arguments with
  | nil => exact Progress.atState _ _
  | cons motive tail =>
    simp only [runNode]
    split
    · exact run_progress ghostProgress modeProgress normalProgress room
    · exact Progress.atState _ _

theorem runNode_invisible (hidden : visibleTable family = none) :
    runNode visibleTable inferGhost inferMode normal limit depth state analysis root family arguments =
      ⟨state,.error (.outsideFragment root)⟩ := by
  cases arguments with
  | nil => rfl
  | cons motive tail =>
    simp only [runNode]
    split
    · simp [run,chooseData,hidden,reject]
    · rfl

private theorem represented_last {refs : List Nat} (source : RepresentsList arena refs terms)
    (found : refs.getLast? = some subject) :
    ∃ branches term, terms = branches ++ [term] ∧ RepresentsList arena refs.dropLast branches ∧
      Represents arena subject term := by
  induction refs generalizing terms with
  | nil => simp at found
  | cons next refs ih =>
    cases source with
    | cons leading rest =>
      cases refs with
      | nil =>
        cases rest
        cases found
        exact ⟨[],_,rfl,.nil,leading⟩
      | cons following refs =>
        obtain ⟨branches,term,shape,held,last⟩ := ih rest found
        rw [shape]
        exact ⟨_ :: branches,term,rfl,.cons leading held,last⟩

/-- Dispatch at the original graph node keeps the case count encoded in
its constructor header and the independently formed original scrutinee. -/
theorem runNode_refines_formed
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (table : TableRep env state.arena familyRows visibleTable)
    (ghostSound : InferSound env base ctx limit inferGhost)
    (modeSound : ∀ (mode : Bool), ModeSound env loans base ctx limit mode (inferMode mode))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferGhost state root))
    (modeProgress : ∀ (mode : Bool) state root, state.steps ≤ limit → Progress limit state (inferMode mode state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : RepresentsList state.arena arguments terms)
    (arity : arguments.length = (if analysis then Op.caseOf family count else Op.elim family count).arity)
    (formation : ∀ {subject answer original}, arguments.getLast? = some subject →
      (inferGhost state subject).result = .ok answer →
      Represents (inferGhost state subject).state.arena answer.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term)
    (success : (runNode visibleTable inferGhost inferMode normal limit depth state analysis root family arguments).result = .ok answer)
    (ambient : Prefix (runNode visibleTable inferGhost inferMode normal limit depth state analysis root family arguments).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (runNode visibleTable inferGhost inferMode normal limit depth state analysis root family arguments).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ output, Represents after answer.typeRoot output ∧ LoanTyping.HasType env loans ctx false
        (expand env (.node (if analysis then .caseOf family count else .elim family count) terms)) (expand env output) := by
  have length := NativeCoreIdentical.represented_length source
  cases source with
  | nil => cases success
  | @cons motive M tail terms motiveRep others =>
    cases found : tail.getLast? with
    | none => simp [runNode,found,reject] at success
    | some subject =>
      simp only [runNode,found] at success ambient ⊢
      obtain ⟨branches,X,rfl,branchRep,subjectRep⟩ := represented_last others found
      have width : branches.length = count := by
        simp only [dataCaseOp_arity,List.length_cons,List.length_append,List.length_nil] at length arity
        omega
      subst count
      exact run_refines_formed history rows table ghostSound (@modeSound) normalSound ghostProgress modeProgress normalProgress
        onBase room motiveRep subjectRep branchRep (fun visit held => formation (by
          cases tail with
          | nil => simp at found
          | cons _ _ => exact found) visit held) success ambient retained

/-- The table and subject annotation can be certified independently of the
recursive CODE visitor. This contract composes its ghost and CODE callbacks
at the original expanded context. -/
def Sound (env : Environment) (base : Arena) (visibleTable : FamilyTable)
    (ghost : Nat → List GraphBinding → Infer) : Prop :=
  ∀ {start : Arena} {state : State} {ctx : Context} {bindings : List GraphBinding} {depth limit : Nat}
    {loans : Loans.Stack} {inferMode : Bool → Infer} {normal : Visit} {analysis : Bool}
    {root family count : Nat} {arguments : List Nat} {terms : List Term} {answer : Inferred} {final : Arena},
    Prefix base start → ContextRep env start bindings ctx → Prefix start state.arena → state.steps ≤ limit →
    InferSound env start ctx limit (ghost depth bindings) →
    (∀ (mode : Bool), ModeSound env loans start ctx limit mode (inferMode mode)) →
    VisitsFrom start (ExpandedNormalization env) normal →
    (∀ state root, state.steps ≤ limit → Progress limit state (ghost depth bindings state root)) →
    (∀ (mode : Bool) state root, state.steps ≤ limit → Progress limit state (inferMode mode state root)) →
    (∀ state root, Progress limit state (normal state root)) →
    RepresentsList state.arena arguments terms →
    arguments.length = (if analysis then Op.caseOf family count else Op.elim family count).arity →
    (runNode visibleTable (ghost depth bindings) inferMode normal limit depth state analysis root family arguments).result = .ok answer →
    Prefix (runNode visibleTable (ghost depth bindings) inferMode normal limit depth state analysis root family arguments).state.arena final →
    RetainedComparisons final answer →
    let after := (runNode visibleTable (ghost depth bindings) inferMode normal limit depth state analysis root family arguments).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ output, Represents after answer.typeRoot output ∧ LoanTyping.HasType env loans ctx false
        (expand env (.node (if analysis then .caseOf family count else .elim family count) terms)) (expand env output)

/-- A dispatch with no visible data family rejects every data request. -/
theorem empty_sound : Sound env base (fun _ => none) ghost := by
  intro start state ctx bindings depth limit loans inferMode normal analysis root family count arguments terms answer final
    onStart context onBase room ghostSound modeSound normalSound ghostWork modeWork normalWork source arity success ambient retained
  rw [runNode_invisible (show (fun _ : Nat => (none : Option NativeCoreGhostFamilyElimination.VisibleFamily)) family = none from rfl)] at success
  cases success

/-- A checked historical table and original annotation formation supply
all cases of the dispatch contract at the actual retained source roots. -/
theorem sound_of_formed_annotations
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies base familyRows familyTerms)
    (table : TableRep env base familyRows visibleTable)
    (formation : ∀ {start : Arena} {state : State} {bindings : List GraphBinding} {ctx : Context}
      {subject depth : Nat} {answer : Inferred} {original : Term},
      Prefix base start → ContextRep env start bindings ctx → Prefix start state.arena →
      (ghost depth bindings state subject).result = .ok answer →
      Represents (ghost depth bindings state subject).state.arena answer.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term) :
    Sound env base visibleTable ghost := by
  intro start state ctx bindings depth limit loans inferMode normal analysis root family count arguments terms answer final
    onStart context onBase room ghostSound modeSound normalSound ghostWork modeWork normalWork source arity success ambient retained
  have kept := onStart.trans onBase
  exact runNode_refines_formed history (NativeCoreGhostDataCases.families_frame rows kept) (table.frame kept)
    ghostSound (@modeSound) normalSound ghostWork modeWork normalWork onBase room source arity
    (fun _ accepted represented => formation onStart context onBase accepted represented) success ambient retained

end Jihoo.NativeKernel.NativeCoreCodeDataDispatch
