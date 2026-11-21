import Jihoo.NativeCoreGhostDataElimination
import Jihoo.NativeCoreGhostPropElimination

/-! The two elimination heads use the same family visibility test. An
Elim on a proposition reads the stored constructor signature table, a
flat data Elim uses the written data cases, and a boxed Case requests the
one-level branch types. The boxed recursive branch is handled separately. -/
namespace Jihoo.NativeKernel.NativeCoreGhostFamilyElimination

open NativeArena NativeFamilyWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred InferSound Refines RetainedComparisons)
open NativeCorePropCaseType (SignatureRoots)
open FamilyEnvironment (RelList)
open EnvironmentDelta (expand)

structure VisibleFamily where
  source : FamilyRoots
  boxed : Bool
  signatures : List SignatureRoots

abbrev FamilyTable := Nat → Option VisibleFamily

private def reject (state : State) (root : Nat) : Outcome Inferred :=
  ⟨state,.error (.outsideFragment root)⟩

def run (visibleTable : FamilyTable) (infer : Infer) (normal : Visit) (limit depth : Nat)
    (state : State) (analysis : Bool) (root family motive subject : Nat) (branches : List Nat) : Outcome Inferred :=
  match visibleTable family with
  | none => reject state root
  | some row =>
    if analysis then
      if row.boxed && row.source.data then
        NativeCoreGhostDataElimination.run infer normal limit depth state family motive subject root row.source branches
      else reject state root
    else if row.source.data then
      if row.boxed then reject state root
      else NativeCoreGhostDataElimination.run infer normal limit depth state family motive subject root row.source branches
    else
      NativeCoreGhostPropElimination.run infer normal limit depth state family row.source.arity motive subject root row.signatures branches

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run visibleTable infer normal limit depth state analysis root family motive subject branches) := by
  unfold run
  split
  · exact Progress.atState _ _
  · split
    · split
      · exact NativeCoreGhostDataElimination.run_progress childProgress normalProgress room
      · exact Progress.atState _ _
    · split
      · split
        · exact Progress.atState _ _
        · exact NativeCoreGhostDataElimination.run_progress childProgress normalProgress room
      · exact NativeCoreGhostPropElimination.run_progress childProgress normalProgress room

/-- The graph metadata and signature table are justified by the original
ordered declarations and their accepted family entries. -/
def TableRep (env : Environment) (arena : Arena) (rows : List FamilyRoots) (visibleTable : FamilyTable) : Prop :=
  ∀ (family : Nat) row, visibleTable family = some row →
    ∃ entry, rows[family]? = some row.source ∧ env.families[family]? = some entry ∧
      row.boxed = entry.boxed ∧ (row.source.data = false →
        RelList (NativeCoreGhostPropCases.CheckedSignature env arena) row.signatures entry.signatures)

theorem TableRep.frame (table : TableRep env arena rows visibleTable) (kept : Prefix arena after) :
    TableRep env after rows visibleTable := by
  intro family row found
  obtain ⟨entry,written,checked,boxed,signatures⟩ := table family row found
  exact ⟨entry,written,checked,boxed,fun prop => NativeCoreGhostPropCases.table_frame (signatures prop) kept⟩

/-- The selected checked family determines the motive telescope and the
order of its branch types. The quantified arity property concerns only
the original scrutinee in this context. -/
theorem run_refines
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (table : TableRep env state.arena familyRows visibleTable)
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (branchReps : RepresentsList state.arena branches cases)
    (subjectArity : ∀ {entry count values}, env.families[family]? = some entry →
      LoanTyping.HasType env [] ctx true (expand env X) (.node (.ind family count) values) → count = entry.declaration.arity)
    (success : (run visibleTable infer normal limit depth state analysis root family motive subject branches).result = .ok answer)
    (ambient : Prefix (run visibleTable infer normal limit depth state analysis root family motive subject branches).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx
      (.node (if analysis then .caseOf family cases.length else .elim family cases.length) (M :: (cases ++ [X])))
      (run visibleTable infer normal limit depth state analysis root family motive subject branches) answer := by
  unfold run at success ambient ⊢
  split at success
  · cases success
  · rename_i row chosen
    simp only [chosen] at ambient ⊢
    obtain ⟨entry,written,found,boxed,signatures⟩ := table family row chosen
    obtain ⟨checked,checkedFound,data,_,arity⟩ :=
      NativeCoreConstructorTelescopeAlignment.checked_family_layout history rows written
    have same := Option.some.inj (checkedFound.symm.trans found)
    subst checked
    cases analysis
    · simp only [Bool.false_eq_true,ite_false] at success ambient ⊢
      cases dataRow : row.source.data with
      | false =>
        simp only [dataRow,Bool.false_eq_true,ite_false,←arity] at success ambient ⊢
        exact NativeCoreGhostPropElimination.run_refines history.wellFormed inferSound normalSound childProgress
          normalProgress onBase room found (data.trans dataRow) (signatures dataRow) motiveRep subjectRep branchReps
          (fun typed conversion => subjectArity found (typed.convert conversion)) success ambient retained
      | true =>
        simp only [dataRow,ite_true] at success ambient ⊢
        cases boxedRow : row.boxed with
        | true => simp [boxedRow,reject] at success
        | false =>
          simp only [boxedRow,Bool.false_eq_true,ite_false] at success ambient ⊢
          exact NativeCoreGhostDataElimination.run_refines (analysis := false)
            history inferSound normalSound childProgress normalProgress onBase room rows written dataRow found
            (by intro impossible; cases impossible) (by simp [←boxed,boxedRow])
            (fun typed => (subjectArity found typed).trans arity) motiveRep subjectRep branchReps success ambient retained
    · simp only [ite_true] at success ambient ⊢
      split at success
      · rename_i allowed
        simp only [ite_eq_left allowed] at ambient ⊢
        obtain ⟨boxedRow,dataRow⟩ := Bool.and_eq_true_iff.mp allowed
        exact NativeCoreGhostDataElimination.run_refines (analysis := true)
          history inferSound normalSound childProgress normalProgress onBase room rows written dataRow found
          (fun _ => boxed.symm.trans boxedRow) (by simp)
          (fun typed => (subjectArity found typed).trans arity) motiveRep subjectRep branchReps success ambient retained
      · cases success

/-- In the arena the motive precedes the branch list, and the subject is
the final argument. The incoming visit has already charged the head. -/
def runNode (visibleTable : FamilyTable) (infer : Infer) (normal : Visit) (limit depth : Nat)
    (state : State) (analysis : Bool) (root family : Nat) : List Nat → Outcome Inferred
  | motive :: tail =>
    match tail.getLast? with
    | some subject => run visibleTable infer normal limit depth state analysis root family motive subject tail.dropLast
    | none => reject state root
  | [] => reject state root

theorem runNode_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runNode visibleTable infer normal limit depth state analysis root family arguments) := by
  cases arguments with
  | nil => exact Progress.atState _ _
  | cons motive tail =>
    simp only [runNode]
    cases found : tail.getLast?
    · exact Progress.atState _ _
    · exact run_progress childProgress normalProgress room

theorem runNode_invisible (hidden : visibleTable family = none) :
    runNode visibleTable infer normal limit depth state analysis root family arguments =
      ⟨state,.error (.outsideFragment root)⟩ := by
  cases arguments with
  | nil => rfl
  | cons motive tail =>
    simp only [runNode]
    cases tail.getLast?
    · rfl
    · simp only [run,hidden,reject]

end Jihoo.NativeKernel.NativeCoreGhostFamilyElimination
