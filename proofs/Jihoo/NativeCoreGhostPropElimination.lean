import Jihoo.NativeCoreGhostFamilyEvidence
import Jihoo.NativeCoreGhostPropCases
import Jihoo.NativeCorePropMotiveType
import Jihoo.NativeCoreCaseNormal
import Jihoo.NativeLoanFamilyIotaConstructor

/-! The proposition branch of Core.infer checks the motive and written
branches before visiting the evidence. The final motive spine uses the
indices read from the evidence's normalized type. -/
namespace Jihoo.NativeKernel.NativeCoreGhostPropElimination

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines RetainedComparisons next_progress)
open NativeCoreGhostFoldInference (checkAgainst checkAgainst_progress checkAgainst_refines)
open NativeCoreGhostPropCases (CheckedSignature)
open NativeCoreGhostFamilyEvidence (evidence evidence_progress evidence_refines expand_spine)
open NativeCorePropCaseType (SignatureRoots)
open NativeCoreCaseNormal (appendApplications appendApplications_progress appendApplications_refines)
open FamilyEnvironment (RelList)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

/-- The family lookup and data dispatch occur before this proposition branch. -/
def run (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (family arity motive subject rejected : Nat) (roots : List SignatureRoots) (branches : List Nat) : Outcome Inferred :=
  if branches.length = roots.length then
    (NativeCorePropMotiveType.run state arity).next fun formed expected =>
      (checkAgainst infer normal limit depth formed expected motive).next fun checkedMotive motivePairs =>
        (NativeCoreGhostPropCases.run infer normal limit depth motive rejected roots branches checkedMotive).next
          fun checkedCases branchPairs =>
            (evidence infer normal checkedCases family subject).next fun checkedSubject exposed =>
              (appendApplications checkedSubject motive exposed.2.2).next fun after result =>
                ⟨after,.ok ⟨result,motivePairs ++ (branchPairs ++ exposed.1.compared)⟩⟩
  else reject state rejected

private theorem application_progress (state : State) (motive : Nat) (indices : List Nat) :
    Progress limit state (appendApplications state motive indices) := by
  obtain ⟨kept,steps,_,_⟩ := appendApplications_progress state motive indices
  exact Progress.uncharged kept steps

theorem run_progress
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth state family arity motive subject rejected roots branches) := by
  unfold run
  split
  · apply next_progress (NativeCorePropMotiveType.run_progress _ _) room
    intro _ _ formedRoom
    apply next_progress (checkAgainst_progress childProgress normalProgress formedRoom) formedRoom
    intro _ _ checkedRoom
    apply next_progress (NativeCoreGhostPropCases.run_progress childProgress normalProgress checkedRoom) checkedRoom
    intro _ _ casesRoom
    exact (evidence_progress childProgress normalProgress casesRoom).next (fun _ =>
      (application_progress _ _ _).next (fun _ => Progress.atState _ _))
  · exact Progress.atState _ _

/-- Once the evidence's type is known to have the declaration's arity,
the graph produces the original motive applied to its normalized indices.
Each branch is checked against the signature from the earlier history. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (inferSound : InferSound env base ctx limit infer)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (found : env.families[family]? = some entry) (proposition : entry.declaration.data = false)
    (table : RelList (CheckedSignature env state.arena) roots entry.signatures)
    (motiveRep : Represents state.arena motive M) (subjectRep : Represents state.arena subject X)
    (branchReps : RepresentsList state.arena branches cases)
    (subjectArity : ∀ {T values count}, LoanTyping.HasType env [] ctx true (expand env X) T →
      RawLend.Conv env T (.node (.ind family count) values) → count = entry.declaration.arity)
    (success : (run infer normal limit depth state family entry.declaration.arity motive subject rejected roots branches).result =
      .ok answer)
    (ambient : Prefix
      (run infer normal limit depth state family entry.declaration.arity motive subject rejected roots branches).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.elim family cases.length) (M :: (cases ++ [X])))
      (run infer normal limit depth state family entry.declaration.arity motive subject rejected roots branches) answer := by
  unfold run at success ambient ⊢
  split at success
  · rename_i enough
    simp only [ite_eq_left enough] at ambient ⊢
    obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
    rw [expectedNext] at success ambient ⊢
    obtain ⟨motivePairs,motiveOk,motiveNext⟩ := Outcome.next_success success
    rw [motiveNext] at success ambient ⊢
    obtain ⟨branchPairs,branchesOk,branchesNext⟩ := Outcome.next_success success
    rw [branchesNext] at success ambient ⊢
    obtain ⟨exposed,subjectOk,subjectNext⟩ := Outcome.next_success success
    rw [subjectNext] at success ambient ⊢
    obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
    rw [resultNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let formed := NativeCorePropMotiveType.run state entry.declaration.arity
    let checkedMotive := checkAgainst infer normal limit depth formed.state expected motive
    let checkedCases := NativeCoreGhostPropCases.run infer normal limit depth motive rejected roots branches checkedMotive.state
    let checkedSubject := evidence infer normal checkedCases.state family subject
    have formedRoom := (NativeCorePropMotiveType.run_progress (limit := limit) state entry.declaration.arity).accepted
      room expected expectedOk
    have motiveCost := checkAgainst_progress (state := formed.state) (depth := depth) (expected := expected)
      (argument := motive) childProgress normalProgress formedRoom
    have casesRoom := motiveCost.accepted formedRoom motivePairs motiveOk
    have casesCost := NativeCoreGhostPropCases.run_progress (state := checkedMotive.state) (depth := depth)
      (motive := motive) (rejected := rejected) (roots := roots) (branches := branches) childProgress normalProgress casesRoom
    have subjectRoom := casesCost.accepted casesRoom branchPairs branchesOk
    have subjectCost := evidence_progress (state := checkedCases.state) (family := family) (subject := subject)
      childProgress normalProgress subjectRoom
    have afterEvidence := (application_progress (limit := limit) checkedSubject.state motive exposed.2.2).kept.trans ambient
    have afterCases := subjectCost.kept.trans afterEvidence
    have afterMotive := casesCost.kept.trans afterCases
    obtain ⟨formedKept,formedBack,expectedRep⟩ := NativeCorePropMotiveType.run_refines expectedOk
    obtain ⟨motiveKept,motiveBack,motiveTyped⟩ := checkAgainst_refines normalSound normalProgress inferSound childProgress
      (onBase.trans formedKept) formedRoom (motiveRep.frame formedKept) expectedRep motiveOk afterMotive
      (fun pair member => retained pair (List.mem_append_left _ member))
    have beforeCases := formedKept.trans motiveKept
    obtain ⟨casesKept,casesBack,casesTyped⟩ := NativeCoreGhostPropCases.run_refines wf normalSound normalProgress
      inferSound childProgress (onBase.trans beforeCases) casesRoom (motiveRep.frame beforeCases)
      (branchReps.frame beforeCases) (NativeCoreGhostPropCases.table_frame table beforeCases) branchesOk afterCases
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
    have beforeSubject := beforeCases.trans casesKept
    obtain ⟨subjectKept,subjectBack,values,valuesRep,_,typedSubject⟩ :=
      evidence_refines normalProgress inferSound normalSound (onBase.trans beforeSubject)
        subjectRoom (subjectRep.frame beforeSubject) subjectOk afterEvidence
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
    have arityMatches := subjectArity typedSubject (.refl _)
    rw [arityMatches] at typedSubject
    have beforeResult := beforeSubject.trans subjectKept
    obtain ⟨resultKept,resultBack,_,resultRep⟩ := appendApplications_refines (motiveRep.frame beforeResult) valuesRep resultOk
    refine ⟨beforeResult.trans resultKept,resultBack ∘ subjectBack ∘ casesBack ∘ motiveBack ∘ formedBack,
      _,resultRep,?_⟩
    have expandMotive : expand env (propMotiveType entry.declaration.arity) = propMotiveType entry.declaration.arity := by
      generalize entry.declaration.arity = arity
      induction arity with
      | zero => simp only [propMotiveType,Term.prop,expand,expandArgs]
      | succ arity ih => simp only [propMotiveType,Term.pi,expand,expandArgs,ih]
    have typed := LoanTyping.HasType.propElim (ghost := true) found proposition
      (expandMotive ▸ motiveTyped) casesTyped typedSubject
    rw [expand_spine]
    simpa only [expand,EnvironmentDelta.expandArgs_map,List.map_append,List.map_cons,List.map_nil,List.length_map] using typed
  · cases success

/-- When source evidence is a constructor, its checked telescope fixes the
arity of every convertible evidence type, even after dependent substitution. -/
theorem constructor_subject_arity (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (typed : LoanTyping.HasType env [] ctx true (.node (.con family constructor count) fields) type)
    (normalized : RawLend.Conv env type (.node (.ind family arity) values)) :
    arity = entry.declaration.arity := by
  obtain ⟨checkedEntry,signature,oldCount,indices,sourceFamily,sourceSig,arguments,result⟩ := typed.principalView
  cases Option.some.inj (found.symm.trans sourceFamily)
  obtain ⟨scope,width,_⟩ := LoanTyping.FamilyIota.signature_metadata history sourceFamily sourceSig
  rw [Environment.closed_rename (scope.signatureTerm_scoped family)] at arguments
  obtain ⟨checkedEntry,checkedSignature,actualFamily,actualSignature,fieldsLength⟩ :=
    LoanTyping.FamilyIota.checked_constructor_fields history typed
  cases Option.some.inj (sourceFamily.symm.trans actualFamily)
  cases Option.some.inj (sourceSig.symm.trans actualSignature)
  have original := LoanTyping.FamilyIota.constructor_result_conversion history.wellFormed arguments fieldsLength
  have counts := ((original.trans (result.trans normalized)).ind_injective history.wellFormed.admissible).2.1
  exact counts.symm.trans width

end Jihoo.NativeKernel.NativeCoreGhostPropElimination
