import Jihoo.NativeCoreGhostConstructorFields
import Jihoo.NativeCoreConstructorGraphLink
import Jihoo.NativeLoanContextualPreservation

/-! A ghost constructor checks actual field terms in the original caller
context. Its shifted signature is the raw constructor root published by
the validated family declaration. -/
namespace Jihoo.NativeKernel.NativeCoreGhostConstructorInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Visit Infer Inferred InferSound Refines RetainedComparisons)
open NativeCoreConstructorTelescopeAlignment (signature_ends_in_family replay_retains_declared_family)
open EnvironmentDelta (expand expandArgs)

private def shiftSignature (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  let shifted := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨shifted.state,shifted.result.mapError .substitution⟩

def run (infer : Infer) (normal : Visit) (limit depth root contextLength : Nat)
    (state : State) (signature : Nat) (fields : List Nat) : Outcome Inferred :=
  (shiftSignature limit depth state signature contextLength).next fun after shifted =>
    NativeCoreGhostConstructorFields.run infer normal limit depth root fields after shifted

private theorem shift_success (success : (shiftSignature limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shiftSignature at success
  cases read : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [read,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

private theorem shift_progress (limit depth : Nat) (state : State) (root amount : Nat) :
    Progress limit state (shiftSignature limit depth state root amount) := by
  have checked := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨checked.kept,checked.monotone,checked.bounded,
    fun room value accepted => checked.accepted room value (shift_success accepted)⟩

private theorem shift_refines (source : Represents state.arena root written)
    (success : (shiftSignature limit depth state root amount).result = .ok selected) :
    let output := shiftSignature limit depth state root amount
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected (written.rename (fun index => index+amount)) := by
  obtain ⟨kept,backward,term,related,held⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift amount) (binders := 0) (value := written)
      source trivial (shift_success success)).1
  change PartialRenaming.shift amount 0 written = some term at related
  rw [PartialRenaming.shift_nonnegative (by omega)] at related
  have direction : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun index => index+amount := by
    funext index
    simp [PartialRenaming.raiseIndex]
  rw [direction] at related
  cases related
  exact ⟨kept,backward,held⟩

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth root contextLength state signature fields) := by
  let shifted := shiftSignature limit depth state signature contextLength
  have shift := shift_progress limit depth state signature contextLength
  unfold run
  cases read : shifted.result with
  | error reason =>
    change Progress limit state (shifted.next _)
    simp only [Outcome.next,read]
    exact ⟨shift.kept,shift.monotone,shift.bounded,fun _ _ impossible => by cases impossible⟩
  | ok rootType =>
    have enough := shift.accepted room rootType read
    have fieldsChecked := NativeCoreGhostConstructorFields.run_progress (state := shifted.state)
      (fields := fields) (telescope := rootType) (root := root) (depth := depth) infers normalizes enough
    change Progress limit state (shifted.next _)
    simp only [Outcome.next,read]
    exact ⟨shift.kept.trans fieldsChecked.kept,Nat.le_trans shift.monotone fieldsChecked.monotone,
      fun _ => fieldsChecked.bounded enough,fun _ value accepted => fieldsChecked.accepted enough value accepted⟩

/-- The actual raw graph signature is shifted in the caller scope. Its
successful field walk is an original-type checked ghost constructor. -/
theorem run_refines
    {family constructor count : Nat} {entry : CheckedFamily} {signature : Signature}
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (familyFound : env.families[family]? = some entry) (signatureFound : entry.signatures[constructor]? = some signature)
    (rawRep : Represents state.arena rawRoot rawType)
    (original : RawLend.Conv env (expand env rawType) (signatureTerm family signature))
    (fieldsRep : RepresentsList state.arena fields args) (length : fields.length = count)
    (success : (run infer normal limit depth root ctx.length state rawRoot fields).result = .ok answer)
    (ambient : Prefix (run infer normal limit depth root ctx.length state rawRoot fields).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.con family constructor count) args)
      (run infer normal limit depth root ctx.length state rawRoot fields) answer := by
  unfold run at success ambient ⊢
  obtain ⟨shifted,shiftedOk,shiftedNext⟩ := Outcome.next_success success
  rw [shiftedNext] at success ambient ⊢
  obtain ⟨initial,back,typeRep⟩ := shift_refines rawRep shiftedOk
  have within := (shift_progress limit depth state rawRoot ctx.length).accepted room shifted shiftedOk
  obtain ⟨kept,backward,actual,arity,indices,resultRep,replayed⟩ :=
    NativeCoreGhostConstructorFields.run_refines (data := entry.declaration.data) wf normalSound normalProgress
      inferSound inferProgress (onBase.trans initial) within typeRep (fieldsRep.frame initial) success ambient retained
  have aligned : RawLend.Conv env (expand env (rawType.rename (fun index => index+ctx.length)))
      ((signatureTerm family signature).rename (fun index => index+ctx.length)) := by
    rw [EnvironmentDelta.expand_renaming wf.admissible]
    exact original.renaming _ wf.closed
  have ends := (signature_ends_in_family family signature).renaming (fun index => index+ctx.length)
  have same := replay_retains_declared_family wf replayed ends aligned rfl
  subst actual
  have fieldCount : count = (expandArgs env args).length := by
    rw [EnvironmentDelta.expandArgs_map,List.length_map,← NativeCoreIdentical.represented_length fieldsRep,length]
  have constructorTyped := LoanTyping.HasType.con familyFound signatureFound fieldCount
    (replayed.convertTelescope aligned.symm)
  refine ⟨initial.trans kept,backward ∘ back,_,resultRep,?_⟩
  simpa only [expand] using constructorTyped

/-- The family and constructor positions select the original live telescope
through the actual admitted family history and byte graph. -/
theorem run_from_checked_graph {family constructor count : Nat} {row : NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions
      (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : NativeFamilyWire.RepresentsFamilies base familyRows familyTerms)
    (selected : familyRows[family]? = some row)
    (read : row.constructors[constructor]? = some rawRoot)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fieldsRep : RepresentsList state.arena fields args) (length : fields.length = count)
    (success : (run infer normal limit depth root ctx.length state rawRoot fields).result = .ok answer)
    (ambient : Prefix (run infer normal limit depth root ctx.length state rawRoot fields).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.con family constructor count) args)
      (run infer normal limit depth root ctx.length state rawRoot fields) answer := by
  obtain ⟨entry,signature,source,found,signatureFound,_,sourceRep,aligned⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_constructor_root
      (ScopedProgram.History.ofLoanMixed history) rows selected read
  exact run_refines history.wellFormed normalSound normalProgress inferSound inferProgress onBase room
    found signatureFound (sourceRep.frame onBase) aligned fieldsRep length success ambient retained

open NativeProgramWire

private def constructorSnapshot : NativeFamilyWire.Snapshot where
  definitions := []
  families := [⟨false,0,1,0,[7]⟩]
  arena := #[.node (.natural 3) [],.node .u64 [],.var 0,.var 1,.node .eq [2,2],
    .node (.ind 0 1) [3],.node (.pi true) [4,5],.node (.pi false) [1,6],.node .refl [0],
    .node (.con 0 0 1) [0],.node (.con 0 0 2) [0,8],.node (.universe 0) [],.node .u64 [],
    .node .prop [],.node .u64 []]

private def constructorEnvironment : Option Environment := do
  let (defs,families) ← NativeFamilyWire.decodeProgram constructorSnapshot
  LoanTyping.MixedProgram.checkProgram 64 128 defs (families.map NativeLoanMixedAdmission.declaration)

private def constructorVisit (limit root : Nat) (fields : List Nat) : Outcome Inferred :=
  let env := constructorEnvironment.getD empty
  let normal := NativeCoreExpandedFamilies.raw env constructorSnapshot.families [] 0 limit
  let infer := NativeCoreGhostSpineInference.runWithFamilyShapes normal [] 0 limit
    (NativeCoreGhostSort.isDataAt env) (NativeCoreGhostReferenceTypes.isBoxedAt env)
    (NativeCoreGhostSpineInference.visibleFamilyShape env 0) 31 []
  run infer (normal 31) limit 31 root 0 ⟨constructorSnapshot.arena,1⟩ 7 fields

/-- The initial graph is the checked native family arena. Its dependent
evidence field sees the first argument and the final result contains the
same index root. The outer inference visit has already spent one tick. -/
theorem admitted_dependent_constructor_meters_fields :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot constructorSnapshot) = true ∧
    (let complete := constructorVisit 54 10 [0,8]
     complete.state.steps = 54 ∧ complete.state.arena.size = 22 ∧
       complete.state.arena[16]? = some (.node .eq [0,0]) ∧
       complete.state.arena[17]? = some (.node (.ind 0 1) [0]) ∧
       complete.result.map Inferred.typeRoot = .ok 17) ∧
    (constructorVisit 54 9 [0]).result = .error (.outsideFragment 9) := by
  rw [NativeLoanMixedAdmission.checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeCoreGhostConstructorInference
