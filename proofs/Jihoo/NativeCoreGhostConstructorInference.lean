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

def ConstructorTable (env : Environment) (arena : Arena) (constructors : Nat → Nat → Option Nat) : Prop :=
  ∀ family constructor root, constructors family constructor = some root → ∃ entry signature source,
    env.families[family]? = some entry ∧ entry.signatures[constructor]? = some signature ∧
    Represents arena root source ∧ RawLend.Conv env (expand env source) (signatureTerm family signature)

theorem ConstructorTable.frame (checked : ConstructorTable env arena constructors) (kept : Prefix arena after) :
    ConstructorTable env after constructors := by
  intro family constructor root selected
  obtain ⟨entry,signature,source,found,signatureFound,represented,converted⟩ := checked family constructor root selected
  exact ⟨entry,signature,source,found,signatureFound,represented.frame kept,converted⟩

def constructorAt (rows : List NativeFamilyWire.FamilyRoots) (visible family constructor : Nat) : Option Nat := do
  let row ← rows[family]?
  if row.globals ≤ visible then row.constructors[constructor]? else none

theorem constructorAt_sound
    (history : LoanTyping.MixedProgram.History definitions
      (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : NativeFamilyWire.RepresentsFamilies arena familyRows familyTerms) (visible : Nat) :
    ConstructorTable env arena (constructorAt familyRows visible) := by
  intro family constructor root selected
  unfold constructorAt at selected
  obtain ⟨row,found,pending⟩ := Option.bind_eq_some_iff.mp selected
  split at pending
  · obtain ⟨entry,signature,source,familyFound,signatureFound,_,represented,converted⟩ :=
      NativeCoreConstructorTelescopeAlignment.checked_constructor_root
        (ScopedProgram.History.ofLoanMixed history) rows found pending
    exact ⟨entry,signature,source,familyFound,signatureFound,represented,converted⟩
  · cases pending

/-- The constructor table query precedes all of the charged checking and
does not allocate a new type. Its success selects the original raw root. -/
def runSelected (infer : Infer) (normal : Visit) (limit depth root contextLength : Nat)
    (constructors : Nat → Nat → Option Nat) (state : State) (family constructor : Nat)
    (fields : List Nat) : Outcome Inferred :=
  match constructors family constructor with
  | none => ⟨state,.error (.outsideFragment root)⟩
  | some signature => run infer normal limit depth root contextLength state signature fields

theorem runSelected_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runSelected infer normal limit depth root contextLength constructors state family constructor fields) := by
  unfold runSelected
  split
  · exact Progress.atState _ _
  · exact run_progress infers normalizes room

theorem runSelected_refines {family constructor count : Nat}
    (wf : UnifiedProgram.EnvWellFormed env) (checked : ConstructorTable env base constructors)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fieldsRep : RepresentsList state.arena fields args) (length : fields.length = count)
    (success : (runSelected infer normal limit depth root ctx.length constructors state family constructor fields).result =
      .ok answer)
    (ambient : Prefix (runSelected infer normal limit depth root ctx.length constructors state family constructor fields).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.node (.con family constructor count) args)
      (runSelected infer normal limit depth root ctx.length constructors state family constructor fields) answer := by
  unfold runSelected at success ambient ⊢
  split at success
  · cases success
  · rename_i rawRoot read
    simp only [read] at ambient ⊢
    obtain ⟨entry,signature,source,found,signatureFound,represented,converted⟩ := checked family constructor rawRoot read
    exact run_refines wf normalSound normalProgress inferSound inferProgress onBase room
      found signatureFound (represented.frame onBase) converted fieldsRep length success ambient retained

end Jihoo.NativeKernel.NativeCoreGhostConstructorInference
