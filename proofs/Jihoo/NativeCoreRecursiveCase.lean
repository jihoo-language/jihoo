import Jihoo.NativeCoreRecursiveElim

/-! Case uses the same recursive visitor as Elim and the ordinary pure
operators. The constructor guard checks the signature before publishing a
raw family contraction. Authentic typing supplies that guard at a native
constructor fast path. -/
namespace Jihoo.NativeKernel.NativeCoreRecursiveCase

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress Refines PostExtension nodeResult nodeResult_refines
  nodeResult_progress runWithExtension runWithExtension_progress runWithExtension_refines)
open NativeCoreCaseNormal (appendApplications appendApplications_refines appendApplications_progress
  represented_get represented_drop)
open NativeCoreCaseEvaluation (represented_branches)
open NativeCoreElimNormal (selectSignature selectSignature_sound represented_ref iota_normalization)
open FamilyIota (caseTerm)

def applyFields (visit : State → Nat → Outcome Nat) (state : State) (branch : Nat)
    (fields : List Nat) : Outcome Nat :=
  let built := appendApplications state branch fields
  match built.result with
  | .error reason => ⟨built.state, .error reason⟩
  | .ok root => visit built.state root

def finishScrutinee (env : Environment) (visit : State → Nat → Outcome Nat) (root family count : Nat)
    (state : State) (before after cases : List Nat) (scrutinee : Nat) : Outcome Nat :=
  let neutral := nodeResult state root (.caseOf family count) before after
  match state.arena[scrutinee]? with
  | none | some (.node .strict _) => ⟨state, .error (.outsideFragment scrutinee)⟩
  | some (.node (.con actual constructor _) fields) =>
      if actual = family ∧ constructor < cases.length then
        match selectSignature env family actual constructor cases fields.length with
        | some (entry, _, branch) =>
            if entry.declaration.data then applyFields visit state branch (fields.drop entry.declaration.params)
            else ⟨state, .error (.outsideFragment scrutinee)⟩
        | none => ⟨state, .error (.outsideFragment scrutinee)⟩
      else neutral
  | some _ => neutral

private def finish (env : Environment) (visit : State → Nat → Outcome Nat) (root family count : Nat)
    (state : State) (before : List Nat) : List Nat → Outcome Nat
  | motive :: operands =>
      match operands[count]? with
      | some scrutinee => finishScrutinee env visit root family count state before (motive :: operands)
          (operands.take count) scrutinee
      | none => ⟨state, .error (.outsideFragment root)⟩
  | [] => ⟨state, .error (.outsideFragment root)⟩

def extension (env : Environment) : PostExtension where
  accepts
    | .caseOf .. | .elim .. => true
    | _ => false
  finish visit limit depth root state op before after :=
    match op with
    | .caseOf family count => finish env visit root family count state before after
    | _ => (NativeCoreRecursiveElim.extension env).finish visit limit depth root state op before after

def run (env : Environment) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runWithExtension (extension env) limit depth state root

private theorem applyFields_progress (visitor : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (applyFields visit state branch fields) := by
  obtain ⟨kept, clock, _, _⟩ := appendApplications_progress state branch fields
  cases emitted : (appendApplications state branch fields).result with
  | error reason =>
      simp only [applyFields, emitted]
      exact ⟨kept, Nat.le_of_eq clock.symm, fun room => Nat.le.step (clock ▸ room), fun _ _ found => by cases found⟩
  | ok root =>
      simp only [applyFields, emitted]
      have progressed := visitor (appendApplications state branch fields).state root
      exact ⟨kept.trans progressed.kept, Nat.le_trans (Nat.le_of_eq clock.symm) progressed.monotone,
        fun room => progressed.bounded (clock ▸ room), fun room => progressed.accepted (clock ▸ room)⟩

private theorem finish_progress (visitor : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (finish env visit root family count state before after) := by
  simp only [finish, finishScrutinee]
  repeat' first
    | exact Progress.atState _ _
    | exact nodeResult_progress _ _ _ _ _ _
    | exact applyFields_progress visitor
    | split

theorem extension_metered (env : Environment) : (extension env).Metered := by
  intro visit limit depth root state op before after accepts visitor
  cases op <;> try contradiction
  case caseOf family count => exact finish_progress visitor
  case elim family count =>
    exact NativeCoreRecursiveElim.extension_metered env (op := .elim family count)
      (depth := depth) (before := before) rfl visitor

private theorem applyFields_refines (history : ScopedProgram.History definitions declarations env)
    (visitor : ∀ {state root term selected}, Represents state.arena root term →
      (visit state root).result = .ok selected → Refines env state term (visit state root) selected)
    (branchRep : Represents state.arena branchRef branch)
    (fieldsRep : RepresentsList state.arena fieldRefs values)
    (contraction : FamilyIota.Root env input (applications branch values))
    (success : (applyFields visit state branchRef fieldRefs).result = .ok selected) :
    Refines env state input (applyFields visit state branchRef fieldRefs) selected := by
  cases emitted : (appendApplications state branchRef fieldRefs).result with
  | error reason => simp [applyFields, emitted] at success
  | ok spine =>
      simp only [applyFields, emitted] at success ⊢
      obtain ⟨kept, backward, _, represented⟩ := appendApplications_refines branchRep fieldsRep emitted
      obtain ⟨later, laterBackward, output, outputRep, changes⟩ := visitor represented success
      exact ⟨kept.trans later, fun old => laterBackward (backward old), output, outputRep,
        (iota_normalization history contraction).trans changes⟩

private theorem finishScrutinee_refines
    (history : ScopedProgram.History definitions declarations env)
    (visitor : ∀ {state root term selected}, Represents state.arena root term →
      (visit state root).result = .ok selected → Refines env state term (visit state root) selected)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee value)
    (neutral : (nodeResult state root (.caseOf family count) before after).result = .ok selected →
      Refines env state (caseTerm family motive cases value)
        (nodeResult state root (.caseOf family count) before after) selected)
    (success : (finishScrutinee env visit root family count state before after caseRefs scrutinee).result = .ok selected) :
    Refines env state (caseTerm family motive cases value)
      (finishScrutinee env visit root family count state before after caseRefs scrutinee) selected := by
  cases valueRep with
  | var read => simpa only [finishScrutinee, read] using neutral (by simpa only [finishScrutinee, read] using success)
  | @node _ op fieldRefs values read arity fields =>
      cases op
      all_goals try solve
        | simpa only [finishScrutinee, read] using neutral (by simpa only [finishScrutinee, read] using success)
        | simp [finishScrutinee, read] at success
      case con actual constructor width =>
        by_cases fast : actual = family ∧ constructor < caseRefs.length
        · simp only [finishScrutinee, read, ite_eq_left fast] at success ⊢
          cases picked : selectSignature env family actual constructor caseRefs fieldRefs.length with
          | none => simp [picked] at success
          | some triple =>
              obtain ⟨entry, signature, branchRef⟩ := triple
              simp only [picked] at success ⊢
              by_cases data : entry.declaration.data = true
              · simp only [ite_eq_left data] at success ⊢
                obtain ⟨same, found, selectedBranch, signatureRead, branches, fieldCount⟩ := selectSignature_sound picked
                subst actual
                obtain ⟨branch, branchFound, branchRep⟩ := represented_ref caseRep selectedBranch
                have branchWidth := NativeCoreIdentical.represented_length caseRep
                have fieldsWidth := NativeCoreIdentical.represented_length fields
                have sourceWidth : width = values.length := arity.symm.trans fieldsWidth
                subst width
                have contraction := FamilyIota.Root.caseOf (motive := motive) found data signatureRead branchFound
                  (branchWidth.symm.trans branches) (fieldsWidth.symm.trans fieldCount)
                exact applyFields_refines history visitor branchRep (represented_drop fields _) contraction success
              · simp [data] at success
        · simpa only [finishScrutinee, read, ite_eq_right fast] using
            neutral (by simpa only [finishScrutinee, read, ite_eq_right fast] using success)

/-- The metadata guard is forced by authentic typing on a constructor-headed
Case. In the actual native fast path the same selected arm, parameter
skip and visitor are used. -/
theorem finish_typed_constructor
    (history : ScopedProgram.History definitions declarations env)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (fieldsRep : RepresentsList state.arena fieldRefs values)
    (read : state.arena[scrutinee]? = some (.node (.con family constructor values.length) fieldRefs))
    (typed : LoanTyping.HasType env loans ctx mode
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ entry branchRef, env.families[family]? = some entry ∧ caseRefs[constructor]? = some branchRef ∧
      finishScrutinee env visit root family count state before after caseRefs scrutinee =
        applyFields visit state branchRef (fieldRefs.drop entry.declaration.params) := by
  obtain ⟨entry, signature, branch, found, data, sig, countArms, countFields, selected⟩ :=
    LoanTyping.FamilyIota.checked_case_alignment history (typed.ghost [])
  obtain ⟨branchRef, selectedRef, _⟩ := represented_get caseRep selected
  have arms := (NativeCoreIdentical.represented_length caseRep).trans countArms
  have fields := (NativeCoreIdentical.represented_length fieldsRep).trans countFields
  have chosen : selectSignature env family family constructor caseRefs fieldRefs.length =
      some (entry, signature, branchRef) := by
    simp [selectSignature, found, selectedRef, sig, arms, fields]
  have inRange := (List.getElem?_eq_some_iff.mp selectedRef).1
  exact ⟨entry, branchRef, found, selectedRef, by
    simp [finishScrutinee, read, chosen, data, inRange]⟩

theorem extension_sound (history : ScopedProgram.History definitions declarations env) :
    (extension env).Sound env := by
  constructor
  · intro op accepted
    cases op <;> try contradiction
    all_goals
      refine ⟨?_, rfl⟩
      intro equal
      cases equal
  · intro visit limit depth root state op before after terms selected accepted read represented size visitor success
    cases op <;> try contradiction
    case elim family count =>
      exact (NativeCoreRecursiveElim.extension_sound history).2
        (limit := limit) (depth := depth) rfl read represented size visitor success
    case caseOf family count =>
      have neutral := nodeResult_refines (env := env) read represented size (reuse := true) (selected := selected)
      cases represented with
      | nil => cases size
      | @cons motiveRef motive _ _ motiveRep rest =>
          obtain ⟨caseRefs, scrutRef, arms, value, rfl, rfl, width, caseRep, valueRep⟩ :=
            represented_branches rest (Nat.succ.inj size)
          subst count
          have count := NativeCoreIdentical.represented_length caseRep
          have lookup : (caseRefs ++ [scrutRef])[caseRefs.length]? = some scrutRef := by simp
          simp only [extension, finish, lookup, List.take_left] at success ⊢
          simpa only [caseTerm, ← count] using
            finishScrutinee_refines history visitor caseRep valueRep
              (by simpa only [caseTerm, ← count] using neutral) success

theorem run_progress (env : Environment) (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run env limit depth state root) :=
  runWithExtension_progress (extension_metered env) limit depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (run env limit depth state root).result = .ok selected) :
    Refines env state term (run env limit depth state root) selected :=
  runWithExtension_refines history.wellFormed (extension_sound (ScopedProgram.History.ofLoanMixed history)) source success

open NativeProgramWire

/-- Exact-byte admission constructs the environment for the joint walker.
Each successful visit of a stored source definition keeps its declared type. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run env limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run env limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, represented, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, raw, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at represented history found
  obtain ⟨kept, preserves, residual, residualRep, change⟩ := run_refines history source.2 success
  exact ⟨entry, residual, read, kept, preserves backward, residualRep, change.expanded.typed typed⟩

namespace Examples

private def box : Term := .node (.ind 0 0) []
private def bufferType : Term := .buffer (.natural 2)
private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def motive : Term := .lam false box bufferType
private def branch : Term := .lam false bufferType (.var 0)
private def constructor : Term := .node (.con 0 0 1) [allocation]
private def source : Term := .app (.lam false box (caseTerm 0 motive [branch] (.var 0))) constructor
private def requested : Term := .buffer (.uadd (.natural 1) (.natural 1))
private def family : FamilyDeclaration := ⟨true, 0, 0, [.pi false bufferType box], 0⟩
private def signature : Signature := ⟨[⟨false, bufferType, none⟩], []⟩
private def env : Environment := ⟨#[⟨requested, source⟩], #[⟨family, [signature], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨15, 11⟩]
  families := [⟨true, 0, 0, 0, [12]⟩]
  arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
    .node (.ind 0 0) [], .node .buffer [0], .node (.lam false) [3, 4], .var 0,
    .node (.lam false) [4, 6], .node (.con 0 0 1) [2], .node (.caseOf 0 1) [5, 7, 6],
    .node (.lam false) [3, 9], .node .app [10, 8], .node (.pi false) [4, 3],
    .node (.natural 1) [], .node .uadd [13, 13], .node .buffer [14]]

private def opening : Arena := snapshot.arena.push (.node (.caseOf 0 1) [5, 7, 8])
private def finished : Arena := opening.push (.node .app [7, 2])

/-- Before beta the Case retains its neutral row. Substitution emits the
constructor-headed Case and the same visitor handles both its iota and beta. -/
theorem admitted_beta_opens_neutral_case :
    let output := run env 128 32 ⟨snapshot.arena, 0⟩ 11
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    output.result = .ok 2 ∧ output.state.arena = finished ∧
    LoanTyping.HasType env [] [] true allocation requested := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have checked : LoanTyping.MixedProgram.checkProgram 64 128 [⟨requested, source⟩] [family] = some env := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound checked
  have typed := (history.global_typing (index := 0) (declaration := ⟨requested, source⟩) rfl).choose_spec.2
  have original : Represents snapshot.arena 11 source := decode_sound (fuel := 14) rfl
  have computed : (run env 128 32 ⟨snapshot.arena, 0⟩ 11).result = .ok 2 := rfl
  have exactArena : (run env 128 32 ⟨snapshot.arena, 0⟩ 11).state.arena = finished := rfl
  obtain ⟨_, _, residual, represented, change⟩ := run_refines history original computed
  rw [exactArena] at represented
  have expected : Represents finished 2 allocation := decode_sound (fuel := 5) rfl
  have preserved := change.raw.typed typed
  rw [represented.unique expected] at preserved
  exact ⟨admitted, computed, exactArena, preserved⟩

theorem beta_reentry_exhaustion_keeps_substituted_case :
    run env 31 32 ⟨snapshot.arena, 0⟩ 11 =
      ⟨⟨opening, 32⟩, .error (.tick (.stepLimit 16))⟩ := rfl

end Examples

end Jihoo.NativeKernel.NativeCoreRecursiveCase
