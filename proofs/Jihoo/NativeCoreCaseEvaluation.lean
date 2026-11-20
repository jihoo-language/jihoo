import Jihoo.NativeCoreCaseNormal

/-! The pure Case path from the original graph row. The root, motive, case
vector and scrutinee spend one shared clock. A known constructor selects
and applies an arm. The neutral path keeps or rebuilds the original row. -/
namespace Jihoo.NativeKernel.NativeCoreCaseEvaluation

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome normalizeOperands normalizeOperands_refines GhostNormalization
  nodeResult nodeResult_refines)
open Environment.FamilyIota (caseTerm)

private def useConstructor (family count : Nat) : Node → Bool
  | .node (.con actual constructor _) _ => actual == family && decide (constructor < count)
  | _ => false

private def isStrict : Node → Bool
  | .node .strict _ => true
  | _ => false

private def finishScrutinee (env : Environment) (limit depth root family count : Nat) (state : State)
    (before after : List Nat) (branches : List Nat) (scrutinee : Nat) : Outcome Nat :=
  match state.arena[scrutinee]? with
  | none => ⟨state, .error (.outsideFragment scrutinee)⟩
  | some head =>
      if useConstructor family count head then
        NativeCoreCaseNormal.run env limit depth state family branches scrutinee
      else if isStrict head then ⟨state, .error (.outsideFragment scrutinee)⟩
      else nodeResult state root (.caseOf family count) before after

private def finish (env : Environment) (limit depth root family count : Nat) (state : State) (before : List Nat) :
    List Nat → Outcome Nat
  | motive :: operands =>
      match operands[count]? with
      | some scrutinee =>
          finishScrutinee env limit depth root family count state before (motive :: operands)
            (operands.take count) scrutinee
      | none => ⟨state, .error (.outsideFragment root)⟩
  | [] => ⟨state, .error (.outsideFragment root)⟩

def run (env : Environment) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  let checked := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps := checked.2}
  match checked.1, depth with
  | .error reason, _ => ⟨entered, .error (.tick reason)⟩
  | .ok (), 0 => ⟨entered, .error (.tick (.depthLimit root))⟩
  | .ok (), inner + 1 =>
      match state.arena[root]? with
      | some (.node (.caseOf family count) refs) =>
          let normalized := normalizeOperands limit inner entered refs
          match normalized.result with
          | .error reason => ⟨normalized.state, .error reason⟩
          | .ok operands => finish env limit inner root family count normalized.state refs operands
      | _ => ⟨entered, .error (.outsideFragment root)⟩

/-- Split the common eliminator layout into its ordered arms and scrutinee. -/
theorem represented_branches (represented : RepresentsList arena refs terms)
    (shape : refs.length = count + 1) :
    ∃ (caseRefs : List Nat) (scrutineeRef : Nat) (cases : List Term) (scrutinee : Term),
      refs = caseRefs ++ [scrutineeRef] ∧ terms = cases ++ [scrutinee] ∧ caseRefs.length = count ∧
        RepresentsList arena caseRefs cases ∧ Represents arena scrutineeRef scrutinee := by
  induction count generalizing refs terms with
  | zero =>
      cases represented with
      | nil => cases shape
      | cons first rest =>
          cases rest with
          | nil => exact ⟨[], _, [], _, rfl, rfl, rfl, .nil, first⟩
          | cons _ _ => cases shape
  | succ count ih =>
      cases represented with
      | nil => cases shape
      | cons first rest =>
          obtain ⟨caseRefs, scrutineeRef, cases, scrutinee, rfl, rfl, size, caseRep, scrutineeRep⟩ :=
            ih rest (Nat.succ.inj shape)
          exact ⟨_ :: caseRefs, scrutineeRef, _ :: cases, scrutinee, rfl, rfl, congrArg Nat.succ size,
            .cons first caseRep, scrutineeRep⟩

private theorem recognized_case_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (scrutineeRep : Represents state.arena scrutineeRef scrutinee)
    (typed : LoanTyping.HasType env [] ctx true (caseTerm family motive cases scrutinee) type)
    (success : (NativeCoreCaseNormal.run env limit depth state family caseRefs scrutineeRef).result = .ok selected) :
    NativeCoreCaseNormal.Refines env state.arena
      (NativeCoreCaseNormal.run env limit depth state family caseRefs scrutineeRef).state.arena selected ctx
      (caseTerm family motive cases scrutinee) type := by
  cases scrutineeRep with
  | var read => simp [NativeCoreCaseNormal.run, read] at success
  | @node ref op refs terms read arity fields =>
      cases op <;> try solve | simp [NativeCoreCaseNormal.run, read] at success
      case con actual constructor count =>
          by_cases same : actual = family
          · subst actual
            have width : count = terms.length := arity.symm.trans (NativeCoreIdentical.represented_length fields)
            subst count
            exact NativeCoreCaseNormal.run_preserves history caseRep (.node read arity fields) typed success
          · simp [NativeCoreCaseNormal.run, read, same] at success

private theorem finish_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (read : state.arena[root]? = some (.node (.caseOf family count) before))
    (represented : RepresentsList state.arena refs terms) (arity : refs.length = count + 2)
    (typed : LoanTyping.HasType env [] ctx true (.node (.caseOf family count) terms) type)
    (success : (finish env limit depth root family count state before refs).result = .ok selected) :
    NativeCoreCaseNormal.Refines env state.arena (finish env limit depth root family count state before refs).state.arena
      selected ctx (.node (.caseOf family count) terms) type := by
  have neutral (computed : (nodeResult state root (.caseOf family count) before refs).result = .ok selected) :
      NativeCoreCaseNormal.Refines env state.arena
        (nodeResult state root (.caseOf family count) before refs).state.arena
        selected ctx (.node (.caseOf family count) terms) type := by
    obtain ⟨kept, backward, residual, residualRep, transform⟩ :=
      nodeResult_refines read represented arity computed
    exact ⟨kept, backward, residual, residualRep, transform.raw.forward, transform.raw.typed typed⟩
  cases represented with
  | nil => cases arity
  | @cons motiveRef motiveTerm _ _ motive rest =>
      obtain ⟨caseRefs, scrutineeRef, cases, scrutinee, rfl, rfl, countEq, caseRep, scrutineeRep⟩ :=
        represented_branches rest (Nat.succ.inj arity)
      subst count
      have casesLength : cases.length = caseRefs.length := (NativeCoreIdentical.represented_length caseRep).symm
      have lookup : (caseRefs ++ [scrutineeRef])[caseRefs.length]? = some scrutineeRef := by simp
      simp only [finish, lookup, List.take_left] at success ⊢
      have constructorCase
          (computed : (NativeCoreCaseNormal.run env limit depth state family caseRefs scrutineeRef).result = .ok selected) :
          NativeCoreCaseNormal.Refines env state.arena
            (NativeCoreCaseNormal.run env limit depth state family caseRefs scrutineeRef).state.arena
            selected ctx (.node (.caseOf family caseRefs.length) (motiveTerm :: (cases ++ [scrutinee]))) type := by
        simpa only [caseTerm, casesLength] using recognized_case_preserves history caseRep scrutineeRep
          (by simpa only [caseTerm, casesLength] using typed) computed
      have available : ∃ head, state.arena[scrutineeRef]? = some head := by
        cases scrutineeRep with
        | var found | node found _ _ => exact ⟨_, found⟩
      obtain ⟨head, found⟩ := available
      simp only [finishScrutinee, found] at success ⊢
      by_cases constructor : useConstructor family caseRefs.length head = true
      · rw [ite_eq_left constructor] at success ⊢
        exact constructorCase success
      · rw [ite_eq_right constructor] at success ⊢
        by_cases strict : isStrict head = true
        · rw [ite_eq_left strict] at success
          cases success
        · rw [ite_eq_right strict] at success ⊢
          exact neutral success

/-- From the original typed graph row, a successful native Case walk
preserves the exact dependent result, including all operand normalization. -/
theorem run_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root (.node (.caseOf family count) terms))
    (typed : LoanTyping.HasType env loans ctx mode (.node (.caseOf family count) terms) type)
    (success : (run env limit depth state root).result = .ok selected) :
    NativeCoreCaseNormal.Refines env state.arena (run env limit depth state root).state.arena selected ctx
      (.node (.caseOf family count) terms) type := by
  rcases ticked : NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root with ⟨status, spent⟩
  cases status with
  | error reason => simp [run, ticked] at success
  | ok charged =>
      cases charged
      cases depth with
      | zero => simp [run, ticked] at success
      | succ childDepth =>
          cases source with
          | node read shape represented =>
              rename_i inputRefs
              let entered := {state with steps := spent}
              let normalized := normalizeOperands limit childDepth entered inputRefs
              have visit : run env limit (childDepth + 1) state root =
                  match normalized.result with
                  | .error reason => ⟨normalized.state, .error reason⟩
                  | .ok operands => finish env limit childDepth root family count normalized.state inputRefs operands := by
                simp only [run, ticked, read, normalized, entered]
              rw [visit] at success ⊢
              cases reduced : normalized.result with
              | error reason => simp [reduced] at success
              | ok refs =>
                  simp only [reduced] at success ⊢
                  obtain ⟨kept, backward, countEq, residuals, residualRep, changes⟩ :=
                    normalizeOperands_refines history.wellFormed (state := entered) represented reduced
                  have transformed := GhostNormalization.node history.wellFormed (op := .caseOf family count)
                    (by intro equality; cases equality) rfl changes
                  obtain ⟨frame, preserves, residual, output, forward, originalType⟩ :=
                    finish_preserves history (kept.lookup read) residualRep (countEq.trans shape)
                      (transformed.raw.typed typed) success
                  exact ⟨kept.trans frame, fun old => preserves (backward old), residual, output,
                    transformed.raw.forward.trans forward, originalType⟩

namespace Examples

private def box (n : Term) : Term := .node (.ind 0 1) [n]
private def family : FamilyDeclaration :=
  ⟨true, 1, 1, [.pi true .u64 (.pi false (.buffer (.var 0)) (box (.var 1)))], 0⟩
private def signature : Signature := ⟨[⟨true, .u64, none⟩, ⟨false, .buffer (.var 0), none⟩], [.var 1]⟩
private def value : Term := .alloc (.natural 2) (.integer 0)
private def constructor : Term := .node (.con 0 0 2) [.natural 2, value]
private def source : Term := caseTerm 0 (.lam false (box (.natural 2)) (.buffer (.natural 2)))
  [.lam false (.buffer (.natural 2)) (.var 0)] (.app (.lam false .u64 constructor) (.natural 2))
private def requested : Term := .buffer (.uadd (.natural 1) (.natural 1))
private def env : Environment := ⟨#[⟨requested, source⟩], #[⟨family, [signature], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨20, 12⟩]
  families := [⟨true, 1, 1, 0, [17]⟩]
  arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1], .node (.ind 0 1) [0],
    .node .buffer [0], .node (.lam false) [3, 4], .var 0, .node (.lam false) [4, 6], .node (.con 0 0 2) [0, 2],
    .node .u64 [], .node (.lam false) [9, 8], .node .app [10, 0], .node (.caseOf 0 1) [5, 7, 11],
    .node .buffer [6], .var 1, .node (.ind 0 1) [14], .node (.pi false) [13, 15], .node (.pi true) [9, 16],
    .node (.natural 1) [], .node .uadd [18, 18], .node .buffer [19]]

/-- The exact admitted graph hides a constructor under an application. Case
normalizes the scrutinee before selecting the arm and retains the original
converted Buffer index after reducing the arm's application. -/
theorem admitted_case_exposes_constructor :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env 44 16 ⟨snapshot.arena, 0⟩ 12 = ⟨⟨snapshot.arena.push (.node .app [7, 2]), 44⟩, .ok 2⟩ ∧
    LoanTyping.HasType env [] [] true value requested := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨requested, source⟩] [family] = some env := by cbv
  have typed := ((LoanTyping.MixedProgram.checkProgram_sound installed).global_typing (index := 0) (declaration :=
    ⟨requested, source⟩) rfl).choose_spec.2
  have computed : run env 44 16 ⟨snapshot.arena, 0⟩ 12 = ⟨⟨snapshot.arena.push (.node .app [7, 2]), 44⟩, .ok 2⟩ := rfl
  have sourceRep : Represents snapshot.arena 12 source := decode_sound (fuel := 10) rfl
  obtain ⟨_, _, residual, represented, _, preserved⟩ :=
    run_preserves (LoanTyping.MixedProgram.checkProgram_sound installed) sourceRep typed (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents (snapshot.arena.push (.node .app [7, 2])) 2 value := decode_sound (fuel := 3) rfl
  rw [represented.unique expected] at preserved
  exact ⟨admitted, computed, preserved⟩

/-- The application's emitted row survives failure at the first reentry
tick, after all operands completed within budget. -/
theorem operand_budget_carries_to_reentry :
    run env 29 16 ⟨snapshot.arena, 0⟩ 12 =
      ⟨⟨snapshot.arena.push (.node .app [7, 2]), 30⟩, .error (.tick (.stepLimit 21))⟩ :=
  rfl

private def neutral (scrutinee : Term) : Term :=
  caseTerm 0 (.lam false (box (.natural 2)) (.buffer (.natural 2)))
    [.lam false (.buffer (.natural 2)) (.var 0)] scrutinee

private def neutralArena : Arena :=
  (((snapshot.arena.push (.node (.lam false) [3, 6])).push (.node .app [21, 6])).push
    (.node (.caseOf 0 1) [5, 7, 22])).push (.node (.caseOf 0 1) [5, 7, 6])

/-- A checked Case with a variable scrutinee reuses its row. If beta exposes
the same variable, the walk appends only the changed Case and keeps its type. -/
theorem checked_neutral_case_reuses_and_rebuilds :
    run env 11 16 ⟨neutralArena, 0⟩ 24 = ⟨⟨neutralArena, 11⟩, .ok 24⟩ ∧
    run env 19 16 ⟨neutralArena, 0⟩ 23 =
      ⟨⟨neutralArena.push (.node (.caseOf 0 1) [5, 7, 6]), 19⟩, .ok 25⟩ ∧
    LoanTyping.HasType env [] [⟨box (.natural 2), false⟩] true (neutral (.var 0)) requested := by
  let input := neutral (.app (.lam false (box (.natural 2)) (.var 0)) (.var 0))
  have original : LoanTyping.HasType env [] [⟨box (.natural 2), false⟩] true input requested :=
    LoanTyping.Checker.check_sound (fuel := 64) (by cbv)
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨requested, source⟩] [family] = some env := by cbv
  have computed : run env 19 16 ⟨neutralArena, 0⟩ 23 =
      ⟨⟨neutralArena.push (.node (.caseOf 0 1) [5, 7, 6]), 19⟩, .ok 25⟩ := rfl
  have sourceRep : Represents neutralArena 23 input := decode_sound (fuel := 10) rfl
  obtain ⟨_, _, residual, represented, _, preserved⟩ :=
    run_preserves (LoanTyping.MixedProgram.checkProgram_sound installed) sourceRep original
      (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents (neutralArena.push (.node (.caseOf 0 1) [5, 7, 6])) 25 (neutral (.var 0)) :=
    decode_sound (fuel := 10) rfl
  rw [represented.unique expected] at preserved
  exact ⟨rfl, computed, preserved⟩

end Examples

end Jihoo.NativeKernel.NativeCoreCaseEvaluation
