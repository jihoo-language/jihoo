import Jihoo.NativeCoreEarlyNormal
import Jihoo.NativeCoreIterationNormal

/-! The shared pure graph walk visits retained Fold and Loop nodes in native
operand order. At a typed iteration boundary the same child walker can also
return the normalized initializer on zero. -/
namespace Jihoo.NativeKernel.NativeCoreIterationReentry

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (EarlyExtension GhostNormalization Outcome Progress Refines
  runWithExtensions runWithExtensions_progress runWithExtensions_refines
  visitOperands visitOperands_progress visitOperands_refines)
open NativeCoreIterationNormal (Change)

private def iteration : Op → Bool
  | .fold | .loop => true
  | _ => false

def extension (env : Environment) : EarlyExtension where
  accepts op := iteration op || (NativeCoreEarlyNormal.extension env).accepts op
  finish visit limit depth root state op refs :=
    if iteration op then NativeCoreIterationNormal.walk (visitOperands visit) state root op refs false
    else (NativeCoreEarlyNormal.extension env).finish visit limit depth root state op refs

theorem extension_metered (env : Environment) : (extension env).Metered := by
  intro visit limit depth root state op refs accepts metered
  by_cases counted : iteration op = true
  · simp only [extension, ite_eq_left counted]
    exact NativeCoreIterationNormal.walk_progress (visitOperands visit) (visitOperands_progress metered)
  · simpa only [extension, ite_eq_right counted] using
      (NativeCoreEarlyNormal.extension_metered env (depth := depth)
        (by simpa [extension, counted] using accepts) metered :
        Progress limit state ((NativeCoreEarlyNormal.extension env).finish visit limit depth root state op refs))

theorem extension_sound (history : ScopedProgram.History definitions declarations env) :
    (extension env).Sound env := by
  intro visit limit depth root state op refs terms selected accepts read represented size visitor success
  by_cases counted : iteration op = true
  · simp only [extension, ite_eq_left counted] at success ⊢
    obtain ⟨kept, backward, value⟩ := NativeCoreIterationNormal.walk_refines
      (visit := visitOperands visit) (allowZero := false) history.wellFormed
      (fun source done => visitOperands_refines source visitor done) read represented success
    exact ⟨kept, backward, value⟩
  · simp only [extension, ite_eq_right counted] at success ⊢
    exact NativeCoreEarlyNormal.extension_sound history
      (by simpa [extension, counted] using accepts) read represented size visitor success

def runNested (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  runWithExtensions (NativeCoreRecursiveView.extension env families) (extension env) limit depth state root

theorem runNested_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runNested env families limit depth state root) :=
  runWithExtensions_progress (NativeCoreRecursiveView.extension_metered env families)
    (extension_metered env) limit depth state root

theorem runNested_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (runNested env families limit depth state root).result = .ok selected) :
    Refines env state term (runNested env families limit depth state root) selected :=
  runWithExtensions_refines history.wellFormed
    (NativeCoreRecursiveView.extension_sound (ScopedProgram.History.ofLoanMixed history))
    (extension_sound (ScopedProgram.History.ofLoanMixed history)) source success

private def iterationRoot (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node op _) => iteration op
  | _ => false

/-- A typed endpoint can contract zero even when a dependent parent would
require a conversion equation for the discarded Fold or Loop. -/
def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  if iterationRoot state.arena root then
    NativeCoreIterationNormal.runWith (fun childDepth =>
      visitOperands (runNested env families limit childDepth)) limit depth state root
  else runNested env families limit depth state root

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run env families limit depth state root) := by
  unfold run
  split
  · apply NativeCoreIterationNormal.runWith_progress
    intro childDepth
    exact visitOperands_progress (runNested_progress env families limit childDepth)
  · exact runNested_progress env families limit depth state root

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (run env families limit depth state root).result = .ok selected) :
    NativeCoreIterationNormal.Refines env state term (run env families limit depth state root) selected := by
  by_cases counted : iterationRoot state.arena root = true
  · simp only [run, ite_eq_left counted] at success ⊢
    apply NativeCoreIterationNormal.runWith_refines history.wellFormed _ source success
    intro childDepth before refs terms found represented done
    exact visitOperands_refines represented (fun input selected => runNested_refines history input selected) done
  · simp only [run, ite_eq_right counted] at success ⊢
    obtain ⟨kept, backward, output, represented, change⟩ := runNested_refines history source success
    exact ⟨kept, backward, output, represented, Change.retained change⟩

/-- Exact-byte mixed admission supplies the original expanded type. Every
successful joint visit preserves it and the backward graph invariant. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : NativeProgramWire.Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, change⟩ := run_refines history source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, change.preservesExpanded typed⟩

theorem zero_fold_rigid (valid : EnvironmentDelta.Admissible env) :
    ¬ RawLend.Conv env (.fold (.natural 0) (.integer n) body) (.integer n) := by
  intro related
  exact RawLend.Conv.full_rigid_disjoint (op := .fold) (op' := .integer n) rfl rfl (by intro same; cases same)
    related valid

theorem zero_loop_rigid (valid : EnvironmentDelta.Admissible env) :
    ¬ RawLend.Conv env (.loop (.natural 0) motive (.integer n) body) (.integer n) := by
  intro related
  exact RawLend.Conv.full_rigid_disjoint (op := .loop) (op' := .integer n) rfl rfl (by intro same; cases same)
    related valid

namespace Examples

private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def owner : Term := .strict allocation (.node (.con 0 0 1) [allocation])
private def discard (rest : Term) : Term := .node (.drop 0) [owner, rest]
private def callback (count element : Term) : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) count) (.lam false element (.var 0)))
private def three : Term := .natural 3
private def zero : Term := .natural 0
private def seven : Term := .natural 7
private def nine : Term := .integer 9
private def motive : Term := .lam false .u64 .u64
private def nested := Term.eq (.loop three motive (discard seven) (callback three .u64)) seven
private def nestedResult := Term.eq (.loop three motive seven (callback three .u64)) seven
private def fold := Term.fold zero (discard nine) (callback zero .i64)
private def buffer := Term.buffer (.natural 2)
private def data := Term.node (.ind 0 0) []
private def family : FamilyDeclaration := ⟨true, 0, 0, [.pi false buffer data], 0⟩
private def signature : Signature := ⟨[⟨false, buffer, none⟩], []⟩
private def definitions : List Definitions.Definition := [⟨.prop, nested⟩, ⟨.i64, fold⟩]
private def env : Environment := ⟨#[⟨.prop, nested⟩, ⟨.i64, fold⟩], #[⟨family, [signature], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨10, 22⟩, ⟨12, 29⟩]
  families := [⟨true, 0, 0, 0, [5]⟩]
  arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
    .node (.ind 0 0) [], .node .buffer [0], .node (.pi false) [4, 3],
    .node (.con 0 0 1) [2], .node .strict [2, 6], .node (.natural 7) [],
    .node (.drop 0) [7, 8], .node .prop [], .node .u64 [], .node .i64 [],
    .node (.natural 3) [], .node (.natural 0) [], .var 0, .node (.lam false) [11, 11],
    .node .lt [15, 13], .node (.lam false) [11, 15], .node (.lam true) [17, 18],
    .node (.lam false) [11, 19], .node .loop [13, 16, 9, 20], .node .eq [21, 8],
    .node (.integer 9) [], .node (.drop 0) [7, 23], .node .lt [15, 14],
    .node (.lam false) [12, 15], .node (.lam true) [25, 26], .node (.lam false) [11, 27],
    .node .fold [14, 24, 28]]

private def rebuilt := (snapshot.arena.push (.node .loop [13, 16, 8, 20])).push (.node .eq [30, 8])

private theorem checkedHistory : LoanTyping.MixedProgram.History definitions [family] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)

/-- The admitted proposition retains its counted Loop beneath Eq. The
initializer uses the shared Drop dispatch and the discarded owner is skipped. -/
theorem checked_nested_loop_with_drop :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env snapshot.families 18 24 ⟨snapshot.arena, 0⟩ 22 = ⟨⟨rebuilt, 18⟩, .ok 31⟩ ∧
    LoanTyping.HasType env [] [] true nestedResult .prop := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have original := (checkedHistory.global_typing (index := 0) (declaration := ⟨.prop, nested⟩) rfl).choose_spec.2
  have source : Represents snapshot.arena 22 nested := decode_sound (fuel := 18) rfl
  have computed : run env snapshot.families 18 24 ⟨snapshot.arena, 0⟩ 22 = ⟨⟨rebuilt, 18⟩, .ok 31⟩ := by cbv
  obtain ⟨_, _, residual, represented, change⟩ := run_refines checkedHistory source (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents rebuilt 31 nestedResult := decode_sound (fuel := 12) rfl
  have typed : LoanTyping.HasType env [] [] true residual .prop := change.preserves original
  exact ⟨admitted, computed, represented.unique expected ▸ typed⟩

/-- An admitted zero Fold returns the result of the joint Drop visit. The
budget stops exactly at the initializer's last visit and never starts the body. -/
theorem checked_zero_fold_with_drop :
    run env snapshot.families 4 24 ⟨snapshot.arena, 0⟩ 29 = ⟨⟨snapshot.arena, 4⟩, .ok 23⟩ ∧
    run env snapshot.families 3 24 ⟨snapshot.arena, 0⟩ 29 =
      ⟨⟨snapshot.arena, 4⟩, .error (.tick (.stepLimit 23))⟩ ∧
    LoanTyping.HasType env [] [] true nine .i64 := by
  have original := (checkedHistory.global_typing (index := 1) (declaration := ⟨.i64, fold⟩) rfl).choose_spec.2
  have source : Represents snapshot.arena 29 fold := decode_sound (fuel := 18) rfl
  have computed : run env snapshot.families 4 24 ⟨snapshot.arena, 0⟩ 29 = ⟨⟨snapshot.arena, 4⟩, .ok 23⟩ := by cbv
  obtain ⟨_, _, residual, represented, change⟩ := run_refines checkedHistory source (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents snapshot.arena 23 nine := decode_sound (fuel := 2) rfl
  have typed : LoanTyping.HasType env [] [] true residual .i64 := change.preserves original
  exact ⟨computed, by cbv, represented.unique expected ▸ typed⟩

end Examples

end Jihoo.NativeKernel.NativeCoreIterationReentry
