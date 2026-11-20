import Jihoo.NativeCoreCaseStrict
import Jihoo.NativeCoreValueTraversal
import Jihoo.NativeLoanFunctionInversion

/-! The pure post-operand App branch for a neutral conditional callee.
The argument is shifted only for the evidence-bound true arm. Both Apps and
the enclosing conditional are appended before the shared child visit. -/
namespace Jihoo.NativeKernel.NativeCoreConditionalApplication

open NativeArena NativeCoreGraph Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreValueContexts (Change)

local notation "HasType" => LoanTyping.HasType

def testOp (equality : Bool) : Op := if equality then .ifEq else .ifLt

def evidence (equality : Bool) (left right : Term) : Term :=
  if equality then .eq left right else .lt left right

def conditional (equality : Bool) (left right yes no : Term) : Term :=
  .node (testOp equality) [left, right, yes, no]

def distribute (equality : Bool) (left right yes no argument : Term) : Term :=
  conditional equality left right (.app yes (argument.rename Nat.succ)) (.app no argument)

private def ConditionalPremises (env : Environment) (ctx : Context) (term type : Term) : Prop :=
  match term with
  | .ifLt left right yes no =>
      ∃ internal, HasType env [] ctx true left .u64 ∧ HasType env [] ctx true right .u64 ∧
        HasType env [] (⟨.lt left right, true⟩ :: ctx) true yes (internal.rename Nat.succ) ∧
        HasType env [] ctx true no internal ∧ LoanTyping.Conversion.Conv env internal type
  | .ifEq left right yes no =>
      ∃ internal, HasType env [] ctx true left .u64 ∧ HasType env [] ctx true right .u64 ∧
        HasType env [] (⟨.eq left right, true⟩ :: ctx) true yes (internal.rename Nat.succ) ∧
        HasType env [] ctx true no internal ∧ LoanTyping.Conversion.Conv env internal type
  | _ => True

private theorem ConditionalPremises.convert (view : ConditionalPremises env ctx term type)
    (converted : LoanTyping.Conversion.Conv env type target) : ConditionalPremises env ctx term target := by
  fun_cases ConditionalPremises env ctx term type <;> simp only [ConditionalPremises] at view ⊢
  all_goals first
    | exact view
    | obtain ⟨internal, left, right, yes, no, result⟩ := view
      exact ⟨internal, left, right, yes, no, result.trans converted⟩

private theorem conditional_premises (typed : HasType env loans ctx mode term type) :
    ConditionalPremises env ctx term type := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => ConditionalPremises env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case ifLt left right yes no _ _ _ _ =>
    exact ⟨_, left.ghost [], right.ghost [], yes.ghost [], no.ghost [], .refl _⟩
  case ifEq left right yes no _ _ _ _ =>
    exact ⟨_, left.ghost [], right.ghost [], yes.ghost [], no.ghost [], .refl _⟩
  case dataElim => split <;> trivial
  case convert _ converted ih => exact ih.convert converted

private theorem exact_conditional_premises (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] ctx true (conditional equality left right yes no) type) :
    HasType env [] ctx true left .u64 ∧ HasType env [] ctx true right .u64 ∧
      HasType env [] (⟨evidence equality left right, true⟩ :: ctx) true yes (type.rename Nat.succ) ∧
      HasType env [] ctx true no type := by
  cases equality
  · obtain ⟨_, lhs, rhs, yesTyped, noTyped, converted⟩ := conditional_premises typed
    exact ⟨lhs, rhs, yesTyped.convert (converted.renaming Nat.succ wf.closed), noTyped.convert converted⟩
  · obtain ⟨_, lhs, rhs, yesTyped, noTyped, converted⟩ := conditional_premises typed
    exact ⟨lhs, rhs, yesTyped.convert (converted.renaming Nat.succ wf.closed), noTyped.convert converted⟩

private theorem ghost_app (fn : HasType env [] ctx true fnTerm (.pi erased domain result))
    (arg : HasType env [] ctx true argument domain) :
    HasType env [] ctx true (.app fnTerm argument) (result.subst (single argument)) :=
  .app fn arg (Or.inl rfl)

/-- The distributed conditional has the original dependent application type,
including any conversion used to check the callee or the application. -/
theorem distribute_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.app (conditional equality left right yes no) argument) type) :
    HasType env [] ctx true (distribute equality left right yes no argument) type := by
  obtain ⟨erased, domain, result, fn, arg, _, converted⟩ := (typed.ghost []).appView
  obtain ⟨lhs, rhs, yesTyped, noTyped⟩ := exact_conditional_premises wf fn
  have raised := arg.ghostWeaken wf (evidence equality left right) true
  have shiftedYes : HasType env [] (⟨evidence equality left right, true⟩ :: ctx) true yes
      (.pi erased (domain.rename Nat.succ) (result.rename (Indexed.liftRenaming Nat.succ))) := by
    simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using yesTyped
  have yesApp := ghost_app shiftedYes raised
  rw [← Term.rename_instantiate result argument Nat.succ] at yesApp
  have noApp := ghost_app noTyped arg
  have branch : HasType env [] ctx true (distribute equality left right yes no argument)
      (result.subst (single argument)) := by
    cases equality
    · exact .ifLt lhs rhs yesApp noApp
    · exact .ifEq lhs rhs yesApp noApp
  exact branch.convert converted

theorem distribute_change (wf : UnifiedProgram.EnvWellFormed env) :
    Change env (.app (conditional equality left right yes no) argument)
      (distribute equality left right yes no argument) := by
  constructor
  · exact distribute_preserves wf
  · simp only [conditional, distribute, EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs,
      EnvironmentDelta.expand_renaming wf.admissible]
    exact distribute_preserves (equality := equality) wf

private def shiftArgument (limit childDepth : Nat) (state : State) (argument : Nat) : Outcome Nat :=
  let shifted := NativeCoreTransformExact.shift limit childDepth state argument 1 0
  ⟨shifted.state, shifted.result.mapError .substitution⟩

private theorem shiftArgument_success (success : (shiftArgument limit childDepth state argument).result = .ok shifted) :
    (NativeCoreTransformExact.shift limit childDepth state argument 1 0).result = .ok shifted := by
  generalize original : NativeCoreTransformExact.shift limit childDepth state argument 1 0 = raw at ⊢
  cases status : raw.result <;> simp [shiftArgument, original, status, Except.mapError] at success ⊢
  exact success

private theorem shiftArgument_progress (limit childDepth : Nat) (state : State) (argument : Nat) :
    Progress limit state (shiftArgument limit childDepth state argument) := by
  have facts := NativeCoreTransformExact.run_progress limit childDepth state argument (.shift 1) 0
  exact ⟨facts.kept, facts.monotone, facts.bounded, fun room value found =>
    facts.accepted room value (shiftArgument_success found)⟩

private theorem shiftArgument_refines (source : Represents state.arena argument term)
    (success : (shiftArgument limit childDepth state argument).result = .ok shifted) :
    let after := (shiftArgument limit childDepth state argument).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after shifted (term.rename Nat.succ) := by
  obtain ⟨kept, backward, residual, shifts, represented⟩ :=
    NativeCoreTransformExact.shift_refines source (shiftArgument_success success)
  change PartialRenaming.shift 1 0 term = some residual at shifts
  have raises : PartialRenaming.raiseIndex 0 (1 : Int).toNat = Nat.succ := by
    funext x
    simp [PartialRenaming.raiseIndex, Nat.succ_eq_add_one]
  rw [PartialRenaming.shift_nonnegative (by decide), raises] at shifts
  cases shifts
  exact ⟨kept, backward, represented⟩

/-- The shift consumes the shared clock. The three appends keep it and
commit separately in the order of the corresponding native adds. -/
def assemble (limit childDepth : Nat) (state : State) (equality : Bool)
    (left right yes no argument : Nat) : Outcome Nat :=
  (shiftArgument limit childDepth state argument).next fun afterShift shifted =>
    (append afterShift .app [yes, shifted]).next fun afterYes yesApp =>
      (append afterYes .app [no, argument]).next fun afterNo noApp =>
        append afterNo (testOp equality) [left, right, yesApp, noApp]

theorem assemble_progress (limit childDepth : Nat) (state : State) (equality : Bool)
    (left right yes no argument : Nat) :
    Progress limit state (assemble limit childDepth state equality left right yes no argument) :=
  (shiftArgument_progress _ _ _ _).next fun _ =>
    (append_progress _ _ _).next fun _ =>
      (append_progress _ _ _).next fun _ => append_progress _ _ _

theorem assemble_refines
    (lhs : Represents state.arena left x) (rhs : Represents state.arena right y)
    (yesBranch : Represents state.arena yes yesTerm) (noBranch : Represents state.arena no noTerm)
    (arg : Represents state.arena argument argTerm)
    (success : (assemble limit childDepth state equality left right yes no argument).result = .ok selected) :
    let after := (assemble limit childDepth state equality left right yes no argument).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (distribute equality x y yesTerm noTerm argTerm) := by
  unfold assemble at success ⊢
  obtain ⟨shifted, shiftedOk, shiftedNext⟩ := Outcome.next_success success
  obtain ⟨shiftKept, shiftBackward, shiftedRep⟩ := shiftArgument_refines arg shiftedOk
  rw [shiftedNext] at success ⊢
  obtain ⟨yesApp, yesOk, yesNext⟩ := Outcome.next_success success
  obtain ⟨yesKept, yesBackward, yesRep⟩ :=
    append_refines (.cons (yesBranch.frame shiftKept) (.cons shiftedRep .nil)) rfl yesOk
  rw [yesNext] at success ⊢
  obtain ⟨noApp, noOk, noNext⟩ := Outcome.next_success success
  have throughYes := shiftKept.trans yesKept
  obtain ⟨noKept, noBackward, noRep⟩ :=
    append_refines (.cons (noBranch.frame throughYes) (.cons (arg.frame throughYes) .nil)) rfl noOk
  rw [noNext] at success ⊢
  have throughNo := throughYes.trans noKept
  obtain ⟨branchKept, branchBackward, branchRep⟩ :=
    append_refines (.cons (lhs.frame throughNo) (.cons (rhs.frame throughNo)
      (.cons (yesRep.frame noKept) (.cons noRep .nil)))) (by cases equality <;> rfl) success
  exact ⟨throughNo.trans branchKept,
    fun backward => branchBackward (noBackward (yesBackward (shiftBackward backward))), branchRep⟩

/-- Dispatch on the graph row of the previously normalized callee, then
reenter on the newly appended conditional at the same child depth as shift. -/
def finish (visit : State → Nat → Outcome Nat) (limit childDepth : Nat)
    (state : State) (callee argument : Nat) : Outcome Nat :=
  match state.arena[callee]? with
  | some (.node .ifEq [left, right, yes, no]) =>
      (assemble limit childDepth state true left right yes no argument).next visit
  | some (.node .ifLt [left, right, yes, no]) =>
      (assemble limit childDepth state false left right yes no argument).next visit
  | _ => ⟨state, .error (.outsideFragment callee)⟩

theorem finish_progress (metered : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (finish visit limit childDepth state callee argument) := by
  unfold finish
  split
  · exact (assemble_progress _ _ _ _ _ _ _ _ _).next (fun _ => metered _ _)
  · exact (assemble_progress _ _ _ _ _ _ _ _ _).next (fun _ => metered _ _)
  · exact Progress.atState _ _

private theorem finish_known (read : state.arena[callee]? = some (.node (testOp equality) [left, right, yes, no])) :
    finish visit limit childDepth state callee argument =
      (assemble limit childDepth state equality left right yes no argument).next visit := by
  cases equality <;> simp [finish, testOp] at read ⊢ <;> simp [read]

/-- The input representation supplies the exact conditional operands of the
selected graph row. A sound reentry continues from the distributed application
and preserves the checked type of the source App. -/
theorem finish_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (visitor : ∀ {start root input selected}, Represents start.arena root input →
      (visit start root).result = .ok selected →
      NativeCoreValueTraversal.Refines env start input (visit start root) selected)
    (calleeRep : Represents state.arena callee (conditional equality left right yes no))
    (argRep : Represents state.arena argument argTerm)
    (success : (finish visit limit childDepth state callee argument).result = .ok selected) :
    NativeCoreValueTraversal.Refines env state (.app (conditional equality left right yes no) argTerm)
      (finish visit limit childDepth state callee argument) selected := by
  unfold conditional at calleeRep
  cases calleeRep with
  | node read _ children =>
    cases children with
    | cons leftRep tail =>
      cases tail with
      | cons rightRep tail =>
        cases tail with
        | cons yesRep tail =>
          cases tail with
          | cons noRep tail =>
            cases tail with
            | nil =>
              rw [finish_known read] at success ⊢
              obtain ⟨root, prepared, reentry⟩ := Outcome.next_success success
              obtain ⟨kept, backward, represented⟩ := assemble_refines leftRep rightRep yesRep noRep argRep prepared
              rw [reentry] at success ⊢
              obtain ⟨laterKept, laterBackward, residual, residualRep, change⟩ := visitor represented success
              exact ⟨kept.trans laterKept, laterBackward ∘ backward, residual, residualRep,
                (distribute_change wf).trans change⟩

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit childDepth : Nat)
    (state : State) (callee argument : Nat) : Outcome Nat :=
  finish (NativeCoreValueTraversal.run env families limit childDepth) limit childDepth state callee argument

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit childDepth : Nat) :
    Progress limit state (run env families limit childDepth state callee argument) :=
  finish_progress (NativeCoreValueTraversal.run_progress env families limit childDepth)

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (calleeRep : Represents state.arena callee (conditional equality left right yes no))
    (argRep : Represents state.arena argument argTerm)
    (success : (run env families limit childDepth state callee argument).result = .ok selected) :
    NativeCoreValueTraversal.Refines env state (.app (conditional equality left right yes no) argTerm)
      (run env families limit childDepth state callee argument) selected :=
  finish_refines history.wellFormed (fun rep done => NativeCoreValueTraversal.run_refines history rep done)
    calleeRep argRep success

theorem run_preserves {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (calleeRep : Represents state.arena callee (conditional equality left right yes no))
    (argRep : Represents state.arena argument argTerm)
    (typed : HasType env loans ctx mode (.app (conditional equality left right yes no) argTerm) type)
    (success : (run env families limit childDepth state callee argument).result = .ok selected) :
    let output := run env families limit childDepth state callee argument
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ HasType env [] ctx true residual type := by
  obtain ⟨kept, backward, residual, rep, change⟩ := run_refines history calleeRep argRep success
  exact ⟨kept, backward, residual, rep, change.raw (typed.ghost [])⟩

namespace Examples

private def identity : Term := .lam false .u64 (.var 0)
private def callee : Term := conditional true (.var 0) (.natural 0) identity identity
private def body : Term := .app callee (.var 0)
private def source : Term := .lam false .u64 body
private def sourceType : Term := .pi false .u64 .u64
private def env : Environment := ⟨#[⟨sourceType, source⟩], #[]⟩
private def result : Term := .ifEq (.var 0) (.natural 0) (.var 1) (.var 0)

private def snapshot : NativeFamilyWire.Snapshot where
  arena := #[.node .u64 [], .var 0, .node (.natural 0) [], .node (.lam false) [0, 1],
    .node .ifEq [1, 2, 3, 3], .node .app [4, 1], .node (.lam false) [0, 5],
    .node (.pi false) [0, 0]]
  definitions := [⟨7, 6⟩]
  families := []

private def prepared : Arena :=
  snapshot.arena ++ #[.var 1, .node .app [3, 8], .node .app [3, 1], .node .ifEq [1, 2, 9, 10]]

/-- The admitted function's argument refers to the outer binder. It is
raised in the true arm and stays unchanged in the false arm, including
after the two branch applications reenter and contract. -/
theorem admitted_conditional_application_keeps_original_type :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env [] 32 16 ⟨snapshot.arena, 0⟩ 4 1 =
      ⟨⟨prepared.push (.node .ifEq [1, 2, 8, 1]), 20⟩, .ok 12⟩ ∧
    HasType env [] [⟨.u64, false⟩] true result .u64 := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨sourceType, source⟩] [] = some env := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound installed
  obtain ⟨_, _, original⟩ := history.global_typing (index := 0) (declaration := ⟨sourceType, source⟩) rfl
  change HasType env [] [] _ (.lam false .u64 body) (.pi false .u64 .u64) at original
  obtain ⟨_, _, _, appTyped, converted⟩ := original.lamView
  have typed := appTyped.convert (converted.pi_injective history.wellFormed.admissible).2.2
  have ran : run env [] 32 16 ⟨snapshot.arena, 0⟩ 4 1 =
      ⟨⟨prepared.push (.node .ifEq [1, 2, 8, 1]), 20⟩, .ok 12⟩ := by cbv
  have selected : Represents snapshot.arena 4 callee := decode_sound (fuel := 8) rfl
  have arg : Represents snapshot.arena 1 (.var 0) := decode_sound (fuel := 1) rfl
  obtain ⟨_, _, residual, rep, kept⟩ :=
    run_preserves history selected arg typed (congrArg Outcome.result ran)
  rw [ran] at rep
  have expected : Represents (prepared.push (.node .ifEq [1, 2, 8, 1])) 12 result :=
    decode_sound (fuel := 3) rfl
  exact ⟨admitted, ran, rep.unique expected ▸ kept⟩

theorem rejected_child_visit_keeps_exact_application_spine :
    run env [] 1 16 ⟨snapshot.arena, 0⟩ 4 1 =
      ⟨⟨prepared, 2⟩, .error (.tick (.stepLimit 11))⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreConditionalApplication
