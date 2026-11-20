import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeLoanFamilyIotaCasePreservation
import Jihoo.NativeLoanFamilyIotaPropElimPreservation
import Jihoo.NativeLoanFamilyIotaViewRecursivePreservation

/-! Every real family-iota contraction preserves the exact original dependent
type. No output typing, normalization naturality or enlarged confluence is assumed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem elim_preserves {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (elimBody entry signature family motive branch cases values) type := by
  cases kind : entry.declaration.data with
  | false => exact prop_elim_preserves history found sigFound kind selected size typed
  | true => exact data_elim_preserves history found sigFound kind selected size typed

theorem contract_elim_preserves {family count : Nat}
    (history : ScopedProgram.History definitions declarations env)
    (accepted : contract env (.node (.elim family count) args) = some result)
    (typed : HasType env [] ctx true (.node (.elim family count) args) type) :
    HasType env [] ctx true result type := by
  cases contract_sound accepted with
  | elim found signature selected count fields => exact elim_preserves history found signature selected fields typed

theorem view_preserves {recursion : Bool} {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (typed : HasType env [] ctx true
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    HasType env [] ctx true (viewBody recursion family entry.declaration.params motive branch cases values plans) type := by
  cases recursion with
  | false => exact view_preserves_one_level history found sigFound selected size planned typed
  | true => exact view_preserves_recursive history found sigFound selected size planned typed

/-- All concrete roots: indexed Prop/data Elim, parameterized Case,
one-level/recursive borrowed View, and pure Drop. -/
theorem Root.preserves (history : ScopedProgram.History definitions declarations env)
    (step : Root env term result) (typed : HasType env [] ctx true term type) :
    HasType env [] ctx true result type := by
  cases step with
  | elim found signature selected count fields => exact elim_preserves history found signature selected fields typed
  | caseOf found data signature selected count fields => exact case_preserves history found signature selected fields typed
  | view found boxed signature selected count fields bound planned =>
    exact view_preserves history found signature selected fields planned typed
  | drop => exact drop_preserves typed

/-- The actual executable contractor preserves every independently typed
input's original result type under authentic mixed declaration history. -/
theorem contract_preserves (history : ScopedProgram.History definitions declarations env)
    (accepted : contract env term = some result) (typed : HasType env [] ctx true term type) :
    HasType env [] ctx true result type :=
  Root.preserves history (contract_sound accepted) typed

private theorem checked_prop_branch_count (checked : Cases env [] ctx motive signatures cases) :
    cases.length = signatures.length := by
  induction signatures generalizing cases with
  | nil => cases checked; rfl
  | cons signature signatures ih =>
      cases checked with
      | cons _ rest => exact congrArg Nat.succ (ih rest)

/-- Actual Prop or data Elim typing on a constructor guarantees contraction,
including the complete branch and recursive-field layout. -/
theorem contract_elim_from_typing (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ result, contract env (elimTerm family motive cases (.node (.con family constructor values.length) values)) =
      some result ∧ HasType env [] ctx true result type := by
  obtain ⟨entry, motive', _, _, indices, _, layout, found, inputs⟩ := elim_inputs typed
  obtain ⟨rfl, last⟩ := List.append_inj' (List.cons.inj layout).2 (by simp)
  obtain rfl := (List.cons.inj last).1
  obtain ⟨scrutinee, count⟩ :
      HasType env [] ctx true (.node (.con family constructor values.length) values)
        (.node (.ind family entry.declaration.arity) indices) ∧ cases.length = entry.signatures.length := by
    rcases inputs with ⟨_, _, branches, scrutinee, _⟩ | ⟨_, _, _, _, _, scrutinee, generated, branches, _⟩
    · exact ⟨scrutinee, checked_prop_branch_count branches⟩
    · exact ⟨scrutinee, checked_generated_branch_count generated branches⟩
  obtain ⟨signature, branch, sig, fields, selected⟩ := checked_constructor_selection history found scrutinee count
  have root : Root env (elimTerm family motive cases (.node (.con family constructor values.length) values))
      (elimBody entry signature family motive branch cases values) := .elim found sig selected count fields
  exact ⟨_, root.complete, Root.preserves history root typed⟩

/-- Checked View typing supplies the exact field borrowing plan and the
constructor layout. This works with and without recursive hypotheses. -/
theorem contract_view_from_typing (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    ∃ result, contract env (viewTerm recursion family motive cases
      (.borrow (.node (.con family constructor values.length) values))) = some result ∧
      HasType env [] ctx true result type := by
  obtain ⟨entry, _, _, _, _, _, _, _, layout, found, _, boxed, _, _, scrutinee, _, generated, branches, _⟩ :=
    view_inputs typed
  obtain ⟨rfl, last⟩ := List.append_inj' (List.cons.inj layout).2 (by simp)
  obtain rfl := (List.cons.inj last).1
  obtain ⟨_, owner, _⟩ := scrutinee.principalView
  have count := checked_generated_branch_count generated branches
  obtain ⟨signature, branch, sig, fields, selected⟩ := checked_constructor_selection history found owner count
  have parameters := (signature_metadata history found sig).2.2.1
  obtain ⟨_, _, generatedBranch⟩ := viewCaseTypes_get generated sig
  obtain ⟨plans, planned⟩ : ∃ plans, viewPlan env family (signature.fields.drop entry.declaration.params) = some plans := by
    unfold viewCaseType at generatedBranch
    split at generatedBranch
    · contradiction
    · exact ⟨_, (Option.bind_eq_some_iff.mp generatedBranch).choose_spec.1⟩
  have root : Root env (viewTerm recursion family motive cases
      (.borrow (.node (.con family constructor values.length) values)))
      (viewBody recursion family entry.declaration.params motive branch cases values plans) :=
    .view found boxed sig selected count fields parameters planned
  exact ⟨_, root.complete, Root.preserves history root typed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
