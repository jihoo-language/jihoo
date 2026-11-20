import Jihoo.NativeLoanOpenProofNormalization
import Jihoo.NativeLoanPureGlobalObservation

/-! Typed arithmetic proof normalization follows prior transparent
definitions at the head and in scalar application. Call typing follows the
actual stored derivations in the mixed prefix. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.GlobalProofNormalization

open PureHypothesisObservation (Entry ScalarSlot context)
open WideHypothesisObservation (Satisfies closing)
open OpenProofNormalization (TransportEvidence)
open NativeKernel.Conversion (treeSize)
open Semantics.PureArithmetic (Recognized UniversalTruth)

private def global (index : Nat) : Term := .node (.global index) []

/-- A callable head can be revealed through a finite chain of actual
transparent declarations, ending at a U64 lambda. -/
inductive Callable (env : Environment) : Term → Bool → Term → Prop where
  | lambda : Callable env (.lam erased .u64 body) erased body
  | delta : env.globals[index]? = some declaration → Callable env declaration.value erased body →
      Callable env (global index) erased body

def reveal? (env : Environment) : Nat → Term → Option (Bool × Term)
  | 0, _ => none
  | _ + 1, .lam erased .u64 body => some (erased, body)
  | fuel + 1, .node (.global index) [] => do
      let declaration ← env.globals[index]?
      reveal? env fuel declaration.value
  | _ + 1, _ => none

theorem reveal?_sound (found : reveal? env fuel term = some (erased, body)) : Callable env term erased body := by
  fun_induction reveal? env fuel term
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact .lambda
  · rename_i ih
    obtain ⟨_, selected, exposed⟩ := Option.bind_eq_some_iff.mp found
    exact .delta selected (ih _ exposed)
  · contradiction

theorem Callable.reveal_total (call : Callable env term erased body) :
    ∃ needed, ∀ fuel, needed ≤ fuel → reveal? env fuel term = some (erased, body) := by
  induction call with
  | lambda =>
      refine ⟨1, fun fuel plenty => ?_⟩
      cases fuel with
      | zero => omega
      | succ _ => rfl
  | delta found _ ih =>
      obtain ⟨needed, arrives⟩ := ih
      refine ⟨needed + 1, fun fuel plenty => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          have exposed := arrives fuel (by omega)
          simpa [global, reveal?, found] using exposed

theorem Callable.forward (call : Callable env term erased body) :
    RawLend.Forward env term (.lam erased .u64 body) := by
  induction call with
  | lambda => exact .refl
  | delta found _ ih => exact .trans (.old (.old (.delta found))) ih

theorem Callable.application_forward (call : Callable env function erased body) (argument : Term) :
    RawLend.Forward env (.app function argument) (body.subst (single argument)) :=
  .trans (.node .app (.cons call.forward (.cons .refl .nil)))
    (.old (.old (.acu (.compute (.beta erased .u64 body argument)))))

private theorem reference_type (wf : UnifiedProgram.EnvWellFormed env)
    (found : env.globals[index]? = some declaration)
    (typed : PureTyping.HasType env ctx term type) (shape : term = global index) :
    RawValue.Conv env declaration.type type := by
  induction typed with
  | native native =>
      cases shape
      obtain ⟨selected, selectedFound, switched⟩ := native.principalView
      have same := Option.some.inj (selectedFound.symm.trans found)
      subst selected
      rw [Environment.closed_rename (wf.globals index declaration found).1] at switched
      exact .old switched
  | convert _ _ converted ih => exact (ih shape).trans converted
  | pi | lam | app => cases shape

/-- The lambda body in the actual callable chain has its original typing.
The relation to the requested function type is recovered across each
transparent alias, even when that type uses expanded pure conversion. -/
theorem Callable.body_typing (history : PureMixedAdmission.History definitions familyDeclarations env)
    (call : Callable env term erased body) (typed : PureTyping.HasType env ctx term type) :
    ∃ result, PureTyping.HasType env (⟨.u64, erased⟩ :: ctx) body result ∧
      RawValue.Conv env (.pi erased .u64 result) type := by
  induction call generalizing type with
  | lambda => exact PureTyping.lambda_replay typed _ _ _ rfl
  | delta found _ ih =>
      obtain ⟨_, _, stored⟩ := history.slotTyping _ _ found
      have weakening : Ghost.Substitution env [] ctx Term.var := by
        intro index binding invalid
        cases invalid
      have weakened := stored.ghostSubstitution history.wellFormed weakening
      simp only [Term.subst_id] at weakened
      obtain ⟨result, bodyTyped, converted⟩ := ih weakened
      exact ⟨result, bodyTyped, converted.trans (reference_type history.wellFormed found typed rfl)⟩

/-- Delta at the callee and beta at its original U64 binder preserve the
original result type formed by the checker. The caller supplies no typing
of the exposed lambda or its body. -/
theorem application_preserves {sort : SortTag} (history : PureMixedAdmission.History definitions familyDeclarations env)
    (call : Callable env function erased body) (word : value < 2^64)
    (typed : PureTyping.HasType env ctx (.app function (.natural value)) requested)
    (formed : HasType env [] ctx true requested sort.term) :
    PureTyping.HasType env ctx (body.subst (single (.natural value))) requested := by
  obtain ⟨_, _, _, functionTyped, _, resultConverted⟩ :=
    PureTyping.application_replay typed _ _ rfl
  obtain ⟨_, bodyTyped, piConverted⟩ := call.body_typing history functionTyped
  have aligned := (piConverted.pi_injective history.wellFormed.admissible).2.2
  exact .convert (bodyTyped.ghostInstantiate history.wellFormed (.natural word)) formed
    ((aligned.substitution (single (.natural value)) history.wellFormed.admissible).trans resultConverted)

def run? (env : Environment) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, .node (.global index) [] => do
      let declaration ← env.globals[index]?
      run? env fuel declaration.value
  | fuel + 1, .app function (.natural value) => do
      if value < 2^64 then
        let (_, body) ← reveal? env (fuel + 1) function
        run? env fuel (body.subst (single (.natural value)))
      else none
  | fuel + 1, .strict _ rest => run? env fuel rest
  | fuel + 1, .free _ rest => run? env fuel rest
  | fuel + 1, .transport _ equality proof => do
      let _ ← ProofTransportObservation.exposeRefl? equality
      run? env fuel proof
  | _ + 1, term => OpenProofNormalization.normalize? env 1 term

theorem run?_sound {sort : SortTag} (history : PureMixedAdmission.History definitions familyDeclarations env)
    (typed : PureTyping.HasType env ctx term type) (formed : HasType env [] ctx true type sort.term)
    (ran : run? env fuel term = some residual) :
    PureTyping.HasType env ctx residual type ∧ Recognized env residual := by
  fun_induction run? env fuel term generalizing ctx type residual
  · contradiction
  · rename_i ih
    obtain ⟨_, found, replayed⟩ := Option.bind_eq_some_iff.mp ran
    exact ih _ (PureGlobalObservation.delta_preserves history found typed formed) formed replayed
  · rename_i ih
    obtain ⟨⟨_, _⟩, callable, replayed⟩ := Option.bind_eq_some_iff.mp ran
    have reduced := application_preserves history (reveal?_sound callable) (by assumption) typed formed
    first
    | exact ih _ callable reduced formed replayed
    | exact ih _ _ callable reduced formed replayed
    | exact ih _ reduced formed replayed
  · contradiction
  · rename_i ih
    exact ih ((PureProofObservation.Step.strict _ _).preserves history.wellFormed typed) formed ran
  · rename_i ih
    exact ih ((PureProofObservation.Step.free _ _).preserves history.wellFormed typed) formed ran
  · rename_i ih
    obtain ⟨_, exposed, replayed⟩ := Option.bind_eq_some_iff.mp ran
    exact ih ((PureProofObservation.Step.transport exposed).preserves history.wellFormed typed) formed replayed
  · exact OpenProofNormalization.normalize?_sound history.wellFormed typed ran

private theorem run_embeds_open (opened : OpenProofNormalization.normalize? env small term = some residual)
    (enough : small ≤ fuel) : run? env fuel term = some residual := by
  fun_induction OpenProofNormalization.normalize? env small term generalizing fuel
  · contradiction
  · rename_i ih
    cases fuel with
    | zero => omega
    | succ fuel =>
        rw [run?]
        exact ih opened (by omega)
  · rename_i ih
    cases fuel with
    | zero => omega
    | succ fuel =>
        rw [run?]
        exact ih opened (by omega)
  · rename_i ih
    cases fuel with
    | zero => omega
    | succ fuel =>
        obtain ⟨_, exposed, replayed⟩ := Option.bind_eq_some_iff.mp opened
        rw [run?, exposed]
        exact ih replayed (by omega)
  · rename_i input notStrict notFree notTransport ready
    cases fuel with
    | zero => omega
    | succ fuel =>
        have old : OpenProofNormalization.normalize? env 1 input = some residual := by
          rw [OpenProofNormalization.normalize?]
          · simpa [ready] using opened
          · exact notStrict
          · exact notFree
          · exact notTransport
        rw [run?]
        · exact old
        · intro index shape
          subst input
          simp [Semantics.PureArithmetic.recognizes, ProofObservation.supported] at ready
          change false = true at ready
          cases ready
        · intro function value shape
          subst input
          simp [Semantics.PureArithmetic.recognizes, ProofObservation.supported] at ready
          change false = true at ready
          cases ready
        · exact notStrict
        · exact notFree
        · exact notTransport
  · contradiction

private def pushWord (first : Nat) (words : Nat → Nat) : Nat → Nat
  | 0 => first
  | index + 1 => words index

inductive WordOperand : List Entry → Term → Prop where
  | literal : value < 2^64 → WordOperand entries (.natural value)
  | slot : ScalarSlot entries index → WordOperand entries (.var index)

private theorem closed_slot (valid : Satisfies entries words) (slot : ScalarSlot entries index) :
    words index < 2^64 ∧ closing entries words index = .natural (words index) := by
  induction slot generalizing words with
  | here =>
      cases valid with
      | scalar bound _ => exact ⟨bound, rfl⟩
  | there _ ih =>
      cases valid with
      | scalar _ previous | less _ _ _ previous | equal _ _ _ previous => exact ih previous

theorem WordOperand.literal_after_closing (operand : WordOperand entries term) (valid : Satisfies entries words) :
    ∃ value, value < 2^64 ∧ term.subst (closing entries words) = .natural value := by
  cases operand with
  | literal bound =>
      exact ⟨_, bound, by simp [Term.natural, Term.subst, substArgs]⟩
  | slot slot =>
      obtain ⟨bound, aligned⟩ := closed_slot valid slot
      exact ⟨_, bound, by simpa only [Term.subst] using aligned⟩

private theorem subst_scalar (body : Term) (value : Nat) (entries : List Entry) (words : Nat → Nat) :
    (body.subst (liftSubOne (closing entries words))).subst (single (.natural value)) =
      body.subst (closing (.scalar erased :: entries) (pushWord value words)) := by
  rw [Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [liftSubOne, Term.subst, single]; rfl
  | succ index =>
      simp only [liftSubOne, Term.shift_subst_single]
      rfl

private theorem single_scalar {body : Term} (scope : body.Scoped 1) (value : Nat) :
    body.subst (single (.natural value)) =
      body.subst (closing [.scalar erased] (pushWord value (fun _ => 0))) := by
  apply Environment.scoped_subst_congr scope
  intro index bound
  have zero : index = 0 := by omega
  subst index
  rfl

private theorem Callable.closed_lambda_body (wf : UnifiedProgram.EnvWellFormed env)
    (call : Callable env term erased body) (closed : term.Scoped 0) :
    body.Scoped 1 := by
  induction call with
  | lambda =>
      exact Term.Scoped.child (index := 1) closed rfl
  | delta found _ ih =>
      exact ih (wf.globals _ _ found).2.1

/-- Finite root and application shapes. Each global lookup follows the
stored annotation and body of an admitted earlier declaration. -/
inductive Tree (env : Environment) : List Entry → Term → Prop where
  | terminal : OpenProofNormalization.Tree entries term → Tree env entries term
  | delta : env.globals[index]? = some declaration → Tree env [] declaration.value →
      Tree env entries (global index)
  | localCall : WordOperand entries operand → Tree env (.scalar erased :: entries) body →
      Tree env entries (.app (.lam erased .u64 body) operand)
  | globalCall : Callable env (global index) erased body → WordOperand entries operand →
      Tree env [.scalar erased] body → Tree env entries (.app (global index) operand)
  | strict : Tree env entries term → Tree env entries (.strict first term)
  | free : Tree env entries term → Tree env entries (.free owner term)
  | transport : TransportEvidence entries evidence → Tree env entries term →
      Tree env entries (.transport predicate evidence term)

private theorem closed_global_word (index : Nat) (values : Nat → Term) : (global index).subst values = global index :=
  by simp [global, Term.subst, substArgs]

/-- The fuel threshold is reconstructed from the original source shape and
actual stored declarations. Every larger fuel reaches the same residual. -/
theorem Tree.run_total (wf : UnifiedProgram.EnvWellFormed env) (source : Tree env entries term)
    (valuation : Satisfies entries words) :
    ∃ needed result, ∀ fuel, needed ≤ fuel →
      run? env fuel (term.subst (closing entries words)) = some result := by
  induction source generalizing words with
  | @terminal entries proof tree =>
      let size := treeSize (proof.subst (closing entries words))
      obtain ⟨result, ran⟩ := tree.normalization_total (env := env) words (Nat.lt_succ_self size)
      exact ⟨size + 1, result, fun _ enough => run_embeds_open ran enough⟩
  | delta found _ ih =>
      obtain ⟨needed, result, terminates⟩ := ih (Satisfies.empty (words := fun _ => 0))
      have closedDecl := (wf.globals _ _ found).2.1
      refine ⟨needed + 1, result, fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ran := terminates fuel (by omega)
          rw [Environment.closed_subst closedDecl] at ran
          rw [closed_global_word]
          simpa [global, run?, found] using ran
  | @localCall entries _ erased body operand _ ih =>
      obtain ⟨value, width, aligned⟩ := operand.literal_after_closing valuation
      obtain ⟨needed, result, terminates⟩ := ih (Satisfies.scalar (words := pushWord value words) width valuation)
      refine ⟨needed + 1, result, fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ran := terminates fuel (by omega)
          rw [← subst_scalar (erased := erased) body value entries words] at ran
          simp only [Term.app, Term.lam, Term.u64, Term.subst, substArgs, Op.binders, liftSub]
          rw [aligned]
          simpa [run?, reveal?, width] using ran
  | @globalCall index erased _ _ _ call operand _ ih =>
      obtain ⟨value, width, aligned⟩ := operand.literal_after_closing valuation
      obtain ⟨callFuel, reveals⟩ := call.reveal_total
      have closedHead : (global index).Scoped 0 := Term.Scoped.leaf _ _
      have closedBody := call.closed_lambda_body wf closedHead
      obtain ⟨needed, result, terminates⟩ :=
        ih (Satisfies.scalar (words := pushWord value (fun _ => 0)) width .empty)
      refine ⟨max (needed + 1) callFuel, result, fun fuel enough => ?_⟩
      have enoughSteps := Nat.le_trans (Nat.le_max_left _ _) enough
      have enoughCall := Nat.le_trans (Nat.le_max_right _ _) enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ran := terminates fuel (by omega)
          rw [← single_scalar (erased := erased) closedBody value] at ran
          have exposed := reveals (fuel + 1) enoughCall
          simp only [Term.app, Term.subst, substArgs, Op.binders, liftSub]
          rw [aligned, closed_global_word]
          rw [run?, ite_eq_left width, exposed]
          exact ran
  | strict _ ih =>
      obtain ⟨needed, result, terminates⟩ := ih valuation
      refine ⟨needed + 1, result, fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [Term.strict, Term.subst, substArgs, Op.binders, liftSub, run?]
            using terminates fuel (by omega)
  | free _ ih =>
      obtain ⟨needed, result, terminates⟩ := ih valuation
      refine ⟨needed + 1, result, fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [Term.free, Term.subst, substArgs, Op.binders, liftSub, run?]
            using terminates fuel (by omega)
  | transport evidence _ ih =>
      obtain ⟨needed, result, terminates⟩ := ih valuation
      obtain ⟨exposedValue, exposed⟩ := evidence.exposes words
      refine ⟨needed + 1, result, fun fuel enough => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [Term.transport, Term.subst, substArgs, Op.binders, liftSub, run?, exposed]
            using terminates fuel (by omega)

/-- Actual local typing and the authentic mixed history produce a typed
finite result. Its exact requested annotation is closed with the source. -/
theorem typed_normalization {sort : SortTag}
    (history : PureMixedAdmission.History definitions familyDeclarations env)
    (valuation : Satisfies entries words) (source : Tree env entries term)
    (typed : PureTyping.HasType env (context entries) term requested)
    (formed : HasType env [] (context entries) true requested sort.term) :
    ∃ fuel result, run? env fuel (term.subst (closing entries words)) = some result ∧
      PureTyping.HasType env [] result (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨needed, result, terminates⟩ := source.run_total history.wellFormed valuation
  have ran := terminates needed (Nat.le_refl _)
  have closedTyped := typed.ghostSubstitution history.wellFormed valuation.realizes
  have closedFormed := formed.ghostSubstitution history.wellFormed valuation.realizes
  rw [SortTag.subst_term] at closedFormed
  obtain ⟨typedResult, recognized⟩ := run?_sound history closedTyped closedFormed ran
  exact ⟨needed, result, ran, typedResult,
    Semantics.PureArithmetic.recognized_fundamental history.wellFormed typedResult recognized⟩

theorem checked_normalization {limits : PureProofObservation.Limits}
    (history : PureMixedAdmission.History definitions familyDeclarations env)
    (valuation : Satisfies entries words) (source : Tree env entries term)
    (checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
      (context entries) term requested = some sort) :
    ∃ fuel result, run? env fuel (term.subst (closing entries words)) = some result ∧
      PureTyping.HasType env [] result (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨formed, typed⟩ := PureTyping.Checker.check?_sound checked
  exact typed_normalization history valuation source typed formed

theorem checked_bytes_normalization {limits : PureProofObservation.Limits}
    (admitted : PureMixedAdmission.checkBytes admissionLimits bytes = some env)
    (valuation : Satisfies entries words) (source : Tree env entries term)
    (checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
      (context entries) term requested = some sort) :
    ∃ fuel result, run? env fuel (term.subst (closing entries words)) = some result ∧
      PureTyping.HasType env [] result (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨_, _, _, _, _, history, _, _⟩ := PureMixedAdmission.checkBytes_sound admitted
  exact checked_normalization history valuation source checked

theorem no_checked_false_closed_inequality {limits : PureProofObservation.Limits}
    (history : PureMixedAdmission.History definitions familyDeclarations env)
    (source : Tree env [] term) (unordered : ¬ left < right) :
    PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget []
      term (.lt (.natural left) (.natural right)) = none := by
  cases checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget []
      term (.lt (.natural left) (.natural right)) with
  | none => rfl
  | some _ =>
      obtain ⟨_, _, _, _, truth⟩ :=
        checked_normalization history (Satisfies.empty (words := fun _ => 0)) source checked
      have closed : (.lt (.natural left) (.natural right) : Term).subst (closing [] (fun _ => 0)) =
          .lt (.natural left) (.natural right) := by
        simp [Term.lt, Term.natural, Term.subst, substArgs]
      rw [closed] at truth
      exact False.elim (unordered ((UniversalTruth.formula_iff history.wellFormed
        (.less (.literal left) (.literal right))).mp truth (fun _ => 0)))

private def base : GlobalDeclaration := ⟨PureFreeBoundary.annotation, PureFreeBoundary.body⟩
private def alias : GlobalDeclaration := ⟨PureFreeBoundary.annotation, global 0⟩
private def world : Environment := ⟨#[base, base], #[]⟩

private def applied : Term :=
  .app (.lam false .u64 (.strict (.natural 0) (.app (global 1) (.var 0)))) (.natural 7)

private def requested : Term := .eq (.free PureFreeBoundary.owner (.natural 7)) (.natural 7)
private def limits : PureProofObservation.Limits := ⟨32, 32, 8192⟩

private theorem appliedTree : Tree world [] applied :=
  .localCall (.literal (by decide)) (.strict
    (.globalCall (.delta rfl .lambda) (.slot .here)
      (.terminal (.reflexive (.refl (.var .here))))))

/-- The second declaration is an actual prior reference in the source
program. The call goes through its authenticated stored definition, and
local scalar beta, Strict, and the global call preserve the Free type. -/
theorem checked_prior_global_application :
    PureMixedAdmission.checkProgram ⟨32, 32, 32, 8192⟩ [base, alias] [] = some world ∧
    run? world 8 applied = some (.refl (.natural 7)) ∧ UniversalTruth world requested := by
  have admitted : PureMixedAdmission.checkProgram ⟨32, 32, 32, 8192⟩ [base, alias] [] = some world := by cbv
  have checked : PureTyping.Checker.check? world limits.typingFuel limits.conversionFuel limits.budget []
      applied requested = some .prop := by cbv
  have history := PureMixedAdmission.checkProgram_sound admitted
  obtain ⟨_, _, _, _, truth⟩ :=
    checked_normalization history (Satisfies.empty (words := fun _ => 0)) appliedTree checked
  exact ⟨admitted, by cbv,
    by simpa only [show requested.subst (closing [] (fun _ => 0)) = requested by cbv] using truth⟩

end Jihoo.NativeKernel.Environment.LoanTyping.GlobalProofNormalization
