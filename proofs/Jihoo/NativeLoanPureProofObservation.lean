import Jihoo.NativeLoanPureArithmetic
import Jihoo.NativeLoanProofTransportObservation

/-! Observe closed or open ghost evidence using a bounded, typing-preserving
path to the arithmetic grammar. Beta checks its operand at the lambda's actual
binder, whose domain can differ from the application's converted domain. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureProofObservation

open NativeKernel.Conversion (treeSize)
open Semantics.PureArithmetic (Recognized UniversalTruth)

inductive Step (env : Environment) : Context → Term → Term → Prop where
  | beta : HasType env [] ctx true argument domain →
      Step env ctx (.app (.lam erased domain body) argument) (body.subst (single argument))
  | transport : ProofTransportObservation.exposeRefl? evidence = some value →
      Step env ctx (.transport motive evidence payload) payload
  | strict (first rest : Term) : Step env ctx (.strict first rest) rest
  | free (owner rest : Term) : Step env ctx (.free owner rest) rest
  | lambda : Step env (⟨domain, erased⟩ :: ctx) body result →
      Step env ctx (.lam erased domain body) (.lam erased domain result)
  | callee : Step env ctx function result → Step env ctx (.app function argument) (.app result argument)

private theorem Step.native_preserves (step : Step env ctx term result)
    (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env loans ctx mode term type) :
    HasType env [] ctx true result type := by
  induction step generalizing loans mode type with
  | beta => exact compute_ghost_preservation wf (.beta _ _ _ _) typed
  | @transport evidence value localCtx motive payload exposed =>
      have replayed : HasType env [] localCtx true (.transport motive (.refl value) payload) type :=
        ProofTransportObservation.exposeTransport?_preserves typed
        (by simp only [ProofTransportObservation.exposeTransport?, exposed, Option.map_some])
      exact compute_ghost_preservation wf (.transportRefl _ _ _) replayed
  | strict => exact value_root_ghost_preservation (.strict _ _) typed
  | free => exact value_root_ghost_preservation (.free _ _) typed
  | lambda _ ih =>
      obtain ⟨_, _, binder, bodyTyped, converted⟩ := typed.lamView
      cases binder with
      | intro formed allowed =>
          exact (HasType.lam (.intro (formed.ghost []) allowed) (ih bodyTyped)).convert converted
  | callee _ ih =>
      obtain ⟨_, _, _, functionTyped, argumentTyped, _, converted⟩ := typed.appView
      exact (HasType.app (ih functionTyped) (argumentTyped.ghost []) (Or.inl rfl)).convert converted

/-- The result retains the exact requested type. Application formation also
types the new conversion target after substituting the original operand. -/
theorem Step.preserves (step : Step env ctx term result) (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx term type) : PureTyping.HasType env ctx result type := by
  induction typed generalizing result with
  | native original => exact .native (step.native_preserves wf original)
  | convert _ formed converted ih => exact .convert (ih step) formed converted
  | pi => cases step
  | lam binder formed _ ih =>
      cases step with
      | lambda inner => exact .lam binder formed (ih inner)
  | app callee formed argument ih =>
      cases step with
      | beta originalArgument =>
          obtain ⟨_, bodyTyped, converted⟩ := PureTyping.lambda_replay callee _ _ _ rfl
          have results := (converted.pi_injective wf.admissible).2.2
          exact .convert (bodyTyped.ghostInstantiate wf originalArgument)
            (PureTyping.application_result_formed wf formed argument)
            (results.substitution (single _) wf.admissible)
      | callee inner => exact .app (ih inner) formed argument

private def select (env : Environment) (typingFuel : Nat) (visit : Context → Term → Option Term)
    (ctx : Context) : Term → Option Term
  | .app (.lam _ domain body) argument =>
      if Checker.check typingFuel env [] ctx true argument domain then some (body.subst (single argument)) else none
  | .app function argument => (visit ctx function).map (fun result => .app result argument)
  | .lam erased domain body => (visit (⟨domain, erased⟩ :: ctx) body).map (.lam erased domain)
  | .transport _ evidence payload => (ProofTransportObservation.exposeRefl? evidence).map (fun _ => payload)
  | .strict _ rest | .free _ rest => some rest
  | _ => none

private theorem select_sound (sound : ∀ {ctx term result}, visit ctx term = some result → Step env ctx term result)
    (selected : select env typingFuel visit ctx term = some result) : Step env ctx term result := by
  fun_cases select env typingFuel visit ctx term <;> simp only [select] at selected
  · rename_i checked
    simp only [checked, ↓reduceIte] at selected
    cases selected
    exact .beta (Checker.check_sound checked)
  · rename_i declined
    simp only [declined] at selected
    contradiction
  · obtain ⟨function, found, rfl⟩ := Option.map_eq_some_iff.mp selected
    exact .callee (sound found)
  · obtain ⟨body, found, rfl⟩ := Option.map_eq_some_iff.mp selected
    exact .lambda (sound found)
  · obtain ⟨value, exposed, rfl⟩ := Option.map_eq_some_iff.mp selected
    exact .transport exposed
  · cases selected
    exact .strict _ _
  · cases selected
    exact .free _ _
  · contradiction

private def step? (env : Environment) (typingFuel : Nat) : Nat → Context → Term → Option Term
  | 0, _, _ => none
  | depth + 1, ctx, term => select env typingFuel (step? env typingFuel depth) ctx term

private theorem step?_sound (stepped : step? env typingFuel depth ctx term = some result) :
    Step env ctx term result := by
  induction depth generalizing ctx term result with
  | zero => contradiction
  | succ depth ih => exact select_sound (fun found => ih found) stepped

structure Limits where
  typingFuel : Nat
  conversionFuel : Nat
  budget : Nat

/-- Prefer the original recognizer, and otherwise reduce one typed position.
The square work allowance is tested before expanding a beta substitution. -/
def observe? (env : Environment) (limits : Limits) (ctx : Context) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, term =>
      if 4 * (treeSize term + 1)^2 > limits.budget then none
      else if Semantics.PureArithmetic.recognizes env limits.conversionFuel limits.budget (fuel + 1) term then some term
      else (step? env limits.typingFuel (fuel + 1) ctx term).bind (observe? env limits ctx fuel)

theorem observe?_sound (wf : UnifiedProgram.EnvWellFormed env) (typed : PureTyping.HasType env ctx term type)
    (observed : observe? env limits ctx fuel term = some result) :
    PureTyping.HasType env ctx result type ∧ Recognized env result := by
  induction fuel generalizing term result with
  | zero => contradiction
  | succ fuel ih =>
      simp only [observe?] at observed
      split at observed
      · contradiction
      split at observed
      · rename_i recognized
        cases observed
        exact ⟨typed, Semantics.PureArithmetic.recognizes_sound recognized⟩
      · obtain ⟨next, stepped, checked⟩ := Option.bind_eq_some_iff.mp observed
        exact ih ((step?_sound stepped).preserves wf typed) checked

theorem checked_arithmetic_truth (wf : UnifiedProgram.EnvWellFormed env)
    (checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget [] term type = some sort)
    (observed : observe? env limits [] fuel term = some result) : UniversalTruth env type := by
  obtain ⟨typed, recognized⟩ := observe?_sound wf (PureTyping.Checker.check?_sound checked).2 observed
  exact Semantics.PureArithmetic.recognized_fundamental wf typed recognized

/-- Recover truth at the exact annotation stored in a successful version-6
history, using its original checked body under the expanded judgment. -/
theorem checked_global_arithmetic_truth {env : Environment} {declaration : GlobalDeclaration} {index : Nat}
    (accepted : PureMixedAdmission.checkBytes admissionLimits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env limits [] fuel declaration.value = some result) : UniversalTruth env declaration.type := by
  obtain ⟨_, _, _, _, _, history, wf, _⟩ := PureMixedAdmission.checkBytes_sound accepted
  obtain ⟨typed, recognized⟩ := observe?_sound wf (history.global_value_and_reference found).1 observed
  exact Semantics.PureArithmetic.recognized_fundamental wf typed recognized

theorem checker_rejects_observable_false_inequality (wf : UnifiedProgram.EnvWellFormed env)
    (observed : observe? env limits [] fuel term = some result) (unordered : ¬ left < right) :
    PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget [] term
      (.lt (.natural left) (.natural right)) = none := by
  cases checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget [] term
      (.lt (.natural left) (.natural right)) with
  | none => rfl
  | some sort =>
      obtain ⟨typed, recognized⟩ := observe?_sound wf (PureTyping.Checker.check?_sound checked).2 observed
      exact False.elim (Semantics.PureArithmetic.no_false_numeral_inequality wf typed recognized unordered)

private def small : Term := .lt (.natural 0) (.natural 1)
private def proof : Term := .decide (.natural 0) (.natural 1)
private def motive : Term := .lam false .u64 (.lt (.var 0) (.natural 1))
private def transported : Term := .transport motive (.strict (.natural 2) (.refl (.natural 0))) proof
private def appliedProof : Term := .app (.lam true small (.var 0)) transported
private def requested : Term := .lt (.free (.alloc (.natural 1) (.integer 0)) (.natural 0)) (.natural 1)
private def limits : Limits := ⟨32, 32, 8192⟩

/-- The direct recognizer misses an application at an erased proposition and
its transported operand. Typed replay exposes the proof, keeping the original
annotation that requires the extended Free equality. -/
theorem checked_transport_application :
    Semantics.PureArithmetic.recognizes .empty 32 8192 8 appliedProof = false ∧
    Checker.check 32 .empty [] [] true appliedProof requested = false ∧
    observe? .empty limits [] 8 appliedProof = some proof ∧ UniversalTruth .empty requested := by
  have checked : PureTyping.Checker.check? .empty limits.typingFuel limits.conversionFuel limits.budget []
      appliedProof requested = some .prop := by cbv
  have observed : observe? .empty limits [] 8 appliedProof = some proof := by cbv
  exact ⟨by cbv, by cbv, observed, checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked observed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.PureProofObservation
