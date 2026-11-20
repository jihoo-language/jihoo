import Jihoo.NativeLoanPureArithmetic
import Jihoo.NativeLoanProofComparison
import Jihoo.NativeLoanProofTransportObservation

/-! Observe closed or open ghost evidence using a bounded, typing-preserving
path to the arithmetic grammar. Beta checks its operand at the lambda's actual
binder, whose domain can differ from the application's converted domain. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureProofObservation

open NativeKernel.Conversion (treeSize)
open Semantics.PureArithmetic (Recognized UniversalTruth)

inductive Step (env : Environment) : Context → Term → Term → Prop where
  | stay (term : Term) : Step env ctx term term
  | beta : HasType env [] ctx true argument domain →
      Step env ctx (.app (.lam erased domain body) argument) (body.subst (single argument))
  | transport : ProofTransportObservation.exposeRefl? evidence = some value →
      Step env ctx (.transport motive evidence payload) payload
  | strict (first rest : Term) : Step env ctx (.strict first rest) rest
  | free (owner rest : Term) : Step env ctx (.free owner rest) rest
  | lambda : Step env (⟨domain, erased⟩ :: ctx) body result →
      Step env ctx (.lam erased domain body) (.lam erased domain result)
  | callee : Step env ctx function result → Step env ctx (.app function argument) (.app result argument)
  | operand : Step env ctx argument result → RawLend.Conv env result argument →
      Step env ctx (.app function argument) (.app function result)
  | loop : RawLend.Conv env count (.natural n) → n < 2^64 →
      Step env ctx (.loop count motive initial body) (ProofLoop.unroll n initial body n)
  | comparison : ProofComparison.Step env term result → Step env ctx term result
  | evidence {visit : Context → Term → Option Term} :
      (∀ {localCtx input output}, visit localCtx input = some output → Step env localCtx input output) →
      ProofTreeObservation.mapEvidence? (visit ctx) term = some result → Step env ctx term result

private theorem raw_operand_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (aligned : RawLend.Conv env result original) (codomain : Term) :
    RawLend.Conv env (codomain.subst (single result)) (codomain.subst (single original)) := by
  apply RawLend.Conv.subst_congr wf.closed _ codomain
  intro index
  cases index with
  | zero => exact aligned
  | succ index => exact .refl _

private theorem Step.native_preserves (step : Step env ctx term result)
    (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env loans ctx mode term type) :
    HasType env [] ctx true result type := by
  induction step generalizing loans mode type with
  | stay => exact typed.ghost []
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
  | operand _ aligned ih =>
      obtain ⟨_, _, _, functionTyped, argumentTyped, _, converted⟩ := typed.appView
      exact (HasType.app (functionTyped.ghost []) (ih argumentTyped) (Or.inl rfl)).convert
        ((raw_operand_conversion wf aligned _).trans converted)
  | loop count bound => exact ProofLoop.unroll_typed wf typed count bound
  | comparison selected => exact selected.preserves wf typed
  | evidence _ mapped ih =>
      exact ProofTreeObservation.mapEvidence_preserves _ (fun source ran => ih ran source) typed mapped

/-- The result retains the exact requested type. Application formation also
types the new conversion target after substituting the original operand. -/
theorem Step.preserves (step : Step env ctx term result) (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx term type) : PureTyping.HasType env ctx result type := by
  induction typed generalizing result with
  | native original => exact .native (step.native_preserves wf original)
  | convert _ formed converted ih => exact .convert (ih step) formed converted
  | pi binder body _ =>
      cases step with
      | stay => exact .pi binder body
      | comparison selected => cases selected
      | evidence _ mapped => contradiction
  | lam binder formed body ih =>
      cases step with
      | stay => exact .lam binder formed body
      | lambda inner => exact .lam binder formed (ih inner)
      | comparison selected => cases selected
      | evidence _ mapped => contradiction
  | app callee formed argument ih =>
      cases step with
      | stay => exact .app callee formed argument
      | beta originalArgument =>
          obtain ⟨_, bodyTyped, converted⟩ := PureTyping.lambda_replay callee _ _ _ rfl
          have results := (converted.pi_injective wf.admissible).2.2
          exact .convert (bodyTyped.ghostInstantiate wf originalArgument)
            (PureTyping.application_result_formed wf formed argument)
            (results.substitution (single _) wf.admissible)
      | callee inner => exact .app (ih inner) formed argument
      | operand inner aligned =>
          exact .convert (.app callee formed (inner.native_preserves wf argument))
            (PureTyping.application_result_formed wf formed argument) (.old (raw_operand_conversion wf aligned _))
      | comparison selected => cases selected
      | evidence _ mapped => contradiction

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

structure Limits where
  typingFuel : Nat
  conversionFuel : Nat
  budget : Nat

private def selectOperand (env : Environment) (limits : Limits) (visit : Context → Term → Option Term)
    (ctx : Context) : Term → Option Term
  | .app function argument => do
      let result ← visit ctx argument
      if RawLend.equal env limits.budget limits.conversionFuel result argument then
        some (.app function result)
      else none
  | _ => none

private theorem selectOperand_sound
    (sound : ∀ {ctx term result}, visit ctx term = some result → Step env ctx term result)
    (selected : selectOperand env limits visit ctx term = some result) : Step env ctx term result := by
  fun_cases selectOperand env limits visit ctx term <;> simp only [selectOperand] at selected
  · obtain ⟨operand, found, selected⟩ := Option.bind_eq_some_iff.mp selected
    split at selected
    · rename_i aligned
      cases selected
      exact .operand (sound found) (RawLend.equal_sound aligned)
    · contradiction
  · contradiction

private def selectLoop (env : Environment) (limits : Limits) : Term → Option Term
  | .loop count _ initial body => do
      let .natural n ← RawLend.normalize? env limits.budget limits.conversionFuel count | none
      if n < 2^64 ∧ treeSize initial + n * (treeSize body + 7) ≤ limits.budget then
        some (ProofLoop.unroll n initial body n)
      else none
  | _ => none

private theorem selectLoop_sound (selected : selectLoop env limits term = some result) :
    Step env ctx term result := by
  fun_cases selectLoop env limits term <;> simp only [selectLoop] at selected
  · obtain ⟨count, ranCount, selected⟩ := Option.bind_eq_some_iff.mp selected
    split at selected
    · split at selected
      · rename_i bounds
        cases selected
        exact .loop (RawLend.normalize?_sound ranCount) bounds.1
      · contradiction
    · contradiction
  · contradiction

private def keepEvidence (visit : Context → Term → Option Term) (ctx : Context) (evidence : Term) : Option Term :=
  (visit ctx evidence).orElse (fun _ => some evidence)

private def selectEvidence (visit : Context → Term → Option Term) (ctx : Context) (term : Term) : Option Term := do
  let rebuilt ← ProofTreeObservation.mapEvidence? (keepEvidence visit ctx) term
  if rebuilt == term then none else some rebuilt

private theorem selectEvidence_sound
    (sound : ∀ {ctx term result}, visit ctx term = some result → Step env ctx term result)
    (selected : selectEvidence visit ctx term = some result) : Step env ctx term result := by
  obtain ⟨rebuilt, mapped, selected⟩ := Option.bind_eq_some_iff.mp selected
  split at selected
  · contradiction
  · cases selected
    refine .evidence (visit := keepEvidence visit) ?_ mapped
    intro localCtx input output seen
    unfold keepEvidence at seen
    cases advanced : visit localCtx input with
    | none =>
        simp only [advanced, Option.orElse_none, Option.some.injEq] at seen
        subst output
        exact .stay _
    | some residual =>
        simp only [advanced, Option.orElse_some, Option.some.injEq] at seen
        subst output
        exact sound advanced

private theorem orElse_result {first second : Option α}
    (observed : first.orElse (fun _ => second) = some result) : first = some result ∨ second = some result := by
  cases first with
  | none => exact .inr observed
  | some value => exact .inl observed

private inductive Positions where
  | heads
  | operands
  | proofs
  | comparisons

private def step? (env : Environment) (limits : Limits) (positions : Positions) : Nat → Context → Term → Option Term
  | 0, _, _ => none
  | depth + 1, ctx, term =>
      let visit := step? env limits positions depth
      let head (_ : Unit) := select env limits.typingFuel visit ctx term
      let argument (_ : Unit) := (selectOperand env limits visit ctx term).orElse head
      let proof (_ : Unit) := (selectLoop env limits term).orElse (fun _ => selectEvidence visit ctx term)
      match positions with
      | .heads => head ()
      | .operands => argument ()
      | .proofs => (argument ()).orElse proof
      | .comparisons => (argument ()).orElse
          (fun _ => (ProofComparison.select? env limits.budget limits.conversionFuel term).orElse proof)

private theorem step?_sound (stepped : step? env limits positions depth ctx term = some result) :
    Step env ctx term result := by
  induction depth generalizing ctx term result with
  | zero => contradiction
  | succ depth ih =>
      let visit := step? env limits positions depth
      have head (selected : select env limits.typingFuel visit ctx term = some result) : Step env ctx term result :=
        select_sound (fun found => ih found) selected
      have argument (selected : (selectOperand env limits visit ctx term).orElse
          (fun _ => select env limits.typingFuel visit ctx term) = some result) : Step env ctx term result :=
        (orElse_result selected).elim (selectOperand_sound (fun found => ih found)) head
      have proof (selected : (selectLoop env limits term).orElse
          (fun _ => selectEvidence visit ctx term) = some result) : Step env ctx term result :=
        (orElse_result selected).elim selectLoop_sound (selectEvidence_sound (fun found => ih found))
      cases positions with
      | heads => exact head stepped
      | operands => exact argument stepped
      | proofs => exact (orElse_result stepped).elim argument proof
      | comparisons =>
          rcases orElse_result stepped with selected | selected
          · exact argument selected
          · exact (orElse_result selected).elim (fun comparison => .comparison (ProofComparison.select?_sound comparison)) proof

private def observePositions? (env : Environment) (limits : Limits) (ctx : Context) (positions : Positions) :
    Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, term =>
      if 4 * (treeSize term + 1)^2 > limits.budget then none
      else if Semantics.PureArithmetic.recognizes env limits.conversionFuel limits.budget (fuel + 1) term then some term
      else (step? env limits positions (fuel + 1) ctx term).bind (observePositions? env limits ctx positions fuel)

private theorem observePositions?_sound (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx term type)
    (observed : observePositions? env limits ctx positions fuel term = some result) :
    PureTyping.HasType env ctx result type ∧ Recognized env result := by
  induction fuel generalizing term result with
  | zero => contradiction
  | succ fuel ih =>
      simp only [observePositions?] at observed
      split at observed
      · contradiction
      split at observed
      · rename_i recognized
        cases observed
        exact ⟨typed, Semantics.PureArithmetic.recognizes_sound recognized⟩
      · obtain ⟨next, stepped, checked⟩ := Option.bind_eq_some_iff.mp observed
        exact ih ((step?_sound stepped).preserves wf typed) checked

/-- The previous successful paths keep their result. The final replay can
also select a computed comparison branch. -/
def observe? (env : Environment) (limits : Limits) (ctx : Context) (fuel : Nat) (term : Term) : Option Term :=
  (observePositions? env limits ctx .heads fuel term).orElse
    (fun _ => (observePositions? env limits ctx .operands fuel term).orElse
      (fun _ => (observePositions? env limits ctx .proofs fuel term).orElse
        (fun _ => observePositions? env limits ctx .comparisons fuel term)))

theorem observe?_sound (wf : UnifiedProgram.EnvWellFormed env) (typed : PureTyping.HasType env ctx term type)
    (observed : observe? env limits ctx fuel term = some result) :
    PureTyping.HasType env ctx result type ∧ Recognized env result := by
  rcases orElse_result observed with head | replay
  · exact observePositions?_sound wf typed head
  · rcases orElse_result replay with operands | proofs
    · exact observePositions?_sound wf typed operands
    · exact (orElse_result proofs).elim (observePositions?_sound wf typed) (observePositions?_sound wf typed)

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

private def dependentProof : Term := .lam true .u64 (.zeroLe (.var 0))
private def computedOperand : Term := .app (.lam false .u64 (.var 0)) (.natural 3)
private def dependentApplication : Term := .app dependentProof computedOperand
private def dependentResidual : Term := .app dependentProof (.natural 3)
private def dependentAnnotation : Term :=
  .lt (.free (.alloc (.natural 1) (.integer 0)) (.natural 0)) (.natural 4)

/-- Reducing the dependent operand before beta exposes a checked affine
application. Head-only replay substitutes the reducible operand under ZeroLe,
where the arithmetic recognizer cannot read it directly. -/
theorem checked_dependent_argument :
    observePositions? .empty limits [] .heads 8 dependentApplication = none ∧
    observe? .empty limits [] 8 dependentApplication = some dependentResidual ∧
      UniversalTruth .empty dependentAnnotation := by
  have checked : PureTyping.Checker.check? .empty limits.typingFuel limits.conversionFuel limits.budget []
      dependentApplication dependentAnnotation = some .prop := by cbv
  have observed : observe? .empty limits [] 8 dependentApplication = some dependentResidual := by cbv
  exact ⟨by cbv, observed, checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked observed⟩

private def inductionCount : Term := .uadd (.natural 1) (.natural 1)
private def inductionMotive : Term := .lam false .u64 (.lt (.var 0) (.uadd (.var 0) (.natural 1)))
private def inductionStep : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (inductionCount.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) (.natural 1)))
      (.ltAdd (.var 2) (.uadd (.var 2) (.natural 1)) (.natural 1) (.var 0))))
private def inductionDeclaration : GlobalDeclaration :=
  ⟨.lt (.free (.alloc (.natural 1) (.integer 0)) (.natural 2)) (.natural 3),
    .loop inductionCount inductionMotive proof inductionStep⟩
private def inductionEnvironment : Environment := ⟨#[inductionDeclaration], #[]⟩
private def inductionLimits : Limits := ⟨32, 32, 200000⟩
private def inductionResidual : Term :=
  .ltAdd (.natural 1) (.uadd (.natural 1) (.natural 1)) (.natural 1)
    (.ltAdd (.natural 0) (.uadd (.natural 0) (.natural 1)) (.natural 1) proof)

/-- The admitted dependent Loop uses two actual, nested induction
hypotheses. Replaying ordinary operands alone cannot expose the result. -/
theorem checked_nested_induction :
    observePositions? inductionEnvironment inductionLimits [] .operands 24 inductionDeclaration.value = none ∧
    observe? inductionEnvironment inductionLimits [] 24 inductionDeclaration.value = some inductionResidual ∧
      UniversalTruth inductionEnvironment inductionDeclaration.type := by
  have admitted : PureMixedAdmission.checkProgram ⟨32, 32, 32, 200000⟩ [inductionDeclaration] [] =
      some inductionEnvironment := by cbv
  have history := PureMixedAdmission.checkProgram_sound admitted
  have found : inductionEnvironment.globals[0]? = some inductionDeclaration := rfl
  have observed : observe? inductionEnvironment inductionLimits [] 24 inductionDeclaration.value =
      some inductionResidual := by cbv
  obtain ⟨typed, recognized⟩ := observe?_sound history.wellFormed (history.global_value_and_reference found).1 observed
  exact ⟨by cbv, observed, Semantics.PureArithmetic.recognized_fundamental history.wellFormed typed recognized⟩

private def comparisonMotive : Term :=
  .lam false .u64 (.lt (.uadd (.var 1) (.natural 0)) (.uadd (.var 1) (.natural 1)))
private def comparisonEquality : Term := .ifEq (.natural 0) (.natural 0) (.var 0) (.refl (.natural 0))
private def comparisonFunction : Term :=
  .lam false .u64 (.ifLt (.uadd (.var 0) (.natural 0)) (.uadd (.var 0) (.natural 1)) (.var 0)
    (.transport comparisonMotive comparisonEquality
      (.ltAdd (.natural 0) (.natural 1) (.var 0) proof)))
private def comparisonInput : Term := .app comparisonFunction (.natural 3)
private def comparisonAnnotation : Term :=
  .lt (.free (.alloc (.natural 1) (.integer 0)) (.natural 3)) (.natural 4)
private def comparisonResidual : Term := .decide (.uadd (.natural 3) (.natural 0)) (.uadd (.natural 3) (.natural 1))

/-- An actual beta step supplies the original operands of the comparison.
The true branch uses its erased source evidence while keeping the dependent type. -/
theorem checked_dependent_comparison :
    observePositions? .empty limits [] .proofs 16 comparisonInput = none ∧
    observe? .empty limits [] 16 comparisonInput = some comparisonResidual ∧
      UniversalTruth .empty comparisonAnnotation := by
  have checked : PureTyping.Checker.check? .empty limits.typingFuel limits.conversionFuel limits.budget []
      comparisonInput comparisonAnnotation = some .prop := by cbv
  have observed : observe? .empty limits [] 16 comparisonInput = some comparisonResidual := by cbv
  exact ⟨by cbv, observed, checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked observed⟩

private def equalityLeft : Term := .uadd (.natural 1) (.natural 1)
private def equalityInput : Term := .ifEq equalityLeft (.natural 2) (.var 0) (.refl (.natural 2))
private def equalityAnnotation : Term := .eq (.free (.alloc (.natural 1) (.integer 0)) (.natural 2)) (.natural 2)

/-- Reflexivity from the computed true branch retains the left operand's
source syntax, and the requested equality still includes the Free annotation. -/
theorem checked_computed_equality_comparison :
    observe? .empty limits [] 12 equalityInput = some (.refl equalityLeft) ∧ UniversalTruth .empty equalityAnnotation := by
  have checked : PureTyping.Checker.check? .empty limits.typingFuel limits.conversionFuel limits.budget []
      equalityInput equalityAnnotation = some .prop := by cbv
  have observed : observe? .empty limits [] 12 equalityInput = some (.refl equalityLeft) := by cbv
  exact ⟨observed, checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked observed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.PureProofObservation
