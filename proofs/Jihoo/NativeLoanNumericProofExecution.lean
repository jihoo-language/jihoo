import Jihoo.NativeCoreNumericalObservation
import Jihoo.NativeLoanProofNormalization

/-! Numerical proof checking observes the actual computed operands of
the original derivation. The finite tree can represent a wide ghost sum. -/
namespace Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic

open LoanTyping

/-- The exact returned value comes from the numeric tree exposed by
raw conversion's bounded normalizer. -/
def normalizedWord? (env : Environment) (budget fuel : Nat) (term : Term) : Option Nat := do
  let residual ← RawLend.normalize? env budget fuel term
  let value ← NativeCoreNumericalObservation.evaluate residual
  pure value.val

theorem normalizedWord?_sound (accepted : normalizedWord? env budget fuel term = some value) :
    Numeric env term value := by
  unfold normalizedWord? at accepted
  obtain ⟨residual,normalized,checked⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨witness,_,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases checked
  exact ⟨residual,RawLend.normalize?_sound normalized,witness.property⟩

private def operand? (env : Environment) (budget fuel : Nat) (observe : Term → Term) (values : Nat → Term) (term : Term) :
    Option (PLift (∃ value, Numeric env (observe (term.subst values)) value)) :=
  match observed : normalizedWord? env budget fuel (observe (term.subst values)) with
  | some value => some ⟨⟨value,normalizedWord?_sound observed⟩⟩
  | none => none

private theorem operand?_present
    (accepted : normalizedWord? env budget fuel (observe (term.subst values)) = some value) :
    (operand? env budget fuel observe values term).isSome = true := by
  unfold operand?
  split
  · rfl
  · rename_i missing
    rw [accepted] at missing
    contradiction

/-- Every accepted arithmetic node builds the proof of the original
operand observations. Erased or effect-only prefixes need no values. -/
def observationsUsing? (env : Environment) (budget fuel : Nat) (observe : Term → Term) (values : Nat → Term) :
    (term : Term) → Option (PLift (ObservedEvidenceUsing
      (fun operand => ∃ value, Numeric env (observe (operand.subst values)) value) term))
  | .decide _ _ => some ⟨by simp only [ObservedEvidenceUsing]⟩
  | .zeroLe a => (operand? env budget fuel observe values a).map fun observed =>
    ⟨by
      simp only [ObservedEvidenceUsing]
      exact observed.down⟩
  | .ltAdd a b c proof => do
    let first ← operand? env budget fuel observe values a
    let second ← operand? env budget fuel observe values b
    let offset ← operand? env budget fuel observe values c
    let nested ← observationsUsing? env budget fuel observe values proof
    pure ⟨by
      simp only [ObservedEvidenceUsing]
      exact ⟨first.down,second.down,offset.down,nested.down⟩⟩
  | .ltCancel a b c proof => do
    let first ← operand? env budget fuel observe values a
    let second ← operand? env budget fuel observe values b
    let offset ← operand? env budget fuel observe values c
    let nested ← observationsUsing? env budget fuel observe values proof
    pure ⟨by
      simp only [ObservedEvidenceUsing]
      exact ⟨first.down,second.down,offset.down,nested.down⟩⟩
  | .ltLe a b c first second => do
    let lower ← operand? env budget fuel observe values a
    let middle ← operand? env budget fuel observe values b
    let upper ← operand? env budget fuel observe values c
    let first ← observationsUsing? env budget fuel observe values first
    let second ← observationsUsing? env budget fuel observe values second
    pure ⟨by
      simp only [ObservedEvidenceUsing]
      exact ⟨lower.down,middle.down,upper.down,first.down,second.down⟩⟩
  | .strict _ rest => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values rest
  | .free _ rest => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values rest
  | .node (.drop _) [_,rest] => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values rest
  | .ifLt _ _ _ rest => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values rest
  | .ifEq _ _ _ rest => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values rest
  | .absurd _ proof => by
    simpa only [ObservedEvidenceUsing] using observationsUsing? env budget fuel observe values proof
  | _ => none
termination_by term => sizeOf term

def observations? (env : Environment) (budget fuel : Nat) (values : Nat → Term) (term : Term) :
    Option (PLift (ObservedEvidence env values term)) :=
  observationsUsing? env budget fuel id values term

def projectedObservations? (env : Environment) (budget fuel : Nat) (values : Nat → Term) (term : Term) :
    Option (PLift (ProjectedObserved env values term)) :=
  observationsUsing? env budget fuel (ValueErasure.Loan.project env) values term

/-- Offsetting a checked inequality and then cancelling the same offset
uses the same three original word observations throughout. -/
theorem observes_added_and_cancelled_bound
    (left : normalizedWord? env budget fuel a = some leftValue)
    (right : normalizedWord? env budget fuel b = some rightValue)
    (offset : normalizedWord? env budget fuel c = some offsetValue)
    (evidence : (observations? env budget fuel Term.var proof).isSome = true) :
    (observations? env budget fuel Term.var (.ltCancel a b c (.ltAdd a b c proof))).isSome = true := by
  have leftSeen : (operand? env budget fuel id Term.var a).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using left)
  have rightSeen : (operand? env budget fuel id Term.var b).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using right)
  have offsetSeen : (operand? env budget fuel id Term.var c).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using offset)
  obtain ⟨_,keptLeft⟩ := Option.isSome_iff_exists.mp leftSeen
  obtain ⟨_,keptRight⟩ := Option.isSome_iff_exists.mp rightSeen
  obtain ⟨_,keptOffset⟩ := Option.isSome_iff_exists.mp offsetSeen
  obtain ⟨_,keptEvidence⟩ := Option.isSome_iff_exists.mp evidence
  change observationsUsing? env budget fuel id Term.var proof = _ at keptEvidence
  simp [observations?,observationsUsing?,keptLeft,keptRight,keptOffset,keptEvidence] <;> rfl

theorem computed_proof_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (accepted : (observations? env budget fuel values term).isSome = true) :
    Order env (type.subst values) := by
  cases found : observations? env budget fuel values term with
  | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at accepted
  | some checked => exact observed_evidence_order wf typed checked.down

/-- A successful operand visit may use source value projection before
normalization. The order statement keeps the pure interpretation of the
original annotation. -/
theorem computed_projected_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (accepted : (projectedObservations? env budget fuel values term).isSome = true) :
    Order env (ValueErasure.Loan.project env (type.subst values)) := by
  cases found : projectedObservations? env budget fuel values term with
  | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at accepted
  | some checked => exact projected_pure_evidence_order wf typed checked.down

theorem computed_projected_excludes_zero (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env [] term (.lt left (.natural 0)))
    (accepted : (projectedObservations? env budget fuel Term.var term).isSome = true) : False := by
  cases found : projectedObservations? env budget fuel Term.var term with
  | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at accepted
  | some checked => exact projected_closed_evidence_excludes_zero wf typed checked.down

/-- The mixed history justifies the root computation at the original type.
Projected operand visits then establish order even if an operand has a
value-irrelevant prefix. -/
theorem normalized_projected_proof_order (history : MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env [] [] true term type)
    (normalized : ProofNormalization.normalize? env budget reductionFuel term = some residual)
    (accepted : (projectedObservations? env budget operandFuel Term.var residual).isSome = true) :
    Order env (ValueErasure.Loan.project env type) := by
  have preserved := ProofNormalization.normalize?_preserves history typed normalized
  simpa only [Term.subst_id] using computed_projected_order history.wellFormed (.native preserved) accepted

/-- A checked prefix can expose the proof head by typed delta, beta, or
family computation. The arithmetic checker then observes the remaining
operands and retains the requested original closed result. -/
def closedProof? (env : Environment) (budget reductionFuel operandFuel : Nat) (term : Term) : Option Term := do
  let residual ← ProofNormalization.normalize? env budget reductionFuel term
  if (observations? env budget operandFuel Term.var residual).isSome then some residual else none

theorem closedProof?_order (history : MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env [] [] true term type)
    (accepted : closedProof? env budget reductionFuel operandFuel term = some residual) :
    Order env type := by
  unfold closedProof? at accepted
  obtain ⟨selected,normalized,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i known
    have order := computed_proof_order history.wellFormed
      (ProofNormalization.normalize?_preserves history typed normalized) known
    simpa only [Term.subst_id] using order
  · cases accepted

theorem closedProof?_excludes_zero_upper (history : MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env [] [] true term (.lt left (.natural 0)))
    (accepted : closedProof? env budget reductionFuel operandFuel term = some residual) : False :=
  (closedProof?_order history typed accepted).no_zero_upper history.wellFormed.admissible

theorem checked_global_computed_order (history : MixedProgram.History definitions declarations env)
    (found : env.globals[index]? = some declaration)
    (accepted : closedProof? env budget reductionFuel operandFuel (.node (.global index) []) = some residual) :
    Order env declaration.type := by
  have typed : LoanTyping.HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) :=
    .global found
  rw [Term.rename_id] at typed
  exact closedProof?_order history typed accepted

theorem checked_global_computed_excludes_zero_upper (history : MixedProgram.History definitions declarations env)
    (found : env.globals[index]? = some declaration)
    (accepted : closedProof? env budget reductionFuel operandFuel (.node (.global index) []) = some residual)
    (requested : RawLend.Conv env declaration.type (.lt left (.natural 0))) : False :=
  ((checked_global_computed_order history found accepted).convert requested).no_zero_upper history.wellFormed.admissible

private def applied (value : Nat) : Term :=
  .app (.lam false .u64 (.var 0)) (.natural value)

private def offset : Term := applied (2^64-1)
private def low : Term := .uadd (applied 0) offset
private def high : Term := .uadd (applied 1) offset

private def wideProof : GlobalDeclaration :=
  ⟨.lt low high,.ltAdd (applied 0) (applied 1) offset (.decide (applied 0) (applied 1))⟩

private def world : Environment := ⟨#[wideProof],#[]⟩

/-- The mixed checker accepts the original proof with computed operands.
Their real observations recover the wide result and establish strict order. -/
theorem admitted_computed_wide_proof :
    Order world wideProof.type ∧ (2^64-1 : Nat) < 2^64 := by
  have admitted : MixedProgram.checkProgram 64 64 [wideProof] [] = some world := by cbv
  have history := MixedProgram.checkProgram_sound admitted
  obtain ⟨_,_,typed⟩ := history.global_typing (index := 0) (declaration := wideProof) rfl
  have zero : normalizedWord? world 200000 32 (applied 0) = some 0 := by cbv
  have one : normalizedWord? world 200000 32 (applied 1) = some 1 := by cbv
  have maximum : normalizedWord? world 200000 32 offset = some (2^64-1) := by cbv
  have seenZero : (operand? world 200000 32 id Term.var (applied 0)).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using zero)
  have seenOne : (operand? world 200000 32 id Term.var (applied 1)).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using one)
  have seenMax : (operand? world 200000 32 id Term.var offset).isSome = true :=
    operand?_present (by simpa only [Term.subst_id,id_eq] using maximum)
  obtain ⟨_,zeroRead⟩ := Option.isSome_iff_exists.mp seenZero
  obtain ⟨_,oneRead⟩ := Option.isSome_iff_exists.mp seenOne
  obtain ⟨_,maxRead⟩ := Option.isSome_iff_exists.mp seenMax
  have checked : (observations? world 200000 32 Term.var wideProof.value).isSome = true := by
    simp [wideProof,observations?,observationsUsing?,zeroRead,oneRead,maxRead] <;> rfl
  have ordered : Order world wideProof.type := by
    simpa only [Term.subst_id] using computed_proof_order history.wellFormed typed checked
  have first : normalizedWord? world 200000 32 low = some (2^64-1) := by cbv
  have second : normalizedWord? world 200000 32 high = some (2^64) := by cbv
  exact ⟨ordered,ordered.reflect history.wellFormed.admissible
    (normalizedWord?_sound first) (normalizedWord?_sound second)⟩

private def strictWord : Term := .strict (.integer 3) (.natural 0)
private def strictDeclaration : GlobalDeclaration :=
  ⟨.lt (.natural 0) (.uadd strictWord (.natural 1)),.zeroLe strictWord⟩
private def strictWorld : Environment := ⟨#[strictDeclaration],#[]⟩

/-- Actual computed observations follow the value projection of a Strict
operand in a proof whose original type the mixed checker admitted. -/
theorem observed_projected_strict_order :
    (projectedObservations? strictWorld 200000 32 Term.var strictDeclaration.value).isSome = true ∧
      Order strictWorld (ValueErasure.Loan.project strictWorld strictDeclaration.type) := by
  have admitted : MixedProgram.checkProgram 64 64 [strictDeclaration] [] = some strictWorld := by cbv
  have history := MixedProgram.checkProgram_sound admitted
  obtain ⟨_,_,typed⟩ := history.global_typing (index := 0) (declaration := strictDeclaration) rfl
  have read : normalizedWord? strictWorld 200000 32 (ValueErasure.Loan.project strictWorld strictWord) = some 0 := by cbv
  have seen : (operand? strictWorld 200000 32 (ValueErasure.Loan.project strictWorld) Term.var strictWord).isSome = true :=
    operand?_present (by simpa only [Term.subst_id] using read)
  obtain ⟨_,kept⟩ := Option.isSome_iff_exists.mp seen
  have checked : (projectedObservations? strictWorld 200000 32 Term.var strictDeclaration.value).isSome = true := by
    simp [strictDeclaration,projectedObservations?,observationsUsing?,kept] <;> rfl
  exact ⟨checked,by
    simpa only [Term.subst_id] using computed_projected_order history.wellFormed (.native (typed.ghost [])) checked⟩

end Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
