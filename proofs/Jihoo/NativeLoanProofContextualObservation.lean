import Jihoo.NativeLoanProofTransportObservation

/-! Bounded replay of Transport at nested arithmetic evidence positions, also
after finite Loop unrolling. Each parent constructor uses its original operand
types and original indices. Literal Strict exposure happens only in reflexive
equality evidence and does not assert a new RawLend conversion. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofContextualObservation
open NativeKernel.Conversion (treeSize)

private def replayOperands? (visit : Term → Option Term) : Term → Option Term
  | .ltAdd a b c proof => (visit proof).map (.ltAdd a b c)
  | .ltCancel a b c proof => (visit proof).map (.ltCancel a b c)
  | .ltLe a b c lower upper => do
      let lower ← visit lower
      let upper ← visit upper
      pure (.ltLe a b c lower upper)
  | .strict first rest => (visit rest).map (.strict first)
  | .free owner rest => (visit rest).map (.free owner)
  | .node (.drop family) [owner,rest] => (visit rest).map (fun result => .node (.drop family) [owner,result])
  | .ifLt left right yes no => (visit no).map (.ifLt left right yes)
  | .ifEq left right yes no => (visit no).map (.ifEq left right yes)
  | .absurd target proof => (visit proof).map (.absurd target)
  | term@(.transport _ _ _) => (ProofTransportObservation.exposeTransport? term).bind visit
  | _ => none

private theorem replayOperands_preserves (visit : Term → Option Term)
    (visitSound : ∀ {ctx input type result}, HasType env [] ctx true input type →
      visit input = some result → HasType env [] ctx true result type)
    (typed : HasType env loans ctx mode term type) (mapped : replayOperands? visit term = some result) :
    HasType env [] ctx true result type := by
  revert result
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => ∀ result, replayOperands? visit term = some result →
      HasType env [] ctx true result type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (next result mapped => simp only [replayOperands?] at mapped; contradiction)
  case ltAdd left right shift proof ihLeft ihRight ihShift ihProof result mapped =>
    obtain ⟨proof',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .ltAdd (left.ghost []) (right.ghost []) (shift.ghost []) (visitSound (proof.ghost []) ran)
  case ltCancel left right shift proof ihLeft ihRight ihShift ihProof result mapped =>
    obtain ⟨proof',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .ltCancel (left.ghost []) (right.ghost []) (shift.ghost []) (visitSound (proof.ghost []) ran)
  case ltLe left middle right lower upper ihLeft ihMiddle ihRight ihLower ihUpper result mapped =>
    obtain ⟨lower',ranLower,mapped⟩ := Option.bind_eq_some_iff.mp mapped
    obtain ⟨upper',ranUpper,exactResult⟩ := Option.bind_eq_some_iff.mp mapped
    cases exactResult
    exact .ltLe (left.ghost []) (middle.ghost []) (right.ghost [])
      (visitSound (lower.ghost []) ranLower) (visitSound (upper.ghost []) ranUpper)
  case strict first rest ihFirst ihRest result mapped =>
    obtain ⟨rest',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .strict (first.ghost []) (visitSound (rest.ghost []) ran)
  case free owner rest ihOwner ihRest result mapped =>
    obtain ⟨rest',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .free (owner.ghost []) (visitSound (rest.ghost []) ran)
  case drop found boxed owner rest ihOwner ihRest result mapped =>
    obtain ⟨rest',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .drop found boxed (owner.ghost []) (visitSound (rest.ghost []) ran)
  case ifLt left right yes no ihLeft ihRight ihYes ihNo result mapped =>
    obtain ⟨no',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .ifLt (left.ghost []) (right.ghost []) (yes.ghost []) (visitSound (no.ghost []) ran)
  case ifEq left right yes no ihLeft ihRight ihYes ihNo result mapped =>
    obtain ⟨no',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .ifEq (left.ghost []) (right.ghost []) (yes.ghost []) (visitSound (no.ghost []) ran)
  case absurd target proof allowed ihTarget ihProof result mapped =>
    obtain ⟨proof',ran,rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact .absurd (target.ghost []) (visitSound (proof.ghost []) ran) (Or.inl rfl)
  case transport motive evidence proof ihMotive ihEvidence ihProof result mapped =>
    obtain ⟨exposed, observed, visited⟩ := Option.bind_eq_some_iff.mp mapped
    exact visitSound (ProofTransportObservation.exposeTransport?_preserves (mode := true)
      (.transport (motive.ghost []) (evidence.ghost []) (proof.ghost [])) observed) visited
  case convert source converted ih result mapped => exact (ih _ mapped).convert converted
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches result mapped
    cases analysis <;> simp [replayOperands?] at mapped

private def replayRoot? (env : Environment) (budget countFuel reductionFuel : Nat)
    (visit : Term → Option Term) : Term → Option Term
  | term@(.loop _ _ _ _) => (ProofLoop.normalizeLoop? env budget countFuel reductionFuel term).bind visit
  | term => replayOperands? visit term

private theorem replayRoot_preserves (visit : Term → Option Term)
    (visitSound : ∀ {ctx input type result}, HasType env [] ctx true input type →
      visit input = some result → HasType env [] ctx true result type)
    (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env [] ctx true term type)
    (replayed : replayRoot? env budget countFuel reductionFuel visit term = some result) :
    HasType env [] ctx true result type := by
  unfold replayRoot? at replayed
  split at replayed
  · obtain ⟨unrolled, observed, visited⟩ := Option.bind_eq_some_iff.mp replayed
    exact visitSound (ProofLoop.normalizeLoop?_preserves history typed observed) visited
  · exact replayOperands_preserves visit visitSound typed replayed

private theorem rootObservation_bounded
    (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode term type)
    (observed : ProofTransportObservation.observe? env budget countFuel reductionFuel fuel term = some residual) :
    treeSize residual ≤ budget := by
  unfold ProofTransportObservation.observe? at observed
  split at observed
  · rename_i output original
    cases observed
    exact (ProofTreeObservation.observe?_sound history typed original).2.2
  · obtain ⟨normalized, ran, observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨exposed, exposure, observed⟩ := Option.bind_eq_some_iff.mp observed
    have typedNormal := ProofNormalization.normalize?_preserves history typed ran
    have typedReplay := ProofTransportObservation.exposeTransport?_preserves typedNormal exposure
    exact (ProofTreeObservation.observe?_sound history typedReplay observed).2.2

/-- Keep successful root and tree observations and try contextual replay only
when the existing observer gets stuck. Replay consumes one recursion level
per repaired operand, transport exposure, or finite induction replay. -/
def observe? (env : Environment) (budget countFuel reductionFuel : Nat) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, term =>
    match ProofTransportObservation.observe? env budget countFuel reductionFuel (fuel + 1) term with
    | some residual => some residual
    | none => do
      let normalized ← ProofNormalization.normalize? env budget reductionFuel term
      let residual ← replayRoot? env budget countFuel reductionFuel
        (observe? env budget countFuel reductionFuel fuel) normalized
      if treeSize residual ≤ budget ∧ ProofObservation.supported residual = true then some residual else none

theorem observe?_extends_transport
    (observed : ProofTransportObservation.observe? env budget countFuel reductionFuel fuel term = some residual) :
    observe? env budget countFuel reductionFuel fuel term = some residual := by
  cases fuel with
  | zero => simp [ProofTransportObservation.observe?, ProofTreeObservation.observe?] at observed
  | succ fuel => simp only [observe?, observed]

theorem observe?_extends_tree
    (observed : ProofTreeObservation.observe? env budget countFuel reductionFuel fuel term = some residual) :
    observe? env budget countFuel reductionFuel fuel term = some residual :=
  observe?_extends_transport (by simp only [ProofTransportObservation.observe?, observed])

theorem observe?_sound (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode term type)
    (observed : observe? env budget countFuel reductionFuel fuel term = some residual) :
    HasType env [] ctx true residual type ∧ Semantics.LoanArithmetic.Supported residual ∧
      treeSize residual ≤ budget := by
  induction fuel generalizing loans ctx mode term type residual with
  | zero => simp [observe?] at observed
  | succ fuel ih =>
    unfold observe? at observed
    split at observed
    · rename_i output original
      cases observed
      obtain ⟨typedResult, supported⟩ := ProofTransportObservation.observe?_sound history typed original
      exact ⟨typedResult, supported, rootObservation_bounded history typed original⟩
    · obtain ⟨normalized, ran, observed⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨result, replayed, observed⟩ := Option.bind_eq_some_iff.mp observed
      have typedNormal := ProofNormalization.normalize?_preserves history typed ran
      have typedResult := replayRoot_preserves _
        (fun typed visited => (ih typed visited).1) history typedNormal replayed
      split at observed
      · rename_i within
        cases observed
        exact ⟨typedResult, (ProofObservation.supported_iff _).mp within.2, within.1⟩
      · contradiction

/-- The successful observation of the stored global supplies both the exact
type of its evidence and the arithmetic interpretation of its annotation. -/
theorem observed_global_truth (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env budget countFuel reductionFuel fuel (.node (.global index) []) = some residual) :
    Semantics.LoanArithmetic.Truth env declaration.type := by
  have typed : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  rw [Term.rename_id] at typed
  obtain ⟨observedTyped, supported, _⟩ := observe?_sound history typed observed
  exact Semantics.LoanArithmetic.supported_truth history.wellFormed observedTyped supported

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def three : Term := .natural 3
private def count : Term := .uadd one one
private def motive : Term := .lam false .u64 (.lt (.var 0) (.uadd (.var 0) one))

private def computedEquality (index : Term) : Term :=
  .strict count (.refl (.uadd index zero))

private def step : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (count.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) one))
      (.ltAdd (.var 2) (.uadd (.var 2) one) one
        (.transport motive (computedEquality (.var 2)) (.var 0)))))

private def exampleDeclaration : GlobalDeclaration :=
  ⟨.lt three (.natural 4), .ltAdd two three one (.loop count motive (.decide zero one) step)⟩

private def exampleEnv : Environment := ⟨#[exampleDeclaration], #[]⟩

private def exampleResidual : Term :=
  .ltAdd two three one (.ltAdd one two one (.ltAdd zero one one (.decide zero one)))

/-- The mixed checker admits the original proof. After finite computed-count
induction, each Transport's closed computed equality exposes its genuine
induction hypothesis, even within the nested LtAdd proof operands. -/
theorem checked_nested_transport_induction :
    ProofTransportObservation.observe? exampleEnv 200000 32 32 10 (.node (.global 0) []) = none ∧
    observe? exampleEnv 200000 32 32 10 (.node (.global 0) []) = some exampleResidual ∧
    Semantics.LoanArithmetic.Truth exampleEnv exampleDeclaration.type := by
  have admitted : MixedProgram.checkProgram 32 32 [exampleDeclaration] [] = some exampleEnv := by cbv
  have observed : observe? exampleEnv 200000 32 32 10 (.node (.global 0) []) = some exampleResidual := by cbv
  have oldBlocked : ProofTransportObservation.observe? exampleEnv 200000 32 32 10
      (.node (.global 0) []) = none := by cbv
  exact ⟨oldBlocked, observed, observed_global_truth (MixedProgram.checkProgram_sound admitted) rfl observed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ProofContextualObservation
