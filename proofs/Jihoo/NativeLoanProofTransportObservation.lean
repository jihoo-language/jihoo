import Jihoo.NativeLoanProofTreeObservation
import Jihoo.NativeLoanProofNormalForms

/-! Observe a transport whose normalized equality evidence is a reflexivity
witness preceded by effect-free literal Strict prefixes. This is the literal
case of Core.normal's safe Strict elimination, followed by its existing
Transport/Refl contraction. Exposure is confined to the typed equality
operand. It adds no conversion equation for Strict. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofTransportObservation

def exposeRefl? : Term → Option Term
  | .refl value => some value
  | .strict (.natural _) rest => exposeRefl? rest
  | _ => none
termination_by term => sizeOf term

/-- Principal inversion strips only a literal Strict prefix of the evidence,
retaining all conversions to the original equality annotation. -/
theorem exposeRefl?_preserves (typed : HasType env loans ctx mode evidence type)
    (exposed : exposeRefl? evidence = some witness) :
    HasType env [] ctx true (.refl witness) type := by
  fun_induction exposeRefl? evidence with
  | case1 value =>
    cases exposed
    exact typed.ghost []
  | case2 literal rest ih =>
    obtain ⟨restType, continuation, converted⟩ := typed.principalView
    exact ih (continuation.convert converted) exposed
  | case3 => contradiction

def exposeTransport? : Term → Option Term
  | .transport family evidence payload =>
    (exposeRefl? evidence).map (fun value => .transport family (.refl value) payload)
  | _ => none

/-- The same motive, endpoints and payload type justify replay with the
exposed evidence. No equality or correctness of the original payload needs
to be supplied by the observer. -/
theorem exposeTransport?_preserves (typed : HasType env loans ctx mode input type)
    (exposed : exposeTransport? input = some result) :
    HasType env [] ctx true result type := by
  revert result
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => ∀ result,
      exposeTransport? term = some result → HasType env [] ctx true result type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (next result exposed => simp only [exposeTransport?] at exposed; contradiction)
  case transport motive evidence proof ihMotive ihEvidence ihProof result exposed =>
    obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp exposed
    exact .transport (motive.ghost []) (exposeRefl?_preserves evidence found) (proof.ghost [])
  case convert source converted ih result exposed => exact (ih _ exposed).convert converted
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches result exposed
    cases analysis <;> simp [exposeTransport?] at exposed

/-- Preserve the existing successful observation path. If it cannot
expose a proof, try literal equality exposure at the normalized root. -/
def observe? (env : Environment) (budget countFuel reductionFuel fuel : Nat) (input : Term) : Option Term :=
  match ProofTreeObservation.observe? env budget countFuel reductionFuel fuel input with
  | some residual => some residual
  | none => do
    let normalized ← ProofNormalization.normalize? env budget reductionFuel input
    let exposed ← exposeTransport? normalized
    ProofTreeObservation.observe? env budget countFuel reductionFuel fuel exposed

theorem observe?_sound (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode input type)
    (observed : observe? env budget countFuel reductionFuel fuel input = some residual) :
    HasType env [] ctx true residual type ∧ Semantics.LoanArithmetic.Supported residual := by
  unfold observe? at observed
  split at observed
  · rename_i output original
    cases observed
    obtain ⟨typedResult, supported, _⟩ := ProofTreeObservation.observe?_sound history typed original
    exact ⟨typedResult, supported⟩
  · obtain ⟨normalized, first, observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨exposed, exposure, observed⟩ := Option.bind_eq_some_iff.mp observed
    have typedNormal := ProofNormalization.normalize?_preserves history typed first
    have replay := exposeTransport?_preserves typedNormal exposure
    obtain ⟨typedResult, supported, _⟩ := ProofTreeObservation.observe?_sound history replay observed
    exact ⟨typedResult, supported⟩

theorem checked_global_truth (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env budget countFuel reductionFuel fuel (.node (.global index) []) = some residual) :
    Semantics.LoanArithmetic.Truth env declaration.type := by
  have renamed : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  rw [Term.rename_id] at renamed
  obtain ⟨typed, supported⟩ := observe?_sound history renamed observed
  exact Semantics.LoanArithmetic.supported_truth history.wellFormed typed supported

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def inequality : Term := .lt zero one
private def evidence : Term := .decide zero one
private def motive : Term := .lam false .u64 (.lt (.var 0) one)
private def wrappedEquality : Term := .strict (.natural 2) (.refl zero)
private def blocked : Term := .transport motive wrappedEquality evidence
private def source : GlobalDeclaration := ⟨inequality, blocked⟩
private def world : Environment := ⟨#[source], #[]⟩

private theorem admitted : MixedProgram.checkProgram 32 32 [source] [] = some world := by cbv

private theorem original_runs :
    ProofNormalization.normalize? world 4096 16 (.node (.global 0) []) = some blocked := by cbv

/-- The old normal form predicate cannot imply arithmetic canonical coverage.
The checked declaration normalizes successfully to a transport, while the
older observer fails even though the transport hides a concrete proof. -/
theorem admitted_normal_transport_gap :
    MixedProgram.History [source] [] world ∧
    HasType world [] [] true blocked inequality ∧ ProofNormalization.Normal world blocked ∧
    ¬Semantics.LoanArithmetic.Supported blocked ∧
    ProofTreeObservation.observe? world 4096 16 16 16 (.node (.global 0) []) = none := by
  have history := MixedProgram.checkProgram_sound admitted
  have globalTyped : HasType world [] [] true (.node (.global 0) []) (source.type.rename id) :=
    .global rfl
  rw [Term.rename_id] at globalTyped
  have unsupported : ¬Semantics.LoanArithmetic.Supported blocked := by
    simp [blocked, Semantics.LoanArithmetic.Supported]
  have failed : ProofTreeObservation.observe? world 4096 16 16 16 (.node (.global 0) []) = none := by cbv
  exact ⟨history, ProofNormalization.normalize?_preserves history globalTyped original_runs,
    ProofNormalization.normalize?_normal original_runs, unsupported, failed⟩

theorem normal_closed_lt_not_always_supported :
    ∃ definitions env left right proof, MixedProgram.History definitions [] env ∧
      HasType env [] [] true proof (.lt left right) ∧ ProofNormalization.Normal env proof ∧
      ¬Semantics.LoanArithmetic.Supported proof := by
  obtain ⟨history, typed, normal, unsupported, _⟩ := admitted_normal_transport_gap
  exact ⟨[source], world, zero, one, blocked, history, typed, normal, unsupported⟩

/-- The literal Strict/Transport replay produces actual evidence and
establishes truth of the same checked declaration's annotation. -/
theorem observes_admitted_normal_transport :
    observe? world 4096 16 16 16 (.node (.global 0) []) = some evidence ∧
    Semantics.LoanArithmetic.Truth world inequality := by
  have observed : observe? world 4096 16 16 16 (.node (.global 0) []) = some evidence := by cbv
  exact ⟨observed, checked_global_truth (MixedProgram.checkProgram_sound admitted) rfl observed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ProofTransportObservation
