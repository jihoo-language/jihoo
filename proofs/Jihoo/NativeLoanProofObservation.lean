import Jihoo.NativeLoanProofLoopObservation

/-! Observe closed arithmetic proof results from the executable Loan64
source evaluator. A root proof Loop can continue by finite unrolling. The
residual syntax is checked by the observer, and its exact type follows from
preservation along the resulting executable path. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofObservation

private def affine (term : Term) : Bool := (AffineSum.parse term).isSome

private theorem affine_iff : affine term = true ↔ ∃ e : AffineSum.Expr, e.toTerm = term := by
  constructor
  · intro parsed
    unfold affine at parsed
    obtain ⟨expr,found⟩ := Option.isSome_iff_exists.mp parsed
    exact ⟨expr,AffineSum.parse_sound found⟩
  · rintro ⟨expr,rfl⟩
    simp [affine,AffineSum.parse_toTerm]

/-- Recognize precisely the residual grammar of the mathematical arithmetic
truth proof. This check supplies no typing or equality judgment. -/
def supported : Term → Bool
  | .decide _ _ => true
  | .zeroLe a => affine a
  | .ltAdd a b c proof | .ltCancel a b c proof => affine a && affine b && affine c && supported proof
  | .ltLe a b c first second => affine a && affine b && affine c && supported first && supported second
  | .strict _ rest | .free _ rest | .node (.drop _) [_,rest] => supported rest
  | .ifLt _ _ _ rest | .ifEq _ _ _ rest => supported rest
  | .absurd _ proof => supported proof
  | _ => false
termination_by term => sizeOf term

theorem supported_iff (term : Term) : supported term = true ↔ Semantics.LoanArithmetic.Supported term := by
  fun_induction supported term <;> simp_all [Semantics.LoanArithmetic.Supported,affine_iff,and_assoc]
  all_goals rfl

private def finishRoot? (env : Environment) (budget countFuel fuel : Nat) (term : Term) : Option Term :=
  match term with
  | .loop _ _ _ _ => ProofLoop.normalizeLoop? env budget countFuel fuel term
  | _ => some term

def observeProof? (env : Environment) (budget countFuel fuel : Nat) (input : Term) : Option Term := do
  let first ← ProofNormalization.normalize? env budget fuel input
  let residual ← finishRoot? env budget countFuel fuel first
  if supported residual then some residual else none

theorem observeProof?_sound (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode input type)
    (observed : observeProof? env budget countFuel fuel input = some residual) :
    HasType env [] ctx true residual type ∧ Semantics.LoanArithmetic.Supported residual := by
  unfold observeProof? at observed
  obtain ⟨first,normalized,observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨last,reduced,observed⟩ := Option.bind_eq_some_iff.mp observed
  have firstTyped := ProofNormalization.normalize?_preserves history typed normalized
  have lastTyped : HasType env [] ctx true last type := by
    unfold finishRoot? at reduced
    split at reduced
    · exact ProofLoop.normalizeLoop?_preserves history firstTyped reduced
    · cases reduced
      exact firstTyped
  split at observed
  · rename_i accepted
    cases observed
    exact ⟨lastTyped,(supported_iff _).mp accepted⟩
  · contradiction

private theorem global_original (found : env.globals[index]? = some declaration) :
    HasType env [] [] true (.node (.global index) []) declaration.type := by
  have renamed : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  simpa only [Term.rename_id] using renamed

/-- A successful observer run for a stored global derives mathematical truth
from the actual mixed history and lookup. -/
theorem checked_global_observation_truth (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observeProof? env budget countFuel fuel (.node (.global index) []) = some residual) :
    Semantics.LoanArithmetic.Truth env declaration.type := by
  obtain ⟨typed,recognition⟩ := observeProof?_sound history (global_original found) observed
  exact Semantics.LoanArithmetic.supported_truth history.wellFormed typed recognition

theorem no_checked_global_observation_less_zero (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observeProof? env budget countFuel fuel (.node (.global index) []) = some residual)
    (requested : RawLend.Conv env declaration.type (.lt left (.natural 0))) : False := by
  obtain ⟨typed,recognition⟩ := observeProof?_sound history (global_original found) observed
  exact Semantics.LoanArithmetic.no_supported_less_zero history.wellFormed (typed.convert requested) recognition

end Jihoo.NativeKernel.Environment.LoanTyping.ProofObservation
