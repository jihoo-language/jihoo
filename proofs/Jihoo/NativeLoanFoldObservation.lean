import Jihoo.NativeLoanFoldUnrolling
import Jihoo.NativeLoanProofLoopObservation

/-! Observing a bounded Fold reuses the same precharged unroller as
dependent Loop. Subsequent contextual reduction keeps the original
accumulator type. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FoldUnrolling

def normalizeFold? (env : Environment) (budget countFuel reductionFuel : Nat) : Term → Option Term
  | .fold count initial body => ProofLoop.normalizeIteration? env budget countFuel reductionFuel count initial body
  | _ => none

theorem normalizeFold?_preserves (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.fold count initial body) type)
    (accepted : normalizeFold? env budget countFuel reductionFuel (.fold count initial body) = some result) :
    HasType env [] ctx true result type :=
  ProofLoop.normalizeIteration_preserves history
    (fun exactCount range => unroll_preserves typed exactCount range _ (Nat.le_refl _)) accepted

private def count := Term.uadd (.natural 1) (.natural 2)

private def callback :=
  Term.lam false .u64 (.lam true (.lt (.var 0) (count.rename Nat.succ))
    (.lam false .i64 (.var 0)))

private def signedFold : GlobalDeclaration := ⟨.i64,.fold count (.integer 7) callback⟩
private def checkedWorld : Environment := ⟨#[signedFold],#[]⟩

/-- A checked Fold at a computed count returns the original signed
accumulator. The small allowance rejects before building the unroll. -/
theorem computed_signed_fold_observation :
    HasType checkedWorld [] [] true (.integer 7) signedFold.type ∧
      normalizeFold? checkedWorld 16 64 64 signedFold.value = none := by
  have admitted : MixedProgram.checkProgram 64 64 [signedFold] [] = some checkedWorld := by cbv
  have history := MixedProgram.checkProgram_sound admitted
  have selected : checkedWorld.globals[0]? = some signedFold := rfl
  obtain ⟨_,_,typed⟩ := history.global_typing selected
  have ran : normalizeFold? checkedWorld 200000 64 64 signedFold.value = some (.integer 7) := by cbv
  exact ⟨normalizeFold?_preserves history typed ran,by cbv⟩

end Jihoo.NativeKernel.Environment.LoanTyping.FoldUnrolling
