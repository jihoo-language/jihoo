import Jihoo.NativeLoanProofLoopUnrolling
import Jihoo.NativeLoanProofNormalization

/-! Execute proof induction at an observed count. The original source Loop
types the finite unrolling, whose successful contextual reduction yields a
typed observation. This interprets a root Loop without giving it a raw
conversion equation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofLoop
open NativeKernel.Conversion (treeSize)

theorem unroll_treeSize (count : Nat) (initial body : Term) (i : Nat) :
    treeSize (unroll count initial body i) = treeSize initial + i * (treeSize body + 7) := by
  induction i with
  | zero => simp [unroll]
  | succ i ih =>
    simp only [unroll,Term.app,Term.decide,Term.natural,treeSize,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,ih,Nat.succ_mul]
    omega

/-- Charge the exact size of the unrolled term before allocating it. An
unavailable count, oversized unroll, or exhausted reduction returns failure. -/
def normalizeIteration? (env : Environment) (budget countFuel reductionFuel : Nat)
    (count initial body : Term) : Option Term := do
  let .natural n ← Conversion.normalize? env countFuel count | none
  if n < 2^64 ∧ treeSize initial + n * (treeSize body + 7) ≤ budget then
    ProofNormalization.normalize? env budget reductionFuel (unroll n initial body n)
  else none

theorem normalizeIteration_preserves (history : MixedProgram.History definitions familyDeclarations env)
    (typed : ∀ {n}, Conversion.Conv env count (.natural n) → n < 2^64 →
      HasType env [] ctx true (unroll n initial body n) type)
    (accepted : normalizeIteration? env budget countFuel reductionFuel count initial body = some result) :
    HasType env [] ctx true result type := by
  unfold normalizeIteration? at accepted
  obtain ⟨countTerm,observed,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · split at accepted
    · rename_i within
      exact ProofNormalization.normalize?_preserves history
        (typed (Conversion.normalize?_sound observed) within.1) accepted
    · contradiction
  · contradiction

def normalizeLoop? (env : Environment) (budget countFuel reductionFuel : Nat) : Term → Option Term
  | .loop count _ initial body => normalizeIteration? env budget countFuel reductionFuel count initial body
  | _ => none

theorem normalizeLoop?_preserves (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.loop count motive initial body) type)
    (accepted : normalizeLoop? env budget countFuel reductionFuel (.loop count motive initial body) = some result) :
    HasType env [] ctx true result type :=
  normalizeIteration_preserves history (fun exactCount range => unroll_typed history.wellFormed typed exactCount range) accepted

theorem observed_loop_truth (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.loop count motive initial body) type)
    (accepted : normalizeLoop? env budget countFuel reductionFuel (.loop count motive initial body) = some residual)
    (supported : Semantics.LoanArithmetic.Supported residual) : Semantics.LoanArithmetic.Truth env type :=
  Semantics.LoanArithmetic.supported_truth history.wellFormed (normalizeLoop?_preserves history typed accepted) supported

theorem no_observed_loop_less_zero (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.loop count motive initial body) (.lt left (.natural 0)))
    (accepted : normalizeLoop? env budget countFuel reductionFuel (.loop count motive initial body) = some residual)
    (supported : Semantics.LoanArithmetic.Supported residual) : False :=
  Semantics.LoanArithmetic.no_supported_less_zero history.wellFormed
    (normalizeLoop?_preserves history typed accepted) supported

private def zero := Term.natural 0
private def one := Term.natural 1
private def two := Term.natural 2
private def computedCount := Term.uadd one one
private def inductionMotive := Term.lam false .u64 (.lt (.var 0) (.uadd (.var 0) one))
private def inductionStep :=
  Term.lam false .u64 (.lam true (.lt (.var 0) (computedCount.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) one)) (.ltAdd (.var 2) (.uadd (.var 2) one) one (.var 0))))

private def inductionProof : GlobalDeclaration :=
  ⟨.lt two (.natural 3),.loop computedCount inductionMotive (.decide zero one) inductionStep⟩

private def inductionEnvironment : Environment := ⟨#[inductionProof],#[]⟩

private def inductionResidual := Term.ltAdd one two one (.ltAdd zero one one (.decide zero one))

/-- A real mixed-declaration check admits dependent induction at a computed
count. Both observed steps use their actual erased induction hypothesis. -/
theorem checked_computed_loop_induction : Semantics.LoanArithmetic.Truth inductionEnvironment inductionProof.type := by
  have checked : MixedProgram.checkProgram 64 64 [inductionProof] [] = some inductionEnvironment := by cbv
  have history := MixedProgram.checkProgram_sound checked
  have found : inductionEnvironment.globals[0]? = some inductionProof := rfl
  obtain ⟨_,_,typed⟩ := history.global_typing found
  have ran : normalizeLoop? inductionEnvironment 200000 64 64 inductionProof.value = some inductionResidual := by cbv
  exact observed_loop_truth history typed ran
    (by
      simp only [inductionResidual,Semantics.LoanArithmetic.Supported]
      exact ⟨⟨.literal 1,rfl⟩,⟨.literal 2,rfl⟩,⟨.literal 1,rfl⟩,
        ⟨⟨.literal 0,rfl⟩,⟨.literal 1,rfl⟩,⟨.literal 1,rfl⟩,trivial⟩⟩)

end Jihoo.NativeKernel.Environment.LoanTyping.ProofLoop
