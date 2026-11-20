import Jihoo.NativeLoanProofObservation

/-! Bounded observation of nested arithmetic evidence. The proof operands of
arithmetic constructors can be observed independently because the enclosing
typing rule requests their types without using their terms in its result index.
Each rebuilt term preserves the original Loan64 type. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofTreeObservation
open NativeKernel.Conversion (treeSize)

def mapEvidence? (visit : Term → Option Term) : Term → Option Term
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
  | _ => none

/-- Evidence positions request exact types from the original typing rule. A
visitor may use the current local context when checking a replacement. -/
theorem mapEvidence_preserves (visit : Context → Term → Option Term)
    (visitSound : ∀ {ctx input type result}, HasType env [] ctx true input type →
      visit ctx input = some result → HasType env [] ctx true result type)
    (typed : HasType env loans ctx mode term type) (mapped : mapEvidence? (visit ctx) term = some result) :
    HasType env [] ctx true result type := by
  revert result
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => ∀ result, mapEvidence? (visit ctx) term = some result →
      HasType env [] ctx true result type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (next result mapped => simp only [mapEvidence?] at mapped; contradiction)
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
  case convert source converted ih result mapped => exact (ih _ mapped).convert converted
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches result mapped
    cases analysis <;> simp [mapEvidence?] at mapped

private def finishRoot? (env : Environment) (budget countFuel reductionFuel : Nat) (term : Term) : Option Term :=
  match term with
  | .loop _ _ _ _ => ProofLoop.normalizeLoop? env budget countFuel reductionFuel term
  | _ => some term

private theorem finishRoot_preserves (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env [] ctx true term type)
    (observed : finishRoot? env budget countFuel reductionFuel term = some residual) :
    HasType env [] ctx true residual type := by
  unfold finishRoot? at observed
  split at observed
  · exact ProofLoop.normalizeLoop?_preserves history typed observed
  · cases observed
    exact typed

/-- Observe each needed proof operand with one fewer level of fuel. Each
normalization and Loop unrolling uses the given size and reduction bounds. -/
def observe? (env : Environment) (budget countFuel reductionFuel : Nat) : Nat → Term → Option Term
  | 0, _ => none
  | fuel+1, term => do
    let normalized ← ProofNormalization.normalize? env budget reductionFuel term
    let interpreted ← finishRoot? env budget countFuel reductionFuel normalized
    let result ← (if ProofObservation.supported interpreted then some interpreted
      else mapEvidence? (observe? env budget countFuel reductionFuel fuel) interpreted)
    if treeSize result ≤ budget ∧ ProofObservation.supported result = true then some result else none

/-- Successful tree observation reconstructs actual evidence of the original
type and supplies the arithmetic grammar certificate by computation. -/
theorem observe?_sound (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode term type)
    (observed : observe? env budget countFuel reductionFuel fuel term = some residual) :
    HasType env [] ctx true residual type ∧ Semantics.LoanArithmetic.Supported residual ∧ treeSize residual ≤ budget := by
  induction fuel generalizing loans ctx mode term type residual with
  | zero => simp [observe?] at observed
  | succ fuel ih =>
    unfold observe? at observed
    obtain ⟨normalized,ranNormal,observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨interpreted,ranRoot,observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨result,ranEvidence,observed⟩ := Option.bind_eq_some_iff.mp observed
    have typedNormal := ProofNormalization.normalize?_preserves history typed ranNormal
    have typedRoot := finishRoot_preserves history typedNormal ranRoot
    have typedResult : HasType env [] ctx true result type := by
      split at ranEvidence
      · cases ranEvidence
        exact typedRoot
      · exact mapEvidence_preserves (fun _ => observe? env budget countFuel reductionFuel fuel)
          (fun typed observed => (ih typed observed).1) typedRoot ranEvidence
    split at observed
    · rename_i within
      cases observed
      exact ⟨typedResult,(ProofObservation.supported_iff _).mp within.2,within.1⟩
    · contradiction

theorem checked_global_truth (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env budget countFuel reductionFuel fuel (.node (.global index) []) = some residual) :
    Semantics.LoanArithmetic.Truth env declaration.type := by
  have renamed : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  rw [Term.rename_id] at renamed
  obtain ⟨typed,supported,_⟩ := observe?_sound history renamed observed
  exact Semantics.LoanArithmetic.supported_truth history.wellFormed typed supported

theorem no_checked_global_less_zero (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env budget countFuel reductionFuel fuel (.node (.global index) []) = some residual)
    (requested : RawLend.Conv env declaration.type (.lt left (.natural 0))) : False := by
  have renamed : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  rw [Term.rename_id] at renamed
  obtain ⟨typed,supported,_⟩ := observe?_sound history renamed observed
  exact Semantics.LoanArithmetic.no_supported_less_zero history.wellFormed (typed.convert requested) supported

private def zero := Term.natural 0
private def one := Term.natural 1
private def two := Term.natural 2
private def three := Term.natural 3
private def computedCount := Term.uadd one one
private def inductionMotive := Term.lam false .u64 (.lt (.var 0) (.uadd (.var 0) one))
private def inductionStep :=
  Term.lam false .u64 (.lam true (.lt (.var 0) (computedCount.rename Nat.succ))
    (.lam true (.lt (.var 1) (.uadd (.var 1) one)) (.ltAdd (.var 2) (.uadd (.var 2) one) one (.var 0))))

private def nestedProof : GlobalDeclaration :=
  ⟨.lt three (.natural 4),
    .ltAdd two three one (.loop computedCount inductionMotive (.decide zero one) inductionStep)⟩

private def world : Environment := ⟨#[nestedProof],#[]⟩

private def evidence := Term.ltAdd two three one (.ltAdd one two one (.ltAdd zero one one (.decide zero one)))

/-- The checked global uses computed-count induction as a proof operand of
an arithmetic constructor. Each induction step uses its erased hypothesis. -/
theorem checked_nested_induction : Semantics.LoanArithmetic.Truth world nestedProof.type := by
  have admitted : MixedProgram.checkProgram 64 64 [nestedProof] [] = some world := by cbv
  have found : world.globals[0]? = some nestedProof := rfl
  have observed : observe? world 200000 64 64 4 (.node (.global 0) []) = some evidence := by cbv
  exact checked_global_truth (MixedProgram.checkProgram_sound admitted) found observed

end Jihoo.NativeKernel.Environment.LoanTyping.ProofTreeObservation
