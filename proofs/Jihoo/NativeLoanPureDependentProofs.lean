import Jihoo.NativeLoanPureDependentCodes
import Jihoo.NativeLoanPureGlobalObservation

set_option maxUniverseOffset 40

/-! Recover inhabitants of dependent proposition codes from actual ghost
typing. The syntax certificate follows checked reductions and identifies
affine leaves. It supplies neither an output derivation nor an inhabitant. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.Proofs

open Finite (Carrier Universe)
open LoanTyping.PureHypothesisObservation (ScalarExpr)

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | less (left : ScalarExpr [] a) (right : ScalarExpr [] b) :
      PureArithmetic.Recognized env term → Tree env (levels := levels) term (.less left right)
  | equal (left : ScalarExpr [] a) (right : ScalarExpr [] b) :
      PureArithmetic.Recognized env term → Tree env (levels := levels) term (.equal left right)
  | universeLambda (level : Fin 32) {result : Code (level :: levels) .proposition} : Tree env body result →
      Tree env (.lam false (.univ level.val) body) (.abstract level result)
  | universeBeta (level : Fin 32) (argument : Code levels (inputSort level)) {result : Code levels .proposition} :
      Tree env (body.subst (single argument.syntax)) result →
      Tree env (.app (.lam false (.univ level.val) body) argument.syntax) result
  | erasedBeta (fuel : Nat) {result : Code levels .proposition} :
      LoanTyping.Checker.check fuel env [] (parameterContext levels) true argument domain = true →
      Tree env (body.subst (single argument)) result →
      Tree env (.app (.lam true domain body) argument) result
  | delta {index : Nat} (type : Code levels .proposition) :
      env.globals[index]? = some declaration → Tree env declaration.value type →
      Tree env (.node (.global index) []) type

/-- The original typing yields the truth of the interpreted proposition at
every assignment to its universe parameters. In the dependent Pi case the
proof applies to every decoded input code. -/
theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Finite.decodeProp (code.meaning assignment) := by
  induction tree generalizing requested with
  | less left right recognized =>
      have truth := (PureArithmetic.recognized_fundamental history.wellFormed typed recognized).convert aligned
      exact (PureArithmetic.UniversalTruth.formula_iff history.wellFormed (.less _ _)).mp truth (fun _ => 0)
  | equal left right recognized =>
      have truth := (PureArithmetic.recognized_fundamental history.wellFormed typed recognized).convert aligned
      exact (PureArithmetic.UniversalTruth.formula_iff history.wellFormed (.equal _ _)).mp truth (fun _ => 0)
  | universeLambda level _ ih =>
      obtain ⟨_, bodyTyped, principal⟩ := LoanTyping.PureTyping.lambda_replay typed false (.univ level.val) _ rfl
      have codomain := ((principal.trans aligned).pi_injective history.wellFormed.admissible).2.2
      intro parameter
      exact ih bodyTyped codomain (assignment.extend level (Finite.Values.decode level parameter))
  | universeBeta level argument _ ih =>
      have bodyTyped := (LoanTyping.PureProofObservation.Step.beta (argument.formed history.wellFormed)).preserves
        history.wellFormed typed
      exact ih bodyTyped aligned assignment
  | erasedBeta fuel checked _ ih =>
      have bodyTyped := (LoanTyping.PureProofObservation.Step.beta (LoanTyping.Checker.check_sound checked)).preserves
        history.wellFormed typed
      exact ih bodyTyped aligned assignment
  | delta type found _ ih =>
      have formed := type.formed history.wellFormed
      have atType := LoanTyping.PureTyping.HasType.convert typed formed aligned
      have bodyTyped := LoanTyping.PureGlobalObservation.delta_preserves history found atType formed
      exact ih bodyTyped (.refl _) assignment

private theorem truth_inhabits {code : Universe .proposition} (truth : Finite.decodeProp code) :
    Nonempty (Carrier code) := by
  cases code with
  | proposition p => exact ⟨⟨⟨truth⟩⟩⟩

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) :=
  truth_inhabits (tree.truth history typed aligned assignment)

/-- No recognized proof inhabits a proposition that quantifies over any
sequence of native universe levels and ends in Lt(0,0). -/
theorem no_quantified_false (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term (quantifiedFalse (outer := []) levels))
    (typed : LoanTyping.PureTyping.HasType env [] term (quantifiedFalse (outer := []) levels).syntax) : False := by
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  exact quantified_false_uninhabited levels assignment (tree.inhabits history typed (.refl _) assignment)

theorem checker_rejects_quantified_false (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term (quantifiedFalse (outer := []) levels)) :
    LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget [] term
      (quantifiedFalse (outer := []) levels).syntax = none := by
  cases checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget [] term
      (quantifiedFalse (outer := []) levels).syntax with
  | none => rfl
  | some _ => exact False.elim (no_quantified_false history tree (LoanTyping.PureTyping.Checker.check?_sound checked).2)

/-- An authenticated native snapshot cannot contain such a proof at the
claimed false annotation. The value's derivation comes from the actual slot. -/
theorem no_admitted_quantified_false {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (tree : Tree env declaration.value (quantifiedFalse (outer := []) levels))
    (annotation : declaration.type = (quantifiedFalse (outer := []) levels).syntax) : False := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have typed := (history.global_value_and_reference found).1
  rw [annotation] at typed
  exact no_quantified_false history tree typed

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.Proofs
