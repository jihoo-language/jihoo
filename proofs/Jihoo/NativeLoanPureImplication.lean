import Jihoo.NativeLoanPureDependentProofs
import Jihoo.NativeLoanWideHypothesisObservation

set_option maxUniverseOffset 40

/-! Erased affine implications realize the actual proposition carrier. An
inhabited premise gives a typed source witness by wide affine closing. An
empty premise requires no witness or continuation certificate. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.Implication

open Finite (Carrier Universe)
open LoanTyping.PureHypothesisObservation (Entry ScalarExpr)
open LoanTyping.WideHypothesisObservation (Satisfies closing)

inductive Premise where
  | less : ScalarExpr [] left → ScalarExpr [] right → Premise
  | equal : ScalarExpr [] left → ScalarExpr [] right → Premise

def Premise.entry : Premise → Entry
  | .less (left := left) (right := right) _ _ => .less left right
  | .equal (left := left) (right := right) _ _ => .equal left right

def Premise.code (levels : List (Fin 32)) : Premise → Code levels .proposition
  | .less left right => .less left right
  | .equal left right => .equal left right

def Premise.syntax (premise : Premise) : Term := (premise.code []).syntax

theorem Premise.code_syntax (premise : Premise) (levels : List (Fin 32)) :
    (premise.code levels).syntax = premise.syntax := by
  cases premise <;> rfl

def Premise.Holds : Premise → Prop
  | .less (left := left) (right := right) _ _ => left.eval (fun _ => 0) < right.eval (fun _ => 0)
  | .equal (left := left) (right := right) _ _ => left.eval (fun _ => 0) = right.eval (fun _ => 0)

def Premise.evidence (premise : Premise) : Term := closing [premise.entry] (fun _ => 0) 0

def Premise.arrow {levels : List (Fin 32)} (premise : Premise) (result : Code levels .proposition) :
    Code levels .proposition :=
  .arrow true (by rfl) (premise.code levels) result

theorem Premise.arrow_syntax {levels : List (Fin 32)} (premise : Premise) (result : Code levels .proposition) :
    (premise.arrow result).syntax = .pi true premise.syntax (result.syntax.rename Nat.succ) := by
  change Term.pi true ((premise.code levels).syntax) (result.syntax.rename Nat.succ) = _
  rw [premise.code_syntax]

theorem Premise.code_truth {levels : List (Fin 32)} (premise : Premise) (assignment : Assignment levels.get) :
    Finite.decodeProp ((premise.code levels).meaning assignment) ↔ premise.Holds := by
  cases premise <;> rfl

private theorem argument_truth {code : Universe .proposition} (argument : Carrier code) : Finite.decodeProp code := by
  cases code with
  | proposition truth => exact argument.down.down

private theorem truth_argument {code : Universe .proposition} (truth : Finite.decodeProp code) : Nonempty (Carrier code) := by
  cases code with
  | proposition proposition => exact ⟨⟨⟨truth⟩⟩⟩

/-- Irrespective of the outer universe assignment, this product gives the
usual implication between the interpreted closed premise and its result. -/
theorem Premise.arrow_truth {levels : List (Fin 32)} (premise : Premise)
    (result : Code levels .proposition) (assignment : Assignment levels.get) :
    Finite.decodeProp ((premise.arrow result).meaning assignment) ↔
      (premise.Holds → Finite.decodeProp (result.meaning assignment)) := by
  change (∀ _ : Carrier ((premise.code levels).meaning assignment), Finite.decodeProp (result.meaning assignment)) ↔ _
  constructor
  · intro function truePremise
    obtain ⟨argument⟩ := truth_argument ((premise.code_truth assignment).mpr truePremise)
    exact function argument
  · intro function argument
    exact function ((premise.code_truth assignment).mp (argument_truth argument))

private theorem Premise.closed (premise : Premise) : premise.syntax.Scoped 0 := by
  cases premise with
  | less left right | equal left right =>
      apply Term.Scoped.nonbinding (by intro index; rfl)
      intro term included
      rcases List.mem_cons.mp included with rfl | included
      · exact left.scoped
      · cases List.mem_singleton.mp included
        exact right.scoped

/-- Truth of a closed affine premise constructs a genuine Loan64 value of
the original type, including sums whose mathematical values exceed U64. -/
theorem Premise.evidence_typed (wf : UnifiedProgram.EnvWellFormed env) (premise : Premise)
    (truth : premise.Holds) : LoanTyping.HasType env [] ctx true premise.evidence premise.syntax := by
  have realized : Satisfies [premise.entry] (fun _ => 0) := by
    cases premise with
    | less left right => exact .less left right truth .empty
    | equal left right => exact .equal left right truth .empty
  have found : NativeKernel.lookup (LoanTyping.PureHypothesisObservation.context [premise.entry]) 0 =
      some ⟨premise.syntax.rename Nat.succ,true⟩ := by
    cases premise <;> rfl
  have native := realized.realizes (env := env) _ _ found
  change LoanTyping.HasType env [] [] true premise.evidence
    ((premise.syntax.rename Nat.succ).subst (closing [premise.entry] (fun _ => 0))) at native
  rw [Environment.closed_rename premise.closed,Environment.closed_subst premise.closed] at native
  have weakening : LoanTyping.Ghost.Substitution env [] ctx Term.var := by
    intro index binding absent
    cases absent
  simpa only [Term.subst_id] using native.ghostSubstitution wf weakening

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | known : Proofs.Tree env term result → Tree env term result
  | universeLambda (level : Fin 32) {result : Code (level :: levels) .proposition} : Tree env body result →
      Tree env (.lam false (.univ level.val) body) (.abstract level result)
  | introduce (premise : Premise) {result : Code levels .proposition} :
      (premise.Holds → Tree env (body.subst (single premise.evidence)) result) →
      Tree env (.lam true premise.syntax body) (premise.arrow result)
  | apply (premise : Premise) (result : Code levels .proposition) :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        function (premise.arrow result).syntax = some sort →
      Tree env function (premise.arrow result) → Tree env argument (premise.code levels) →
      Tree env (.app function argument) result
  | delta {index : Nat} (type : Code levels .proposition) :
      env.globals[index]? = some declaration → Tree env declaration.value type →
      Tree env (.node (.global index) []) type

/-- Actual typed proof abstraction and application give semantic implication
introduction and elimination at the original annotations. No output typing
or semantic witness is part of the source certificate. -/
theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Finite.decodeProp (code.meaning assignment) := by
  induction tree generalizing requested with
  | known previous => exact previous.truth history typed aligned assignment
  | universeLambda level _ ih =>
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed false (.univ level.val) _ rfl
      have codomain := ((principal.trans aligned).pi_injective history.wellFormed.admissible).2.2
      intro parameter
      exact ih bodyTyped codomain (assignment.extend level (Finite.Values.decode level parameter))
  | introduce premise _ ih =>
      apply (premise.arrow_truth _ assignment).mpr
      intro truth
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed true premise.syntax _ rfl
      have related := principal.trans aligned
      rw [premise.arrow_syntax] at related
      have codomain := (related.pi_injective history.wellFormed.admissible).2.2
      have actualBody := bodyTyped.ghostInstantiate history.wellFormed (premise.evidence_typed history.wellFormed truth)
      have bodyConv := codomain.substitution (single premise.evidence) history.wellFormed.admissible
      rw [Term.shift_subst_single] at bodyConv
      exact ih truth actualBody bodyConv assignment
  | apply premise result checked _ _ functionIH argumentIH =>
      obtain ⟨_,_,_,functionTyped,argumentTyped,_⟩ := LoanTyping.PureTyping.application_replay typed _ _ rfl
      have expected := (LoanTyping.PureTyping.Checker.check?_sound checked).2
      have functionConv := functionTyped.unique history.wellFormed expected
      have asPi := functionConv
      rw [premise.arrow_syntax] at asPi
      have argumentConv := (asPi.pi_injective history.wellFormed.admissible).2.1
      rw [← premise.code_syntax] at argumentConv
      have argumentTruth := argumentIH (.native argumentTyped) argumentConv assignment
      exact ((premise.arrow_truth result assignment).mp (functionIH functionTyped functionConv assignment))
        ((premise.code_truth assignment).mp argumentTruth)
  | delta type found _ ih =>
      have formed := type.formed history.wellFormed
      have atType := LoanTyping.PureTyping.HasType.convert typed formed aligned
      have bodyTyped := LoanTyping.PureGlobalObservation.delta_preserves history found atType formed
      exact ih bodyTyped (.refl _) assignment

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) :=
  truth_argument (tree.truth history typed aligned assignment)

/-- Exact mixed bytes cannot admit a false quantified proof in the enlarged
grammar, even when it introduces or eliminates erased hypotheses. -/
theorem no_admitted_quantified_false {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (tree : Tree env declaration.value (quantifiedFalse (outer := []) levels))
    (annotation : declaration.type = (quantifiedFalse (outer := []) levels).syntax) : False := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  have aligned : RawValue.Conv env declaration.type (quantifiedFalse (outer := []) levels).syntax := by
    rw [annotation]
    exact .refl _
  exact quantified_false_uninhabited levels assignment
    (tree.inhabits history (history.global_value_and_reference found).1 aligned assignment)

private def reflexive : Premise :=
  .equal (left := .literal 0) (right := .literal 0) (.literal (by decide)) (.literal (by decide))
private def falsePremise : Premise :=
  .less (left := .literal 0) (right := .literal 0) (.literal (by decide)) (.literal (by decide))
private def upper : Fin 32 := ⟨31,by decide⟩
private def proofIdentity (premise : Premise) : Term := .lam true premise.syntax (.var 0)
private def reflexivity : Term := .refl (.natural 0)
private def applied : Term := .lam false (.univ upper.val) (.app (proofIdentity reflexive) reflexivity)
private def appliedType : Code [] .proposition := .abstract upper (reflexive.code [upper])
private def vacuity : Term := proofIdentity falsePremise
private def vacuityType : Code [] .proposition := falsePremise.arrow (falsePremise.code [])
private def first : GlobalDeclaration := ⟨appliedType.syntax,applied⟩
private def second : GlobalDeclaration := ⟨vacuityType.syntax,vacuity⟩
private def world : Environment := ⟨#[first,second],#[]⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨32,32,32,8192⟩

private theorem reflTree : Tree world reflexivity (reflexive.code [upper]) :=
  .known (.equal (.literal (by decide)) (.literal (by decide)) (.refl (.literal 0)))

private theorem appliedTree : Tree world applied appliedType := by
  refine .universeLambda upper (.apply (typingFuel := 32) (conversionFuel := 32) (budget := 8192) (sort := .prop)
    reflexive (reflexive.code [upper]) (by cbv) ?_ reflTree)
  refine .introduce reflexive ?_
  intro _
  have instantiated : (Term.var 0).subst (single reflexive.evidence) = reflexivity := by cbv
  rw [instantiated]
  exact reflTree

private theorem vacuityTree : Tree world vacuity vacuityType := by
  refine .introduce falsePremise ?_
  intro impossible
  exact False.elim (Nat.lt_irrefl 0 impossible)

/-- The mixed checker accepts an actual application under Type31 and an
erased identity at an empty premise. Semantic replay derives the positive
witness and the vacuous function from their respective stored derivations. -/
theorem checked_implication_and_vacuity :
    LoanTyping.PureMixedAdmission.checkProgram limits [first,second] [] = some world ∧
    ∀ assignment : Assignment (List.get ([] : List (Fin 32))),
      Nonempty (Carrier (appliedType.meaning assignment)) ∧ Nonempty (Carrier (vacuityType.meaning assignment)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [first,second] [] = some world := by cbv
  have history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have sourceApplied := (history.global_value_and_reference (index := 0) (declaration := first) rfl).1
  have sourceVacuity := (history.global_value_and_reference (index := 1) (declaration := second) rfl).1
  exact ⟨admitted,fun assignment => ⟨appliedTree.inhabits history sourceApplied (.refl _) assignment,
    vacuityTree.inhabits history sourceVacuity (.refl _) assignment⟩⟩

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.Implication
