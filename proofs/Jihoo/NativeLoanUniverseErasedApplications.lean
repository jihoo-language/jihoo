import Jihoo.NativeLoanUniverseFamilyReplay

set_option maxUniverseOffset 40

/-! Sound erased proof applications in the existing universe-code model.
Native application inversion recovers the real argument and its result type.
Contextual replay may occur in the callee, the evidence, or the continuation
of a constructive erased abstraction. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.ErasedApplications

open Finite (Carrier decodeProp)
open LoanTyping.PureFamilyArithmeticReplay (observe? observe?_preserves)
open IndexedProposition.MixedFields (codeLambdas codeLambdas_body_typed)

def erasedArrow (premise result : Code levels .proposition) : Code levels .proposition :=
  .arrow true (by rfl) premise result

private theorem carrier_of_truth {code : Finite.Universe .proposition} (truth : decodeProp code) : Nonempty (Carrier code) := by
  cases code with
  | proposition proposition => exact ⟨⟨⟨truth⟩⟩⟩

/-- This works for any two supported proposition codes, including a premise
whose interpretation contains a quantified type-code family. -/
theorem implication_truth {levels : List (Fin 32)} (premise result : Code levels .proposition)
    (assignment : Assignment levels.get) :
    decodeProp ((erasedArrow premise result).meaning assignment) ↔
      (decodeProp (premise.meaning assignment) → decodeProp (result.meaning assignment)) := by
  change (∀ _ : Carrier (premise.meaning assignment), decodeProp (result.meaning assignment)) ↔ _
  constructor
  · intro fn truth
    obtain ⟨value⟩ := carrier_of_truth truth
    exact fn value
  · intro fn value
    generalize premise.meaning assignment = model at fn value
    cases model with
    | proposition proposition => exact fn value.down.down

/-- The actual application supplies its original argument derivation. The
checked callee annotation determines the erased binder and transports the
original dependent codomain to the supported result code. -/
theorem checked_erased_application {levels : List (Fin 32)} (wf : UnifiedProgram.EnvWellFormed env)
    (premise result : Code levels .proposition)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) (.app function argument) requested)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
      function (erasedArrow premise result).syntax = some .prop) :
    LoanTyping.PureTyping.HasType env (parameterContext levels) function (erasedArrow premise result).syntax ∧
      LoanTyping.PureTyping.HasType env (parameterContext levels) argument premise.syntax ∧
      RawValue.Conv env requested result.syntax := by
  obtain ⟨_,_,_,functionTyped,argumentTyped,principal⟩ := LoanTyping.PureTyping.application_replay typed _ _ rfl
  have atArrow := (LoanTyping.PureTyping.Checker.check?_sound checked).2
  have related := functionTyped.unique wf atArrow
  obtain ⟨_,domain,codomain⟩ := related.pi_injective wf.admissible
  have supplied := LoanTyping.PureTyping.HasType.convert (.native argumentTyped) (premise.formed wf) domain
  have codomain := codomain.substitution (single argument) wf.admissible
  rw [Term.shift_subst_single] at codomain
  exact ⟨atArrow,supplied,principal.symm.trans codomain⟩

/-- An affine hypothesis that holds yields native evidence at the actual
erased binder. Substitution preserves the checked body at the result code. -/
theorem affine_body_typed {levels : List (Fin 32)} (wf : UnifiedProgram.EnvWellFormed env)
    (premise : Implication.Premise) (result : Code levels .proposition)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) (.lam true premise.syntax body) requested)
    (aligned : RawValue.Conv env requested (premise.arrow result).syntax) (truth : premise.Holds) :
    LoanTyping.PureTyping.HasType env (parameterContext levels) (body.subst (single premise.evidence)) result.syntax := by
  obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed true premise.syntax _ rfl
  have related := principal.trans aligned
  rw [premise.arrow_syntax] at related
  have codomain := (related.pi_injective wf.admissible).2.2
  have instantiated := bodyTyped.ghostInstantiate wf (premise.evidence_typed wf truth)
  have converted := codomain.substitution (single premise.evidence) wf.admissible
  rw [Term.shift_subst_single] at converted
  exact .convert instantiated (result.formed wf) converted

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | known : UniverseFamilyReplay.Tree env term result → Tree env term result
  | contextual (typingFuel depth replayFuel budget fuel : Nat) {result : Code levels .proposition} :
      observe? env (parameterContext levels) typingFuel depth replayFuel budget fuel term = some residual →
      Tree env residual result → Tree env term result
  | family {result : Code levels .proposition} : LoanTyping.PureFamilyProofs.ConstructorHead term →
      (∀ residual, Environment.FamilyIota.contract env term = some residual → Tree env residual result) → Tree env term result
  | universeLambda (level : Fin 32) {body : Code (level :: levels) .proposition} :
      Tree env term body → Tree env (.lam false (.univ level.val) term) (.abstract level body)
  | affineLambda (premise : Implication.Premise) {result : Code levels .proposition} :
      (premise.Holds → Tree env (body.subst (single premise.evidence)) result) →
      Tree env (.lam true premise.syntax body) (premise.arrow result)
  | erasedApply (premise result : Code levels .proposition) :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        function (erasedArrow premise result).syntax = some .prop →
      Tree env function (erasedArrow premise result) → Tree env argument premise → Tree env (.app function argument) result
  | erasedBeta (typingFuel : Nat) {result : Code levels .proposition} :
      LoanTyping.Checker.check typingFuel env [] (parameterContext levels) true argument domain = true →
      Tree env (body.subst (single argument)) result → Tree env (.app (.lam true domain body) argument) result
  | universeApply (level : Fin 32) (body : Code (level :: levels) .proposition) (argument : Code levels (inputSort level)) :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        function (Code.abstract level body).syntax = some .prop →
      Tree env function (.abstract level body) → Tree env (.app function argument.syntax) (.apply level body argument)

/-- Modus ponens and constructive substitution preserve the interpretation
at every assignment of actual native universe codes. -/
theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (tree : Tree env term code) (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    decodeProp (code.meaning assignment) := by
  let scope := ScopedProgram.History.ofPureMixed history
  induction tree generalizing requested with
  | known previous => exact previous.truth history typed aligned assignment
  | contextual _ _ _ _ _ executed _ ih =>
      exact ih ((observe?_preserves scope).2 typed executed) aligned assignment
  | family shape _ ih =>
      obtain ⟨residual,executed,retained⟩ := LoanTyping.PureFamilyProofs.contract_from_pure_typing scope typed shape
      exact ih residual executed retained aligned assignment
  | universeLambda level _ ih =>
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed false (.univ level.val) _ rfl
      have codomain := ((principal.trans aligned).pi_injective history.wellFormed.admissible).2.2
      intro parameter
      exact ih bodyTyped codomain (assignment.extend level (Finite.Values.decode level parameter))
  | affineLambda premise _ ih =>
      apply (premise.arrow_truth _ assignment).mpr
      intro witness
      exact ih witness (affine_body_typed history.wellFormed premise _ typed aligned witness) (.refl _) assignment
  | erasedApply premise result checked _ _ ihFunction ihArgument =>
      obtain ⟨functionTyped,argumentTyped,_⟩ := checked_erased_application history.wellFormed premise result typed checked
      exact (implication_truth premise result assignment).mp (ihFunction functionTyped (.refl _) assignment)
        (ihArgument argumentTyped (.refl _) assignment)
  | erasedBeta typingFuel checked _ ih =>
      exact ih (LoanTyping.PureProofObservation.Step.preserves (.beta (LoanTyping.Checker.check_sound checked))
        history.wellFormed typed) aligned assignment
  | universeApply level body argument checked _ ih =>
      have functionTyped := (LoanTyping.PureTyping.Checker.check?_sound checked).2
      have semantic := ih functionTyped (.refl _) assignment
      rw [Code.application_meaning]
      exact semantic (Finite.Values.encode level (argument.meaning assignment))

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (tree : Tree env term code) (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) :=
  carrier_of_truth (tree.truth history typed aligned assignment)

/-- Exact admitted bytes give the proof application under its original
written universe binders. The result annotation is recovered by application
inversion without accepting a proposed output typing or conversion. -/
theorem checked_global_erased_application_inhabits {levels : List (Fin 32)} {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (source : declaration.value = codeLambdas levels (.app function argument))
    (premise result : Code levels .proposition)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
      function (erasedArrow premise result).syntax = some .prop)
    (fn : Tree env function (erasedArrow premise result)) (arg : Tree env argument premise) (assignment : Assignment levels.get) :
    Nonempty (Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have original := (history.global_value_and_reference found).1
  rw [source] at original
  obtain ⟨_,bodyTyped⟩ := codeLambdas_body_typed (outer := []) original
  rw [List.append_nil] at bodyTyped
  have aligned := (checked_erased_application history.wellFormed premise result bodyTyped checked).2.2
  exact (Tree.erasedApply premise result checked fn arg).inhabits history bodyTyped aligned assignment

theorem no_admitted_erased_application_quantified_false {levels : List (Fin 32)}
    {declaration : GlobalDeclaration} {index : Nat} (quantifiers : List (Fin 32))
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (source : declaration.value = codeLambdas levels (.app function argument))
    (premise : Code levels .proposition)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
      function (erasedArrow premise (quantifiedFalse (outer := levels) quantifiers)).syntax = some .prop)
    (fn : Tree env function (erasedArrow premise (quantifiedFalse (outer := levels) quantifiers)))
    (arg : Tree env argument premise) (assignment : Assignment levels.get) : False :=
  quantified_false_uninhabited quantifiers assignment
    (checked_global_erased_application_inhabits admitted found source premise _ checked fn arg assignment)

section Example

open Environment.FamilyIota (elimTerm)
open AffineSum (Expr)

private def upper : Fin 32 := ⟨31,by decide⟩
private def lower : Fin 32 := ⟨0,by decide⟩
private def levels : List (Fin 32) := [lower,upper]
private def atIndex (index : Term) : Term := .node (.ind 0 1) [index]
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def three : Term := .natural 3
private def next (index : Term) : Term := .uadd index one
private def afterTwo (index : Term) : Term := .uadd index two
private def familyDeclaration : FamilyDeclaration := ⟨false,0,1,
  [atIndex zero,.pi false .u64 (.pi true (atIndex (.var 0)) (atIndex (afterTwo (.var 1))))],0⟩
private def signature : Signature := ⟨[⟨false,.u64,none⟩,⟨true,atIndex (.var 0),some [.var 0]⟩],[afterTwo (.var 1)]⟩
private def entry : CheckedFamily := ⟨familyDeclaration,[⟨[],[zero]⟩,signature],false⟩
private def motive : Term := .lam false .u64 (.lt (.var 0) (next (.var 0)))
private def base : Term := .zeroLe zero
private def step : Term := .lam false .u64 (.lam true (atIndex (.var 0))
  (.lam true (.lt (.var 1) (next (.var 1))) (.ltAdd (.var 2) (next (.var 2)) two (.var 0))))
private def argument : Term := elimTerm 0 motive [base,step] (.node (.con 0 1 2) [zero,.node (.con 0 0 0) []])
private def evidence : Term := .ltAdd zero (next zero) two base
private def premise : Implication.Premise :=
  .less (left := .literal 2) (right := .literal 3) (.literal (by decide)) (.literal (by decide))
private def conclusion : Code levels .proposition :=
  .less (left := .literal 3) (right := .literal 4) (.literal (by decide)) (.literal (by decide))
private def body : Term := .ltAdd two three one (.var 0)
private def function : Term := .lam true premise.syntax body
private def application : Term := .app function argument
private def annotation : Code [] .proposition := .abstract upper (.abstract lower conclusion)
private def source : GlobalDeclaration := ⟨annotation.syntax,codeLambdas levels application⟩
private def world : Environment := ⟨#[source],#[entry]⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private theorem arithmetic_tree {levels : List (Fin 32)} {left right : Expr}
    (validLeft : IndexedProposition.Closed left) (validRight : IndexedProposition.Closed right)
    (supported : LoanArithmetic.Supported term) : Tree env term (Code.less (levels := levels) validLeft validRight) :=
  .known (.known (.known (.known (.less validLeft validRight (.arithmetic supported)))))

private theorem function_tree : Tree world function (erasedArrow (premise.code levels) conclusion) := by
  refine .affineLambda premise ?_
  intro _
  exact arithmetic_tree (left := .literal 3) (right := .literal 4) (.literal (by decide)) (.literal (by decide))
    ((LoanTyping.ProofObservation.supported_iff _).mp (by cbv))

private theorem argument_tree : Tree world argument (premise.code levels) := by
  have executed : observe? world (parameterContext levels) 48 16 16 4096 8 argument = some evidence := by cbv
  refine .contextual 48 16 16 4096 8 executed ?_
  exact arithmetic_tree (left := .literal 2) (right := .literal 3) (.literal (by decide)) (.literal (by decide))
    ((LoanTyping.ProofObservation.supported_iff _).mp (by cbv))

private theorem checked_function : LoanTyping.PureTyping.Checker.check? world 48 48 16000 (parameterContext levels)
    function (erasedArrow (premise.code levels) conclusion).syntax = some .prop := by cbv

/-- Two written universe binders surround a native erased application. Its
recursive argument inhabits Lt(2,3), and the body uses that actual proof to
derive Lt(3,4). The executable replay exposes both proof steps. -/
theorem checked_erased_recursive_application :
    LoanTyping.PureMixedAdmission.checkProgram limits [source] [familyDeclaration] = some world ∧
    observe? world (parameterContext levels) 48 16 16 4096 8 application = some (.ltAdd two three one evidence) ∧
    ∀ assignment : Assignment levels.get, Nonempty (Carrier (conclusion.meaning assignment)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [source] [familyDeclaration] = some world := by cbv
  have executed : observe? world (parameterContext levels) 48 16 16 4096 8 application = some (.ltAdd two three one evidence) := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have original : LoanTyping.PureTyping.HasType world (parameterContext []) (codeLambdas levels application) source.type :=
    (history.global_value_and_reference (index := 0) (declaration := source) rfl).1
  obtain ⟨_,opened⟩ := codeLambdas_body_typed original
  rw [List.append_nil] at opened
  have aligned := (checked_erased_application history.wellFormed (premise.code levels) conclusion opened checked_function).2.2
  exact ⟨admitted,executed,fun assignment =>
    (Tree.erasedApply _ _ checked_function function_tree argument_tree).inhabits history opened aligned assignment⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.ErasedApplications
