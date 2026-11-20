import Jihoo.NativeLoanIndexedPropositionMixedFields

set_option maxUniverseOffset 40

/-! Contextual family induction composes with code quantification, actual
universe-code application and erased affine assumptions. Successful bounded
arithmetic replay retains the original native result annotation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.UniverseFamilyReplay

open Finite (Carrier)
open LoanTyping.PureFamilyArithmeticReplay (observe? observe?_preserves)

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | known : FamilyProofs.Tree env term result → Tree env term result
  | contextual (typingFuel depth replayFuel budget fuel : Nat) {result : Code levels .proposition} :
      observe? env (parameterContext levels) typingFuel depth replayFuel budget fuel term = some residual →
      Tree env residual result → Tree env term result
  | family {result : Code levels .proposition} : LoanTyping.PureFamilyProofs.ConstructorHead term →
      (∀ residual, Environment.FamilyIota.contract env term = some residual → Tree env residual result) → Tree env term result
  | universeLambda (level : Fin 32) {body : Code (level :: levels) .proposition} :
      Tree env term body → Tree env (.lam false (.univ level.val) term) (.abstract level body)
  | erasedLambda (premise : Implication.Premise) {result : Code levels .proposition} :
      (premise.Holds → Tree env (body.subst (single premise.evidence)) result) →
      Tree env (.lam true premise.syntax body) (premise.arrow result)
  | universeApply (level : Fin 32) (body : Code (level :: levels) .proposition) (argument : Code levels (inputSort level)) :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        function (Code.abstract level body).syntax = some .prop →
      Tree env function (.abstract level body) → Tree env (.app function argument.syntax) (.apply level body argument)
  | delta (result : Code levels .proposition) {index : Nat} :
      env.globals[index]? = some declaration → Tree env declaration.value result → Tree env (.node (.global index) []) result

theorem checked_universe_application_type {levels : List (Fin 32)} (wf : UnifiedProgram.EnvWellFormed env)
    (level : Fin 32) (body : Code (level :: levels) .proposition) (argument : Code levels (inputSort level))
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) (.app function argument.syntax) requested)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
      function (Code.abstract level body).syntax = some .prop) :
    RawValue.Conv env requested (Code.apply level body argument).syntax := by
  obtain ⟨_,_,_,functionTyped,_,principal⟩ := LoanTyping.PureTyping.application_replay typed _ _ rfl
  have formed := (LoanTyping.PureTyping.Checker.check?_sound checked).2
  have functionConv := functionTyped.unique wf formed
  have codomain := (functionConv.pi_injective wf.admissible).2.2
  exact (principal.symm.trans (codomain.substitution (single argument.syntax) wf.admissible)).trans
    (Code.application_beta wf level body argument).1.symm

/-- Interpret a native proof with every actual universe-code assignment.
Proof replay and instantiation derive their types from the original checked
derivation and the existing semantic rules for dependent codes. -/
theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (tree : Tree env term code) (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Finite.decodeProp (code.meaning assignment) := by
  let scope := ScopedProgram.History.ofPureMixed history
  induction tree generalizing requested with
  | known previous => exact previous.truth history typed aligned assignment
  | contextual typingFuel depth replayFuel budget fuel executed _ ih =>
      exact ih ((observe?_preserves scope).2 typed executed) aligned assignment
  | family shape _ ih =>
      obtain ⟨residual,executed,retained⟩ := LoanTyping.PureFamilyProofs.contract_from_pure_typing scope typed shape
      exact ih residual executed retained aligned assignment
  | universeLambda level _ ih =>
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed false (.univ level.val) _ rfl
      have codomain := ((principal.trans aligned).pi_injective history.wellFormed.admissible).2.2
      intro parameter
      exact ih bodyTyped codomain (assignment.extend level (Finite.Values.decode level parameter))
  | erasedLambda premise _ ih =>
      apply (premise.arrow_truth _ assignment).mpr
      intro witness
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed true premise.syntax _ rfl
      have related := principal.trans aligned
      rw [premise.arrow_syntax] at related
      have codomain := (related.pi_injective history.wellFormed.admissible).2.2
      have instantiated := bodyTyped.ghostInstantiate history.wellFormed (premise.evidence_typed history.wellFormed witness)
      have resultType := codomain.substitution (single premise.evidence) history.wellFormed.admissible
      rw [Term.shift_subst_single] at resultType
      exact ih witness instantiated resultType assignment
  | universeApply level body argument checked _ ih =>
      obtain ⟨_,_,_,functionTyped,_,_⟩ := LoanTyping.PureTyping.application_replay typed _ _ rfl
      have expected := (LoanTyping.PureTyping.Checker.check?_sound checked).2
      have functionConv := functionTyped.unique history.wellFormed expected
      have fn := ih functionTyped functionConv assignment
      rw [Code.application_meaning]
      exact fn (Finite.Values.encode level (argument.meaning assignment))
  | delta result found _ ih =>
      have formed := result.formed history.wellFormed
      have atType := LoanTyping.PureTyping.HasType.convert typed formed aligned
      have bodyTyped := LoanTyping.PureGlobalObservation.delta_preserves history found atType formed
      exact ih bodyTyped (.refl _) assignment

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (tree : Tree env term code) (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) := by
  have truth := tree.truth history typed aligned assignment
  generalize code.meaning assignment = model at truth ⊢
  cases model with
  | proposition p => exact ⟨⟨⟨truth⟩⟩⟩

theorem checked_global_inhabits {declaration : GlobalDeclaration} {index : Nat} (code : Code [] .proposition)
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (tree : Tree env declaration.value code)
    (aligned : RawValue.Conv env declaration.type code.syntax) (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Carrier (code.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  exact tree.inhabits history (history.global_value_and_reference found).1 aligned assignment

theorem no_admitted_quantified_false {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (tree : Tree env declaration.value (quantifiedFalse (outer := []) levels))
    (aligned : RawValue.Conv env declaration.type (quantifiedFalse (outer := []) levels).syntax) : False := by
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  exact quantified_false_uninhabited levels assignment (checked_global_inhabits _ admitted found tree aligned assignment)

section Example

open Environment.FamilyIota (elimTerm)
open AffineSum (Expr)

private def level : Fin 32 := ⟨0,by decide⟩
private def atIndex (index : Term) : Term := .node (.ind 0 1) [index]
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def next (index : Term) : Term := .uadd index one
private def afterTwo (index : Term) : Term := .uadd index two
private def familyDecl : FamilyDeclaration := ⟨false,0,1,
  [atIndex zero,.pi false .u64 (.pi true (atIndex (.var 0)) (atIndex (afterTwo (.var 1))))],0⟩
private def recursiveSig : Signature := ⟨[⟨false,.u64,none⟩,⟨true,atIndex (.var 0),some [.var 0]⟩],[afterTwo (.var 1)]⟩
private def entry : CheckedFamily := ⟨familyDecl,[⟨[],[zero]⟩,recursiveSig],false⟩
private def motive : Term := .lam false .u64 (.lt (.var 0) (next (.var 0)))
private def base : Term := .zeroLe zero
private def step : Term := .lam false .u64 (.lam true (atIndex (.var 0))
  (.lam true (.lt (.var 1) (next (.var 1))) (.ltAdd (.var 2) (next (.var 2)) two (.var 0))))
private def input : Term := .node (.con 0 1 2) [zero,.node (.con 0 0 0) []]
private def source : Term := elimTerm 0 motive [base,step] input
private def evidence : Term := .ltAdd zero (next zero) two base
private def bodyCode : Code [level] .proposition :=
  .less (left := .literal 2) (right := .literal 3) (.literal (by decide)) (.literal (by decide))
private def polyCode : Code [] .proposition := .abstract level bodyCode
private def appliedCode : Code [] .proposition := .apply level bodyCode .natural
private def polymorphic : GlobalDeclaration := ⟨polyCode.syntax,.lam false (.univ level.val) source⟩
private def instantiated : GlobalDeclaration := ⟨.lt two (.natural 3),.app (.node (.global 0) []) .u64⟩
private def storedInstance : GlobalDeclaration := ⟨instantiated.type,.app polymorphic.value .u64⟩
private def world : Environment := ⟨#[polymorphic,storedInstance],#[entry]⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private theorem contextual_replay : observe? world (parameterContext [level]) 48 16 16 4096 8 source = some evidence := by cbv

private theorem polymorphic_tree : Tree world polymorphic.value polyCode := by
  refine .universeLambda level (.contextual 48 16 16 4096 8 contextual_replay ?_)
  have supported := (LoanTyping.ProofObservation.supported_iff evidence).mp (by cbv)
  exact .known (.known (.known (.less (a := .literal 2) (b := .literal 3)
    (.literal (by decide)) (.literal (by decide)) (.arithmetic supported))))

private theorem checked_polymorphic : LoanTyping.PureTyping.Checker.check? world 48 48 16000 []
    polymorphic.value polyCode.syntax = some .prop := by cbv

private theorem instantiated_tree : Tree world storedInstance.value appliedCode :=
  .universeApply level bodyCode .natural checked_polymorphic polymorphic_tree

/-- Mixed checking accepts a genuine recursive branch under a universe
binder. Applying the stored proof to the U64 type code uses the interpreted
code application, and contextual replay reaches the checked induction proof. -/
theorem checked_universe_applied_recursive_induction :
    LoanTyping.PureMixedAdmission.checkProgram limits [polymorphic,instantiated] [familyDecl] = some world ∧
    observe? world (parameterContext [level]) 48 16 16 4096 8 source = some evidence ∧
    ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Nonempty (Carrier (appliedCode.meaning assignment)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [polymorphic,instantiated] [familyDecl] = some world := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have original := (history.global_value_and_reference (index := 1) (declaration := storedInstance) rfl).1
  have aligned := checked_universe_application_type history.wellFormed level bodyCode .natural original checked_polymorphic
  exact ⟨admitted,contextual_replay,fun assignment => instantiated_tree.inhabits history original aligned assignment⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.UniverseFamilyReplay

namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.MixedFields

open Environment.FamilyIota (elimTerm)
open MultiUniverse (Assignment parameterContext)
open MultiUniverse.DependentCodes (Code)
open Vectors (terms)

variable {id : Nat}

/-- A reified closed constructor can be used inside any native context.
The motive and every branch still need their actual typing in that context. -/
theorem Realization.elimination_typed_in {family : Vectors.Family env id} (input : Realization family index)
    (wf : UnifiedProgram.EnvWellFormed env)
    (motiveTyped : LoanTyping.HasType env [] ctx true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] ctx motive family.entry.signatures cases) :
    LoanTyping.HasType env [] ctx true (elimTerm id motive cases input.term) (applications motive (terms input.expressions)) := by
  have weakening : LoanTyping.Ghost.Substitution env [] ctx Term.var := by
    intro index binding missing
    cases missing
  have scrutinee : LoanTyping.HasType env [] ctx true input.term (Vectors.propositionAt id (terms input.expressions)) := by
    simpa only [Term.subst_id] using input.typed.ghostSubstitution wf weakening
  have arity : (terms input.expressions).length = family.entry.declaration.arity := (List.length_map _).trans input.code.size
  rw [Vectors.propositionAt,arity] at scrutinee
  exact .propElim family.found family.proposition motiveTyped branches scrutinee

/-- Interpret checked native elimination of a mixed-field carrier inhabitant
in a context of actual universe codes. The replay certificate selects only
syntax, with the motive and supplied arguments typed by native rules. -/
theorem Fiber.universe_elimination {levels : List (Fin 32)} (family : Vectors.Family env id)
    (inhabited : Fiber id family.entry index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] (parameterContext levels) true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] (parameterContext levels) motive family.entry.signatures cases)
    (result : Code levels .proposition)
    (aligned : ∀ input : Realization family index, RawValue.Conv env (applications motive (terms input.expressions)) result.syntax)
    (covered : ∀ input : Realization family index,
      MultiUniverse.DependentCodes.UniverseFamilyReplay.Tree env (elimTerm id motive cases input.term) result)
    (assignment : Assignment levels.get) : Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨input⟩ := Fiber.reify family inhabited
  have source := input.elimination_typed_in history.wellFormed motiveTyped branches
  exact (covered input).inhabits history (.native source) (aligned input) assignment

/-- The head of the index list is the innermost written universe binder,
matching the de Bruijn order of `parameterContext`. -/
def codeLambdas : List (Fin 32) → Term → Term
  | [], body => body
  | level :: outer, body => codeLambdas outer (.lam false (.univ level.val) body)

theorem codeLambdas_body_typed {outer levels : List (Fin 32)}
    (typed : LoanTyping.PureTyping.HasType env (parameterContext outer) (codeLambdas levels body) type) :
    ∃ requested, LoanTyping.PureTyping.HasType env (parameterContext (levels ++ outer)) body requested := by
  induction levels generalizing body type with
  | nil => exact ⟨type,typed⟩
  | cons level levels ih =>
      have wrapped : LoanTyping.PureTyping.HasType env (parameterContext outer)
          (codeLambdas levels (.lam false (.univ level.val) body)) type := typed
      obtain ⟨_,opened⟩ := ih wrapped
      obtain ⟨result,bodyTyped,_⟩ := LoanTyping.PureTyping.lambda_replay opened false (.univ level.val) body rfl
      exact ⟨result,bodyTyped⟩

/-- Exact admission of a global with written universe binders supplies its
original motive and branch derivations after opening the binders. -/
theorem checked_global_universe_eliminates {levels : List (Fin 32)} {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Vectors.Family env id) (found : env.globals[index]? = some declaration)
    (source : declaration.value = codeLambdas levels (elimTerm id motive cases scrutinee))
    (inhabited : Fiber id family.entry indices) (result : Code levels .proposition)
    (aligned : ∀ input : Realization family indices, RawValue.Conv env (applications motive (terms input.expressions)) result.syntax)
    (covered : ∀ input : Realization family indices,
      MultiUniverse.DependentCodes.UniverseFamilyReplay.Tree env (elimTerm id motive cases input.term) result)
    (assignment : Assignment levels.get) : Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have original := (history.global_value_and_reference found).1
  rw [source] at original
  obtain ⟨_,bodyTyped⟩ := codeLambdas_body_typed (outer := []) original
  rw [List.append_nil] at bodyTyped
  obtain ⟨motiveTyped,branches⟩ := Vectors.checked_cases (family := family) bodyTyped rfl
  exact Fiber.universe_elimination family inhabited history motiveTyped branches result aligned covered assignment

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.MixedFields
