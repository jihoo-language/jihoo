import Jihoo.NativeLoanFamilyIotaPreservation
import Jihoo.NativeLoanPureImplication

set_option maxUniverseOffset 40

/-! Authenticated extended-ghost declarations carry the family metadata
needed for subject reduction. Constructor-headed eliminations compute at
their original annotation and expose the actual selected proof branch. -/
namespace Jihoo.NativeKernel.ScopedProgram

theorem History.ofPureMixed
    (history : Environment.LoanTyping.PureMixedAdmission.History definitions declarations env) :
    History definitions declarations env := by
  induction history with
  | empty => exact .empty
  | definition _ checked ih =>
      exact .definition ih ⟨checked.typeExpansion,checked.valueExpansion,checked.valid.closed,checked.valid.transparent⟩
  | family _ checked ih => exact .family ih checked

end Jihoo.NativeKernel.ScopedProgram

namespace Jihoo.NativeKernel.Environment.LoanTyping.PureFamilyProofs

open _root_.Jihoo.NativeKernel.Environment.FamilyIota (Root caseTerm elimTerm contract contract_sound)

inductive ConstructorHead : Term → Prop where
  | elim (family constructor : Nat) (motive : Term) (cases values : List Term) :
      ConstructorHead (elimTerm family motive cases (.node (.con family constructor values.length) values))
  | caseOf (family constructor : Nat) (motive : Term) (cases values : List Term) :
      ConstructorHead (caseTerm family motive cases (.node (.con family constructor values.length) values))

/-- The actual typing of a visible constructor forces the executable
contraction to succeed, even if the source's requested annotation used
expanded pure conversion. -/
theorem contract_from_pure_typing (history : ScopedProgram.History definitions declarations env)
    (typed : PureTyping.HasType env ctx term type) (shape : ConstructorHead term) :
    ∃ result, contract env term = some result ∧ PureTyping.HasType env ctx result type := by
  induction typed with
  | native native =>
      cases shape
      · obtain ⟨result,ran,preserved⟩ := FamilyIota.contract_elim_from_typing history native
        exact ⟨result,ran,.native preserved⟩
      · obtain ⟨result,ran,preserved⟩ := FamilyIota.contract_case_from_typing history native
        exact ⟨result,ran,.native preserved⟩
  | convert _ formed conversion ih =>
      obtain ⟨result,ran,preserved⟩ := ih shape
      exact ⟨result,ran,.convert preserved formed conversion⟩
  | pi | lam | app => cases shape

inductive Head (env : Environment) (ctx : Context) : Term → Term → Prop where
  | family : Root env term result → Head env ctx term result
  | beta : HasType env [] ctx true argument domain →
      Head env ctx (.app (.lam erased domain body) argument) (body.subst (single argument))
  | callee : Head env ctx function result → Head env ctx (.app function argument) (.app result argument)

theorem Head.native_preserves (history : ScopedProgram.History definitions declarations env)
    (step : Head env ctx term result) (typed : HasType env [] ctx true term type) :
    HasType env [] ctx true result type := by
  induction step generalizing type with
  | family root => exact FamilyIota.Root.preserves history root typed
  | beta => exact compute_ghost_preservation history.wellFormed (.beta _ _ _ _) typed
  | callee _ ih =>
      obtain ⟨_,_,_,function,argument,_,converted⟩ := typed.appView
      exact (HasType.app (ih function) argument (Or.inl rfl)).convert converted

theorem Head.preserves (history : ScopedProgram.History definitions declarations env)
    (step : Head env ctx term result) (typed : PureTyping.HasType env ctx term type) :
    PureTyping.HasType env ctx result type := by
  induction typed generalizing result with
  | native typed => exact .native (step.native_preserves history typed)
  | convert _ formed converted ih => exact .convert (ih step) formed converted
  | pi | lam => cases step with | family root => cases root
  | app function formed argument ih =>
      cases step with
      | callee step => exact .app (ih step) formed argument
      | beta originalArgument =>
          obtain ⟨_,bodyTyped,converted⟩ := PureTyping.lambda_replay function _ _ _ rfl
          have output := (converted.pi_injective history.wellFormed.admissible).2.2
          exact .convert (bodyTyped.ghostInstantiate history.wellFormed originalArgument)
            (PureTyping.application_result_formed history.wellFormed formed argument)
            (output.substitution (single _) history.wellFormed.admissible)
      | family root => cases root

/-- The head walk contracts concrete family roots and uses the original
checked beta argument when a selected branch exposes a lambda. -/
def step? (env : Environment) (ctx : Context) (typingFuel : Nat) : Nat → Term → Option Term
  | _ + 1, term@(.node (.elim _ _) _) | _ + 1, term@(.node (.caseOf _ _) _) => contract env term
  | _ + 1, .app (.lam _ domain body) argument =>
      if Checker.check typingFuel env [] ctx true argument domain then some (body.subst (single argument)) else none
  | depth + 1, .app function argument => (step? env ctx typingFuel depth function).map (fun result => .app result argument)
  | _, _ => none

theorem step?_sound (ran : step? env ctx typingFuel depth term = some result) : Head env ctx term result := by
  fun_induction step? env ctx typingFuel depth term generalizing result
  all_goals first
    | exact .family (contract_sound ran)
    | contradiction
    | obtain rfl : _ = result := Option.some.inj ran
      exact .beta (Checker.check_sound (by assumption))
    | rename_i ih
      obtain ⟨_,found,rfl⟩ := Option.map_eq_some_iff.mp ran
      exact .callee (ih found)

theorem step_from_pure_typing (history : ScopedProgram.History definitions declarations env)
    (typed : PureTyping.HasType env ctx term type) (shape : ConstructorHead term) (typingFuel depth : Nat) :
    ∃ result, step? env ctx typingFuel (depth + 1) term = some result ∧ PureTyping.HasType env ctx result type := by
  obtain ⟨result,ran,output⟩ := contract_from_pure_typing history typed shape
  refine ⟨result,?_,output⟩
  cases shape <;> simpa only [elimTerm,caseTerm,step?] using ran

def replay (env : Environment) (ctx : Context) (typingFuel depth : Nat) : Nat → Term → Term
  | 0, term => term
  | fuel + 1, term =>
      match step? env ctx typingFuel depth term with
      | none => term
      | some result => replay env ctx typingFuel depth fuel result

theorem replay_preserves (history : ScopedProgram.History definitions declarations env)
    (typed : PureTyping.HasType env ctx term type) (typingFuel depth fuel : Nat) :
    PureTyping.HasType env ctx (replay env ctx typingFuel depth fuel term) type := by
  induction fuel generalizing term with
  | zero => exact typed
  | succ fuel ih =>
      rw [replay]
      split
      · exact typed
      · exact ih ((step?_sound (by assumption)).preserves history typed)

end Jihoo.NativeKernel.Environment.LoanTyping.PureFamilyProofs

namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.FamilyProofs

open Finite (Carrier Universe)
open LoanTyping.PureFamilyProofs (ConstructorHead replay contract_from_pure_typing replay_preserves)

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | known : Implication.Tree env term result → Tree env term result
  | universeLambda (level : Fin 32) {result : Code (level :: levels) .proposition} : Tree env body result →
      Tree env (.lam false (.univ level.val) body) (.abstract level result)
  | family {result : Code levels .proposition} : ConstructorHead term →
      (∀ residual, Environment.FamilyIota.contract env term = some residual → Tree env residual result) →
      Tree env term result
  | headReplay (typingFuel depth fuel : Nat) {result : Code levels .proposition} :
      Tree env (replay env (parameterContext levels) typingFuel depth fuel term) result → Tree env term result

/-- The dependent semantic result follows from actual typing and the
executable family branch. The source tree requires finite recognizable
reentry, with no proposed output derivation. -/
theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Finite.decodeProp (code.meaning assignment) := by
  have scope := ScopedProgram.History.ofPureMixed history
  induction tree generalizing requested with
  | known previous => exact previous.truth history typed aligned assignment
  | universeLambda level _ ih =>
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay typed false (.univ level.val) _ rfl
      have child := ((principal.trans aligned).pi_injective history.wellFormed.admissible).2.2
      intro parameter
      exact ih bodyTyped child (assignment.extend level (Finite.Values.decode level parameter))
  | family shape _ ih =>
      obtain ⟨result,ran,retained⟩ := contract_from_pure_typing scope typed shape
      exact ih result ran retained aligned assignment
  | headReplay typingFuel depth fuel _ ih =>
      exact ih (replay_preserves scope typed typingFuel depth fuel) aligned assignment

private theorem decode_inhabits {code : Universe .proposition} (truth : Finite.decodeProp code) :
    Nonempty (Carrier code) := by
  cases code with
  | proposition _ => exact ⟨⟨⟨truth⟩⟩⟩

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions familyDeclarations env)
    (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) := decode_inhabits (tree.truth history typed aligned assignment)

theorem no_admitted_quantified_false {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (tree : Tree env declaration.value (quantifiedFalse (outer := []) levels))
    (annotation : RawValue.Conv env declaration.type (quantifiedFalse (outer := []) levels).syntax) : False := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have original := (history.global_value_and_reference found).1
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  exact quantified_false_uninhabited levels assignment (tree.inhabits history original annotation assignment)

private def upper : Fin 32 := ⟨31,by decide⟩
private def propositionAt (index : Term) : Term := .node (.ind 0 1) [index]
private def family : FamilyDeclaration := ⟨false,0,1,[propositionAt (.natural 0),
  .pi false .u64 (.pi true (propositionAt (.var 0)) (propositionAt (.uadd (.var 1) (.natural 1))))],0⟩
private def successor : Signature := ⟨[⟨false,.u64,none⟩,⟨true,propositionAt (.var 0),some [.var 0]⟩],
  [.uadd (.var 1) (.natural 1)]⟩
private def familyEntry : CheckedFamily := ⟨family,[⟨[],[.natural 0]⟩,successor],false⟩
private def evidence : Term := .decide (.natural 0) (.natural 1)
private def goalCode : Code [upper] .proposition :=
  .less (left := .literal 0) (right := .literal 1) (.literal (by decide)) (.literal (by decide))
private def motive : Term := .lam false .u64 goalCode.syntax
private def branch : Term := .lam false .u64 (.lam true (propositionAt (.var 0)) (.lam true goalCode.syntax (.var 0)))
private def arms : List Term := [evidence,branch]
private def firstConstructor : Term := .node (.con 0 1 2) [.natural 0,.node (.con 0 0 0) []]
private def fields : List Term := [.natural 1,firstConstructor]
private def elimination : Term := Environment.FamilyIota.elimTerm 0 motive arms (.node (.con 0 1 2) fields)
private def selected : Term := Environment.FamilyIota.elimBody familyEntry successor 0 motive branch arms fields
private def annotation : Code [] .proposition := .abstract upper goalCode
private def source : GlobalDeclaration := ⟨annotation.syntax,.lam false (.univ upper.val) elimination⟩
private def world : Environment := ⟨#[source],#[familyEntry]⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨40,40,40,12000⟩

private theorem selected_replays : replay world (parameterContext [upper]) 64 64 64 selected = evidence := by cbv

private theorem sourceTree : Tree world source.value annotation := by
  refine .universeLambda upper (.family (.elim 0 1 motive arms fields) ?_)
  intro residual ran
  have chooses : Environment.FamilyIota.contract world elimination = some selected := by cbv
  change Environment.FamilyIota.contract world elimination = some residual at ran
  rw [chooses] at ran
  cases ran
  apply Tree.headReplay 64 64 64
  rw [selected_replays]
  exact .known (.known (.less (.literal (by decide)) (.literal (by decide))
    (.arithmetic (by simp [evidence,LoanArithmetic.Supported]))))

/-- A mixed checked proposition family takes two genuine recursive
induction branches. Under Type31 the model evaluates the source family
branch applications back to the retained base evidence. -/
theorem checked_recursive_proposition_elimination :
    LoanTyping.PureMixedAdmission.checkProgram limits [source] [family] = some world ∧
    ∀ assignment : Assignment (List.get ([] : List (Fin 32))),
      Nonempty (Carrier (annotation.meaning assignment)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [source] [family] = some world := by cbv
  have history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have original := (history.global_value_and_reference (index := 0) (declaration := source) rfl).1
  exact ⟨admitted,fun assignment => sourceTree.inhabits history original (.refl _) assignment⟩

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.FamilyProofs
