import Jihoo.NativeLoanUniverseErasedApplications

set_option maxUniverseOffset 40

/-! Typed equality elimination into checked dependent motives. Closed
affine equality is read from the original proof, then converted into a real
kernel equation at the native operands of `Transport`. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def NativeTransportInputs (env : Environment) (ctx : Context) : Term → Term → Prop
  | .transport motive equation payload, requested =>
    ∃ left right, HasType env [] ctx true motive (.pi false .u64 .prop) ∧
      HasType env [] ctx true equation (.eq left right) ∧ HasType env [] ctx true payload (.app motive left) ∧
      RawLend.Conv env (.app motive right) requested
  | _, _ => True

private theorem NativeTransportInputs.convert (view : NativeTransportInputs env ctx term original)
    (converted : RawLend.Conv env original requested) : NativeTransportInputs env ctx term requested := by
  fun_cases NativeTransportInputs env ctx term original <;> simp only [NativeTransportInputs] at view ⊢
  · obtain ⟨left,right,motive,equation,payload,result⟩ := view
    exact ⟨left,right,motive,equation,payload,result.trans converted⟩

private theorem native_transport_inputs (typed : HasType env loans ctx mode term type) : NativeTransportInputs env ctx term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => NativeTransportInputs env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case transport motive equation payload _ _ _ =>
    exact ⟨_,_,motive.ghost [],equation.ghost [],payload.ghost [],.refl _⟩
  case convert _ converted ih => exact ih.convert converted
  case dataElim => split <;> trivial

/-- Read both original endpoints and all three native premises beneath a
pure conversion. The explicit final conversion belongs to the source type. -/
theorem typed_transport_inputs (typed : PureTyping.HasType env ctx term requested)
    (source : term = .transport motive equation payload) :
    ∃ left right, HasType env [] ctx true motive (.pi false .u64 .prop) ∧
      HasType env [] ctx true equation (.eq left right) ∧ HasType env [] ctx true payload (.app motive left) ∧
      RawValue.Conv env (.app motive right) requested := by
  induction typed with
  | native native =>
      rw [source] at native
      obtain ⟨left,right,motive,equation,payload,result⟩ := native_transport_inputs native
      exact ⟨left,right,motive,equation,payload,.old result⟩
  | convert _ _ converted ih =>
      obtain ⟨left,right,motive,equation,payload,result⟩ := ih source
      exact ⟨left,right,motive,equation,payload,result.trans converted⟩
  | pi | lam | app => cases source

namespace EqualityTransport

open PureFamilyProofs (replay step?_sound)

private theorem replay_native (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true term type) (typingFuel depth fuel : Nat) :
    HasType env [] ctx true (replay env ctx typingFuel depth fuel term) type := by
  induction fuel generalizing term with
  | zero => exact typed
  | succ fuel ih =>
      rw [replay]
      split
      · exact typed
      · exact ih ((step?_sound (by assumption)).native_preserves history typed)

/-- Replay only the actual equality operand. An executable reflexive
exposure selects the source payload. -/
def observe? (env : Environment) (ctx : Context) (typingFuel depth fuel : Nat) : Term → Option Term
  | .transport _ equation payload =>
      (ProofTransportObservation.exposeRefl? (replay env ctx typingFuel depth fuel equation)).map (fun _ => payload)
  | _ => none

theorem observe?_preserves (history : ScopedProgram.History definitions declarations env)
    (typed : PureTyping.HasType env ctx term type)
    (observed : observe? env ctx typingFuel depth fuel term = some result) : PureTyping.HasType env ctx result type := by
  induction typed with
  | native native =>
      unfold observe? at observed
      split at observed
      · obtain ⟨_,exposed,rfl⟩ := Option.map_eq_some_iff.mp observed
        obtain ⟨_,_,motive,equation,payload,original⟩ := native_transport_inputs native
        have replaced := HasType.transport (ghost := true) motive (replay_native history equation typingFuel depth fuel) payload
        exact (PureProofObservation.Step.transport exposed).preserves history.wellFormed (.native (replaced.convert original))
      · contradiction
  | convert _ formed converted ih => exact .convert (ih observed) formed converted
  | pi | lam | app => simp [observe?] at observed

end EqualityTransport

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.EqualityTransport

open AffineSum (Expr)
open Finite (Carrier decodeProp)
open IndexedProposition (Closed)
open IndexedProposition.Elimination (closed_affine_conversion)
open IndexedProposition.MixedFields (codeLambdas)

structure Equation where
  left : Expr
  right : Expr
  leftClosed : Closed left
  rightClosed : Closed right

def Equation.code (equation : Equation) (levels : List (Fin 32)) : Code levels .proposition :=
  .equal equation.leftClosed equation.rightClosed

private theorem payload_from_equality {levels : List (Fin 32)} (wf : UnifiedProgram.EnvWellFormed env)
    (equation : Equation)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) (.transport motive evidence payload) requested)
    (actualEvidence : LoanTyping.PureTyping.HasType env (parameterContext levels) evidence (equation.code levels).syntax)
    (equal : equation.left.eval (fun _ => 0) = equation.right.eval (fun _ => 0)) :
    ∃ original, LoanTyping.PureTyping.HasType env (parameterContext levels) payload original ∧
      RawValue.Conv env original requested := by
  obtain ⟨left,right,_,checkedEquation,checkedPayload,result⟩ := LoanTyping.typed_transport_inputs typed rfl
  have equalityConv := (LoanTyping.PureTyping.HasType.native checkedEquation).unique wf actualEvidence
  obtain ⟨alignLeft,alignRight⟩ := equalityConv.eq_injective wf.admissible
  have raw := closed_affine_conversion (env := env) equation.leftClosed equation.rightClosed equal
  have original : RawValue.Conv env left right := alignLeft.trans ((RawValue.Conv.old raw).trans alignRight.symm)
  have motiveConv : RawValue.Conv env (.app motive left) (.app motive right) := .node .app (.cons (.refl _) (.cons original .nil))
  exact ⟨_,.native checkedPayload,motiveConv.trans result⟩

/-- Interpret the equality operand of this actual source elimination and
recover the original payload at a type that converts to the requested result.
The result motive need only be the one checked by native Transport. -/
theorem checked_transport_payload {levels : List (Fin 32)}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env) (equation : Equation)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) (.transport motive evidence payload) requested)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
      evidence (equation.code levels).syntax = some .prop)
    (evidenceTree : ErasedApplications.Tree env evidence (equation.code levels)) (assignment : Assignment levels.get) :
    ∃ original, LoanTyping.PureTyping.HasType env (parameterContext levels) payload original ∧
      RawValue.Conv env original requested := by
  have actual := (LoanTyping.PureTyping.Checker.check?_sound checked).2
  have equal := evidenceTree.truth history actual (.refl _) assignment
  exact payload_from_equality history.wellFormed equation typed actual equal

inductive Tree (env : Environment) : {levels : List (Fin 32)} → Term → Code levels .proposition → Prop where
  | known : ErasedApplications.Tree env term result → Tree env term result
  | transport (equation : Equation) {result : Code levels .proposition} :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        evidence (equation.code levels).syntax = some .prop →
      Tree env evidence (equation.code levels) → Tree env payload result → Tree env (.transport motive evidence payload) result
  | replayTransport (typingFuel depth fuel : Nat) {result : Code levels .proposition} :
      LoanTyping.EqualityTransport.observe? env (parameterContext levels) typingFuel depth fuel term = some payload →
      Tree env payload result → Tree env term result
  | family {result : Code levels .proposition} : LoanTyping.PureFamilyProofs.ConstructorHead term →
      (∀ residual, Environment.FamilyIota.contract env term = some residual → Tree env residual result) → Tree env term result
  | universeLambda (level : Fin 32) {body : Code (level :: levels) .proposition} :
      Tree env term body → Tree env (.lam false (.univ level.val) term) (.abstract level body)
  | affineLambda (premise : Implication.Premise) {result : Code levels .proposition} :
      (premise.Holds → Tree env (body.subst (single premise.evidence)) result) →
      Tree env (.lam true premise.syntax body) (premise.arrow result)
  | erasedApply (premise result : Code levels .proposition) :
      LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget (parameterContext levels)
        function (ErasedApplications.erasedArrow premise result).syntax = some .prop →
      Tree env function (ErasedApplications.erasedArrow premise result) → Tree env argument premise → Tree env (.app function argument) result

theorem Tree.truth {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env) (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    decodeProp (code.meaning assignment) := by
  let scope := ScopedProgram.History.ofPureMixed history
  induction tree generalizing requested with
  | known previous => exact previous.truth history typed aligned assignment
  | transport equation checked _ _ ihEquation ihPayload =>
      have actual := (LoanTyping.PureTyping.Checker.check?_sound checked).2
      have equal := ihEquation actual (.refl _) assignment
      obtain ⟨_,payloadTyped,conversion⟩ := payload_from_equality history.wellFormed equation typed actual equal
      exact ihPayload payloadTyped (conversion.trans aligned) assignment
  | replayTransport typingFuel depth fuel observed _ ih =>
      exact ih (LoanTyping.EqualityTransport.observe?_preserves scope typed observed) aligned assignment
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
      exact ih witness (ErasedApplications.affine_body_typed history.wellFormed premise _ typed aligned witness) (.refl _) assignment
  | erasedApply premise result checked _ _ ihFunction ihArgument =>
      obtain ⟨functionTyped,argumentTyped,_⟩ := ErasedApplications.checked_erased_application history.wellFormed premise result typed checked
      exact (ErasedApplications.implication_truth premise result assignment).mp (ihFunction functionTyped (.refl _) assignment)
        (ihArgument argumentTyped (.refl _) assignment)

theorem Tree.inhabits {levels : List (Fin 32)} {code : Code levels .proposition}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env) (tree : Tree env term code)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested)
    (aligned : RawValue.Conv env requested code.syntax) (assignment : Assignment levels.get) :
    Nonempty (Carrier (code.meaning assignment)) := by
  have truth := tree.truth history typed aligned assignment
  generalize code.meaning assignment = model at truth ⊢
  cases model with
  | proposition p => exact ⟨⟨⟨truth⟩⟩⟩

/-- Pi annotations follow the same written binder order as code lambdas. -/
def codeProducts : List (Fin 32) → Term → Term
  | [], body => body
  | level :: outer, body => codeProducts outer (.pi false (.univ level.val) body)

theorem codeLambdas_typed_annotation {outer levels : List (Fin 32)} (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext outer) (codeLambdas levels body) requested)
    (written : RawValue.Conv env requested (codeProducts levels annotation)) :
    ∃ original, LoanTyping.PureTyping.HasType env (parameterContext (levels ++ outer)) body original ∧
      RawValue.Conv env original annotation := by
  induction levels generalizing body annotation requested with
  | nil => exact ⟨requested,typed,written⟩
  | cons level levels ih =>
      obtain ⟨_,opened,converted⟩ := ih (body := .lam false (.univ level.val) body)
        (annotation := .pi false (.univ level.val) annotation) typed written
      obtain ⟨_,bodyTyped,principal⟩ := LoanTyping.PureTyping.lambda_replay opened false (.univ level.val) body rfl
      exact ⟨_,bodyTyped,((principal.trans converted).pi_injective wf.admissible).2.2⟩

theorem checked_global_transport_inhabits {levels : List (Fin 32)} {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (result : Code levels .proposition)
    (source : declaration.value = codeLambdas levels (.transport motive evidence payload))
    (annotation : declaration.type = codeProducts levels result.syntax)
    (tree : Tree env (.transport motive evidence payload) result) (assignment : Assignment levels.get) :
    Nonempty (Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have original := (history.global_value_and_reference found).1
  rw [source,annotation] at original
  obtain ⟨_,bodyTyped,aligned⟩ := codeLambdas_typed_annotation (outer := []) history.wellFormed original (.refl _)
  rw [List.append_nil] at bodyTyped
  exact tree.inhabits history bodyTyped aligned assignment

open IndexedProposition

/-- Equality elimination can use the original native constructor payload
to inhabit the family at its checked, transported vector index. -/
theorem checked_transport_family {id : Nat} {expected : List Expr}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env) (family : Vectors.Family env id)
    (equation : Equation)
    (typed : LoanTyping.PureTyping.HasType env [] (.transport motive evidence payload) (Vectors.propositionAt id (Vectors.terms expected)))
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget [] evidence (equation.code []).syntax = some .prop)
    (evidenceTree : ErasedApplications.Tree env evidence (equation.code []))
    (payloadTree : MixedFields.ConstructorTree id family.entry payload) : MixedFields.Fiber id family.entry (Vectors.evaluate 0 expected) := by
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  obtain ⟨_,payloadTyped,converted⟩ := checked_transport_payload (levels := []) history equation typed checked evidenceTree assignment
  exact payloadTree.pure_sound history family payloadTyped converted

theorem checked_global_transported_family {id : Nat} {expected : List Expr} {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Vectors.Family env id) (found : env.globals[index]? = some declaration) (equation : Equation)
    (source : declaration.value = .transport motive evidence payload)
    (annotation : declaration.type = Vectors.propositionAt id (Vectors.terms expected))
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel conversionFuel budget [] evidence (equation.code []).syntax = some .prop)
    (evidenceTree : ErasedApplications.Tree env evidence (equation.code []))
    (payloadTree : MixedFields.ConstructorTree id family.entry payload) :
    Nonempty (Carrier (MixedFields.meaning family (Vectors.evaluate 0 expected))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  have actual := (history.global_value_and_reference found).1
  rw [source,annotation] at actual
  exact ⟨⟨⟨checked_transport_family history family equation actual checked evidenceTree payloadTree⟩⟩⟩

section Example

private def upper : Fin 32 := ⟨31,by decide⟩
private def lower : Fin 32 := ⟨0,by decide⟩
private def levels : List (Fin 32) := [lower,upper]
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def three : Term := .natural 3
private def sum : Term := .uadd one one
private def next (index : Term) : Term := .uadd index one
private def equation : Equation := ⟨.add (.literal 1) (.literal 1),.literal 2,
  .add (.literal (by decide)) (.literal (by decide)),.literal (by decide)⟩
private def reflProof : Term := .refl sum
private def equality : Term := .app (.lam true (equation.code []).syntax (.var 0)) reflProof
private def targetIndices : List Expr := [.literal 2,.literal 3]
private def declaration : FamilyDeclaration := ⟨false,0,2,[Vectors.propositionAt 0 [two,three]],0⟩
private def table : CheckedFamily := ⟨declaration,[Vectors.baseSignature targetIndices],false⟩
private def familyMotive : Term := .lam false .u64 (Vectors.propositionAt 0 [.var 0,next (.var 0)])
private def familyPayload : Term := .node (.con 0 0 0) []
private def transferredFamily : Term := .transport familyMotive equality familyPayload
private def familySource : GlobalDeclaration := ⟨Vectors.propositionAt 0 [two,three],transferredFamily⟩
private def propositionMotive : Term := .lam false .u64 (.lt (.var 0) (next (.var 0)))
private def propositionPayload : Term := .ltAdd zero one sum (.zeroLe zero)
private def transferredProposition : Term := .transport propositionMotive equality propositionPayload
private def resultCode : Code levels .proposition :=
  .less (left := .literal 2) (right := .literal 3) (.literal (by decide)) (.literal (by decide))
private def propositionSource : GlobalDeclaration :=
  ⟨codeProducts levels resultCode.syntax,codeLambdas levels transferredProposition⟩
private def world : Environment := ⟨#[familySource,propositionSource],#[table]⟩
private def family : Vectors.Family world 0 := ⟨table,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private theorem equality_tree (ambient : List (Fin 32))
    (checked : LoanTyping.Checker.check 48 world [] (parameterContext ambient) true reflProof (equation.code []).syntax = true) :
    ErasedApplications.Tree world equality (equation.code ambient) := by
  refine .erasedBeta 48 checked ?_
  simp only [Term.subst,single]
  let leaf : Proofs.Tree world reflProof (equation.code ambient) :=
    .equal equation.leftClosed equation.rightClosed (.refl equation.left)
  exact .known (.known (.known (.known leaf)))

private theorem family_tree : MixedFields.ConstructorTree 0 table familyPayload := by
  let code : Vectors.IndexCode (MixedFields.ScalarIndex []) 2 targetIndices := ⟨rfl,by
    intro expression found
    rcases List.mem_cons.mp found with rfl | found
    · exact ⟨.literal (by decide),by simp [Expr.variables]⟩
    · cases List.mem_singleton.mp found
      exact ⟨.literal (by decide),by simp [Expr.variables]⟩⟩
  refine .intro (constructor := 0) (fields := []) (.result targetIndices code) rfl ?_
  exact .result code

private theorem proposition_tree : Tree world transferredProposition resultCode := by
  refine .transport (typingFuel := 48) (conversionFuel := 48) (budget := 16000) equation (by cbv)
    (.known (equality_tree levels (by cbv))) ?_
  have supported := (LoanTyping.ProofObservation.supported_iff propositionPayload).mp (by cbv)
  let leaf : Proofs.Tree world propositionPayload resultCode :=
    .less (a := .literal 2) (b := .literal 3) (.literal (by decide)) (.literal (by decide)) (.arithmetic supported)
  exact .known (.known (.known (.known (.known leaf))))

/-- The actual native rule accepts source endpoint `1+1` and target endpoint
`2` at distinct expressions. Mixed admission also accepts both transported
results, including the family vector and an arithmetic motive under two
written universe binders. -/
theorem checked_family_and_universe_transport :
    LoanTyping.PureMixedAdmission.checkProgram limits [familySource,propositionSource] [declaration] = some world ∧
    LoanTyping.HasType world [] [] true transferredFamily (.app familyMotive two) ∧
    LoanTyping.EqualityTransport.observe? world (parameterContext levels) 48 16 16 transferredProposition = some propositionPayload ∧
    Nonempty (Carrier (MixedFields.meaning family [2,3])) ∧
    ∀ assignment : Assignment levels.get, Nonempty (Carrier (resultCode.meaning assignment)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [familySource,propositionSource] [declaration] = some world := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have distinct : LoanTyping.HasType world [] [] true transferredFamily (.app familyMotive two) :=
    .transport (LoanTyping.Checker.check_sound (fuel := 48) (by cbv))
      (a := sum) (b := two) (LoanTyping.Checker.check_sound (fuel := 48) (by cbv))
      (LoanTyping.Checker.check_sound (fuel := 48) (by cbv))
  have replayed : LoanTyping.EqualityTransport.observe? world (parameterContext levels) 48 16 16 transferredProposition = some propositionPayload := by cbv
  have familyTyped := (history.global_value_and_reference (index := 0) (declaration := familySource) rfl).1
  have member := checked_transport_family (expected := targetIndices) history family equation familyTyped
    (typingFuel := 48) (conversionFuel := 48) (budget := 16000) (by cbv) (equality_tree [] (by cbv)) family_tree
  have original := (history.global_value_and_reference (index := 1) (declaration := propositionSource) rfl).1
  obtain ⟨_,bodyTyped,aligned⟩ := codeLambdas_typed_annotation (outer := []) history.wellFormed original (.refl _)
  rw [List.append_nil] at bodyTyped
  exact ⟨admitted,distinct,replayed,⟨⟨⟨member⟩⟩⟩,fun assignment => proposition_tree.inhabits history bodyTyped aligned assignment⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes.EqualityTransport
