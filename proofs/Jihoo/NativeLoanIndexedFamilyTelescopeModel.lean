import Jihoo.NativeLoanIndexedPropositionModel

set_option maxUniverseOffset 40

/-! An indexed proposition carrier may have any sequence of word fields
and erased recursive fields. Its indices use only the preceding word
slots, with the original de Bruijn positions retained. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedFamilyTelescope

open AffineSum (Expr)
open LoanTyping.PureHypothesisObservation (Entry ScalarExpr ScalarSlot)
open ValueErasure.Loan (project project_ordinary_node)
open LoanTyping.FamilyIota (arguments_pi_view signature_metadata)
open NativeKernel.Conversion (ListRel)

private def slotKind (word : Bool) : Entry :=
  if word then .scalar false else .equal (.literal 0) (.literal 0)

abbrev IndexCode (scope : List Bool) (expression : Expr) := ScalarExpr (scope.map slotKind) expression
abbrev IndexCodes (scope : List Bool) (expressions : List Expr) :=
  ∀ index ∈ expressions, IndexCode scope index

def indexType (family : Nat) (indices : List Expr) : Term :=
  .node (.ind family indices.length) (indices.map Expr.toTerm)

inductive Telescope : List Bool → Type where
  | result (indices : List Expr) : IndexCodes scope indices → Telescope scope
  | word (erased : Bool) : Telescope (true :: scope) → Telescope scope
  | recursive (indices : List Expr) : IndexCodes scope indices → Telescope (false :: scope) → Telescope scope

def Telescope.fields (family : Nat) : Telescope scope → List Field
  | .result _ _ => []
  | .word erased tail => ⟨erased,.u64,none⟩ :: tail.fields family
  | .recursive indices _ tail => ⟨true,indexType family indices,some (indices.map Expr.toTerm)⟩ :: tail.fields family

def Telescope.resultIndices : Telescope scope → List Expr
  | .result indices _ => indices
  | .word _ tail => tail.resultIndices
  | .recursive _ _ tail => tail.resultIndices

def Telescope.signature (family : Nat) (telescope : Telescope scope) : Signature :=
  ⟨telescope.fields family,telescope.resultIndices.map Expr.toTerm⟩

def Telescope.type (family : Nat) : Telescope scope → Term
  | .result indices _ => indexType family indices
  | .word erased tail => .pi erased .u64 (tail.type family)
  | .recursive indices _ tail => .pi true (indexType family indices) (tail.type family)

private theorem signature_type (schema : Telescope scope) :
    signatureTerm family (schema.signature family) = schema.type family := by
  induction schema with
  | result indices valid => simp only [Telescope.signature,Telescope.fields,Telescope.resultIndices,Telescope.type,
      indexType,signatureTerm,List.foldr_nil,List.length_map]
  | word erased tail ih => exact congrArg (Term.pi erased .u64) ih
  | recursive indices valid tail ih => exact congrArg (Term.pi true (indexType family indices)) ih

private def extend (value : α) (values : Nat → α) : Nat → α
  | 0 => value
  | i+1 => values i

private def representWord (words : Nat → Nat) (expression : Expr) : Expr :=
  expression.subst (fun i => .literal (words i))

def indicesAt (indices : List Expr) (words : Nat → Nat) : List Nat :=
  indices.map (Expr.eval words)

mutual

inductive Fiber (family : Nat) (entry : CheckedFamily) : List Nat → Prop where
  | constructor {id : Nat} {schema : Telescope []} :
      entry.signatures[id]? = some (schema.signature family) →
      InterpretedFields family entry schema (fun _ => 0) result → Fiber family entry result

inductive InterpretedFields (family : Nat) (entry : CheckedFamily) :
    {scope : List Bool} → Telescope scope → (Nat → Nat) → List Nat → Prop where
  | result (valid : IndexCodes scope indices) : InterpretedFields family entry (.result indices valid) words (indicesAt indices words)
  | word : value < 2^64 → InterpretedFields family entry tail (extend value words) result →
      InterpretedFields family entry (.word erased tail) words result
  | recursive (valid : IndexCodes scope indices) :
      Fiber family entry (indicesAt indices words) → InterpretedFields family entry tail (extend 0 words) result →
      InterpretedFields family entry (.recursive indices valid tail) words result

end

mutual

inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
  | constructor {id : Nat} (schema : Telescope []) :
      entry.signatures[id]? = some (schema.signature family) →
      FieldTree family entry schema fields → ConstructorTree family entry (.node (.con family id fields.length) fields)

inductive FieldTree (family : Nat) (entry : CheckedFamily) :
    {scope : List Bool} → Telescope scope → List Term → Prop where
  | result (valid : IndexCodes scope indices) : FieldTree family entry (.result indices valid) []
  | word : FieldTree family entry tail fields → FieldTree family entry (.word erased tail) (.natural value :: fields)
  | recursive (valid : IndexCodes scope indices) :
      ConstructorTree family entry child → FieldTree family entry tail fields →
      FieldTree family entry (.recursive indices valid tail) (child :: fields)

end

def FamilyMeaning (family : Nat) (entry : CheckedFamily) (indices : List Nat) : Finite.Universe .proposition :=
  .proposition (Fiber family entry indices)

private def Assignment (scope : List Bool) (values : Nat → Term) (words : Nat → Nat) : Prop :=
  ∀ index, scope[index]? = some true → values index = .natural (words index)

private theorem assignment_extend_word (values : Assignment scope assigned words) (value : Nat) :
    Assignment (true :: scope) (extend (.natural value) assigned) (extend value words) := by
  intro index found
  cases index with
  | zero => rfl
  | succ index => exact values index found

private theorem assignment_extend_proof (values : Assignment scope assigned words) (proof : Term) :
    Assignment (false :: scope) (extend proof assigned) (extend 0 words) := by
  intro index found
  cases index with
  | zero => cases found
  | succ index => exact values index found

private theorem selected_word {scope : List Bool} (slot : ScalarSlot (scope.map slotKind) index) : scope[index]? = some true := by
  induction scope generalizing index with
  | nil => cases slot
  | cons tag tail ih =>
    cases tag <;> simp only [List.map_cons,slotKind,Bool.false_eq_true,ite_false,ite_true] at slot
    · cases slot with
      | there inside => exact ih inside
    · cases slot with
      | here => rfl
      | there inside => exact ih inside

private theorem expression_closing (valid : IndexCode scope expression) (aligned : Assignment scope assigned words) :
    expression.toTerm.subst assigned = (representWord words expression).toTerm := by
  induction valid with
  | var slot =>
    simpa only [Expr.toTerm,Term.subst,representWord,Expr.subst] using aligned _ (selected_word slot)
  | literal bound => simp [representWord,Expr.subst,Expr.toTerm,Term.subst,substArgs]
  | add first second ihFirst ihSecond =>
    simp only [Expr.toTerm,Term.subst,substArgs,Op.binders,liftSub,representWord,Expr.subst] at ihFirst ihSecond ⊢
    rw [ihFirst,ihSecond]

private theorem indices_closing (valid : IndexCodes scope indices) (aligned : Assignment scope assigned words) :
    (indexType family indices).subst assigned = indexType family (indices.map (representWord words)) := by
  simp only [indexType,Term.subst,substArgs_dataInd,List.length_map,List.map_map]
  apply congrArg (Term.node (.ind family indices.length))
  apply List.map_congr_left
  intro expression member
  exact expression_closing (valid expression member) aligned

private theorem closed_index_values (indices : List Expr) (words : Nat → Nat) :
    indicesAt (indices.map (representWord words)) (fun _ => 0) = indicesAt indices words := by
  simp only [indicesAt,List.map_map,Function.comp_def,representWord,Expr.subst_eval,Expr.eval]

private theorem under_open_field (body : Term) (values : Nat → Term) (new : Term) :
    (body.subst (liftSubOne values)).subst (single new) = body.subst (extend new values) := by
  rw [Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [liftSubOne,Term.subst,single,extend]
  | succ index =>
    simp only [liftSubOne,Term.subst_rename,extend,single]
    exact Term.subst_id _

private theorem project_indices (env : Environment) (family : Nat) (indices : List Expr) :
    project env (indexType family indices) = indexType family indices := by
  simp only [indexType,project_ordinary_node (op := .ind family indices.length) rfl (by intro impossible; cases impossible),
    ValueErasure.emit,List.map_map,Function.comp_def,IndexedProposition.project_expression]

private theorem vector_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (related : ListRel (FamilyIota.Extended.Conv env) (first.map Expr.toTerm) (second.map Expr.toTerm)) :
    indicesAt first words = indicesAt second words := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons _ _ => cases related
  | cons first rest ih =>
    cases second with
    | nil => cases related
    | cons second remaining =>
      cases related with
      | cons head tail =>
        have same := PureArithmetic.affine_conversion_value wf first second (.old (.old head)) words
        simp only [indicesAt,List.map_cons] at ⊢
        exact congr (congrArg List.cons same) (ih tail)

theorem index_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (related : RawValue.Conv env (indexType family first) (indexType family second)) :
    indicesAt first words = indicesAt second words := by
  have converted := related.projected wf.admissible
  rw [project_indices,project_indices] at converted
  exact vector_conversion wf (converted.ind_injective wf.admissible).2.2

private def TreeSound (env : Environment) (ctx : Context) (family : Nat) (entry : CheckedFamily) (term : Term) : Prop :=
  ∀ {type requested}, LoanTyping.HasType env [] ctx true term type →
    RawValue.Conv env type (indexType family requested) → Fiber family entry (indicesAt requested (fun _ => 0))

private def FieldsSound (env : Environment) (ctx : Context) (family : Nat) (entry : CheckedFamily)
    (schema : Telescope scope) (fields : List Term) : Prop :=
  ∀ {assigned words result}, Assignment scope assigned words →
    LoanTyping.Arguments env [] ctx true entry.declaration.data ((schema.type family).subst assigned) fields result →
    ∃ observed, InterpretedFields family entry schema words (indicesAt observed (fun _ => 0)) ∧
      RawLend.Conv env (indexType family observed) result

/-- The source type of every recursive field comes from the live
constructor arguments. All result indices use the original instantiated
telescope and the shared natural-number interpretation. -/
theorem ConstructorTree.sound
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (tree : ConstructorTree family entry term) :
    ∀ {type requested}, LoanTyping.HasType env [] ctx true term type →
      RawValue.Conv env type (indexType family requested) → Fiber family entry (indicesAt requested (fun _ => 0)) := by
  let wf := history.wellFormed
  intro firstType firstRequest firstTyped firstConverted
  refine ConstructorTree.rec
    (motive_1 := fun term _ => TreeSound env ctx family entry term)
    (motive_2 := fun schema fields _ => FieldsSound env ctx family entry schema fields)
    ?constructor ?result ?word ?recursive tree firstTyped firstConverted
  case constructor =>
    intro fields constructor schema selected argsTree fieldSound type requested typed converted
    obtain ⟨actual,signature,arity,indices,actualFound,actualSignature,arguments,result⟩ := typed.principalView
    cases Option.some.inj (found.symm.trans actualFound)
    cases Option.some.inj (selected.symm.trans actualSignature)
    have signatureClosed := (signature_metadata history found selected).1.signatureTerm_scoped family
    rw [Environment.closed_rename signatureClosed,signature_type,←Term.subst_id (schema.type family)] at arguments
    obtain ⟨observed,fields,indices⟩ := fieldSound (words := fun _ => 0) (by intro i absent; cases absent) arguments
    have alignment := index_conversion (words := fun _ => 0) wf
      ((RawValue.Conv.old (indices.trans result)).trans converted)
    rw [←alignment]
    exact .constructor selected fields
  case result =>
    intro scope indices valid assigned words result assignment args
    cases args with
    | nil converted =>
      have reworded := indices_closing (family := family) valid assignment
      change RawLend.Conv env ((indexType family indices).subst assigned) result at converted
      rw [reworded] at converted
      refine ⟨_,?_,converted⟩
      rw [closed_index_values]
      exact .result valid
  case word =>
    intro scope tail fields erased value tailTyped fieldSound assigned words result assignment args
    simp only [Telescope.type,Term.pi,Term.subst,substArgs,Op.binders,liftSub] at args
    obtain ⟨typed,tail⟩ := arguments_pi_view wf args
    have bound := IndexedProposition.natural_bound typed
    rw [under_open_field] at tail
    obtain ⟨observed,interpreted,related⟩ := fieldSound (assignment_extend_word assignment _) tail
    exact ⟨observed,.word bound interpreted,related⟩
  case recursive =>
    intro scope indices child tail fields valid childTree tailTree childSound tailSound assigned words result assignment args
    have reworded := indices_closing (family := family) valid assignment
    change LoanTyping.Arguments env [] ctx true entry.declaration.data
      ((Term.pi true (indexType family indices) _).subst assigned) _ result at args
    simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] at args
    obtain ⟨typed,tail⟩ := arguments_pi_view wf args
    have indexAlignment : RawLend.Conv env ((indexType family indices).subst assigned)
        (indexType family (indices.map (representWord words))) := by
      rw [reworded]
      exact .refl _
    have child := childSound typed (RawValue.Conv.old indexAlignment)
    rw [closed_index_values] at child
    rw [under_open_field] at tail
    obtain ⟨observed,interpreted,related⟩ := tailSound (assignment_extend_proof assignment _) tail
    exact ⟨observed,.recursive valid child interpreted,related⟩

theorem ConstructorTree.pure_sound
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (found : env.families[family]? = some entry) (tree : ConstructorTree family entry term)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (requested : RawValue.Conv env type (indexType family indices)) :
    Fiber family entry (indicesAt indices (fun _ => 0)) := by
  have shape : ∃ constructor count values, term = .node (.con family constructor count) values := by
    cases tree
    exact ⟨_,_,_,rfl⟩
  obtain ⟨_,_,_,root⟩ := shape
  obtain ⟨_,native,prior⟩ := IndexedProposition.native_constructor typed root
  exact tree.sound (ScopedProgram.History.ofPureMixed history) found native (prior.trans requested)

theorem checked_global_carrier {index : Nat} {declaration : GlobalDeclaration}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : env.families[familyId]? = some entry) (found : env.globals[index]? = some declaration)
    (tree : ConstructorTree familyId entry declaration.value)
    (requested : RawValue.Conv env declaration.type (indexType familyId indices)) :
    Nonempty (Finite.Carrier (FamilyMeaning familyId entry (indicesAt indices (fun _ => 0)))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  exact ⟨⟨⟨tree.pure_sound history family (history.global_value_and_reference found).1 requested⟩⟩⟩

private theorem field_result_indices (interpreted : InterpretedFields family entry schema words result) :
    ∃ assignment, result = indicesAt schema.resultIndices assignment := by
  refine InterpretedFields.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun schema _ result _ => ∃ assignment, result = indicesAt schema.resultIndices assignment)
    ?constructor ?result ?word ?recursive interpreted
  case constructor => intros; trivial
  case result => intros; exact ⟨_,rfl⟩
  case word => intros; assumption
  case recursive => intros; assumption

theorem Fiber.original_result_indices (inhabited : Fiber family entry result) :
    ∃ (constructor : Nat) (schema : Telescope []) (assignment : Nat → Nat),
      entry.signatures[constructor]? = some (schema.signature family) ∧
        result = indicesAt schema.resultIndices assignment := by
  cases inhabited with
  | constructor selected fields =>
    obtain ⟨assignment,matched⟩ := field_result_indices fields
    exact ⟨_,_,assignment,selected,matched⟩

private def beginSchema : Telescope [] :=
  .result [.literal 0,.literal 7] (by
    intro code included
    simp only [List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl | rfl <;> exact .literal (by decide))

private def branchSchema : Telescope [] :=
  .word false (.recursive [.var 0,.literal 7] (by
    intro code included
    simp only [List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl | rfl
    · exact .var .here
    · exact .literal (by decide))
    (.recursive [.var 1,.literal 7] (by
      intro code included
      simp only [List.mem_cons,List.not_mem_nil,or_false] at included
      rcases included with rfl | rfl
      · exact .var (.there .here)
      · exact .literal (by decide))
      (.result [.literal 2,.literal 7] (by
        intro code included
        simp only [List.mem_cons,List.not_mem_nil,or_false] at included
        rcases included with rfl | rfl <;> exact .literal (by decide)))))

private def familyDeclaration : FamilyDeclaration :=
  ⟨false,0,2,[beginSchema.type 0,branchSchema.type 0],0⟩
private def familyEntry : CheckedFamily :=
  ⟨familyDeclaration,[beginSchema.signature 0,branchSchema.signature 0],false⟩
private def leaf : Term := .node (.con 0 0 0) []
private def tree : Term := .node (.con 0 1 3) [.natural 0,leaf,leaf]
private def declaredValue : GlobalDeclaration := ⟨indexType 0 [.literal 2,.literal 7],tree⟩
private def declaredEnv : Environment := ⟨#[declaredValue],#[familyEntry]⟩

private theorem read_branch : ConstructorTree 0 familyEntry tree := by
  refine .constructor branchSchema rfl (.word (.recursive _ ?_ (.recursive _ ?_ (.result _))))
  all_goals exact .constructor beginSchema rfl (.result _)

/-- An admitted two-index proposition uses two erased recursive arguments
at the scopes of the original word field. Its exact declared value
inhabits the interpreted result vector. -/
theorem two_index_constructor_tree_checked :
    LoanTyping.PureMixedAdmission.checkProgram ⟨32,32,32,8192⟩ [declaredValue] [familyDeclaration] = some declaredEnv ∧
      Nonempty (Finite.Carrier (FamilyMeaning 0 familyEntry [2,7])) := by
  have accepted : LoanTyping.PureMixedAdmission.checkProgram ⟨32,32,32,8192⟩ [declaredValue] [familyDeclaration] =
      some declaredEnv := by cbv
  have history := LoanTyping.PureMixedAdmission.checkProgram_sound accepted
  have typed := (history.global_value_and_reference (index := 0) (declaration := declaredValue) rfl).1
  exact ⟨accepted,⟨⟨⟨read_branch.pure_sound (indices := [.literal 2,.literal 7]) history rfl typed (.refl _)⟩⟩⟩⟩

private theorem read_indices {first second : List Expr}
    (same : first.map Expr.toTerm = second.map Expr.toTerm) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons head rest ih =>
    cases second with
    | nil => simp at same
    | cons next tail =>
      simp only [List.map_cons,List.cons.injEq] at same
      have headEq := congrArg AffineSum.parse same.1
      simp only [AffineSum.parse_toTerm,Option.some.injEq] at headEq
      rw [headEq,ih same.2]

/-- All constructors of the admitted family have second index seven,
including the branch with two recursive proofs. -/
theorem two_index_family_excludes_other_second_index (other : second ≠ 7) :
    ¬ Fiber 0 familyEntry [first,second] := by
  intro inhabited
  obtain ⟨constructor,schema,assignment,found,indices⟩ := inhabited.original_result_indices
  have selected := List.mem_iff_getElem?.mpr ⟨constructor,found⟩
  have signature : schema.signature 0 = beginSchema.signature 0 ∨
      schema.signature 0 = branchSchema.signature 0 := by
    simpa only [familyEntry,List.mem_cons,List.not_mem_nil,or_false] using selected
  rcases signature with base | branch
  · have read : schema.resultIndices = [.literal 0,.literal 7] :=
      read_indices (congrArg Signature.result base)
    rw [read] at indices
    exact other (List.cons.inj (List.cons.inj indices).2).1
  · have read : schema.resultIndices = [.literal 2,.literal 7] :=
      read_indices (congrArg Signature.result branch)
    rw [read] at indices
    exact other (List.cons.inj (List.cons.inj indices).2).1


private def wordCode (scope : List Bool) : Expr → Bool
  | .var index => scope[index]? == some true
  | .literal word => decide (word < 2^64)
  | .add left right => wordCode scope left && wordCode scope right

private theorem lookup_word {scope : List Bool} (found : scope[index]? = some true) :
    ScalarSlot (scope.map slotKind) index := by
  induction scope generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst head
      exact .here
    | succ index =>
      exact .there (ih found)

private theorem wordCode_sound (checked : wordCode scope expression = true) : IndexCode scope expression := by
  induction expression with
  | var index =>
    exact .var (lookup_word (beq_iff_eq.mp checked))
  | literal word => exact .literal (of_decide_eq_true checked)
  | add left right ihLeft ihRight =>
    obtain ⟨checkedLeft,checkedRight⟩ := Bool.and_eq_true_iff.mp checked
    exact .add (ihLeft checkedLeft) (ihRight checkedRight)

private def parseIndex (scope : List Bool) (term : Term) :
    Option {code : Expr // code.toTerm = term ∧ IndexCode scope code} :=
  let parsed := AffineSum.parse term
  if known : parsed.isSome then
    let code := parsed.get known
    if checked : wordCode scope code = true then
      some ⟨code,AffineSum.parse_sound (Option.some_get known).symm,wordCode_sound checked⟩
    else none
  else none

private def parseVector (scope : List Bool) :
    (terms : List Term) → Option {codes : List Expr // codes.map Expr.toTerm = terms ∧ IndexCodes scope codes}
  | [] => some ⟨[],rfl,by intro index absent; cases absent⟩
  | term :: terms => do
    let first ← parseIndex scope term
    let rest ← parseVector scope terms
    pure ⟨first.val :: rest.val,by rw [List.map_cons,first.property.1,rest.property.1],by
      intro index member
      rcases List.mem_cons.mp member with rfl | later
      · exact first.property.2
      · exact rest.property.2 index later⟩

private def parseTelescope (family : Nat) :
    (scope : List Bool) → (fields : List Field) → (result : List Term) →
      Option {code : Telescope scope // code.fields family = fields ∧ code.resultIndices.map Expr.toTerm = result}
  | scope,[],result => do
    let indices ← parseVector scope result
    pure ⟨.result indices.val indices.property.2,rfl,indices.property.1⟩
  | scope,⟨erased,domain,none⟩ :: fields,result =>
    if checked : domain == Term.u64 then do
      let tail ← parseTelescope family (true :: scope) fields result
      pure ⟨.word erased tail.val,by
        simp only [Telescope.fields,beq_iff_eq.mp checked,tail.property.1],tail.property.2⟩
    else none
  | scope,⟨erased,domain,some recursive⟩ :: fields,result => do
    let indices ← parseVector scope recursive
    if checked : erased = true ∧ domain == indexType family indices.val then do
      let tail ← parseTelescope family (false :: scope) fields result
      pure ⟨.recursive indices.val indices.property.2 tail.val,by
        simp only [Telescope.fields,checked.1,beq_iff_eq.mp checked.2,indices.property.1,tail.property.1],tail.property.2⟩
    else none
termination_by _ fields _ => fields.length

/-- Compile a stored constructor signature to its exact finite telescope.
The compiler checks the scopes and transports equality of the original
index syntax into its output. -/
def parseSignature (family : Nat) (signature : Signature) :
    Option {schema : Telescope [] // schema.signature family = signature} := do
  let schema ← parseTelescope family [] signature.fields signature.result
  pure ⟨schema.val,by
    cases signature
    simp only [Telescope.signature,schema.property.1,schema.property.2]⟩

private def checkFields (checkChild : Term → Bool) : Telescope scope → List Term → Bool
  | .result _ _,[] => true
  | .word _ tail, .natural _ :: fields => checkFields checkChild tail fields
  | .recursive _ _ tail, child :: fields => checkChild child && checkFields checkChild tail fields
  | _,_ => false

/-- Recognize only the syntax needed by the indexed carrier construction.
The stored signature fixes the schema and the eligible recursive fields.
Actual index equalities are still derived by the typing theorem. -/
def checkTree (family : Nat) (entry : CheckedFamily) : Nat → Term → Bool
  | 0,_ => false
  | fuel+1,.node (.con actual constructor arity) fields =>
    if actual = family ∧ arity = fields.length then
      match entry.signatures[constructor]? with
      | none => false
      | some signature =>
        match parseSignature family signature with
        | some schema => checkFields (checkTree family entry fuel) schema.val fields
        | none => false
    else false
  | _+1,_ => false

private theorem checkFields_sound (childSound : ∀ child, checkChild child = true → ConstructorTree family entry child)
    {schema : Telescope scope}
    (accepted : checkFields checkChild schema fields = true) : FieldTree family entry schema fields := by
  induction schema generalizing fields with
  | result indices valid =>
    cases fields with
    | nil => exact .result valid
    | cons _ _ => cases accepted
  | word erased tail ih =>
    cases fields with
    | nil => cases accepted
    | cons field fields =>
      cases field with
      | var => cases accepted
      | node op args =>
        cases op <;> try cases accepted
        case natural value =>
          cases args with
          | nil => exact .word (ih accepted)
          | cons _ _ => cases accepted
  | recursive indices valid tail ih =>
    cases fields with
    | nil => cases accepted
    | cons child fields =>
      have aligned := Bool.and_eq_true_iff.mp accepted
      exact .recursive valid (childSound child aligned.1) (ih aligned.2)

theorem checkTree_sound (accepted : checkTree family entry fuel term = true) : ConstructorTree family entry term := by
  induction fuel generalizing term with
  | zero => cases accepted
  | succ fuel ih =>
    cases term with
    | var => simp [checkTree] at accepted
    | node op fields =>
      cases op <;> try simp [checkTree] at accepted
      case con actual constructor arity =>
        obtain ⟨⟨rfl,rfl⟩,accepted⟩ := accepted
        split at accepted
        · cases accepted
        · rename_i signature read
          split at accepted
          · rename_i schema parsed
            rw [←schema.property] at read
            exact .constructor schema.val read (checkFields_sound (fun _ child => ih child) accepted)
          · cases accepted

/-- The byte checker supplies the value, and the signature parser and
shape recognizer supply its indexed constructor tree. -/
theorem checked_recognized_global_carrier {index : Nat} {declaration : GlobalDeclaration}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : env.families[familyId]? = some entry) (found : env.globals[index]? = some declaration)
    (recognized : checkTree familyId entry fuel declaration.value = true)
    (requested : RawValue.Conv env declaration.type (indexType familyId indices)) :
    Nonempty (Finite.Carrier (FamilyMeaning familyId entry (indicesAt indices (fun _ => 0)))) :=
  checked_global_carrier accepted family found (checkTree_sound recognized) requested

/-- The original checked proof may first compute by indexed elimination
and typed beta. The replay keeps its declared type while the recognizer
constructs the semantic witness from the selected constructor. -/
theorem checked_replayed_global_carrier {index : Nat} {declaration : GlobalDeclaration}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : env.families[familyId]? = some entry) (found : env.globals[index]? = some declaration)
    (recognized : checkTree familyId entry treeFuel
      (LoanTyping.PureFamilyProofs.replay env [] typingFuel depth steps declaration.value) = true)
    (requested : RawValue.Conv env declaration.type (indexType familyId indices)) :
    Nonempty (Finite.Carrier (FamilyMeaning familyId entry (indicesAt indices (fun _ => 0)))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  have typed := LoanTyping.PureFamilyProofs.replay_preserves (ScopedProgram.History.ofPureMixed history)
    (history.global_value_and_reference found).1 typingFuel depth steps
  exact ⟨⟨⟨(checkTree_sound recognized).pure_sound history family typed requested⟩⟩⟩

/-- The same admitted example can be recognized directly from its stored
signature and original constructor value. -/
theorem recognizes_two_recursive_fields : checkTree 0 familyEntry 3 declaredValue.value = true := by cbv

private def targetType : Term := indexType 0 [.literal 2,.literal 7]

private def indexedMotive : Term := .lam false .u64 (.lam false .u64 targetType)

private def inductionBranch : Term := .lam false .u64
  (.lam true (indexType 0 [.var 0,.literal 7])
    (.lam true (indexType 0 [.var 1,.literal 7])
      (.lam true targetType (.lam true targetType (.var 0)))))

private def inductionProof : Term :=
  FamilyIota.elimTerm 0 indexedMotive [tree,inductionBranch] tree

private def inductionDeclaration : GlobalDeclaration := ⟨targetType,inductionProof⟩
private def inductionEnv : Environment := ⟨#[inductionDeclaration],#[familyEntry]⟩
private def inductionLimits : LoanTyping.PureMixedAdmission.Limits := ⟨40,40,40,12000⟩

/-- The checked source eliminates a constructor with two recursive proof
fields. Its branch returns the second recursive hypothesis whose base
case computes to the actual constructor at the original result vector. -/
theorem checked_indexed_induction_replays_to_carrier :
    LoanTyping.PureMixedAdmission.checkProgram inductionLimits [inductionDeclaration] [familyDeclaration] = some inductionEnv ∧
      Nonempty (Finite.Carrier (FamilyMeaning 0 familyEntry [2,7])) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram inductionLimits [inductionDeclaration] [familyDeclaration] =
      some inductionEnv := by cbv
  have history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have typed := LoanTyping.PureFamilyProofs.replay_preserves (ScopedProgram.History.ofPureMixed history)
    (history.global_value_and_reference (index := 0) (declaration := inductionDeclaration) rfl).1 48 48 12
  have replayed : LoanTyping.PureFamilyProofs.replay inductionEnv [] 48 48 12 inductionProof = tree := by cbv
  change LoanTyping.PureTyping.HasType inductionEnv []
    (LoanTyping.PureFamilyProofs.replay inductionEnv [] 48 48 12 inductionProof) targetType at typed
  rw [replayed] at typed
  exact ⟨admitted,⟨⟨⟨read_branch.pure_sound (indices := [.literal 2,.literal 7]) history rfl typed (.refl _)⟩⟩⟩⟩

end Jihoo.NativeKernel.Environment.Semantics.IndexedFamilyTelescope
