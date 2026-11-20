import Jihoo.NativeLoanIndexedPropositionScalarPrefixes

/-! Interpret native proposition constructors whose scalar fields and recursive
proof fields interleave. An index expression may refer only to a preceding
scalar slot, though the native substitution retains every actual proof term. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.MixedFields

open AffineSum (Expr)
open Vectors (IndexCode terms baseSignature)
open LoanTyping.FamilyIota (arguments_pi_view extendField lift_single_extend)
open Environment.FamilyIota (elimTerm)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes (Code)

variable {id : Nat}

inductive Slot where
  | scalar
  | recursive

def ScalarIndex (previous : List Slot) (expression : Expr) : Prop :=
  ScalarPrefixes.ScalarCode previous.length expression ∧
    ∀ index ∈ expression.variables, previous[index]? = some .scalar

inductive Scheme (arity : Nat) : List Slot → Type where
  | result (indices : List Expr) : IndexCode (ScalarIndex previous) arity indices → Scheme arity previous
  | scalar : Scheme arity (.scalar :: previous) → Scheme arity previous
  | recursive (indices : List Expr) : IndexCode (ScalarIndex previous) arity indices →
      Scheme arity (.recursive :: previous) → Scheme arity previous

def Scheme.signature (family : Nat) : Scheme arity previous → Signature
  | .result indices _ => baseSignature indices
  | .scalar rest =>
      let tail := rest.signature family
      ⟨⟨false,.u64,none⟩ :: tail.fields,tail.result⟩
  | .recursive indices _ rest =>
      let tail := rest.signature family
      let indexTerms := terms indices
      ⟨⟨true,Vectors.propositionAt family indexTerms,some indexTerms⟩ :: tail.fields,tail.result⟩

private def push (value : Expr) (previous : Nat → Expr) : Nat → Expr
  | 0 => value
  | index+1 => previous index

def ground (values : Nat → Expr) (indices : List Expr) : List Expr := indices.map (Expr.subst values)

def interpret (values : Nat → Expr) (indices : List Expr) : List Nat :=
  indices.map (Expr.eval (fun index => (values index).eval (fun _ => 0)))

private theorem ground_evaluates (values : Nat → Expr) (indices : List Expr) :
    Vectors.evaluate 0 (ground values indices) = interpret values indices := by
  simp only [Vectors.evaluate,ground,interpret,List.map_map]
  apply List.map_congr_left
  intro expression _
  exact Expr.subst_eval _ _ _

/-- Scalar index slots agree with the actual raw substitution. Recursive
slots are carried only by the native substitution and do not have a numeric
meaning in indices. -/
structure Prefix (previous : List Slot) (values : Nat → Expr) (σ : Nat → Term) : Prop where
  closed : ∀ index, Closed (values index)
  agreed : ∀ index, previous[index]? = some .scalar → σ index = (values index).toTerm

private theorem Prefix.initial : Prefix [] (fun _ => .literal 0) Term.var := by
  exact ⟨fun _ => .literal (by decide),by intro index missing; simp at missing⟩

private theorem Prefix.scalar (before : Prefix previous values σ) (closed : Closed value) :
    Prefix (.scalar :: previous) (push value values) (extendField σ value.toTerm) := by
  constructor
  · intro index
    cases index with
    | zero => exact closed
    | succ index => exact before.closed index
  · intro index selected
    cases index with
    | zero => rfl
    | succ index => exact before.agreed index selected

private theorem Prefix.recursive (before : Prefix previous values σ) (proof : Term) :
    Prefix (.recursive :: previous) (push (.literal 0) values) (extendField σ proof) := by
  constructor
  · intro index
    cases index with
    | zero => exact .literal (by decide)
    | succ index => exact before.closed index
  · intro index selected
    cases index with
    | zero => cases selected
    | succ index => exact before.agreed index selected

private theorem subst_used {expression : Expr} {σ τ : Nat → Term} (agreed : ∀ index ∈ expression.variables, σ index = τ index) :
    expression.toTerm.subst σ = expression.toTerm.subst τ := by
  induction expression with
  | var index => simpa only [Expr.toTerm,Term.subst] using agreed index (by simp [Expr.variables])
  | literal value => simp only [Expr.toTerm,Term.subst,substArgs]
  | add first second ihFirst ihSecond =>
      simp only [Expr.toTerm,Term.subst,substArgs,Op.binders,liftSub]
      rw [ihFirst (fun index used => agreed index (by simp [Expr.variables,used])),
        ihSecond (fun index used => agreed index (by simp [Expr.variables,used]))]

theorem Prefix.index_substitution (before : Prefix previous values σ)
    (code : IndexCode (ScalarIndex previous) arity indices) :
    (Vectors.propositionAt id (terms indices)).subst σ = Vectors.propositionAt id (terms (ground values indices)) := by
  rw [Vectors.proposition_subst]
  apply congrArg (Vectors.propositionAt id)
  simp only [terms,ground,List.map_map]
  apply List.map_congr_left
  intro expression member
  simp only [Function.comp_apply]
  rw [Expr.subst_toTerm]
  exact subst_used (fun index used => before.agreed index ((code.valid expression member).2 index used))

private theorem Prefix.grounded (before : Prefix previous values σ)
    (code : IndexCode (ScalarIndex previous) arity indices) : IndexCode Closed arity (ground values indices) := by
  refine ⟨(List.length_map _).trans code.size,?_⟩
  intro expression member
  obtain ⟨original,selected,rfl⟩ := List.mem_map.mp member
  exact ScalarPrefixes.expression_closed (code.valid original selected).1 before.closed

private theorem pi_substitution (erased : Bool) (domain tail : Term) (σ : Nat → Term) :
    (Term.pi erased domain tail).subst σ = .pi erased (domain.subst σ) (tail.subst (liftSubOne σ)) := by
  simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub]

private theorem field_instantiation (tail : Term) (σ : Nat → Term) (value : Term) :
    (tail.subst (liftSubOne σ)).subst (single value) = tail.subst (extendField σ value) := by
  rw [Term.subst_comp,lift_single_extend]

private theorem u64_substitution (σ : Nat → Term) : Term.u64.subst σ = .u64 := by
  simp only [Term.u64,Term.subst,substArgs]

mutual
  inductive Fiber (family : Nat) (entry : CheckedFamily) : List Nat → Prop where
    | intro {constructor : Nat} (scheme : Scheme entry.declaration.arity []) : entry.signatures[constructor]? = some (scheme.signature family) →
        SemanticFields family entry (fun _ => .literal 0) scheme index → Fiber family entry index

  inductive SemanticFields (family : Nat) (entry : CheckedFamily) :
      {previous : List Slot} → (Nat → Expr) → Scheme entry.declaration.arity previous → List Nat → Prop where
    | result (code : IndexCode (ScalarIndex previous) entry.declaration.arity indices) :
        SemanticFields family entry values (.result indices code) (interpret values indices)
    | scalar {value : Expr} : Closed value → SemanticFields family entry (push value values) rest index →
        SemanticFields family entry values (.scalar rest) index
    | recursive (code : IndexCode (ScalarIndex previous) entry.declaration.arity indices) :
        Fiber family entry (interpret values indices) → SemanticFields family entry (push (.literal 0) values) rest index →
        SemanticFields family entry values (.recursive indices code rest) index
end

mutual
  inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
    | intro {constructor : Nat} (scheme : Scheme entry.declaration.arity []) : entry.signatures[constructor]? = some (scheme.signature family) →
        SourceFields family entry scheme fields → ConstructorTree family entry (.node (.con family constructor fields.length) fields)

  inductive SourceFields (family : Nat) (entry : CheckedFamily) :
      {previous : List Slot} → Scheme entry.declaration.arity previous → List Term → Prop where
    | result (code : IndexCode (ScalarIndex previous) entry.declaration.arity indices) :
        SourceFields family entry (.result indices code) []
    | scalar (value : Expr) : SourceFields family entry rest fields →
        SourceFields family entry (.scalar rest) (value.toTerm :: fields)
    | recursive (code : IndexCode (ScalarIndex previous) entry.declaration.arity indices) :
        ConstructorTree family entry child → SourceFields family entry rest fields →
        SourceFields family entry (.recursive indices code rest) (child :: fields)
end

def meaning (family : Vectors.Family env id) (index : List Nat) : Finite.Universe .proposition := .proposition (Fiber id family.entry index)

/-- Walk the actual constructor `Arguments` through every field. Recursive
positions are interpreted at their exact indices under the original prefix. -/
theorem ConstructorTree.sound {expected : List Expr} (history : ScopedProgram.History definitions declarations env)
    (family : Vectors.Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.HasType env [] [] true term type)
    (requested : RawValue.Conv env type (Vectors.propositionAt id (terms expected))) :
    Fiber id family.entry (Vectors.evaluate 0 expected) := by
  let wf := history.wellFormed
  refine ConstructorTree.rec
    (motive_1 := fun source _ => ∀ {type : Term} {expected : List Expr},
      LoanTyping.HasType env [] [] true source type → RawValue.Conv env type (Vectors.propositionAt id (terms expected)) →
      Fiber id family.entry (Vectors.evaluate 0 expected))
    (motive_2 := fun {previous} scheme fields _ => ∀ {type : Term} {values : Nat → Expr} {σ : Nat → Term},
      Prefix previous values σ →
      LoanTyping.Arguments env [] [] true family.entry.declaration.data ((signatureTerm id (scheme.signature id)).subst σ) fields type →
      ∃ actual : List Expr, SemanticFields id family.entry values scheme (Vectors.evaluate 0 actual) ∧
        RawLend.Conv env (Vectors.propositionAt id (terms actual)) type)
    ?_ ?_ ?_ ?_ tree typed requested
  · intro fields constructor scheme selected _ ih type expected typed aligned
    obtain ⟨_,_,arguments,converted⟩ := Vectors.constructor_arguments history family selected typed
    rw [← Term.subst_id (signatureTerm id (scheme.signature id))] at arguments
    obtain ⟨actual,semantic,result⟩ := ih Prefix.initial arguments
    have equal := Vectors.index_conversion (scalar := 0) wf ((RawValue.Conv.old (result.trans converted)).trans aligned)
    rw [← equal]
    exact .intro scheme selected semantic
  · intro previous indices code type values σ agreed arguments
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Vectors.propositionAt id (terms indices)).subst σ) [] type at arguments
    rw [agreed.index_substitution code] at arguments
    cases arguments with
    | nil converted => exact ⟨ground values indices,(by rw [ground_evaluates]; exact .result code),converted⟩
  · intro previous rest fields value _ ih type values σ agreed arguments
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Term.pi false .u64 (signatureTerm id (rest.signature id))).subst σ) (value.toTerm :: fields) type at arguments
    rw [pi_substitution,u64_substitution] at arguments
    obtain ⟨valueTyped,remaining⟩ := arguments_pi_view wf arguments
    rw [field_instantiation] at remaining
    have closed := ScalarPrefixes.checked_affine_argument valueTyped
    obtain ⟨actual,other,converted⟩ := ih (agreed.scalar closed) remaining
    exact ⟨actual,.scalar closed other,converted⟩
  · intro previous indices child rest fields code _ _ ihChild ihRest type values σ agreed arguments
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Term.pi true (Vectors.propositionAt id (terms indices)) (signatureTerm id (rest.signature id))).subst σ) (child :: fields) type at arguments
    rw [pi_substitution,agreed.index_substitution code] at arguments
    obtain ⟨childTyped,remaining⟩ := arguments_pi_view wf arguments
    rw [field_instantiation] at remaining
    have childSemantic := ihChild childTyped (.refl _)
    rw [ground_evaluates] at childSemantic
    obtain ⟨actual,other,converted⟩ := ihRest (agreed.recursive child) remaining
    exact ⟨actual,.recursive code childSemantic other,converted⟩

private theorem ConstructorTree.head (tree : ConstructorTree id entry term) :
    ∃ constructor values, term = .node (.con id constructor values.length) values := by
  cases tree with | intro scheme selected fields => exact ⟨_,_,rfl⟩

theorem ConstructorTree.pure_sound {expected : List Expr} (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (family : Vectors.Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.PureTyping.HasType env [] term type)
    (requested : RawValue.Conv env type (Vectors.propositionAt id (terms expected))) :
    Fiber id family.entry (Vectors.evaluate 0 expected) := by
  obtain ⟨_,_,head⟩ := tree.head
  obtain ⟨_,native,conversion⟩ := native_constructor typed head
  exact tree.sound (ScopedProgram.History.ofPureMixed history) family native (conversion.trans requested)

theorem checked_global_carrier {declaration : GlobalDeclaration} {index : Nat} {expected : List Expr}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Vectors.Family env id) (found : env.globals[index]? = some declaration) (tree : ConstructorTree id family.entry declaration.value)
    (requested : RawValue.Conv env declaration.type (Vectors.propositionAt id (terms expected))) :
    Nonempty (Finite.Carrier (meaning family (Vectors.evaluate 0 expected))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  exact ⟨⟨⟨tree.pure_sound history family (history.global_value_and_reference found).1 requested⟩⟩⟩

structure Realization (family : Vectors.Family env id) (index : List Nat) where
  expressions : List Expr
  code : IndexCode Closed family.entry.declaration.arity expressions
  evaluated : Vectors.evaluate 0 expressions = index
  term : Term
  tree : ConstructorTree id family.entry term
  typed : LoanTyping.HasType env [] [] true term (Vectors.propositionAt id (terms expressions))

/-- Reification reconstructs fields in declaration order. At a recursive
field the actual proof enters the native substitution and later indices
continue to use only the preceding scalars they declare. -/
theorem Fiber.reify (family : Vectors.Family env id) (inhabited : Fiber id family.entry index) : Nonempty (Realization family index) := by
  refine Fiber.rec
    (motive_1 := fun index _ => Nonempty (Realization family index))
    (motive_2 := fun {previous} values scheme index _ => ∀ {σ : Nat → Term}, Prefix previous values σ →
      ∃ fields expressions, SourceFields id family.entry scheme fields ∧
        IndexCode Closed family.entry.declaration.arity expressions ∧ Vectors.evaluate 0 expressions = index ∧
        LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((signatureTerm id (scheme.signature id)).subst σ) fields (Vectors.propositionAt id (terms expressions)))
    ?_ ?_ ?_ ?_ inhabited
  · intro index constructor scheme selected _ ih
    obtain ⟨fields,expressions,trees,code,evaluated,arguments⟩ := ih Prefix.initial
    rw [Term.subst_id] at arguments
    exact ⟨⟨expressions,code,evaluated,.node (.con id constructor fields.length) fields,.intro scheme selected trees,
      Vectors.constructor_typed family selected arguments⟩⟩
  · intro previous indices values code σ agreed
    refine ⟨[],ground values indices,.result code,agreed.grounded code,ground_evaluates values indices,?_⟩
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Vectors.propositionAt id (terms indices)).subst σ) [] _
    rw [agreed.index_substitution code]
    exact .nil (.refl _)
  · intro values previous rest index value closed _ ih σ agreed
    obtain ⟨fields,expressions,trees,code,evaluated,arguments⟩ := ih (agreed.scalar closed)
    refine ⟨value.toTerm :: fields,expressions,.scalar value trees,code,evaluated,?_⟩
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Term.pi false .u64 (signatureTerm id (rest.signature id))).subst σ) (value.toTerm :: fields) _
    rw [pi_substitution,u64_substitution]
    refine .cons (.refl _) closed.typed ?_
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      (((signatureTerm id (rest.signature id)).subst (liftSubOne σ)).subst (single value.toTerm)) fields _
    rwa [field_instantiation]
  · intro previous indices values rest index code _ _ ihChild ihRest σ agreed
    obtain ⟨child⟩ := ihChild
    have alignment := Vectors.closed_index_conversion (env := env) (id := id) child.code (agreed.grounded code)
      (child.evaluated.trans (ground_evaluates values indices).symm)
    obtain ⟨fields,expressions,trees,resultCode,evaluated,arguments⟩ := ihRest (agreed.recursive child.term)
    refine ⟨child.term :: fields,expressions,.recursive code child.tree trees,resultCode,evaluated,?_⟩
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      ((Term.pi true (Vectors.propositionAt id (terms indices)) (signatureTerm id (rest.signature id))).subst σ) (child.term :: fields) _
    rw [pi_substitution,agreed.index_substitution code]
    refine .cons (.refl _) (child.typed.convert alignment) ?_
    change LoanTyping.Arguments env [] [] true family.entry.declaration.data
      (((signatureTerm id (rest.signature id)).subst (liftSubOne σ)).subst (single child.term)) fields _
    rwa [field_instantiation]

theorem Realization.elimination_contracts {family : Vectors.Family env id} (input : Realization family index)
    (history : ScopedProgram.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    ∃ residual, Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual ∧
      LoanTyping.PureTyping.HasType env [] residual (applications motive (terms input.expressions)) := by
  have scrutinee := input.typed
  have arity : (terms input.expressions).length = family.entry.declaration.arity := (List.length_map _).trans input.code.size
  rw [Vectors.propositionAt,arity] at scrutinee
  have original : LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term) (applications motive (terms input.expressions)) :=
    .propElim family.found family.proposition motiveTyped branches scrutinee
  obtain ⟨constructor,values,shape⟩ := input.tree.head
  have canContract : LoanTyping.PureFamilyProofs.ConstructorHead (elimTerm id motive cases input.term) := by
    rw [shape]
    exact .elim id constructor motive cases values
  exact LoanTyping.PureFamilyProofs.contract_from_pure_typing history (.native original) canContract

theorem Fiber.semantic_elimination (family : Vectors.Family env id) (inhabited : Fiber id family.entry index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) (result : Code [] .proposition)
    (aligned : ∀ input : Realization family index, RawValue.Conv env (applications motive (terms input.expressions)) result.syntax)
    (covered : ∀ (input : Realization family index) residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨input⟩ := Fiber.reify family inhabited
  obtain ⟨residual,contracted,retained⟩ := input.elimination_contracts
    (ScopedProgram.History.ofPureMixed history) motiveTyped branches
  exact (covered input residual contracted).inhabits history retained (aligned input) assignment

theorem checked_global_eliminates {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Vectors.Family env id) (found : env.globals[index]? = some declaration)
    (source : declaration.value = elimTerm id motive cases scrutinee)
    (inhabited : Fiber id family.entry indices) (result : Code [] .proposition)
    (aligned : ∀ input : Realization family indices, RawValue.Conv env (applications motive (terms input.expressions)) result.syntax)
    (covered : ∀ (input : Realization family indices) residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  obtain ⟨motiveTyped,branches⟩ := Vectors.checked_cases (family := family) (history.global_value_and_reference found).1 source
  exact Fiber.semantic_elimination family inhabited history motiveTyped branches result aligned covered assignment

section Example

open LoanTyping.PureFamilyArithmeticReplay (observe? observed_fundamental)

private theorem pair_codes {α : Type} {valid : α → Prop} {first second : α}
    (left : valid first) (right : valid second) : ∀ x ∈ [first,second], valid x :=
  List.forall_mem_cons.mpr ⟨left,List.forall_mem_cons.mpr ⟨right,(by simp)⟩⟩

private theorem scalar_slot {previous : List Slot} {index : Nat}
    (typed : ScalarPrefixes.ScalarCode previous.length (.var index)) (selected : previous[index]? = some .scalar) :
    ScalarIndex previous (.var index) := by
  refine ⟨typed,?_⟩
  intro position included
  cases List.mem_singleton.mp included
  exact selected

private theorem literal_slot (previous : List Slot) (width : value < 2^64) : ScalarIndex previous (.literal value) :=
  ⟨.literal width,by simp [Expr.variables]⟩

private theorem add_slots (first : ScalarIndex previous left) (second : ScalarIndex previous right) :
    ScalarIndex previous (.add left right) := by
  refine ⟨.add first.1 second.1,?_⟩
  intro index included
  rcases List.mem_append.mp included with selected | selected
  · exact first.2 index selected
  · exact second.2 index selected

private def firstIndices : List Expr := [.var 0,.add (.var 0) (.literal 1)]
private def secondSum : Expr := .add (.var 0) (.var 2)
private def secondIndices : List Expr := [secondSum,.add secondSum (.literal 1)]
private def resultSum : Expr := .add (.add (.var 1) (.var 3)) (.var 3)
private def resultIndices : List Expr := [resultSum,.add resultSum (.literal 1)]

private theorem firstCode : IndexCode (ScalarIndex [.scalar]) 2 firstIndices := by
  have word : ScalarIndex [.scalar] (.var 0) := scalar_slot (.var .here) rfl
  exact ⟨rfl,pair_codes word (add_slots word (literal_slot _ (value := 1) (by decide)))⟩

private theorem secondCode : IndexCode (ScalarIndex [.scalar,.recursive,.scalar]) 2 secondIndices := by
  have recent : ScalarIndex [.scalar,.recursive,.scalar] (.var 0) := scalar_slot (.var .here) rfl
  have older : ScalarIndex [.scalar,.recursive,.scalar] (.var 2) := scalar_slot (.var (.there (.there .here))) rfl
  have sum := add_slots recent older
  exact ⟨rfl,pair_codes sum (add_slots sum (literal_slot _ (value := 1) (by decide)))⟩

private theorem resultCode : IndexCode (ScalarIndex [.recursive,.scalar,.recursive,.scalar]) 2 resultIndices := by
  have recent : ScalarIndex [.recursive,.scalar,.recursive,.scalar] (.var 1) := scalar_slot (.var (.there .here)) rfl
  have older : ScalarIndex [.recursive,.scalar,.recursive,.scalar] (.var 3) := scalar_slot (.var (.there (.there (.there .here)))) rfl
  have sum := add_slots (add_slots recent older) older
  exact ⟨rfl,pair_codes sum (add_slots sum (literal_slot _ (value := 1) (by decide)))⟩

private def branchScheme : Scheme 2 [] := .scalar (.recursive firstIndices firstCode
  (.scalar (.recursive secondIndices secondCode (.result resultIndices resultCode))))

private theorem baseCode (first second : Nat) (lo : first < 2^64) (hi : second < 2^64) :
    IndexCode (ScalarIndex []) 2 [.literal first,.literal second] := ⟨rfl,pair_codes (literal_slot [] lo) (literal_slot [] hi)⟩

private def leftBase : Scheme 2 [] := .result [.literal 1,.literal 2] (baseCode 1 2 (by decide) (by decide))
private def rightBase : Scheme 2 [] := .result [.literal 6,.literal 7] (baseCode 6 7 (by decide) (by decide))
private def signatures : List Signature := [leftBase.signature 0,rightBase.signature 0,branchScheme.signature 0]
private def declaration : FamilyDeclaration := ⟨false,0,2,signatures.map (signatureTerm 0),0⟩
private def checkedTable : CheckedFamily := ⟨declaration,signatures,false⟩

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def next (index : Term) : Term := .uadd index one
private def increasing (index : Term) : Term := .lt index (next index)
private def pairAt (index : Term) : Term := Vectors.propositionAt 0 [index,next index]
private def motive : Term := .lam false .u64 (.lam false .u64 (.lt (.var 1) (.var 0)))
private def baseEvidence (index : Term) : Term := .ltAdd zero one index (.zeroLe zero)
private def branchEvidence (first second previousFirst previousSecond : Term) : Term :=
  .ltLe (.uadd first second) (.uadd (next first) second) (.uadd (next first) second)
    (.ltAdd first (next first) second previousFirst)
    (.ltAdd second (next second) (next first) previousSecond)
private def branch : Term :=
  .lam false .u64 (.lam true (pairAt (.var 0)) (.lam false .u64
    (.lam true (pairAt (.uadd (.var 0) (.var 2))) (.lam true (increasing (.var 3))
      (.lam true (increasing (.uadd (.var 2) (.var 4)))
        (branchEvidence (.var 5) (.uadd (.var 3) (.var 5)) (.var 1) (.var 0)))))))
private def arms : List Term := [baseEvidence one,baseEvidence (.natural 6),branch]
private def leftChild : Term := .node (.con 0 0 0) []
private def rightChild : Term := .node (.con 0 1 0) []
private def secondArgument : Expr := .add (.literal 2) (.literal 3)
private def constructorProof : Term := .node (.con 0 2 4) [one,leftChild,secondArgument.toTerm,rightChild]
private def inputSource : GlobalDeclaration := ⟨Vectors.propositionAt 0 [.natural 7,.natural 8],constructorProof⟩
private def elimSource : GlobalDeclaration := ⟨.lt (.natural 7) (.natural 8),elimTerm 0 motive arms constructorProof⟩
private def world : Environment := ⟨#[inputSource,elimSource],#[checkedTable]⟩
private def family : Vectors.Family world 0 := ⟨checkedTable,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨56,56,56,18000⟩

private theorem exampleTree : ConstructorTree 0 checkedTable constructorProof := by
  refine .intro (fields := [one,leftChild,secondArgument.toTerm,rightChild]) (constructor := 2) branchScheme rfl ?_
  refine .scalar (.literal 1) (.recursive firstCode ?_ (.scalar secondArgument (.recursive secondCode ?_ (.result resultCode))))
  · refine .intro (fields := []) (constructor := 0) leftBase rfl ?_
    exact .result (baseCode 1 2 (by decide) (by decide))
  · refine .intro (fields := []) (constructor := 1) rightBase rfl ?_
    exact .result (baseCode 6 7 (by decide) (by decide))

/-- The second recursive domain reads both scalar fields across the first
proof binder. Checked elimination consumes both actual induction hypotheses. -/
theorem checked_interleaved_elimination :
    LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world ∧
    Nonempty (Realization family [7,8]) ∧
    observe? world [] 64 24 24 8192 10 elimSource.value =
      some (branchEvidence one (.uadd secondArgument.toTerm one) (baseEvidence one) (baseEvidence (.natural 6))) ∧
    PureArithmetic.UniversalTruth world elimSource.type := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world := by cbv
  have executed : observe? world [] 64 24 24 8192 10 elimSource.value =
      some (branchEvidence one (.uadd secondArgument.toTerm one) (baseEvidence one) (baseEvidence (.natural 6))) := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have inputTyped := (history.global_value_and_reference (index := 0) (declaration := inputSource) rfl).1
  have elimTyped := (history.global_value_and_reference (index := 1) (declaration := elimSource) rfl).1
  have inhabited := exampleTree.pure_sound (expected := [.literal 7,.literal 8]) history family inputTyped (.refl _)
  exact ⟨admitted,Fiber.reify family inhabited,executed,observed_fundamental history elimTyped executed⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.MixedFields
