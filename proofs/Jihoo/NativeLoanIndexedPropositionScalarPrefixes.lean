import Jihoo.NativeLoanIndexedPropositionVectors

/-! Native indexed proposition branches with an arbitrary scalar prefix. Each
scalar may be a checked closed affine term. All recursive and result indices
use the simultaneous substitution from the genuine constructor telescope. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.ScalarPrefixes

open AffineSum (Expr)
open LoanTyping.PureHypothesisObservation (ScalarExpr Entry context)
open LoanTyping.FamilyIota (arguments_pi_view fieldSubstitution fieldSubstitution_selected)
open Environment.FamilyIota (elimTerm)
open Vectors (IndexCode terms baseSignature recursiveTail shifted telescope proposition_subst pi_subst)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes (Code)

variable {id : Nat}

abbrev ScalarCode (count : Nat) (expression : Expr) : Prop := ScalarExpr (List.replicate count (.scalar false)) expression

private def valueAt (values : List Expr) (index : Nat) : Expr := values.reverse[index]?.getD (.literal 0)

def instantiateIndices (values indices : List Expr) : List Expr := indices.map (Expr.subst (valueAt values))

def interpretIndices (values indices : List Expr) : List Nat :=
  indices.map (Expr.eval (fun index => (valueAt values index).eval (fun _ => 0)))

theorem evaluate_instantiation (values indices : List Expr) :
    Vectors.evaluate 0 (instantiateIndices values indices) = interpretIndices values indices := by
  simp only [Vectors.evaluate,instantiateIndices,interpretIndices,List.map_map]
  apply List.map_congr_left
  intro expression _
  exact Expr.subst_eval _ _ _

/-- Literal bounds and the validity of every affine operand come from the
actual typing of the scalar argument. Its mathematical sum can be wide. -/
theorem checked_affine_argument (typed : LoanTyping.HasType env [] [] true expression.toTerm type) : Closed expression := by
  induction expression generalizing type with
  | var index =>
      obtain ⟨_,found,_⟩ := typed.principalView
      simp [NativeKernel.lookup] at found
  | literal value => exact .literal (natural_bound typed)
  | add left right ihLeft ihRight =>
      obtain ⟨first,second,_⟩ := typed.uadd_inputs
      exact .add (ihLeft first) (ihRight second)

/-- Peel every actual U64 argument, retaining the native `Arguments`
derivation for the recursive suffix under the simultaneous substitution. -/
theorem checked_scalar_prefix (wf : UnifiedProgram.EnvWellFormed env) (values : List Expr)
    (arguments : LoanTyping.Arguments env [] [] true data (u64Telescope values.length tail)
      (terms values ++ rest) type) :
    (∀ value ∈ values, Closed value) ∧
    LoanTyping.Arguments env [] [] true data (tail.subst (fieldSubstitution (terms values))) rest type := by
  induction values generalizing tail with
  | nil => simpa only [terms,List.map_nil,List.length_nil,List.nil_append,u64Telescope,fieldSubstitution,Term.subst_id] using
      And.intro (by intro x missing; simp at missing : ∀ value ∈ ([] : List Expr), Closed value) arguments
  | cons first values ih =>
      change LoanTyping.Arguments env [] [] true data (.pi false .u64 (u64Telescope values.length tail))
        (first.toTerm :: (terms values ++ rest)) type at arguments
      obtain ⟨typed,remaining⟩ := arguments_pi_view wf arguments
      have shifted := u64Telescope_subst values.length 0 tail (single first.toTerm)
      simp only [liftSub,Nat.zero_add] at shifted
      rw [shifted] at remaining
      obtain ⟨closed,finished⟩ := ih remaining
      rw [Term.subst_comp] at finished
      have size : (terms values).length = values.length := List.length_map _
      rw [← size] at finished
      refine ⟨?_,finished⟩
      exact List.forall_mem_cons.mpr ⟨checked_affine_argument typed,closed⟩

private theorem build_scalar_prefix (values : List Expr) (closed : ∀ value ∈ values, Closed value)
    (suffix : LoanTyping.Arguments env [] [] true data (tail.subst (fieldSubstitution (terms values))) rest type) :
    LoanTyping.Arguments env [] [] true data (u64Telescope values.length tail) (terms values ++ rest) type := by
  induction values generalizing tail with
  | nil => simpa only [terms,List.map_nil,List.length_nil,List.nil_append,u64Telescope,fieldSubstitution,Term.subst_id] using suffix
  | cons first values ih =>
      change LoanTyping.Arguments env [] [] true data (.pi false .u64 (u64Telescope values.length tail))
        (first.toTerm :: (terms values ++ rest)) type
      refine .cons (.refl _) (closed first (by simp)).typed ?_
      change LoanTyping.Arguments env [] [] true data ((u64Telescope values.length tail).subst (single first.toTerm))
        (terms values ++ rest) type
      have shifted := u64Telescope_subst values.length 0 tail (single first.toTerm)
      simp only [liftSub,Nat.zero_add] at shifted
      rw [shifted]
      apply ih (fun value inside => closed value (by simp [inside]))
      rw [Term.subst_comp]
      have size : (terms values).length = values.length := List.length_map _
      rw [← size]
      exact suffix

private theorem valueAt_closed (closed : ∀ value ∈ values, Closed value) (index : Nat) : Closed (valueAt values index) := by
  unfold valueAt
  cases found : values.reverse[index]? with
  | none => exact .literal (by decide)
  | some value => exact closed value (List.mem_reverse.mp (List.mem_of_getElem? found))

private theorem fieldSubstitution_value (inside : index < values.length) :
    fieldSubstitution (terms values) index = (valueAt values index).toTerm := by
  let position := values.length - 1 - index
  have bound : position < values.length := by dsimp [position]; omega
  have selected : values[position]? = some values[position] := List.getElem?_eq_getElem bound
  have operand : (terms values)[position]? = some values[position].toTerm := by
    simp only [terms,List.getElem?_map,selected,Option.map_some]
  have computation := fieldSubstitution_selected operand
  have slot : (terms values).length - 1 - position = index := by
    simp only [terms,List.length_map,position]
    omega
  rw [slot] at computation
  unfold valueAt
  rw [List.getElem?_reverse (by simpa using inside)]
  change fieldSubstitution (terms values) index = ((values[position]?).getD (.literal 0)).toTerm
  rw [selected]
  exact computation

private theorem liftSub_closed (scope : (σ index).Scoped 0) (depth : Nat) :
    liftSub depth σ (index+depth) = σ index := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change (liftSub depth σ (index+depth)).rename Nat.succ = _
      rw [ih,Environment.closed_rename scope]

private theorem expression_instantiation (code : ScalarCode values.length expression)
    (closed : ∀ value ∈ values, Closed value) (depth : Nat) :
    (expression.toTerm.rename (fun x => x + depth)).subst (liftSub depth (fieldSubstitution (terms values))) =
      (expression.subst (valueAt values)).toTerm := by
  rw [Term.subst_rename,Expr.subst_toTerm]
  apply Environment.scoped_subst_congr code.scoped
  intro index bound
  have inside : index < values.length := by simpa only [context,List.length_map,List.length_replicate] using bound
  have selected := fieldSubstitution_value inside
  have scope : (fieldSubstitution (terms values) index).Scoped 0 := by
    rw [selected]
    exact (valueAt_closed closed index).scoped
  exact (liftSub_closed scope depth).trans selected

theorem expression_closed (valid : ScalarExpr entries expression) (closed : ∀ x, Closed (assignment x)) :
    Closed (expression.subst assignment) := by
  induction valid with
  | var slot => exact closed _
  | literal width => exact .literal width
  | add _ _ first second => exact .add first second

private theorem grounded_code (valid : IndexCode (ScalarCode values.length) arity indices)
    (closed : ∀ value ∈ values, Closed value) : IndexCode Closed arity (instantiateIndices values indices) := by
  refine ⟨(List.length_map _).trans valid.size,?_⟩
  intro expression found
  obtain ⟨original,included,rfl⟩ := List.mem_map.mp found
  exact expression_closed (valid.valid original included) (valueAt_closed closed)

private theorem grounded_codes {predecessors : List (List Expr)}
    (codes : ∀ indices ∈ predecessors, IndexCode (ScalarCode values.length) arity indices)
    (closed : ∀ value ∈ values, Closed value) :
    ∀ grounded ∈ predecessors.map (instantiateIndices values), IndexCode Closed arity grounded := by
  intro grounded member
  obtain ⟨indices,selected,rfl⟩ := List.mem_map.mp member
  exact grounded_code (codes indices selected) closed

def branchSignature (family count : Nat) (predecessors : List (List Expr)) (result : List Expr) : Signature :=
  let tail := recursiveTail family 0 predecessors result
  ⟨List.replicate count ⟨false,.u64,none⟩ ++ tail.fields,tail.result⟩

theorem signature_prefix (family count : Nat) (predecessors : List (List Expr)) (result : List Expr) :
    signatureTerm family (branchSignature family count predecessors result) =
      u64Telescope count (signatureTerm family (recursiveTail family 0 predecessors result)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [branchSignature,signatureTerm,List.replicate_succ,List.cons_append,List.foldr_cons,u64Telescope] using
        congrArg (Term.pi false .u64) ih

private theorem instantiate_terms {indices : List Expr} (valid : ∀ expression ∈ indices, ScalarCode values.length expression)
    (closed : ∀ value ∈ values, Closed value) (depth : Nat) :
    (shifted depth indices).map (Term.subst (liftSub depth (fieldSubstitution (terms values)))) = terms (instantiateIndices values indices) := by
  simp only [shifted,terms,instantiateIndices,List.map_map]
  apply List.map_congr_left
  intro expression member
  exact expression_instantiation (valid expression member) closed depth

/-- Simultaneous scalar substitution grounds every recursive domain and the
result of the native signature, retaining original field order. -/
theorem instantiate_telescope {predecessors : List (List Expr)}
    (codes : ∀ p ∈ predecessors, IndexCode (ScalarCode values.length) arity p)
    (resultCode : IndexCode (ScalarCode values.length) arity result) (closed : ∀ value ∈ values, Closed value) (depth : Nat) :
    (signatureTerm id (recursiveTail id depth predecessors result)).subst (liftSub depth (fieldSubstitution (terms values))) =
      telescope id (predecessors.map (instantiateIndices values)) (instantiateIndices values result) := by
  induction predecessors generalizing depth with
  | nil =>
      change (Vectors.propositionAt id (shifted depth result)).subst (liftSub depth (fieldSubstitution (terms values))) = _
      rw [proposition_subst,instantiate_terms resultCode.valid closed]
      rfl
  | cons predecessor rest ih =>
      rw [Vectors.signatureTail_cons,pi_subst]
      rw [show liftSubOne (liftSub depth (fieldSubstitution (terms values))) =
        liftSub (depth+1) (fieldSubstitution (terms values)) from rfl]
      rw [proposition_subst,instantiate_terms (codes predecessor (by simp)).valid closed,ih (fun p hp => codes p (by simp [hp]))]
      rfl

inductive Fiber (family : Nat) (entry : CheckedFamily) : List Nat → Prop where
  | base {constructor : Nat} (code : IndexCode Closed entry.declaration.arity result) :
      entry.signatures[constructor]? = some (baseSignature result) → Fiber family entry (Vectors.evaluate 0 result)
  | branch {values : List Expr} {predecessors : List (List Expr)} {constructor : Nat}
      (codes : ∀ p ∈ predecessors, IndexCode (ScalarCode values.length) entry.declaration.arity p)
      (resultCode : IndexCode (ScalarCode values.length) entry.declaration.arity result) :
      entry.signatures[constructor]? = some (branchSignature family values.length predecessors result) →
      (∀ value ∈ values, Closed value) →
      (∀ p ∈ predecessors, Fiber family entry (interpretIndices values p)) → Fiber family entry (interpretIndices values result)

def meaning (family : Vectors.Family env id) (index : List Nat) : Finite.Universe .proposition := .proposition (Fiber id family.entry index)

inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
  | base (code : IndexCode Closed entry.declaration.arity result) :
      entry.signatures[constructor]? = some (baseSignature result) →
      ConstructorTree family entry (.node (.con family constructor 0) [])
  | branch {values : List Expr} {predecessors : List (List Expr)} {constructor : Nat}
      (codes : ∀ p ∈ predecessors, IndexCode (ScalarCode values.length) entry.declaration.arity p)
      (resultCode : IndexCode (ScalarCode values.length) entry.declaration.arity result) :
      entry.signatures[constructor]? = some (branchSignature family values.length predecessors result) →
      children.length = predecessors.length → (∀ child ∈ children, ConstructorTree family entry child) →
      ConstructorTree family entry (.node (.con family constructor (terms values ++ children).length) (terms values ++ children))

theorem ConstructorTree.sound {expected : List Expr} (history : ScopedProgram.History definitions declarations env)
    (family : Vectors.Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.HasType env [] [] true term type)
    (requested : RawValue.Conv env type (Vectors.propositionAt id (terms expected))) :
    Fiber id family.entry (Vectors.evaluate 0 expected) := by
  let wf := history.wellFormed
  induction tree generalizing type expected with
  | @base result constructor code found =>
      obtain ⟨_,_,arguments,converted⟩ := Vectors.constructor_arguments history family found typed
      cases arguments with
      | nil resultType =>
          have aligned := Vectors.index_conversion (scalar := 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
          rw [← aligned]
          exact .base code found
  | @branch result children values predecessors constructor codes resultCode found size _ ih =>
      obtain ⟨_,_,arguments,converted⟩ := Vectors.constructor_arguments history family found typed
      rw [signature_prefix] at arguments
      obtain ⟨closed,remainder⟩ := checked_scalar_prefix wf values arguments
      change LoanTyping.Arguments env [] [] true family.entry.declaration.data
        ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (fieldSubstitution (terms values))))
        children _ at remainder
      rw [instantiate_telescope codes resultCode closed] at remainder
      obtain ⟨resultType,fields⟩ := Vectors.tail_arguments wf (grounded_codes codes closed) (grounded_code resultCode closed)
        (size.trans (List.length_map _).symm) remainder
      have aligned := Vectors.index_conversion (scalar := 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
      rw [← aligned,evaluate_instantiation]
      refine .branch codes resultCode found closed ?_
      intro predecessor included
      obtain ⟨position,selected⟩ := List.mem_iff_getElem?.mp included
      obtain ⟨child,childFound,childTyped⟩ := fields (position := position) (p := instantiateIndices values predecessor)
        (by simp only [List.getElem?_map,selected,Option.map_some])
      rw [← evaluate_instantiation values predecessor]
      exact ih child (List.mem_of_getElem? childFound) childTyped (.refl _)

private theorem ConstructorTree.head (tree : ConstructorTree id entry term) :
    ∃ constructor values, term = .node (.con id constructor values.length) values := by
  cases tree with
  | base => exact ⟨_,[],rfl⟩
  | branch => exact ⟨_,_,rfl⟩

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

/-- Realize every field at exactly its affine-substituted vector, then
rebuild the original scalar prefix with the same checked argument types. -/
theorem Fiber.reify (family : Vectors.Family env id) (inhabited : Fiber id family.entry index) : Nonempty (Realization family index) := by
  induction inhabited with
  | @base result constructor code found =>
      exact ⟨⟨result,code,rfl,.node (.con id constructor 0) [],.base code found,
        Vectors.constructor_typed family found (.nil (.refl _))⟩⟩
  | @branch result values predecessors constructor codes resultCode found closed _ ih =>
      have resultClosed := grounded_code resultCode closed
      have realized : ∀ grounded ∈ predecessors.map (instantiateIndices values), ∃ child,
          ConstructorTree id family.entry child ∧ LoanTyping.HasType env [] [] true child (Vectors.propositionAt id (terms grounded)) := by
        intro grounded included
        obtain ⟨predecessor,member,rfl⟩ := List.mem_map.mp included
        obtain ⟨child⟩ := ih predecessor member
        have alignment := Vectors.closed_index_conversion (env := env) (id := id) child.code
          (grounded_code (codes predecessor member) closed) (child.evaluated.trans (evaluate_instantiation values predecessor).symm)
        exact ⟨child.term,child.tree,.convert child.typed alignment⟩
      obtain ⟨children,size,trees,arguments⟩ := Vectors.build_tail (family := family) (grounded_codes codes closed) resultClosed realized
      let fields := terms values ++ children
      have native : LoanTyping.Arguments env [] [] true family.entry.declaration.data
          (signatureTerm id (branchSignature id values.length predecessors result)) fields
          (Vectors.propositionAt id (terms (instantiateIndices values result))) := by
        rw [signature_prefix]
        apply build_scalar_prefix values closed
        change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (fieldSubstitution (terms values)))) children _
        rw [instantiate_telescope codes resultCode closed]
        exact arguments
      exact ⟨⟨instantiateIndices values result,resultClosed,evaluate_instantiation values result,
        .node (.con id constructor fields.length) fields,
        .branch codes resultCode found (size.trans (List.length_map _)) trees,Vectors.constructor_typed family found native⟩⟩

theorem Realization.elimination_typed {family : Vectors.Family env id} (input : Realization family index)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term) (applications motive (terms input.expressions)) := by
  have scrutinee := input.typed
  have arity : (terms input.expressions).length = family.entry.declaration.arity := (List.length_map _).trans input.code.size
  rw [Vectors.propositionAt,arity] at scrutinee
  exact .propElim family.found family.proposition motiveTyped branches scrutinee

theorem Realization.elimination_contracts {family : Vectors.Family env id} (input : Realization family index)
    (history : ScopedProgram.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    ∃ residual, Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual ∧
      LoanTyping.PureTyping.HasType env [] residual (applications motive (terms input.expressions)) := by
  obtain ⟨constructor,values,shape⟩ := input.tree.head
  have canContract : LoanTyping.PureFamilyProofs.ConstructorHead (elimTerm id motive cases input.term) := by
    rw [shape]
    exact .elim id constructor motive cases values
  exact LoanTyping.PureFamilyProofs.contract_from_pure_typing history (.native (input.elimination_typed motiveTyped branches)) canContract

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

private def x : Expr := .var 1
private def y : Expr := .var 0
private def leftIndices : List Expr := [x,.add x (.literal 1)]
private def rightIndices : List Expr := [y,.add y (.literal 1)]
private def resultIndices : List Expr := [.add y x,.add (.add y x) (.literal 1)]
private def leftBase : List Expr := [.literal 1,.literal 2]
private def rightBase : List Expr := [.literal 5,.literal 6]
private def branching : Signature := branchSignature 0 2 [leftIndices,rightIndices] resultIndices
private def declaration : FamilyDeclaration := ⟨false,0,2,
  [Vectors.propositionAt 0 (terms leftBase),Vectors.propositionAt 0 (terms rightBase),signatureTerm 0 branching],0⟩
private def checkedTable : CheckedFamily := ⟨declaration,[baseSignature leftBase,baseSignature rightBase,branching],false⟩
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def next (index : Term) : Term := .uadd index one
private def increasing (index : Term) : Term := .lt index (next index)
private def motive : Term := .lam false .u64 (.lam false .u64 (.lt (.var 1) (.var 0)))
private def baseEvidence (index : Term) : Term := .ltAdd zero one index (.zeroLe zero)
private def branchEvidence (first second previousFirst previousSecond : Term) : Term :=
  .ltLe (.uadd first second) (.uadd (next first) second) (.uadd (next first) second)
    (.ltAdd first (next first) second previousFirst)
    (.ltAdd second (next second) (next first) previousSecond)
private def branch : Term := .lam false .u64 (.lam false .u64
  (.lam true (Vectors.propositionAt 0 [.var 1,next (.var 1)])
    (.lam true (Vectors.propositionAt 0 [.var 1,next (.var 1)])
      (.lam true (increasing (.var 3))
        (.lam true (increasing (.var 3)) (branchEvidence (.var 5) (.var 4) (.var 1) (.var 0)))))))
private def arms : List Term := [baseEvidence one,baseEvidence (.natural 5),branch]
private def scalarArguments : List Expr := [.literal 1,.add (.literal 2) (.literal 3)]
private def leftChild : Term := .node (.con 0 0 0) []
private def rightChild : Term := .node (.con 0 1 0) []
private def constructorProof : Term := .node (.con 0 2 4) (terms scalarArguments ++ [leftChild,rightChild])
private def inputSource : GlobalDeclaration := ⟨Vectors.propositionAt 0 [.natural 6,.natural 7],constructorProof⟩
private def elimSource : GlobalDeclaration := ⟨.lt (.natural 6) (.natural 7),elimTerm 0 motive arms constructorProof⟩
private def world : Environment := ⟨#[inputSource,elimSource],#[checkedTable]⟩
private def family : Vectors.Family world 0 := ⟨checkedTable,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨56,56,56,18000⟩

private theorem pair_codes {α : Type} {valid : α → Prop} {first second : α}
    (left : valid first) (right : valid second) : ∀ x ∈ [first,second], valid x :=
  List.forall_mem_cons.mpr ⟨left,List.forall_mem_cons.mpr ⟨right,(by simp)⟩⟩

private theorem x_code : ScalarCode 2 x := .var (.there .here)
private theorem y_code : ScalarCode 2 y := .var .here
private theorem one_code : ScalarCode 2 (.literal 1) := .literal (by decide)

private theorem predecessorCodes : ∀ p ∈ [leftIndices,rightIndices], IndexCode (ScalarCode 2) 2 p :=
  pair_codes ⟨rfl,pair_codes x_code (.add x_code one_code)⟩ ⟨rfl,pair_codes y_code (.add y_code one_code)⟩

private theorem literalCode (first second : Nat) (lo : first < 2^64) (hi : second < 2^64) :
    IndexCode Closed 2 [.literal first,.literal second] := ⟨rfl,pair_codes (.literal lo) (.literal hi)⟩

private theorem exampleTree : ConstructorTree 0 checkedTable constructorProof := by
  refine .branch (result := resultIndices) (values := scalarArguments) (children := [leftChild,rightChild]) (constructor := 2)
    predecessorCodes ⟨rfl,pair_codes (.add y_code x_code) (.add (.add y_code x_code) one_code)⟩ rfl rfl ?_
  exact pair_codes (.base (result := leftBase) (constructor := 0) (literalCode 1 2 (by decide) (by decide)) rfl)
    (.base (result := rightBase) (constructor := 1) (literalCode 5 6 (by decide) (by decide)) rfl)

/-- The checked constructor uses two scalars, including a source UAdd, to
build distinct recursive fields. Both induction hypotheses are observed in
the checked source elimination and its arithmetic result is interpreted. -/
theorem checked_two_scalar_elimination :
    LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world ∧
    Nonempty (Realization family [6,7]) ∧
    observe? world [] 64 24 24 8192 10 elimSource.value =
      some (branchEvidence one (.uadd (.natural 2) (.natural 3)) (baseEvidence one) (baseEvidence (.natural 5))) ∧
    PureArithmetic.UniversalTruth world elimSource.type := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world := by cbv
  have executed : observe? world [] 64 24 24 8192 10 elimSource.value =
      some (branchEvidence one (.uadd (.natural 2) (.natural 3)) (baseEvidence one) (baseEvidence (.natural 5))) := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have inputTyped := (history.global_value_and_reference (index := 0) (declaration := inputSource) rfl).1
  have elimTyped := (history.global_value_and_reference (index := 1) (declaration := elimSource) rfl).1
  have inhabited := exampleTree.pure_sound (expected := [.literal 6,.literal 7]) history family inputTyped (.refl _)
  exact ⟨admitted,Fiber.reify family inhabited,executed,observed_fundamental history elimTyped executed⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.ScalarPrefixes
