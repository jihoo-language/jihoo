import Jihoo.NativeLoanIndexedPropositionModel
import Jihoo.NativeLoanFamilyIotaElimTyping

set_option maxUniverseOffset 40

/-! Reify inhabitants of the checked indexed proposition carrier into typed
constructor syntax. Actual checked proposition Elim can then use any such
inhabitant with its existing dependent branch vector. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Elimination

open AffineSum (Expr)
open LoanTyping.FamilyIota (fieldSubstitution)
open LoanTyping.PureHypothesisObservation (Entry ScalarExpr)
open Environment.FamilyIota (elimTerm)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes (Code)
variable {id : Nat}

theorem specialize_closed (code : Unary expression) (width : value < 2^64) : Closed (specialize expression value) := by
  induction code with
  | var slot => exact .literal width
  | literal bound => exact .literal bound
  | add _ _ left right => exact .add left right

private theorem affine_ones (valid : Closed expression) : ACU.Conv expression.toTerm
    (ACU.sumTerms (List.replicate (expression.eval (fun _ => 0)) (.natural 1))) := by
  induction valid with
  | var slot => cases slot
  | literal bound => exact ACU.Conv.literal_ones _ bound
  | add _ _ left right =>
      simp only [Expr.toTerm,Expr.eval,← List.replicate_append_replicate]
      exact (ACU.Conv.addCong left right).trans (ACU.Conv.sumTerms_append _ _)

/-- Closed affine indices agree by a real kernel equation, even when the
mathematical sum cannot itself be written as a machine literal. -/
theorem closed_affine_conversion (left : Closed first) (right : Closed second)
    (same : first.eval (fun _ => 0) = second.eval (fun _ => 0)) : RawLend.Conv env first.toTerm second.toTerm := by
  have firstConversion := affine_ones left
  rw [same] at firstConversion
  exact .old (.acu (firstConversion.trans (affine_ones right).symm))

private theorem proposition_subst (family : Nat) (index : Term) (σ : Nat → Term) :
    (propositionAt family index).subst σ = propositionAt family (index.subst σ) := by
  simp only [propositionAt,Term.subst,substArgs,Op.binders,liftSub]

private theorem double_subst (term : Term) (first second : Term) :
    (term.subst (liftSubOne (single first))).subst (single second) =
      term.subst (fieldSubstitution [first,second]) := by
  rw [Term.subst_comp]
  congr 1
  funext index
  simp only [fieldSubstitution,List.length_cons,List.length_nil,liftSub,Term.subst_id]

theorem constructor_typed (family : Family env id) {constructor : Nat}
    (selected : family.entry.signatures[constructor]? = some signature)
    (arguments : LoanTyping.Arguments env [] [] true family.entry.declaration.data (signatureTerm id signature) fields
      (propositionAt id index)) :
    LoanTyping.HasType env [] [] true (.node (.con id constructor fields.length) fields) (propositionAt id index) := by
  apply LoanTyping.HasType.con family.found selected rfl
  change LoanTyping.Arguments env [] [] true family.entry.declaration.data
    ((signatureTerm id signature).rename _root_.id) fields (propositionAt id index)
  rw [Term.rename_id]
  exact arguments

private theorem scalar_arguments (resultCode : Unary result) (width : value < 2^64) :
    LoanTyping.Arguments env [] [] true data (signatureTerm id (scalarSignature result)) [.natural value]
      (propositionAt id (specialize result value).toTerm) := by
  change LoanTyping.Arguments env [] [] true data (.pi false .u64 (propositionAt id result.toTerm)) [.natural value] _
  refine .cons (.refl _) (.natural width) (.nil ?_)
  rw [proposition_subst,specialize_single resultCode]
  exact .refl _

private theorem recursive_arguments (predecessorCode : Unary predecessor) (resultCode : Unary result)
    (width : value < 2^64) (child : LoanTyping.HasType env [] [] true term (propositionAt id (specialize predecessor value).toTerm)) :
    LoanTyping.Arguments env [] [] true data (signatureTerm id (recursiveSignature id predecessor result)) [.natural value,term]
      (propositionAt id (specialize result value).toTerm) := by
  change LoanTyping.Arguments env [] [] true data (.pi false .u64
    (.pi true (propositionAt id predecessor.toTerm) (propositionAt id (result.toTerm.rename Nat.succ)))) _ _
  refine .cons (.refl _) (.natural width) ?_
  have stepped : (Term.pi true (propositionAt id predecessor.toTerm)
      (propositionAt id (result.toTerm.rename Nat.succ))).subst (single (.natural value)) =
      .pi true (propositionAt id (specialize predecessor value).toTerm)
        ((propositionAt id (result.toTerm.rename Nat.succ)).subst (liftSubOne (single (.natural value)))) := by
    simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub,propositionAt,specialize_single predecessorCode]
  change LoanTyping.Arguments env [] [] true data
    ((Term.pi true (propositionAt id predecessor.toTerm) (propositionAt id (result.toTerm.rename Nat.succ))).subst
      (single (.natural value))) [term] _
  rw [stepped]
  refine .cons (.refl _) child (.nil ?_)
  change RawLend.Conv env
    (((propositionAt id (result.toTerm.rename Nat.succ)).subst (liftSubOne (single (.natural value)))).subst
      (single term)) _
  rw [double_subst,proposition_subst,specialize_fields resultCode]
  exact .refl _

structure Realization (family : Family env id) (index : Nat) where
  expression : Expr
  closed : Closed expression
  evaluated : expression.eval (fun _ => 0) = index
  term : Term
  tree : ConstructorTree id family.entry term
  typed : LoanTyping.HasType env [] [] true term (propositionAt id expression.toTerm)

/-- The least carrier is realized by genuine native constructor proofs.
Recursive source fields are reconstructed at their exact checked index. -/
theorem Fiber.reify (family : Family env id) (inhabited : Fiber id family.entry index) :
    Nonempty (Realization family index) := by
  induction inhabited with
  | @nullary result constructor valid found =>
      refine ⟨⟨result,valid,rfl,.node (.con id constructor 0) [],.nullary valid found,?_⟩⟩
      exact constructor_typed family found (.nil (.refl _))
  | @scalar result constructor value valid found width =>
      refine ⟨⟨specialize result value,specialize_closed valid width,specialize_eval result value,
        .node (.con id constructor 1) [.natural value],.scalar valid found,?_⟩⟩
      exact constructor_typed family found (scalar_arguments valid width)
  | @recursive predecessor result constructor value predecessorCode resultCode found width _ previous =>
      obtain ⟨child⟩ := previous
      have predecessorClosed := specialize_closed predecessorCode width
      have aligned := closed_affine_conversion (env := env) child.closed predecessorClosed
        (child.evaluated.trans (specialize_eval predecessor value).symm)
      have nativeChild : LoanTyping.HasType env [] [] true child.term (propositionAt id (specialize predecessor value).toTerm) :=
        .convert child.typed (RawLend.Conv.node (.ind id 1) (.cons aligned .nil))
      refine ⟨⟨specialize result value,specialize_closed resultCode width,specialize_eval result value,
        .node (.con id constructor 2) [.natural value,child.term],.recursive predecessorCode resultCode found child.tree,?_⟩⟩
      exact constructor_typed family found (recursive_arguments predecessorCode resultCode width nativeChild)

theorem Realization.elimination_typed {family : Family env id} (input : Realization family index)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term) (.app motive input.expression.toTerm) := by
  have actualMotive : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity) := by
    rw [family.unary]
    exact motiveTyped
  have actualInput : LoanTyping.HasType env [] [] true input.term
      (.node (.ind id family.entry.declaration.arity) [input.expression.toTerm]) := by
    rw [family.unary]
    exact input.typed
  exact .propElim family.found family.proposition actualMotive branches actualInput

/-- Every semantic inhabitant can be passed through the original native
proposition eliminator with its actual checked motive and branch vector. -/
theorem Fiber.checked_elimination (family : Family env id) (inhabited : Fiber id family.entry index)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    ∃ input : Realization family index, LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term)
      (.app motive input.expression.toTerm) := by
  obtain ⟨input⟩ := Fiber.reify family inhabited
  exact ⟨input,input.elimination_typed motiveTyped branches⟩

/-- Constructor-backed elimination selects its actual branch without a
caller-provided reduction result or post-contraction typing proof. -/
theorem Realization.elimination_contracts {family : Family env id} (input : Realization family index)
    (history : ScopedProgram.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    ∃ residual, Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual ∧
      LoanTyping.PureTyping.HasType env [] residual (.app motive input.expression.toTerm) := by
  have shape : LoanTyping.PureFamilyProofs.ConstructorHead (elimTerm id motive cases input.term) := by
    obtain ⟨_,_,_,_,tree,_⟩ := input
    cases tree with
    | nullary => exact .elim id _ motive cases []
    | scalar => exact .elim id _ motive cases [.natural _]
    | recursive => exact .elim id _ motive cases [.natural _,_]
  exact LoanTyping.PureFamilyProofs.contract_from_pure_typing history (.native (input.elimination_typed motiveTyped branches)) shape

/-- The branch vector and motive are recovered from an actual typed Elim,
including when the stored type used expanded pure conversion. -/
theorem checked_cases {family : Family env id}
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (source : term = elimTerm id motive cases scrutinee) :
    LoanTyping.HasType env [] ctx true motive (propMotiveType 1) ∧
      LoanTyping.Cases env [] ctx motive family.entry.signatures cases := by
  induction typed with
  | native native =>
      rw [source] at native
      obtain ⟨entry,actualMotive,actualCases,_,_,_,layout,found,classified⟩ := LoanTyping.FamilyIota.elim_inputs native
      have same := Option.some.inj (family.found.symm.trans found)
      subst entry
      obtain ⟨motives,rest⟩ := List.cons.inj layout
      subst actualMotive
      obtain ⟨arms,_⟩ := List.append_inj' rest (by simp)
      subst actualCases
      rcases classified with ⟨_,motiveTyped,branches,_,_⟩ | ⟨data,_⟩
      · rw [family.unary] at motiveTyped
        exact ⟨motiveTyped,branches⟩
      · rw [family.proposition] at data
        contradiction
  | convert _ _ _ ih => exact ih source
  | pi | lam | app => cases source

/-- Interpretation is uniform over supported proposition codes. The only
replay premise describes the syntax of the actual selected branch and its
finite reentry. Native typing supplies all argument and output derivations. -/
theorem Realization.semantic_elimination {family : Family env id} (input : Realization family index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases)
    (result : Code [] .proposition)
    (aligned : RawValue.Conv env (.app motive input.expression.toTerm) result.syntax)
    (covered : ∀ residual, Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨residual,ran,typed⟩ := input.elimination_contracts (ScopedProgram.History.ofPureMixed history) motiveTyped branches
  exact (covered residual ran).inhabits history typed aligned assignment

theorem Fiber.semantic_elimination (family : Family env id) (inhabited : Fiber id family.entry index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases)
    (result : Code [] .proposition)
    (aligned : ∀ input : Realization family index, RawValue.Conv env (.app motive input.expression.toTerm) result.syntax)
    (covered : ∀ (input : Realization family index) residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨input⟩ := Fiber.reify family inhabited
  exact input.semantic_elimination history motiveTyped branches result (aligned input) (covered input) assignment

/-- Exact-byte admission supplies the elimination derivation for every
supported proposition result whose motive and selected replay align. -/
theorem checked_global_eliminates {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (source : declaration.value = elimTerm id motive cases scrutinee)
    (inhabited : Fiber id family.entry n) (result : Code [] .proposition)
    (aligned : ∀ input : Realization family n, RawValue.Conv env (.app motive input.expression.toTerm) result.syntax)
    (covered : ∀ (input : Realization family n) residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := family) (history.global_value_and_reference found).1 source
  exact Fiber.semantic_elimination family inhabited history motiveTyped branches result aligned covered assignment

inductive AffineMotive where
  | less : Unary left → Unary right → AffineMotive
  | equal : Unary left → Unary right → AffineMotive

def AffineMotive.syntax : AffineMotive → Term
  | .less (left := left) (right := right) _ _ => .lam false .u64 (.lt left.toTerm right.toTerm)
  | .equal (left := left) (right := right) _ _ => .lam false .u64 (.eq left.toTerm right.toTerm)

def AffineMotive.Holds : AffineMotive → Nat → Prop
  | .less (left := left) (right := right) _ _, n => left.eval (fun _ => n) < right.eval (fun _ => n)
  | .equal (left := left) (right := right) _ _, n => left.eval (fun _ => n) = right.eval (fun _ => n)

private theorem compose_closed (shape : Unary expression) (closed : Closed argument) :
    Closed (expression.subst (fun _ => argument)) := by
  induction shape with
  | var _ => exact closed
  | literal width => exact .literal width
  | add _ _ left right => exact .add left right

private theorem compose_subst (shape : Unary expression) (argument : Expr) :
    (expression.subst (fun _ => argument)).toTerm = expression.toTerm.subst (single argument.toTerm) := by
  rw [Expr.subst_toTerm]
  apply Environment.scoped_subst_congr shape.scoped
  intro index bound
  change index < 1 at bound
  have zero : index = 0 := by omega
  subst index
  rfl

def AffineMotive.instantiate (motive : AffineMotive) (closed : Closed argument) : Code [] .proposition :=
  match motive with
  | .less left right => .less (compose_closed left closed) (compose_closed right closed)
  | .equal left right => .equal (compose_closed left closed) (compose_closed right closed)

theorem AffineMotive.instantiate_conversion (motive : AffineMotive) (closed : Closed argument) :
    RawValue.Conv env (.app motive.syntax argument.toTerm) (motive.instantiate closed).syntax := by
  cases motive with
  | less left right | equal left right =>
      refine (RawValue.Conv.old (.old (.legacy (.beta false .u64 _ _)))).trans ?_
      simp only [AffineMotive.instantiate,MultiUniverse.DependentCodes.Code.syntax,Term.lt,Term.eq,
        Term.subst,substArgs,Op.binders,liftSub,compose_subst left,compose_subst right]
      exact .refl _

theorem AffineMotive.instantiate_truth (motive : AffineMotive) (closed : Closed argument)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Finite.decodeProp ((motive.instantiate closed).meaning assignment) ↔
      motive.Holds (argument.eval (fun _ => 0)) := by
  cases motive <;> simp [AffineMotive.instantiate,MultiUniverse.DependentCodes.Code.meaning,
    Finite.decodeProp,Expr.subst_eval,AffineMotive.Holds]

theorem Realization.eliminates_affine {family : Family env id} (input : Realization family index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motive : AffineMotive) (motiveTyped : LoanTyping.HasType env [] [] true motive.syntax (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive.syntax family.entry.signatures cases)
    (covered : ∀ residual, Environment.FamilyIota.contract env (elimTerm id motive.syntax cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual (motive.instantiate input.closed)) :
    motive.Holds index := by
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  obtain ⟨residual,ran,typed⟩ := input.elimination_contracts (ScopedProgram.History.ofPureMixed history) motiveTyped branches
  have meaning := (covered residual ran).truth history typed (motive.instantiate_conversion input.closed) assignment
  have evaluated := (motive.instantiate_truth input.closed assignment).mp meaning
  rwa [input.evaluated] at evaluated

/-- Exact byte admission supplies the original native motive and all branch
derivations. Elimination holds at the interpreted index of every carrier
element for which the actual branch replay has the supported syntax. -/
theorem checked_global_eliminates_affine {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (motive : AffineMotive) (source : declaration.value = elimTerm id motive.syntax cases scrutinee)
    (inhabited : Fiber id family.entry n)
    (covered : ∀ (input : Realization family n) residual,
      Environment.FamilyIota.contract env (elimTerm id motive.syntax cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual (motive.instantiate input.closed)) :
    motive.Holds n := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := family) (history.global_value_and_reference found).1 source
  obtain ⟨input⟩ := Fiber.reify family inhabited
  exact input.eliminates_affine history motive motiveTyped branches (covered input)

section Example

private def indexedBase : Expr := .literal 0
private def indexedPredecessor : Expr := .var 0
private def indexedResult : Expr := .add indexedPredecessor (.literal 2)
private def evenSource : FamilyDeclaration :=
  ⟨false,0,1,[propositionAt 0 (.natural 0),.pi false .u64
    (.pi true (propositionAt 0 (.var 0)) (propositionAt 0 (.uadd (.var 1) (.natural 2))))],0⟩
private def evenStep : Signature := recursiveSignature 0 indexedPredecessor indexedResult
private def evenTable : CheckedFamily := ⟨evenSource,[nullarySignature indexedBase,evenStep],false⟩
private def positiveAt (index : Term) : Term := .lt (.natural 0) (.uadd index (.natural 1))
private def positiveMotive : AffineMotive := .less (left := .literal 0) (right := .add (.var 0) (.literal 1))
  (.literal (by decide)) (.add (.var .here) (.literal (by decide)))
private def positiveBranch : Term := .lam false .u64 (.lam true (propositionAt 0 (.var 0))
  (.lam true (positiveAt (.var 1)) (.zeroLe (.uadd (.var 2) (.natural 2)))))
private def positiveBranches : List Term := [.zeroLe (.natural 0),positiveBranch]
private def evenFields : List Term := [.natural 0,.node (.con 0 0 0) []]
private def evenTerm : Term := .node (.con 0 1 2) evenFields
private def source : GlobalDeclaration :=
  ⟨positiveAt (.natural 2),elimTerm 0 positiveMotive.syntax positiveBranches evenTerm⟩
private def world : Environment := ⟨#[source],#[evenTable]⟩
private def evenFamily : Family world 0 := ⟨evenTable,rfl,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨40,40,40,12000⟩
private def selected : Term :=
  Environment.FamilyIota.elimBody evenTable evenStep 0 positiveMotive.syntax positiveBranch positiveBranches evenFields

/-- The mixed checker accepts a recursive indexed elimination at two with a
different proposition at the recursive index zero. The actual selected
branch produces an inhabitant of the interpreted motive at two. -/
theorem checked_index_varying_elimination :
    LoanTyping.PureMixedAdmission.checkProgram limits [source] [evenSource] = some world ∧
    positiveMotive.Holds 2 := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [source] [evenSource] = some world := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  let typed := (history.global_value_and_reference (index := 0) (declaration := source) rfl).1
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := evenFamily) typed rfl
  let realized : Realization evenFamily 2 :=
    ⟨.literal 2,.literal (by decide),rfl,evenTerm,
      .recursive (.var .here) (.add (.var .here) (.literal (by decide))) rfl (.nullary (.literal (by decide)) rfl),
      LoanTyping.Checker.check_sound (fuel := 40) (by cbv)⟩
  refine ⟨admitted,realized.eliminates_affine history positiveMotive motiveTyped branches ?_⟩
  intro residual ran
  have chosen : Environment.FamilyIota.contract world source.value = some selected := by cbv
  change Environment.FamilyIota.contract world source.value = some residual at ran
  rw [chosen] at ran
  cases ran
  apply MultiUniverse.DependentCodes.FamilyProofs.Tree.headReplay 64 64 64
  have replayed : LoanTyping.PureFamilyProofs.replay world (MultiUniverse.parameterContext []) 64 64 64 selected =
      .zeroLe (.uadd (.natural 0) (.natural 2)) := by cbv
  rw [replayed]
  exact .known (.known (.less (.literal (by decide)) (.add (.literal (by decide)) (.literal (by decide)))
    (.arithmetic ((LoanTyping.ProofObservation.supported_iff _).mp (by cbv)))))

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Elimination
