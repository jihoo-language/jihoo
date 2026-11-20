import Jihoo.NativeLoanPureFamilyProofs
import Jihoo.NativeLoanFamilyIotaViewHypotheses

set_option maxUniverseOffset 40

/-! A concrete least carrier for a checked class of native Ind propositions.
Constructor indices are mathematical affine values. The recursive family
field contributes an inhabitant of its actual preceding index. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition

open AffineSum (Expr)
open LoanTyping.PureHypothesisObservation (ScalarExpr Entry)
open LoanTyping.FamilyIota (fieldSubstitution fieldSubstitution_snoc
  arguments_pi_view constructor_result_conversion signature_metadata)
open ValueErasure.Loan (project project_variable project_ordinary_node)
variable {id : Nat}

abbrev Closed (code : Expr) : Prop := ScalarExpr [] code
abbrev Unary (code : Expr) : Prop := ScalarExpr [Entry.scalar false] code

def propositionAt (family : Nat) (index : Term) : Term := .node (.ind family 1) [index]

def nullarySignature (result : Expr) : Signature := ⟨[],[result.toTerm]⟩
def scalarSignature (result : Expr) : Signature := ⟨[⟨false,.u64,none⟩],[result.toTerm]⟩
def recursiveSignature (family : Nat) (predecessor result : Expr) : Signature :=
  ⟨[⟨false,.u64,none⟩,⟨true,propositionAt family predecessor.toTerm,some [predecessor.toTerm]⟩],
    [result.toTerm.rename Nat.succ]⟩

structure Family (env : Environment) (index : Nat) where
  entry : CheckedFamily
  found : env.families[index]? = some entry
  proposition : entry.declaration.data = false
  unary : entry.declaration.arity = 1

/-- Only actual entries in the constructor table contribute constructors
to the semantic carrier. A recursive constructor requires a prior carrier
element at its evaluated predecessor. -/
inductive Fiber (family : Nat) (entry : CheckedFamily) : Nat → Prop where
  | nullary {constructor : Nat} (closed : Closed result) : entry.signatures[constructor]? = some (nullarySignature result) →
      Fiber family entry (result.eval (fun _ => 0))
  | scalar {constructor value : Nat} (resultCode : Unary result) : entry.signatures[constructor]? = some (scalarSignature result) →
      value < 2^64 → Fiber family entry (result.eval (fun _ => value))
  | recursive {constructor value : Nat} (predecessorCode : Unary predecessor) (resultCode : Unary result) :
      entry.signatures[constructor]? = some (recursiveSignature family predecessor result) → value < 2^64 →
      Fiber family entry (predecessor.eval (fun _ => value)) → Fiber family entry (result.eval (fun _ => value))

def Family.meaning (family : Family env id) (index : Nat) : Finite.Universe .proposition :=
  .proposition (Fiber id family.entry index)

theorem Family.index_formed {expression : Expr} (family : Family env id) (valid : Closed expression) :
    LoanTyping.HasType env [] [] true (propositionAt id expression.toTerm) .prop := by
  have formed : LoanTyping.HasType env [] [] true (propositionAt id expression.toTerm)
      (if family.entry.declaration.data then .univ 0 else .prop) := by
    refine .ind family.found family.unary.symm rfl ?_
    intro term included
    cases List.mem_singleton.mp included
    exact valid.typed
  simpa [family.proposition] using formed

/-- Recognition checks source shape and the actual constructor scheme. For
a recursive field it requires a smaller source constructor tree, with no
semantic witness or derived child type attached. -/
inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
  | nullary (closed : Closed result) : entry.signatures[constructor]? = some (nullarySignature result) →
      ConstructorTree family entry (.node (.con family constructor 0) [])
  | scalar (resultCode : Unary result) : entry.signatures[constructor]? = some (scalarSignature result) →
      ConstructorTree family entry (.node (.con family constructor 1) [.natural value])
  | recursive (predecessorCode : Unary predecessor) (resultCode : Unary result) :
      entry.signatures[constructor]? = some (recursiveSignature family predecessor result) →
      ConstructorTree family entry child →
      ConstructorTree family entry (.node (.con family constructor 2) [.natural value,child])

theorem project_expression (expression : Expr) : project env expression.toTerm = expression.toTerm := by
  induction expression with
  | var index => exact project_variable _ _
  | literal value => exact project_ordinary_node (op := .natural value) rfl (by intro impossible; cases impossible) []
  | add _ _ left right =>
      simp only [Expr.toTerm,project_ordinary_node (op := .uadd) rfl (by decide),
        List.map_cons,List.map_nil,ValueErasure.emit,left,right]

private theorem project_index (family : Nat) (expression : Expr) :
    project env (propositionAt family expression.toTerm) = propositionAt family expression.toTerm := by
  simp only [propositionAt,project_ordinary_node (op := .ind family 1) rfl (by intro impossible; cases impossible),
    List.map_cons,List.map_nil,ValueErasure.emit,project_expression]

/-- Full pure conversion of native unary Ind nodes preserves the interpreted
index, even through original-requested conversions of the constructor type. -/
theorem index_conversion (wf : UnifiedProgram.EnvWellFormed env) {left right : Expr}
    (converted : RawValue.Conv env (propositionAt family left.toTerm) (propositionAt family right.toTerm)) :
    left.eval words = right.eval words := by
  have projected := converted.projected wf.admissible
  rw [project_index,project_index] at projected
  have children := (projected.ind_injective wf.admissible).2.2
  cases children with
  | cons aligned _ => exact PureArithmetic.affine_conversion_value wf left right (.old (.old aligned)) words

private def NaturalBound : Term → Prop
  | .natural value => value < 2^64
  | _ => True

theorem natural_bound (typed : LoanTyping.HasType env loans ctx mode term type) : NaturalBound term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => NaturalBound term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case dataElim => split <;> trivial

def specialize (expression : Expr) (value : Nat) : Expr := expression.subst (fun _ => .literal value)

theorem specialize_single (code : Unary expression) (value : Nat) :
    (specialize expression value).toTerm = expression.toTerm.subst (single (.natural value)) := by
  rw [specialize,Expr.subst_toTerm]
  apply Environment.scoped_subst_congr code.scoped
  intro index bound
  change index < 1 at bound
  have zero : index = 0 := by omega
  subst index
  rfl

private theorem oneField (value : Term) : fieldSubstitution [value] = single value := by
  funext index
  simp only [fieldSubstitution,List.length_nil,liftSub,Term.subst_id]

theorem specialize_fields (code : Unary expression) (value : Nat) (child : Term) :
    (expression.toTerm.rename Nat.succ).subst (fieldSubstitution [.natural value,child]) =
      (specialize expression value).toTerm := by
  rw [specialize_single code,Term.subst_rename]
  change expression.toTerm.subst (fun index => fieldSubstitution ([.natural value] ++ [child]) (index+1)) = _
  rw [fieldSubstitution_snoc,oneField]
  rfl

theorem specialize_eval (expression : Expr) (value : Nat) :
    (specialize expression value).eval (fun _ => 0) = expression.eval (fun _ => value) := by
  simp only [specialize,Expr.subst_eval,Expr.eval]

theorem constructor_view (history : ScopedProgram.History definitions declarations env)
    (family : Family env id) (found : family.entry.signatures[constructor]? = some signature)
    (typed : LoanTyping.HasType env [] ctx true (.node (.con id constructor count) values) type) :
    ∃ arity indices, LoanTyping.Arguments env [] ctx true family.entry.declaration.data
      (signatureTerm id signature) values (.node (.ind id arity) indices) ∧
      RawLend.Conv env (.node (.ind id arity) indices) type := by
  obtain ⟨entry,actualSignature,arity,indices,selected,selectedSignature,arguments,converted⟩ := typed.principalView
  cases Option.some.inj (family.found.symm.trans selected)
  cases Option.some.inj (found.symm.trans selectedSignature)
  have closed := (signature_metadata history family.found found).1.signatureTerm_scoped id
  rw [Environment.closed_rename closed] at arguments
  exact ⟨arity,indices,arguments,converted⟩

private theorem result_index {actual expected : Expr} (wf : UnifiedProgram.EnvWellFormed env)
    (arguments : LoanTyping.Arguments env [] ctx true data (signatureTerm family signature) values
      (.node (.ind family arity) indices)) (length : values.length = signature.fields.length)
    (computed : signature.result.map (Term.subst (fieldSubstitution values)) = [actual.toTerm])
    (converted : RawLend.Conv env (.node (.ind family arity) indices) type)
    (requested : RawValue.Conv env type (propositionAt family expected.toTerm)) :
    actual.eval (fun _ => 0) = expected.eval (fun _ => 0) := by
  have raw := (constructor_result_conversion wf arguments length).trans converted
  have one := congrArg List.length computed
  simp only [List.length_map,List.length_singleton] at one
  rw [one,computed] at raw
  exact index_conversion wf ((RawValue.Conv.old raw).trans requested)

/-- From actual constructor typing, construct an inhabitant at the original
index. In the recursive case the child's precise instantiated type comes
from the authentic Arguments derivation. -/
theorem ConstructorTree.sound {expected : Expr} (history : ScopedProgram.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.HasType env [] ctx true term type)
    (requested : RawValue.Conv env type (propositionAt id expected.toTerm)) :
    Fiber id family.entry (expected.eval (fun _ => 0)) := by
  let wf := history.wellFormed
  induction tree generalizing type expected with
  | @nullary result constructor closed found =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_view history family found typed
      have aligned := result_index (actual := result) wf arguments rfl
        (by simp only [nullarySignature,fieldSubstitution,List.map_cons,List.map_nil,Term.subst_id]) converted requested
      rw [← aligned]
      exact .nullary closed found
  | @scalar result constructor value resultCode found =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_view history family found typed
      have valueTyped := (arguments_pi_view wf arguments).1
      have width : value < 2^64 := natural_bound valueTyped
      have computed : (scalarSignature result).result.map (Term.subst (fieldSubstitution [.natural value])) =
          [(specialize result value).toTerm] := by
        simp only [scalarSignature,List.map_cons,List.map_nil,oneField,specialize_single resultCode]
      have aligned := result_index wf arguments rfl computed converted requested
      rw [← aligned,specialize_eval]
      exact .scalar resultCode found width
  | @recursive predecessor result constructor child value predecessorCode resultCode found _ ih =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_view history family found typed
      obtain ⟨valueTyped,tail⟩ := arguments_pi_view wf arguments
      have width : value < 2^64 := natural_bound valueTyped
      simp only [recursiveSignature,List.foldr_cons,List.foldr_nil,Term.pi,Term.subst,substArgs,Op.binders,liftSub] at tail
      have childTyped := (arguments_pi_view wf tail).1
      have childIndex : RawValue.Conv env
          (propositionAt id (predecessor.toTerm.subst (single (.natural value))))
          (propositionAt id (specialize predecessor value).toTerm) := by
        rw [specialize_single predecessorCode]
        exact .refl _
      simp only [propositionAt,Term.subst,substArgs,Op.binders,liftSub] at childTyped
      have inhabited := ih childTyped childIndex
      rw [specialize_eval] at inhabited
      have computed : (recursiveSignature id predecessor result).result.map
          (Term.subst (fieldSubstitution [.natural value,child])) = [(specialize result value).toTerm] := by
        simp only [recursiveSignature,List.map_cons,List.map_nil,specialize_fields resultCode]
      have aligned := result_index wf arguments rfl computed converted requested
      rw [← aligned,specialize_eval]
      exact .recursive predecessorCode resultCode found width inhabited

theorem native_constructor (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (shape : term = .node (.con family constructor count) values) :
    ∃ principal, LoanTyping.HasType env [] ctx true term principal ∧ RawValue.Conv env principal type := by
  induction typed with
  | native original => exact ⟨_,original,.refl _⟩
  | convert _ _ converted ih =>
      obtain ⟨_,native,prior⟩ := ih shape
      exact ⟨_,native,prior.trans converted⟩
  | pi | lam | app => cases shape

theorem ConstructorTree.pure_sound {expected : Expr}
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (requested : RawValue.Conv env type (propositionAt id expected.toTerm)) :
    Fiber id family.entry (expected.eval (fun _ => 0)) := by
  have shape : ∃ constructor count values, term = .node (.con id constructor count) values := by
    cases tree <;> exact ⟨_,_,_,rfl⟩
  obtain ⟨_,_,_,root⟩ := shape
  obtain ⟨_,native,prior⟩ := native_constructor typed root
  exact tree.sound (ScopedProgram.History.ofPureMixed history) family native (prior.trans requested)

theorem checked_global_carrier {index : Nat} {declaration : GlobalDeclaration} {expected : Expr}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (tree : ConstructorTree id family.entry declaration.value)
    (requested : RawValue.Conv env declaration.type (propositionAt id expected.toTerm)) :
    Nonempty (Finite.Carrier (family.meaning (expected.eval (fun _ => 0)))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  exact ⟨⟨⟨tree.pure_sound history family (history.global_value_and_reference found).1 requested⟩⟩⟩

structure Invariant (family : Nat) (entry : CheckedFamily) (property : Nat → Prop) : Prop where
  nullary : ∀ {result : Expr} {constructor : Nat}, Closed result →
    entry.signatures[constructor]? = some (nullarySignature result) → property (result.eval (fun _ => 0))
  scalar : ∀ {result : Expr} {constructor value : Nat}, Unary result →
    entry.signatures[constructor]? = some (scalarSignature result) → value < 2^64 → property (result.eval (fun _ => value))
  recursive : ∀ {predecessor result : Expr} {constructor value : Nat}, Unary predecessor → Unary result →
    entry.signatures[constructor]? = some (recursiveSignature family predecessor result) → value < 2^64 →
    property (predecessor.eval (fun _ => value)) → property (result.eval (fun _ => value))

/-- A native constructor family validates its semantic invariants by the
same indexed induction that defines its least carrier. -/
theorem Fiber.induction_property (inhabited : Fiber family entry index) (invariant : Invariant family entry property) :
    property index := by
  induction inhabited with
  | nullary closed found => exact invariant.nullary closed found
  | scalar result found width => exact invariant.scalar result found width
  | recursive predecessor result found width _ inherited => exact invariant.recursive predecessor result found width inherited

theorem no_checked_family_index {index : Nat} {declaration : GlobalDeclaration} {expected : Expr}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (tree : ConstructorTree id family.entry declaration.value)
    (requested : RawValue.Conv env declaration.type (propositionAt id expected.toTerm))
    (invariant : Invariant id family.entry property) (excluded : ¬ property (expected.eval (fun _ => 0))) : False := by
  obtain ⟨witness⟩ := checked_global_carrier accepted family found tree requested
  have inhabited : Fiber id family.entry (expected.eval (fun _ => 0)) := witness.down.down
  exact excluded (inhabited.induction_property invariant)

private def zeroIndex : Expr := .literal 0
private def recursiveInput : Expr := .var 0
private def recursiveOutput : Expr := .add recursiveInput (.literal 2)
private def evenDeclaration : FamilyDeclaration := ⟨false,0,1,
  [propositionAt 0 (.natural 0),.pi false .u64
    (.pi true (propositionAt 0 (.var 0)) (propositionAt 0 (.uadd (.var 1) (.natural 2))))],0⟩
private def evenEntry : CheckedFamily := ⟨evenDeclaration,
  [nullarySignature zeroIndex,recursiveSignature 0 recursiveInput recursiveOutput],false⟩
private def evenProof : Term := .node (.con 0 1 2) [.natural 0,.node (.con 0 0 0) []]
private def source : GlobalDeclaration := ⟨propositionAt 0 (.natural 2),evenProof⟩
private def world : Environment := ⟨#[source],#[evenEntry]⟩
private def evenFamily : Family world 0 := ⟨evenEntry,rfl,rfl,rfl⟩

private theorem fromEvenTable {constructor : Nat}
    (found : evenEntry.signatures[constructor]? = some signature) :
    signature = nullarySignature zeroIndex ∨ signature = recursiveSignature 0 recursiveInput recursiveOutput := by
  have included := List.mem_iff_getElem?.mpr ⟨constructor,found⟩
  simpa [evenEntry] using included

private theorem readAffine {left right : Expr} (same : left.toTerm = right.toTerm) : left = right := by
  have parsed := congrArg AffineSum.parse same
  simpa only [AffineSum.parse_toTerm,Option.some.injEq] using parsed

private theorem evenInvariant : Invariant 0 evenEntry (fun n => n % 2 = 0) where
  nullary := by
    intro result constructor _ found
    rcases fromEvenTable found with matching | impossible
    · have resultTerm := (List.cons.inj (congrArg Signature.result matching)).1
      change result.toTerm = zeroIndex.toTerm at resultTerm
      rw [readAffine resultTerm]
      rfl
    · have fields := congrArg (fun sig => sig.fields.length) impossible
      simp [nullarySignature,recursiveSignature] at fields
  scalar := by
    intro result constructor value _ found _
    rcases fromEvenTable found with impossible | impossible
    all_goals
      have fields := congrArg (fun sig => sig.fields.length) impossible
      simp [scalarSignature,nullarySignature,recursiveSignature] at fields
  recursive := by
    intro predecessor result constructor value _ _ found _ inherited
    rcases fromEvenTable found with impossible | matching
    · have fields := congrArg (fun sig => sig.fields.length) impossible
      simp [nullarySignature,recursiveSignature] at fields
    · have sourceField := congrArg (fun sig => sig.fields[1]?.map Field.domain) matching
      change some (propositionAt 0 predecessor.toTerm) = some (propositionAt 0 recursiveInput.toTerm) at sourceField
      have predTerm := (List.cons.inj (Term.node.inj (Option.some.inj sourceField)).2).1
      have predecessorEq : predecessor = recursiveInput := readAffine predTerm
      rw [predecessorEq] at inherited
      change value % 2 = 0 at inherited
      have resultTerm := (List.cons.inj (congrArg Signature.result matching)).1
      change result.toTerm.rename Nat.succ = recursiveOutput.toTerm.rename Nat.succ at resultTerm
      rw [← Expr.rename_toTerm,← Expr.rename_toTerm] at resultTerm
      have evaluated := congrArg (fun expression => Expr.eval (fun _ => value) expression) (readAffine resultTerm)
      simp only [Expr.rename_eval] at evaluated
      change result.eval (fun _ => value) = value + 2 at evaluated
      rw [evaluated]
      omega

private theorem evenTree : ConstructorTree 0 evenEntry evenProof :=
  .recursive (.var .here) (.add (.var .here) (.literal (by decide))) rfl (.nullary (.literal (by decide)) rfl)

/-- The checked even-index family has a real constructor proof at two and
its least interpretation excludes one, regardless of the chosen constructor. -/
theorem checked_even_and_odd_boundary :
    LoanTyping.PureMixedAdmission.checkProgram ⟨32,32,32,8192⟩ [source] [evenDeclaration] = some world ∧
    Nonempty (Finite.Carrier (evenFamily.meaning 2)) ∧ ¬ Nonempty (Finite.Carrier (evenFamily.meaning 1)) := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram ⟨32,32,32,8192⟩ [source] [evenDeclaration] = some world := by cbv
  have history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have typed := (history.global_value_and_reference (index := 0) (declaration := source) rfl).1
  have built := evenTree.pure_sound (expected := .literal 2) history evenFamily typed (.refl _)
  refine ⟨admitted,⟨⟨⟨built⟩⟩⟩,?_⟩
  intro inhabited
  obtain ⟨witness⟩ := inhabited
  have atOne : Fiber 0 evenEntry 1 := witness.down.down
  have even := atOne.induction_property evenInvariant
  omega

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition
