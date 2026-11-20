import Jihoo.NativeLoanPureFamilyArithmeticReplay

/-! Native unary indexed propositions with arbitrarily many erased recursive
fields. The indices of every field and the result can depend affinely on a
leading U64 scalar. Each checked child contributes its own fiber inhabitant. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Branches

open AffineSum (Expr)
open LoanTyping.FamilyIota (arguments_pi_view)
open Elimination (constructor_typed specialize_closed closed_affine_conversion)
open Environment.FamilyIota (elimTerm)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes (Code)

variable {id : Nat}

private def recursiveFields (family : Nat) : Nat → List Expr → List Field
  | _, [] => []
  | depth, predecessor :: rest =>
      let index := predecessor.toTerm.rename (fun x => x + depth)
      ⟨true,propositionAt family index,some [index]⟩ :: recursiveFields family (depth+1) rest

private def recursiveTail (family depth : Nat) (predecessors : List Expr) (result : Expr) : Signature :=
  ⟨recursiveFields family depth predecessors,[result.toTerm.rename (fun x => x + (depth + predecessors.length))]⟩

def branchSignature (family : Nat) (predecessors : List Expr) (result : Expr) : Signature :=
  let tail := recursiveTail family 0 predecessors result
  ⟨⟨false,.u64,none⟩ :: tail.fields,tail.result⟩

private theorem rename_identity (term : Term) : term.rename (fun x : Nat => x) = term := Term.rename_id term

theorem branchSignature_nil (family : Nat) (result : Expr) : branchSignature family [] result = scalarSignature result := by
  simp only [branchSignature,recursiveTail,recursiveFields,List.length_nil,Nat.add_zero,rename_identity,scalarSignature]

theorem branchSignature_single (family : Nat) (predecessor result : Expr) :
    branchSignature family [predecessor] result = recursiveSignature family predecessor result := by
  simp only [branchSignature,recursiveTail,recursiveFields,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
    rename_identity,recursiveSignature]

private def closedTelescope (family : Nat) : List Expr → Expr → Term
  | [], result => propositionAt family result.toTerm
  | predecessor :: rest, result => .pi true (propositionAt family predecessor.toTerm) (closedTelescope family rest result)

private theorem lifted_literal (value depth : Nat) : liftSub depth (single (.natural value)) depth = .natural value := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change (liftSub depth (single (.natural value)) depth).rename Nat.succ = _
      rw [ih]
      simp only [Term.natural, Term.rename, renameArgs]

theorem specialize_lifted (code : Unary expression) (depth value : Nat) :
    (expression.toTerm.rename (fun x => x + depth)).subst (liftSub depth (single (.natural value))) =
      (specialize expression value).toTerm := by
  rw [specialize_single code,Term.subst_rename]
  apply Environment.scoped_subst_congr code.scoped
  intro index bound
  change index < 1 at bound
  have zero : index = 0 := by omega
  subst index
  simpa only [Nat.zero_add,single] using lifted_literal value depth

private theorem proposition_subst (family : Nat) (index : Term) (σ : Nat → Term) :
    (propositionAt family index).subst σ = propositionAt family (index.subst σ) := by
  simp only [propositionAt,Term.subst,substArgs,Op.binders,liftSub]

private theorem pi_subst (domain body : Term) (σ : Nat → Term) :
    (Term.pi true domain body).subst σ = .pi true (domain.subst σ) (body.subst (liftSubOne σ)) := by
  simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub]

private theorem tail_specializes (codes : ∀ predecessor ∈ predecessors, Unary predecessor)
    (resultCode : Unary result) (depth value : Nat) :
    (signatureTerm id (recursiveTail id depth predecessors result)).subst (liftSub depth (single (.natural value))) =
      closedTelescope id (predecessors.map (fun predecessor => specialize predecessor value)) (specialize result value) := by
  induction predecessors generalizing depth with
  | nil =>
      change (propositionAt id (result.toTerm.rename (fun x => x + depth))).subst (liftSub depth (single (.natural value))) = _
      rw [proposition_subst,specialize_lifted resultCode]
      rfl
  | cons predecessor rest ih =>
      have length : depth + (predecessor :: rest).length = depth + 1 + rest.length := by simp only [List.length_cons]; omega
      have unfolded : signatureTerm id (recursiveTail id depth (predecessor :: rest) result) =
          .pi true (propositionAt id (predecessor.toTerm.rename (fun x => x + depth)))
            (signatureTerm id (recursiveTail id (depth+1) rest result)) := by
        simp only [recursiveTail,length,recursiveFields,signatureTerm,List.foldr_cons]
      rw [unfolded,pi_subst]
      rw [show liftSubOne (liftSub depth (single (.natural value))) = liftSub (depth+1) (single (.natural value)) from rfl]
      rw [proposition_subst,specialize_lifted (codes predecessor (by simp)),ih (fun p hp => codes p (by simp [hp]))]
      rfl

private theorem proposition_scoped (family : Nat) (scope : index.Scoped 0) : (propositionAt family index).Scoped 0 := by
  apply Term.Scoped.nonbinding (by intro index; rfl)
  intro term included
  cases List.mem_singleton.mp included
  exact scope

private theorem closed_telescope_scoped (codes : ∀ predecessor ∈ predecessors, Closed predecessor)
    (resultCode : Closed result) : (closedTelescope id predecessors result).Scoped 0 := by
  induction predecessors with
  | nil => exact proposition_scoped id resultCode.scoped
  | cons predecessor rest ih =>
      refine Term.Scoped.node (fun position term selected => ?_)
      cases position with
      | zero =>
          cases selected
          exact proposition_scoped id (codes predecessor (by simp)).scoped
      | succ position =>
          cases position with
          | zero =>
              cases selected
              exact (ih (fun p hp => codes p (by simp [hp]))).monotone (by decide)
          | succ position => cases selected

/-- A branch signature contributes an inhabitant when it has a child at
each specified index. The binder order is the actual native field order. -/
inductive Fiber (family : Nat) (entry : CheckedFamily) : Nat → Prop where
  | base {constructor : Nat} (code : Closed result) : entry.signatures[constructor]? = some (nullarySignature result) →
      Fiber family entry (result.eval (fun _ => 0))
  | branch {constructor value : Nat} (codes : ∀ predecessor ∈ predecessors, Unary predecessor) (resultCode : Unary result) :
      entry.signatures[constructor]? = some (branchSignature family predecessors result) → value < 2^64 →
      (∀ predecessor ∈ predecessors, Fiber family entry (predecessor.eval (fun _ => value))) →
      Fiber family entry (result.eval (fun _ => value))

def meaning (family : Family env id) (index : Nat) : Finite.Universe .proposition :=
  .proposition (Fiber id family.entry index)

theorem Fiber.of_single_field (inhabited : IndexedProposition.Fiber id entry index) : Fiber id entry index := by
  induction inhabited with
  | nullary code found => exact .base code found
  | scalar code found width =>
      exact .branch (predecessors := []) (by simp) code (by rwa [branchSignature_nil]) width (by simp)
  | @recursive predecessor result constructor value predecessorCode resultCode found width _ ih =>
      refine .branch (predecessors := [predecessor]) ?_ resultCode (by rwa [branchSignature_single]) width ?_
      · intro expression included
        cases List.mem_singleton.mp included
        exact predecessorCode
      · intro expression included
        cases List.mem_singleton.mp included
        exact ih

inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
  | base (code : Closed result) : entry.signatures[constructor]? = some (nullarySignature result) →
      ConstructorTree family entry (.node (.con family constructor 0) [])
  | branch {constructor value : Nat} (codes : ∀ predecessor ∈ predecessors, Unary predecessor) (resultCode : Unary result) :
      entry.signatures[constructor]? = some (branchSignature family predecessors result) → children.length = predecessors.length →
      (∀ child ∈ children, ConstructorTree family entry child) →
      ConstructorTree family entry (.node (.con family constructor (children.length+1)) (.natural value :: children))

private theorem tail_arguments {predecessors : List Expr} (wf : UnifiedProgram.EnvWellFormed env) (codes : ∀ predecessor ∈ predecessors, Closed predecessor)
    (resultCode : Closed result) (size : children.length = predecessors.length)
    (arguments : LoanTyping.Arguments env [] ctx true data (closedTelescope id predecessors result) children type) :
    RawLend.Conv env (propositionAt id result.toTerm) type ∧
    (∀ {position : Nat} {predecessor : Expr}, predecessors[position]? = some predecessor →
      ∃ child, children[position]? = some child ∧ LoanTyping.HasType env [] ctx true child (propositionAt id predecessor.toTerm)) := by
  induction predecessors generalizing children with
  | nil =>
      have empty : children = [] := List.length_eq_zero_iff.mp size
      subst children
      cases arguments with
      | nil converted => exact ⟨converted, by intro position predecessor found; simp at found⟩
  | cons predecessor rest ih =>
      cases children with
      | nil => simp at size
      | cons child children =>
          obtain ⟨typed,remainder⟩ := arguments_pi_view wf arguments
          have later : ∀ p ∈ rest, Closed p := fun p hp => codes p (by simp [hp])
          have restClosed := closed_telescope_scoped (id := id) later resultCode
          rw [Environment.closed_subst restClosed] at remainder
          obtain ⟨converted,other⟩ := ih later (Nat.succ.inj size) remainder
          refine ⟨converted,?_⟩
          intro position value found
          cases position with
          | zero => cases found; exact ⟨child,rfl,typed⟩
          | succ position => exact other found

private theorem specialized_codes {predecessors : List Expr} (codes : ∀ predecessor ∈ predecessors, Unary predecessor) (width : value < 2^64) :
    ∀ specialized ∈ predecessors.map (fun predecessor => specialize predecessor value), Closed specialized := by
  intro specialized included
  obtain ⟨original,found,rfl⟩ := List.mem_map.mp included
  exact specialize_closed (codes original found) width

/-- The actual checked argument telescope supplies the exact instantiated
type of every recursive field. The returned carrier preserves the result
index even when the original declaration used a convertible annotation. -/
theorem ConstructorTree.sound {expected : Expr} (history : ScopedProgram.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.HasType env [] ctx true term type)
    (requested : RawValue.Conv env type (propositionAt id expected.toTerm)) :
    Fiber id family.entry (expected.eval (fun _ => 0)) := by
  let wf := history.wellFormed
  induction tree generalizing type expected with
  | @base result constructor code found =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_view history family found typed
      cases arguments with
      | nil resultType =>
          have aligned := index_conversion (words := fun _ => 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
          rw [← aligned]
          exact .base code found
  | @branch predecessors result children constructor value codes resultCode found size _ ih =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_view history family found typed
      change LoanTyping.Arguments env [] ctx true family.entry.declaration.data
        (.pi false .u64 (signatureTerm id (recursiveTail id 0 predecessors result))) (.natural value :: children) _ at arguments
      obtain ⟨valueTyped,remainder⟩ := arguments_pi_view wf arguments
      have width : value < 2^64 := natural_bound valueTyped
      change LoanTyping.Arguments env [] ctx true family.entry.declaration.data
        ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (single (.natural value)))) children _ at remainder
      rw [tail_specializes codes resultCode] at remainder
      obtain ⟨resultType,fields⟩ := tail_arguments wf (specialized_codes codes width) (specialize_closed resultCode width)
        (size.trans (List.length_map _).symm) remainder
      have aligned := index_conversion (words := fun _ => 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
      rw [← aligned,specialize_eval]
      refine .branch codes resultCode found width ?_
      intro predecessor included
      obtain ⟨position,selected⟩ := List.mem_iff_getElem?.mp included
      obtain ⟨child,childFound,childTyped⟩ := fields (position := position) (predecessor := specialize predecessor value)
        (by simp only [List.getElem?_map,selected,Option.map_some])
      rw [← specialize_eval predecessor value]
      exact ih child (List.mem_of_getElem? childFound) childTyped (.refl _)

theorem ConstructorTree.pure_sound {expected : Expr} (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (requested : RawValue.Conv env type (propositionAt id expected.toTerm)) :
    Fiber id family.entry (expected.eval (fun _ => 0)) := by
  have shape : ∃ constructor values, term = .node (.con id constructor values.length) values := by
    cases tree with
    | base => exact ⟨_,[],rfl⟩
    | branch => exact ⟨_,.natural _ :: _,rfl⟩
  obtain ⟨_,_,head⟩ := shape
  obtain ⟨_,native,conversion⟩ := native_constructor typed head
  exact tree.sound (ScopedProgram.History.ofPureMixed history) family native (conversion.trans requested)

theorem checked_global_carrier {declaration : GlobalDeclaration} {index : Nat} {expected : Expr}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (tree : ConstructorTree id family.entry declaration.value)
    (requested : RawValue.Conv env declaration.type (propositionAt id expected.toTerm)) :
    Nonempty (Finite.Carrier (meaning family (expected.eval (fun _ => 0)))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  exact ⟨⟨⟨tree.pure_sound history family (history.global_value_and_reference found).1 requested⟩⟩⟩

private theorem build_tail {family : Family env id} {predecessors : List Expr} (codes : ∀ predecessor ∈ predecessors, Closed predecessor)
    (resultCode : Closed result)
    (realized : ∀ predecessor ∈ predecessors, ∃ child,
      ConstructorTree id family.entry child ∧ LoanTyping.HasType env [] [] true child (propositionAt id predecessor.toTerm)) :
    ∃ children, children.length = predecessors.length ∧ (∀ child ∈ children, ConstructorTree id family.entry child) ∧
      LoanTyping.Arguments env [] [] true family.entry.declaration.data (closedTelescope id predecessors result) children
        (propositionAt id result.toTerm) := by
  induction predecessors with
  | nil => exact ⟨[],rfl,(by simp),.nil (.refl _)⟩
  | cons predecessor rest ih =>
      obtain ⟨child,childTree,childTyped⟩ := realized predecessor (by simp)
      have later : ∀ p ∈ rest, Closed p := fun p hp => codes p (by simp [hp])
      obtain ⟨children,size,trees,arguments⟩ := ih later (fun p hp => realized p (by simp [hp]))
      refine ⟨child :: children,congrArg Nat.succ size,?_,.cons (.refl _) childTyped ?_⟩
      · intro field included
        rcases List.mem_cons.mp included with rfl | other
        · exact childTree
        · exact trees field other
      · change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((closedTelescope id rest result).subst (single child)) children _
        rw [Environment.closed_subst (closed_telescope_scoped later resultCode)]
        exact arguments

structure Realization (family : Family env id) (index : Nat) where
  expression : Expr
  closed : Closed expression
  evaluated : expression.eval (fun _ => 0) = index
  term : Term
  tree : ConstructorTree id family.entry term
  typed : LoanTyping.HasType env [] [] true term (propositionAt id expression.toTerm)

/-- Reification rebuilds every constructor argument at its own result of
index substitution. No choice function or blanket child conversion is used. -/
theorem Fiber.reify (family : Family env id) (inhabited : Fiber id family.entry index) :
    Nonempty (Realization family index) := by
  induction inhabited with
  | @base result constructor code found =>
      exact ⟨⟨result,code,rfl,.node (.con id constructor 0) [],.base code found,
        constructor_typed family found (.nil (.refl _))⟩⟩
  | @branch predecessors result constructor value codes resultCode found width _ ih =>
      have resultClosed := specialize_closed resultCode width
      have got : ∀ specialized ∈ predecessors.map (fun p => specialize p value), ∃ child,
          ConstructorTree id family.entry child ∧ LoanTyping.HasType env [] [] true child (propositionAt id specialized.toTerm) := by
        intro specialized included
        obtain ⟨predecessor,foundPredecessor,rfl⟩ := List.mem_map.mp included
        obtain ⟨child⟩ := ih predecessor foundPredecessor
        have alignment := closed_affine_conversion (env := env) child.closed (specialize_closed (codes predecessor foundPredecessor) width)
          (child.evaluated.trans (specialize_eval predecessor value).symm)
        exact ⟨child.term,child.tree,.convert child.typed (RawLend.Conv.node (.ind id 1) (.cons alignment .nil))⟩
      obtain ⟨children,size,trees,arguments⟩ := build_tail (family := family) (specialized_codes codes width) resultClosed got
      have native : LoanTyping.Arguments env [] [] true family.entry.declaration.data
          (signatureTerm id (branchSignature id predecessors result)) (.natural value :: children)
          (propositionAt id (specialize result value).toTerm) := by
        change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          (.pi false .u64 (signatureTerm id (recursiveTail id 0 predecessors result))) (.natural value :: children) _
        refine .cons (.refl _) (.natural width) ?_
        change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (single (.natural value)))) children _
        rw [tail_specializes codes resultCode]
        exact arguments
      refine ⟨⟨specialize result value,resultClosed,specialize_eval result value,
        .node (.con id constructor (children.length+1)) (.natural value :: children),?_,constructor_typed family found native⟩⟩
      exact .branch codes resultCode found (size.trans (List.length_map _)) trees

theorem Realization.elimination_typed {family : Family env id} (input : Realization family index)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term) (.app motive input.expression.toTerm) := by
  have formed : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity) := by
    rw [family.unary]
    exact motiveTyped
  have native : LoanTyping.HasType env [] [] true input.term
      (.node (.ind id family.entry.declaration.arity) [input.expression.toTerm]) := by
    rw [family.unary]
    exact input.typed
  exact .propElim family.found family.proposition formed branches native

/-- Authentic mixed typing checks the chosen branch and its entire vector
of recursive hypotheses when given a reified semantic input. -/
theorem Fiber.elimination_contracts (family : Family env id) (inhabited : Fiber id family.entry index)
    (history : ScopedProgram.History definitions declarations env)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    ∃ input : Realization family index, ∃ residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual ∧
      LoanTyping.PureTyping.HasType env [] residual (.app motive input.expression.toTerm) := by
  obtain ⟨input⟩ := Fiber.reify family inhabited
  have ctor : ∃ constructor values, input.term = .node (.con id constructor values.length) values := by
    obtain ⟨_,_,_,_,tree,_⟩ := input
    cases tree with
    | base => exact ⟨_,[],rfl⟩
    | branch => exact ⟨_,.natural _ :: _,rfl⟩
  obtain ⟨constructor,values,shape⟩ := ctor
  have canContract : LoanTyping.PureFamilyProofs.ConstructorHead (elimTerm id motive cases input.term) := by
    rw [shape]
    exact .elim id constructor motive cases values
  obtain ⟨result,ran,typed⟩ := LoanTyping.PureFamilyProofs.contract_from_pure_typing history
    (.native (input.elimination_typed motiveTyped branches)) canContract
  exact ⟨input,result,ran,typed⟩

/-- Elimination into a supported proposition code follows from the
authenticated Case derivations and the actual replay of the selected branch. -/
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
  obtain ⟨input,residual,contracted,retained⟩ := Fiber.elimination_contracts family inhabited
    (ScopedProgram.History.ofPureMixed history) motiveTyped branches
  exact (covered input residual contracted).inhabits history retained (aligned input) assignment

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
  obtain ⟨motiveTyped,branches⟩ := Elimination.checked_cases (family := family)
    (history.global_value_and_reference found).1 source
  exact Fiber.semantic_elimination family inhabited history motiveTyped branches result aligned covered assignment

section Example

open LoanTyping.PureFamilyArithmeticReplay (observe? observed_fundamental)

private def leftIndex : Expr := .var 0
private def rightIndex : Expr := .add leftIndex (.literal 1)
private def resultIndex : Expr := .add leftIndex (.literal 2)
private def branching : Signature := branchSignature 0 [leftIndex,rightIndex] resultIndex
private def declaration : FamilyDeclaration := ⟨false,0,1,
  [propositionAt 0 (.natural 0),propositionAt 0 (.natural 1),signatureTerm 0 branching],0⟩
private def table : CheckedFamily := ⟨declaration,[nullarySignature (.literal 0),nullarySignature (.literal 1),branching],false⟩
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def successor (index : Term) : Term := .uadd index one
private def shifted (index : Term) : Term := .uadd index two
private def increasing (index : Term) : Term := .lt index (successor index)
private def motive : Term := .lam false .u64 (increasing (.var 0))
private def leftBase : Term := .zeroLe zero
private def rightBase : Term := .ltAdd zero one one leftBase
private def branchEvidence (index leftProof rightProof : Term) : Term :=
  .ltLe (shifted index) (shifted (successor index)) (shifted (successor index))
    (.ltAdd index (successor index) two leftProof)
    (.ltAdd (successor index) (successor (successor index)) two rightProof)
private def branch : Term := .lam false .u64 (.lam true (propositionAt 0 (.var 0))
  (.lam true (propositionAt 0 (successor (.var 1))) (.lam true (increasing (.var 2))
    (.lam true (increasing (successor (.var 3))) (branchEvidence (.var 4) (.var 1) (.var 0))))))
private def arms : List Term := [leftBase,rightBase,branch]
private def leftChild : Term := .node (.con 0 0 0) []
private def rightChild : Term := .node (.con 0 1 0) []
private def constructorProof : Term := .node (.con 0 2 3) [zero,leftChild,rightChild]
private def inputSource : GlobalDeclaration := ⟨propositionAt 0 two,constructorProof⟩
private def elimSource : GlobalDeclaration := ⟨increasing two,elimTerm 0 motive arms constructorProof⟩
private def world : Environment := ⟨#[inputSource,elimSource],#[table]⟩
private def family : Family world 0 := ⟨table,rfl,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private theorem predecessors_supported : ∀ predecessor ∈ [leftIndex,rightIndex], Unary predecessor := by
  intro predecessor found
  rcases List.mem_cons.mp found with rfl | found
  · exact .var .here
  · cases List.mem_singleton.mp found
    exact .add (.var .here) (.literal (by decide))

private theorem example_tree : ConstructorTree 0 table constructorProof := by
  refine .branch (result := resultIndex) (children := [leftChild,rightChild]) (constructor := 2) (value := 0)
    predecessors_supported (.add (.var .here) (.literal (by decide))) rfl rfl ?_
  intro child found
  rcases List.mem_cons.mp found with rfl | found
  · exact .base (result := .literal 0) (.literal (by decide)) (constructor := 0) rfl
  · cases List.mem_singleton.mp found
    exact .base (result := .literal 1) (.literal (by decide)) (constructor := 1) rfl

/-- The mixed checker accepts distinct P(0) and P(1) fields of P(2). Its
selected branch consumes both erased induction hypotheses in separate LtLe
operands, and the executable observation reaches both checked base proofs. -/
theorem checked_distinct_recursive_indices :
    LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world ∧
    Nonempty (Finite.Carrier (meaning family 2)) ∧
    observe? world [] 48 16 16 4096 10 elimSource.value = some (branchEvidence zero leftBase rightBase) ∧
    PureArithmetic.UniversalTruth world elimSource.type := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [declaration] = some world := by cbv
  have executed : observe? world [] 48 16 16 4096 10 elimSource.value = some (branchEvidence zero leftBase rightBase) := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have inputTyped := (history.global_value_and_reference (index := 0) (declaration := inputSource) rfl).1
  have elimTyped := (history.global_value_and_reference (index := 1) (declaration := elimSource) rfl).1
  have inhabited := example_tree.pure_sound (expected := .literal 2) history family inputTyped (.refl _)
  exact ⟨admitted,⟨⟨⟨inhabited⟩⟩⟩,executed,observed_fundamental history elimTyped executed⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Branches
