import Jihoo.NativeLoanIndexedPropositionBranches

/-! Native `Prop` families over finite vectors of U64 indices. Each recursive
field has its own vector of affine indices, all scoped over a leading scalar.
The checked `Arguments` telescope determines both the order of the recursive
fields and the type of every subproof. -/
namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Vectors

open AffineSum (Expr)
open NativeKernel.Conversion (ListRel)
open LoanTyping.FamilyIota (arguments_pi_view signature_metadata)
open Environment.FamilyIota (elimTerm)
open Elimination (specialize_closed closed_affine_conversion)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes (Code)
open ValueErasure.Loan (project project_ordinary_node)

variable {id : Nat}

def propositionAt (family : Nat) (indices : List Term) : Term := .node (.ind family indices.length) indices
def terms (indices : List Expr) : List Term := indices.map Expr.toTerm
private def specializeAt (scalar : Nat) (indices : List Expr) : List Expr := indices.map (fun expr => specialize expr scalar)

def evaluate (scalar : Nat) (indices : List Expr) : List Nat := indices.map (Expr.eval (fun _ => scalar))

structure IndexCode (supported : Expr → Prop) (arity : Nat) (indices : List Expr) : Prop where
  size : indices.length = arity
  valid : ∀ expr ∈ indices, supported expr

structure Family (env : Environment) (family : Nat) where
  entry : CheckedFamily
  found : env.families[family]? = some entry
  proposition : entry.declaration.data = false

private theorem project_indices (indices : List Expr) : (terms indices).map (project env) = terms indices := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
      simpa only [terms,List.map_cons,project_expression] using congrArg (List.cons first.toTerm) ih

private theorem project_proposition (family : Nat) (indices : List Expr) :
    project env (propositionAt family (terms indices)) = propositionAt family (terms indices) := by
  simp only [propositionAt,project_ordinary_node (op := .ind family (terms indices).length) rfl
    (by intro impossible; cases impossible),ValueErasure.emit,project_indices]

private theorem component_conversion {left right : List Expr} (wf : UnifiedProgram.EnvWellFormed env)
    (converted : ListRel (Environment.FamilyIota.Extended.Conv env) (terms left) (terms right)) :
    evaluate scalar left = evaluate scalar right := by
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons first rest => cases converted
  | cons first rest ih => cases right with
    | nil => cases converted
    | cons other remaining =>
        cases converted with
        | cons head tail =>
            have equal := PureArithmetic.affine_conversion_value wf first other (.old (.old head)) (fun _ => scalar)
            exact (congrArg (fun n => n :: evaluate scalar rest) equal).trans (congrArg (List.cons _) (ih tail))

/-- An actual pure conversion respects every affine index, including
conversion through an expanded annotation. -/
theorem index_conversion {left right : List Expr} (wf : UnifiedProgram.EnvWellFormed env)
    (converted : RawValue.Conv env (propositionAt id (terms left)) (propositionAt id (terms right))) :
    evaluate scalar left = evaluate scalar right := by
  have projected := converted.projected wf.admissible
  rw [project_proposition,project_proposition] at projected
  exact component_conversion wf (projected.ind_injective wf.admissible).2.2

private theorem closed_component_equations {left right : List Expr}
    (first : ∀ expr ∈ left, Closed expr) (second : ∀ expr ∈ right, Closed expr)
    (equal : evaluate 0 left = evaluate 0 right) : ListRel (RawLend.Conv env) (terms left) (terms right) := by
  induction left generalizing right with
  | nil => cases right with
    | nil => exact .nil
    | cons head tail => cases equal
  | cons leftHead leftTail ih => cases right with
    | nil => cases equal
    | cons rightHead rightTail =>
        obtain ⟨headEqual,tailEqual⟩ := List.cons.inj equal
        exact .cons (closed_affine_conversion (first _ (by simp)) (second _ (by simp)) headEqual)
          (ih (fun e member => first e (by simp [member])) (fun e member => second e (by simp [member])) tailEqual)

theorem closed_index_conversion {left right : List Expr} (first : IndexCode Closed arity left) (second : IndexCode Closed arity right)
    (equal : evaluate 0 left = evaluate 0 right) : RawLend.Conv env (propositionAt id (terms left)) (propositionAt id (terms right)) := by
  have arityEqual : (terms left).length = (terms right).length := by
    simp only [terms,List.length_map,first.size,second.size]
  unfold propositionAt
  rw [arityEqual]
  exact .node _ (closed_component_equations first.valid second.valid equal)

def shifted (depth : Nat) (indices : List Expr) : List Term :=
  indices.map (fun expr => expr.toTerm.rename (fun x => x + depth))

def baseSignature (result : List Expr) : Signature := ⟨[],terms result⟩

private def recursiveFields (family : Nat) : Nat → List (List Expr) → List Field
  | _, [] => []
  | depth, predecessor :: rest =>
      let indices := shifted depth predecessor
      ⟨true,propositionAt family indices,some indices⟩ :: recursiveFields family (depth+1) rest

def recursiveTail (family depth : Nat) (predecessors : List (List Expr)) (result : List Expr) : Signature :=
  ⟨recursiveFields family depth predecessors,shifted (depth + predecessors.length) result⟩

theorem signatureTail_cons (family depth : Nat) (predecessor : List Expr) (rest : List (List Expr)) (result : List Expr) :
    signatureTerm family (recursiveTail family depth (predecessor :: rest) result) =
      .pi true (propositionAt family (shifted depth predecessor)) (signatureTerm family (recursiveTail family (depth+1) rest result)) := by
  have length : depth + (predecessor :: rest).length = depth + 1 + rest.length := by simp only [List.length_cons]; omega
  simp only [recursiveTail,length,recursiveFields,signatureTerm,List.foldr_cons]

def branchSignature (family : Nat) (predecessors : List (List Expr)) (result : List Expr) : Signature :=
  let tail := recursiveTail family 0 predecessors result
  ⟨⟨false,.u64,none⟩ :: tail.fields,tail.result⟩

def telescope (family : Nat) : List (List Expr) → List Expr → Term
  | [], result => propositionAt family (terms result)
  | predecessor :: rest, result => .pi true (propositionAt family (terms predecessor)) (telescope family rest result)

theorem proposition_subst (family : Nat) (indices : List Term) (σ : Nat → Term) :
    (propositionAt family indices).subst σ = propositionAt family (indices.map (Term.subst σ)) := by
  simp only [propositionAt,Term.subst,substArgs_dataInd,List.length_map]

theorem pi_subst (domain body : Term) (σ : Nat → Term) :
    (Term.pi true domain body).subst σ = .pi true (domain.subst σ) (body.subst (liftSubOne σ)) := by
  simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub]

private theorem specialize_indices {indices : List Expr} (valid : ∀ expr ∈ indices, Unary expr) (depth value : Nat) :
    (shifted depth indices).map (Term.subst (liftSub depth (single (.natural value)))) = terms (specializeAt value indices) := by
  simp only [shifted,terms,specializeAt,List.map_map]
  apply List.map_congr_left
  intro expression included
  exact Branches.specialize_lifted (valid expression included) depth value

private theorem tail_specializes {predecessors : List (List Expr)} (codes : ∀ predecessor ∈ predecessors, IndexCode Unary arity predecessor)
    (resultCode : IndexCode Unary arity result) (depth value : Nat) :
    (signatureTerm id (recursiveTail id depth predecessors result)).subst (liftSub depth (single (.natural value))) =
      telescope id (predecessors.map (specializeAt value)) (specializeAt value result) := by
  induction predecessors generalizing depth with
  | nil =>
      change (propositionAt id (shifted depth result)).subst (liftSub depth (single (.natural value))) = _
      rw [proposition_subst,specialize_indices resultCode.valid]
      rfl
  | cons predecessor rest ih =>
      rw [signatureTail_cons,pi_subst]
      rw [show liftSubOne (liftSub depth (single (.natural value))) = liftSub (depth+1) (single (.natural value)) from rfl]
      rw [proposition_subst,specialize_indices (codes predecessor (by simp)).valid,ih (fun p hp => codes p (by simp [hp]))]
      rfl

private theorem proposition_scoped {indices : List Expr} (codes : ∀ expr ∈ indices, Closed expr) :
    (propositionAt id (terms indices)).Scoped 0 := by
  apply Term.Scoped.nonbinding (by intro index; rfl)
  intro term included
  obtain ⟨expr,member,rfl⟩ := List.mem_map.mp included
  exact (codes expr member).scoped

private theorem telescope_scoped {predecessors : List (List Expr)} (codes : ∀ predecessor ∈ predecessors, IndexCode Closed arity predecessor)
    (resultCode : IndexCode Closed arity result) : (telescope id predecessors result).Scoped 0 := by
  induction predecessors with
  | nil => exact proposition_scoped resultCode.valid
  | cons predecessor rest ih =>
      refine Term.Scoped.node (fun position term selected => ?_)
      cases position with
      | zero =>
          cases selected
          exact proposition_scoped (codes predecessor (by simp)).valid
      | succ position =>
          cases position with
          | zero =>
              cases selected
              exact (ih (fun p hp => codes p (by simp [hp]))).monotone (by decide)
          | succ position => cases selected

private theorem specialized_code (valid : IndexCode Unary arity indices) (width : value < 2^64) :
    IndexCode Closed arity (specializeAt value indices) := by
  refine ⟨(List.length_map _).trans valid.size,?_⟩
  intro specialized included
  obtain ⟨original,found,rfl⟩ := List.mem_map.mp included
  exact specialize_closed (valid.valid original found) width

private theorem specialized_codes {predecessors : List (List Expr)} (codes : ∀ predecessor ∈ predecessors, IndexCode Unary arity predecessor)
    (width : value < 2^64) : ∀ specialized ∈ predecessors.map (specializeAt value), IndexCode Closed arity specialized := by
  intro specialized included
  obtain ⟨original,found,rfl⟩ := List.mem_map.mp included
  exact specialized_code (codes original found) width

private theorem evaluate_specialize (indices : List Expr) (value : Nat) : evaluate 0 (specializeAt value indices) = evaluate value indices := by
  simp only [evaluate,specializeAt,List.map_map]
  apply List.map_congr_left
  intro expression _
  exact specialize_eval expression value

theorem Family.index_formed (family : Family env id) (valid : IndexCode Closed family.entry.declaration.arity indices) :
    LoanTyping.HasType env [] [] true (propositionAt id (terms indices)) .prop := by
  have size : (terms indices).length = family.entry.declaration.arity := (List.length_map _).trans valid.size
  have formed : LoanTyping.HasType env [] [] true (propositionAt id (terms indices))
      (if family.entry.declaration.data then .univ 0 else .prop) := by
    refine .ind family.found size rfl ?_
    intro term included
    obtain ⟨expr,member,rfl⟩ := List.mem_map.mp included
    exact (valid.valid expr member).typed
  simpa only [family.proposition,Bool.false_eq_true,↓reduceIte] using formed

/-- Membership is generated by entries of the actual constructor table.
An erased recursive field contributes at its entire interpreted vector. -/
inductive Fiber (family : Nat) (entry : CheckedFamily) : List Nat → Prop where
  | base {constructor : Nat} (code : IndexCode Closed entry.declaration.arity result) :
      entry.signatures[constructor]? = some (baseSignature result) → Fiber family entry (evaluate 0 result)
  | branch {predecessors : List (List Expr)} {constructor value : Nat}
      (codes : ∀ p ∈ predecessors, IndexCode Unary entry.declaration.arity p)
      (resultCode : IndexCode Unary entry.declaration.arity result) :
      entry.signatures[constructor]? = some (branchSignature family predecessors result) → value < 2^64 →
      (∀ p ∈ predecessors, Fiber family entry (evaluate value p)) → Fiber family entry (evaluate value result)

def meaning (family : Family env id) (index : List Nat) : Finite.Universe .proposition :=
  .proposition (Fiber id family.entry index)

inductive ConstructorTree (family : Nat) (entry : CheckedFamily) : Term → Prop where
  | base (code : IndexCode Closed entry.declaration.arity result) :
      entry.signatures[constructor]? = some (baseSignature result) →
      ConstructorTree family entry (.node (.con family constructor 0) [])
  | branch {predecessors : List (List Expr)} {constructor value : Nat}
      (codes : ∀ p ∈ predecessors, IndexCode Unary entry.declaration.arity p)
      (resultCode : IndexCode Unary entry.declaration.arity result) :
      entry.signatures[constructor]? = some (branchSignature family predecessors result) → children.length = predecessors.length →
      (∀ child ∈ children, ConstructorTree family entry child) →
      ConstructorTree family entry (.node (.con family constructor (children.length+1)) (.natural value :: children))

theorem constructor_arguments (history : ScopedProgram.History definitions declarations env) (family : Family env id)
    (selected : family.entry.signatures[constructor]? = some signature)
    (typed : LoanTyping.HasType env [] ctx true (.node (.con id constructor count) arguments) type) :
    ∃ arity indices, LoanTyping.Arguments env [] ctx true family.entry.declaration.data (signatureTerm id signature)
      arguments (.node (.ind id arity) indices) ∧ RawLend.Conv env (.node (.ind id arity) indices) type := by
  obtain ⟨entry,actualSignature,arity,indices,found,actual,fields,converted⟩ := typed.principalView
  cases Option.some.inj (family.found.symm.trans found)
  cases Option.some.inj (selected.symm.trans actual)
  rw [Environment.closed_rename ((signature_metadata history family.found selected).1.signatureTerm_scoped id)] at fields
  exact ⟨arity,indices,fields,converted⟩

theorem tail_arguments {predecessors : List (List Expr)} (wf : UnifiedProgram.EnvWellFormed env)
    (codes : ∀ p ∈ predecessors, IndexCode Closed arity p) (resultCode : IndexCode Closed arity result)
    (size : children.length = predecessors.length)
    (arguments : LoanTyping.Arguments env [] ctx true data (telescope id predecessors result) children type) :
    RawLend.Conv env (propositionAt id (terms result)) type ∧
    (∀ {position : Nat} {p : List Expr}, predecessors[position]? = some p →
      ∃ child, children[position]? = some child ∧ LoanTyping.HasType env [] ctx true child (propositionAt id (terms p))) := by
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
          have later : ∀ p ∈ rest, IndexCode Closed arity p := fun p hp => codes p (by simp [hp])
          rw [Environment.closed_subst (telescope_scoped later resultCode)] at remainder
          obtain ⟨converted,other⟩ := ih later (Nat.succ.inj size) remainder
          refine ⟨converted,?_⟩
          intro position value found
          cases position with
          | zero => cases found; exact ⟨child,rfl,typed⟩
          | succ position => exact other found

/-- Recover each instantiated vector from the authentic `Arguments`
derivation, using native index conversion to match the requested result. -/
theorem ConstructorTree.sound {expected : List Expr} (history : ScopedProgram.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.HasType env [] ctx true term type)
    (requested : RawValue.Conv env type (propositionAt id (terms expected))) :
    Fiber id family.entry (evaluate 0 expected) := by
  let wf := history.wellFormed
  induction tree generalizing type expected with
  | @base result constructor code found =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_arguments history family found typed
      cases arguments with
      | nil resultType =>
          have aligned := index_conversion (scalar := 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
          rw [← aligned]
          exact .base code found
  | @branch result children predecessors constructor value codes resultCode found size _ ih =>
      obtain ⟨_,_,arguments,converted⟩ := constructor_arguments history family found typed
      change LoanTyping.Arguments env [] ctx true family.entry.declaration.data
        (.pi false .u64 (signatureTerm id (recursiveTail id 0 predecessors result))) (.natural value :: children) _ at arguments
      obtain ⟨valueTyped,remainder⟩ := arguments_pi_view wf arguments
      have width : value < 2^64 := natural_bound valueTyped
      change LoanTyping.Arguments env [] ctx true family.entry.declaration.data
        ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (single (.natural value)))) children _ at remainder
      rw [tail_specializes codes resultCode] at remainder
      obtain ⟨resultType,fields⟩ := tail_arguments wf (specialized_codes codes width) (specialized_code resultCode width)
        (size.trans (List.length_map _).symm) remainder
      have aligned := index_conversion (scalar := 0) wf ((RawValue.Conv.old (resultType.trans converted)).trans requested)
      rw [← aligned,evaluate_specialize]
      refine .branch codes resultCode found width ?_
      intro predecessor included
      obtain ⟨position,selected⟩ := List.mem_iff_getElem?.mp included
      obtain ⟨child,childFound,childTyped⟩ := fields (position := position) (p := specializeAt value predecessor)
        (by simp only [List.getElem?_map,selected,Option.map_some])
      rw [← evaluate_specialize predecessor value]
      exact ih child (List.mem_of_getElem? childFound) childTyped (.refl _)

private theorem ConstructorTree.head (tree : ConstructorTree id entry term) :
    ∃ constructor values, term = .node (.con id constructor values.length) values := by
  cases tree with
  | base => exact ⟨_,[],rfl⟩
  | branch => exact ⟨_,.natural _ :: _,rfl⟩

theorem ConstructorTree.pure_sound {expected : List Expr} (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (family : Family env id) (tree : ConstructorTree id family.entry term)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (requested : RawValue.Conv env type (propositionAt id (terms expected))) :
    Fiber id family.entry (evaluate 0 expected) := by
  obtain ⟨_,_,head⟩ := tree.head
  obtain ⟨_,native,conversion⟩ := native_constructor typed head
  exact tree.sound (ScopedProgram.History.ofPureMixed history) family native (conversion.trans requested)

theorem checked_global_carrier {declaration : GlobalDeclaration} {index : Nat} {expected : List Expr}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration) (tree : ConstructorTree id family.entry declaration.value)
    (requested : RawValue.Conv env declaration.type (propositionAt id (terms expected))) :
    Nonempty (Finite.Carrier (meaning family (evaluate 0 expected))) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  exact ⟨⟨⟨tree.pure_sound history family (history.global_value_and_reference found).1 requested⟩⟩⟩

theorem build_tail {family : Family env id} {predecessors : List (List Expr)} {recognized : Term → Prop}
    (codes : ∀ p ∈ predecessors, IndexCode Closed family.entry.declaration.arity p)
    (resultCode : IndexCode Closed family.entry.declaration.arity result)
    (realized : ∀ p ∈ predecessors, ∃ child,
      recognized child ∧ LoanTyping.HasType env [] [] true child (propositionAt id (terms p))) :
    ∃ children, children.length = predecessors.length ∧ (∀ child ∈ children, recognized child) ∧
      LoanTyping.Arguments env [] [] true family.entry.declaration.data (telescope id predecessors result) children
        (propositionAt id (terms result)) := by
  induction predecessors with
  | nil => exact ⟨[],rfl,(by simp),.nil (.refl _)⟩
  | cons predecessor rest ih =>
      obtain ⟨child,childTree,childTyped⟩ := realized predecessor (by simp)
      have later : ∀ p ∈ rest, IndexCode Closed family.entry.declaration.arity p := fun p hp => codes p (by simp [hp])
      obtain ⟨children,size,trees,arguments⟩ := ih later (fun p hp => realized p (by simp [hp]))
      refine ⟨child :: children,congrArg Nat.succ size,?_,.cons (.refl _) childTyped ?_⟩
      · intro field included
        rcases List.mem_cons.mp included with rfl | other
        · exact childTree
        · exact trees field other
      · change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((telescope id rest result).subst (single child)) children _
        rw [Environment.closed_subst (telescope_scoped later resultCode)]
        exact arguments

theorem constructor_typed (family : Family env id) (selected : family.entry.signatures[constructor]? = some signature)
    (arguments : LoanTyping.Arguments env [] [] true family.entry.declaration.data (signatureTerm id signature) fields
      (propositionAt id indices)) :
    LoanTyping.HasType env [] [] true (.node (.con id constructor fields.length) fields) (propositionAt id indices) := by
  apply LoanTyping.HasType.con family.found selected rfl
  change LoanTyping.Arguments env [] [] true family.entry.declaration.data
    ((signatureTerm id signature).rename _root_.id) fields _
  rwa [Term.rename_id]

structure Realization (family : Family env id) (index : List Nat) where
  expressions : List Expr
  code : IndexCode Closed family.entry.declaration.arity expressions
  evaluated : evaluate 0 expressions = index
  term : Term
  tree : ConstructorTree id family.entry term
  typed : LoanTyping.HasType env [] [] true term (propositionAt id (terms expressions))

/-- Rebuild actual constructor arguments from the least carrier, matching
each child at every component of its substituted index vector. -/
theorem Fiber.reify (family : Family env id) (inhabited : Fiber id family.entry index) : Nonempty (Realization family index) := by
  induction inhabited with
  | @base result constructor code found =>
      exact ⟨⟨result,code,rfl,.node (.con id constructor 0) [],.base code found,
        constructor_typed family found (.nil (.refl _))⟩⟩
  | @branch result predecessors constructor value codes resultCode found width _ ih =>
      have resultClosed := specialized_code resultCode width
      have got : ∀ specialized ∈ predecessors.map (specializeAt value), ∃ child,
          ConstructorTree id family.entry child ∧ LoanTyping.HasType env [] [] true child (propositionAt id (terms specialized)) := by
        intro specialized included
        obtain ⟨predecessor,foundPredecessor,rfl⟩ := List.mem_map.mp included
        obtain ⟨child⟩ := ih predecessor foundPredecessor
        have alignment := closed_index_conversion (env := env) (id := id) child.code
          (specialized_code (codes predecessor foundPredecessor) width)
          (child.evaluated.trans (evaluate_specialize predecessor value).symm)
        exact ⟨child.term,child.tree,.convert child.typed alignment⟩
      obtain ⟨children,size,trees,arguments⟩ := build_tail (family := family) (specialized_codes codes width) resultClosed got
      have native : LoanTyping.Arguments env [] [] true family.entry.declaration.data
          (signatureTerm id (branchSignature id predecessors result)) (.natural value :: children)
          (propositionAt id (terms (specializeAt value result))) := by
        change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          (.pi false .u64 (signatureTerm id (recursiveTail id 0 predecessors result))) (.natural value :: children) _
        refine .cons (.refl _) (.natural width) ?_
        change LoanTyping.Arguments env [] [] true family.entry.declaration.data
          ((signatureTerm id (recursiveTail id 0 predecessors result)).subst (liftSub 0 (single (.natural value)))) children _
        rw [tail_specializes codes resultCode]
        exact arguments
      exact ⟨⟨specializeAt value result,resultClosed,evaluate_specialize result value,
        .node (.con id constructor (children.length+1)) (.natural value :: children),
        .branch codes resultCode found (size.trans (List.length_map _)) trees,constructor_typed family found native⟩⟩

theorem Realization.elimination_typed {family : Family env id} (input : Realization family index)
    (motiveTyped : LoanTyping.HasType env [] [] true motive (propMotiveType family.entry.declaration.arity))
    (branches : LoanTyping.Cases env [] [] motive family.entry.signatures cases) :
    LoanTyping.HasType env [] [] true (elimTerm id motive cases input.term) (applications motive (terms input.expressions)) := by
  have scrub := input.typed
  have arity : (terms input.expressions).length = family.entry.declaration.arity := (List.length_map _).trans input.code.size
  rw [propositionAt,arity] at scrub
  exact .propElim family.found family.proposition motiveTyped branches scrub

theorem Realization.elimination_contracts {family : Family env id} (input : Realization family index)
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

theorem checked_cases {family : Family env id} (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (source : term = elimTerm id motive cases scrutinee) :
    LoanTyping.HasType env [] ctx true motive (propMotiveType family.entry.declaration.arity) ∧
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
      · exact ⟨motiveTyped,branches⟩
      · rw [family.proposition] at data
        contradiction
  | convert _ _ _ ih => exact ih source
  | pi | lam | app => cases source

theorem Fiber.semantic_elimination (family : Family env id) (inhabited : Fiber id family.entry index)
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

/-- Exact-byte admission supplies the complete native `Elim` and `Cases`
derivations for eliminating into a supported proposition at a vector index. -/
theorem checked_global_eliminates {declaration : GlobalDeclaration} {index : Nat}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (family : Family env id) (found : env.globals[index]? = some declaration)
    (source : declaration.value = elimTerm id motive cases scrutinee)
    (inhabited : Fiber id family.entry indices) (result : Code [] .proposition)
    (aligned : ∀ input : Realization family indices, RawValue.Conv env (applications motive (terms input.expressions)) result.syntax)
    (covered : ∀ (input : Realization family indices) residual,
      Environment.FamilyIota.contract env (elimTerm id motive cases input.term) = some residual →
      MultiUniverse.DependentCodes.FamilyProofs.Tree env residual result)
    (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    Nonempty (Finite.Carrier (result.meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := family) (history.global_value_and_reference found).1 source
  exact Fiber.semantic_elimination family inhabited history motiveTyped branches result aligned covered assignment

section Example

open LoanTyping.PureFamilyArithmeticReplay (observe? observed_fundamental)

private def leftVector : List Expr := [.var 0,.add (.var 0) (.literal 1)]
private def rightVector : List Expr := [.add (.var 0) (.literal 1),.add (.var 0) (.literal 2)]
private def resultVector : List Expr := [.add (.var 0) (.literal 2),.add (.var 0) (.literal 3)]
private def leftBaseVector : List Expr := [.literal 0,.literal 1]
private def rightBaseVector : List Expr := [.literal 1,.literal 2]
private def branching : Signature := branchSignature 0 [leftVector,rightVector] resultVector
private def decl : FamilyDeclaration := ⟨false,0,2,
  [propositionAt 0 (terms leftBaseVector),propositionAt 0 (terms rightBaseVector),signatureTerm 0 branching],0⟩
private def table : CheckedFamily := ⟨decl,[baseSignature leftBaseVector,baseSignature rightBaseVector,branching],false⟩
private def zero : Term := .natural 0
private def one : Term := .natural 1
private def two : Term := .natural 2
private def three : Term := .natural 3
private def successor (index : Term) : Term := .uadd index one
private def shiftedByTwo (index : Term) : Term := .uadd index two
private def increasing (index : Term) : Term := .lt index (successor index)
private def pairMotive : Term := .lam false .u64 (.lam false .u64 (.lt (.var 1) (.var 0)))
private def leftEvidence : Term := .zeroLe zero
private def rightEvidence : Term := .ltAdd zero one one leftEvidence
private def branchEvidence (index leftProof rightProof : Term) : Term :=
  .ltLe (shiftedByTwo index) (shiftedByTwo (successor index)) (shiftedByTwo (successor index))
    (.ltAdd index (successor index) two leftProof)
    (.ltAdd (successor index) (successor (successor index)) two rightProof)
private def branch : Term := .lam false .u64
  (.lam true (propositionAt 0 [.var 0,successor (.var 0)])
    (.lam true (propositionAt 0 [successor (.var 1),shiftedByTwo (.var 1)])
      (.lam true (increasing (.var 2))
        (.lam true (.lt (successor (.var 3)) (shiftedByTwo (.var 3))) (branchEvidence (.var 4) (.var 1) (.var 0))))))
private def arms : List Term := [leftEvidence,rightEvidence,branch]
private def leftChild : Term := .node (.con 0 0 0) []
private def rightChild : Term := .node (.con 0 1 0) []
private def constructorProof : Term := .node (.con 0 2 3) [zero,leftChild,rightChild]
private def inputSource : GlobalDeclaration := ⟨propositionAt 0 [two,three],constructorProof⟩
private def elimSource : GlobalDeclaration := ⟨.lt two three,elimTerm 0 pairMotive arms constructorProof⟩
private def world : Environment := ⟨#[inputSource,elimSource],#[table]⟩
private def family : Family world 0 := ⟨table,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private theorem pair_codes {α : Type} {valid : α → Prop} {first second : α}
    (left : valid first) (right : valid second) : ∀ x ∈ [first,second], valid x :=
  List.forall_mem_cons.mpr ⟨left,List.forall_mem_cons.mpr ⟨right,(by simp)⟩⟩

private theorem leftVectorCode : IndexCode Unary 2 leftVector :=
  ⟨rfl,pair_codes (.var .here) (.add (.var .here) (.literal (by decide)))⟩

private theorem shiftedCode (first second : Nat) (lo : first < 2^64) (hi : second < 2^64) :
    IndexCode Unary 2 [.add (.var 0) (.literal first),.add (.var 0) (.literal second)] :=
  ⟨rfl,pair_codes (.add (.var .here) (.literal lo)) (.add (.var .here) (.literal hi))⟩

private theorem literalCode (first second : Nat) (lo : first < 2^64) (hi : second < 2^64) :
    IndexCode Closed 2 [.literal first,.literal second] :=
  ⟨rfl,pair_codes (.literal lo) (.literal hi)⟩

private theorem predecessorCodes : ∀ p ∈ [leftVector,rightVector], IndexCode Unary 2 p :=
  pair_codes leftVectorCode (shiftedCode 1 2 (by decide) (by decide))

private theorem exampleTree : ConstructorTree 0 table constructorProof := by
  refine .branch (result := resultVector) (children := [leftChild,rightChild]) (constructor := 2) (value := 0)
    predecessorCodes (shiftedCode 2 3 (by decide) (by decide)) rfl rfl ?_
  exact pair_codes (.base (result := leftBaseVector) (constructor := 0) (literalCode 0 1 (by decide) (by decide)) rfl)
    (.base (result := rightBaseVector) (constructor := 1) (literalCode 1 2 (by decide) (by decide)) rfl)

/-- A genuinely binary family is checked with distinct subproofs at [0,1]
and [1,2]. Its checked elimination uses both generated induction hypotheses
and computes proof evidence of the motive at [2,3]. -/
theorem checked_binary_indices :
    LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [decl] = some world ∧
    Nonempty (Realization family [2,3]) ∧
    observe? world [] 48 16 16 4096 10 elimSource.value = some (branchEvidence zero leftEvidence rightEvidence) ∧
    PureArithmetic.UniversalTruth world elimSource.type := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [inputSource,elimSource] [decl] = some world := by cbv
  have executed : observe? world [] 48 16 16 4096 10 elimSource.value = some (branchEvidence zero leftEvidence rightEvidence) := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  have inputTyped := (history.global_value_and_reference (index := 0) (declaration := inputSource) rfl).1
  have elimTyped := (history.global_value_and_reference (index := 1) (declaration := elimSource) rfl).1
  have inhabited := exampleTree.pure_sound (expected := [.literal 2,.literal 3]) history family inputTyped (.refl _)
  exact ⟨admitted,Fiber.reify family inhabited,executed,observed_fundamental history elimTyped executed⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Vectors
