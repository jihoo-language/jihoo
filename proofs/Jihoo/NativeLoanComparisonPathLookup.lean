import Jihoo.NativeLoanComparisonBinderPaths

/-! A native comparison path selects typed retained occurrences under
products, lambdas, applications, unary types, and erased Strict prefixes. Selection
uses child positions in the compared shape and recovers source binders. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

open NativeArena
open NativeCoreCompare (Shape project projectArgs syntaxView conversionChildren FullyRetained)

private def chooseChild : Nat → Term → Option (Term × Option Binding)
  | 0,.pi _ domain _ | 0,.lam _ domain _ => some (domain,none)
  | 1,.pi erased domain body | 1,.lam erased domain body => some (body,some ⟨domain,erased⟩)
  | 0,.app function _ => some (function,none)
  | 1,.app _ argument => some (argument,none)
  | 0,.array argument | 0,.buffer argument | 0,.ref argument | 0,.refine argument => some (argument,none)
  | _,_ => none

private def childAt (index : Nat) (shape : Shape) : Option Shape :=
  match shape with
  | .node _ children => children[index]?

def followShape : Shape → List Nat → Option Shape
  | shape,[] => some shape
  | shape,index :: path => (childAt index shape).bind (fun child => followShape child path)

/-- Strict prefixes have no identity-path position. Skipping a prefix
consumes source traversal fuel and never adds a binder. -/
def follow : Nat → Term → List Nat → Option (List Binding × Term)
  | 0,_,_ => none
  | fuel+1,term,path =>
    match term with
    | .strict _ result => follow fuel result path
    | _ =>
      match path with
      | [] => some ([],term)
      | index :: rest => do
        let (child,binding) ← chooseChild index term
        let (entered,selected) ← follow fuel child rest
        pure (entered ++ binding.toList,selected)

private theorem step_focus (found : chooseChild index source = some (child,binding)) :
    (∀ entered selected, Focus child entered selected → Focus source (entered ++ binding.toList) selected) ∧
      childAt index (project source) = some (project child) := by
  fun_cases chooseChild index source <;> simp only [chooseChild,reduceCtorEq,Option.some.injEq,Prod.mk.injEq] at found
  all_goals
    obtain ⟨rfl,rfl⟩ := found
    refine ⟨?_,?_⟩
    · intro entered selected held
      first
      | simpa only [Option.toList_none,List.append_nil] using (Focus.piDomain held)
      | exact .piBody held
      | simpa only [Option.toList_none,List.append_nil] using (Focus.lambdaDomain held)
      | exact .lambdaBody held
      | simpa only [Option.toList_none,List.append_nil] using (Focus.function held)
      | simpa only [Option.toList_none,List.append_nil] using (Focus.argument held)
      | simpa only [Option.toList_none,List.append_nil] using (Focus.typeArgument .array held)
      | simpa only [Option.toList_none,List.append_nil] using (Focus.typeArgument .buffer held)
      | simpa only [Option.toList_none,List.append_nil] using (Focus.typeArgument .reference held)
      | simpa only [Option.toList_none,List.append_nil] using (Focus.typeArgument .refinement held)
    · simp only [project,projectArgs,syntaxView,conversionChildren,reduceCtorEq,ite_false] <;> rfl

private theorem strict_project (effect result : Term) : project (.strict effect result) = project result := by
  simp only [project,projectArgs,syntaxView,ite_true] <;> rfl

/-- Each successful executable path builds a source derivation of focus
and follows the identical path in the projected comparison shape. -/
theorem follow_sound (found : follow fuel term path = some (bindings,selected)) :
    Focus term bindings selected ∧ followShape (project term) path = some (project selected) := by
  induction fuel generalizing term path bindings selected with
  | zero => cases found
  | succ fuel ih =>
    unfold follow at found
    split at found
    · rename_i effect result
      obtain ⟨focused,kept⟩ := ih found
      exact ⟨.strictTail focused,by simpa only [strict_project] using kept⟩
    · cases path with
      | nil =>
        cases found
        exact ⟨.root,rfl⟩
      | cons index path =>
        obtain ⟨⟨child,binding⟩,chosen,rest⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨⟨entered,term⟩,read,returned⟩ := Option.bind_eq_some_iff.mp rest
        cases returned
        obtain ⟨step,projected⟩ := step_focus chosen
        obtain ⟨focused,kept⟩ := ih read
        exact ⟨step _ _ focused,by simp only [followShape,projected,Option.bind_some,kept]⟩

/-- Live comparison supplies the common projected occurrence. The executable
lookup recovers typing at each side's original binder context. -/
theorem live_identity_typed_occurrences
    (firstRep : Represents arena leftRoot left) (secondRep : Represents arena rightRoot right)
    (compared : NativeCoreIdentical.runArena arena limit depth initial leftRoot rightRoot = (.ok true,steps))
    (firstPath : follow firstFuel left path = some (leftBinders,first))
    (secondPath : follow secondFuel right path = some (rightBinders,second))
    (firstTyped : HasType env leftLoans leftContext leftMode left leftType)
    (secondTyped : HasType env rightLoans rightContext rightMode right rightType) :
    project first = project second ∧
      (∃ firstType,HasType env [] (leftBinders ++ leftContext) true first firstType) ∧
      (∃ secondType,HasType env [] (rightBinders ++ rightContext) true second secondType) := by
  obtain ⟨leftFocus,firstSeen⟩ := follow_sound firstPath
  obtain ⟨rightFocus,secondSeen⟩ := follow_sound secondPath
  have same := (NativeCoreIdentical.runArena_refines firstRep secondRep compared).mp rfl
  rw [same] at firstSeen
  exact ⟨Option.some.inj (firstSeen.symm.trans secondSeen),leftFocus.checked_occurrence firstTyped,
    rightFocus.checked_occurrence secondTyped⟩

/-- An identity comparison in the live graph supplies the ignored proofs
under the binders actually visited along its retained path. Compatible
contexts and fully retained operands place both proofs in one proposition. -/
theorem live_identity_path_common_proposition
    (wf : UnifiedProgram.EnvWellFormed env)
    (firstRep : Represents arena leftRoot left) (secondRep : Represents arena rightRoot right)
    (compared : NativeCoreIdentical.runArena arena limit depth initial leftRoot rightRoot = (.ok true,steps))
    (firstPath : follow firstFuel left path = some (leftBinders,.node firstOp [a,b,firstProof]))
    (secondPath : follow secondFuel right path = some (rightBinders,.node secondOp [a',b',secondProof]))
    (firstTyped : HasType env leftLoans leftContext leftMode left leftType)
    (secondTyped : HasType env rightLoans rightContext rightMode right rightType)
    (aligned : Ghost.ContextConversion env (rightBinders ++ rightContext) (leftBinders ++ leftContext))
    (firstField : IgnoredProposition firstOp a b A) (secondField : IgnoredProposition secondOp a' b' B)
    (firstKept : FullyRetained a ∧ FullyRetained b) (secondKept : FullyRetained a' ∧ FullyRetained b') :
    A = B ∧ HasEvidence env (leftBinders ++ leftContext) A firstProof ∧
      HasType env [] (leftBinders ++ leftContext) true secondProof A := by
  obtain ⟨projected,⟨_,first⟩,⟨_,second⟩⟩ := live_identity_typed_occurrences firstRep secondRep compared
    firstPath secondPath firstTyped secondTyped
  obtain ⟨same,formed,leftEvidence,rightEvidence⟩ := projected_common_proposition firstField secondField
    (.native first) (.native (second.ghostContext wf aligned)) firstKept secondKept projected
  exact ⟨same,⟨formed,leftEvidence⟩,rightEvidence⟩


open ACU.Canonical (rank payload)

def bindingShape (binding : Binding) : Bool × Shape := (binding.erased,project binding.ty)

private def bindAt (index : Nat) : Shape → Option (Bool × Shape)
  | .node head (domain :: _) =>
    if index = 1 ∧ (head.1 = rank (.pi false) ∨ head.1 = rank (.lam false)) then
      some (head.2 == payload (.pi true),domain)
    else none
  | .node _ [] => none

/-- Comparison's shape contains the domain and erasure of each visited
binder. The source traversal and shape traversal keep de Bruijn order. -/
def followScope : Shape → List Nat → Option (List (Bool × Shape))
  | _,[] => some []
  | shape,index :: path => do
    let child ← childAt index shape
    let tail ← followScope child path
    pure (tail ++ (bindAt index shape).toList)

private theorem chosen_binding (found : chooseChild index term = some (child,binding)) :
    bindAt index (project term) = binding.map bindingShape := by
  fun_cases chooseChild index term <;> simp only [chooseChild,reduceCtorEq,Option.some.injEq,Prod.mk.injEq] at found
  all_goals
    obtain ⟨rfl,rfl⟩ := found
    simp only [project,projectArgs,syntaxView,conversionChildren,reduceCtorEq,ite_false] <;> try rfl
  all_goals
    rename_i erased domain body
    cases erased <;> rfl

/-- Every binding created by following the selected source occurrence is
present in the projected comparison shape with its original domain. -/
theorem follow_scope (found : follow fuel term path = some (bindings,selected)) :
    followScope (project term) path = some (bindings.map bindingShape) := by
  induction fuel generalizing term path bindings selected with
  | zero => cases found
  | succ fuel ih =>
    unfold follow at found
    split at found
    · rw [strict_project]
      exact ih found
    · cases path with
      | nil => cases found; rfl
      | cons index path =>
        obtain ⟨⟨child,binding⟩,chosen,rest⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨⟨entered,term⟩,read,returned⟩ := Option.bind_eq_some_iff.mp rest
        cases returned
        have body := (step_focus chosen).2
        have scope := ih read
        have optional : (binding.map bindingShape).toList = binding.toList.map bindingShape := by cases binding <;> rfl
        simp [followScope,body,scope,List.map_append,chosen_binding chosen,optional,Bind.bind,Option.bind,Pure.pure]

private theorem same_scope {left right : List Binding}
    (shapes : left.map bindingShape = right.map bindingShape)
    (keptLeft : ∀ binding ∈ left,FullyRetained binding.ty)
    (keptRight : ∀ binding ∈ right,FullyRetained binding.ty) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at shapes ⊢
  | cons before tail ih =>
    cases right with
    | nil => simp at shapes
    | cons after rest =>
      simp only [List.map_cons,List.cons.injEq] at shapes
      have flags := (Prod.mk.inj shapes.1).1
      have domain := NativeCoreCompare.project_injective_of_fully_retained
        (keptLeft before (.head _)) (keptRight after (.head _)) (Prod.mk.inj shapes.1).2
      have same : before = after := by
        cases before
        cases after
        cases flags
        cases domain
        rfl
      have tails := ih shapes.2 (fun b present => keptLeft b (.tail _ present))
        (fun b present => keptRight b (.tail _ present))
      rw [same,tails]

/-- A single accepted live comparison derives equality of the dispatched
source binder contexts when it retains every domain on that path in full. -/
theorem live_identity_path_scope
    (firstRep : Represents arena leftRoot left) (secondRep : Represents arena rightRoot right)
    (compared : NativeCoreIdentical.runArena arena limit depth initial leftRoot rightRoot = (.ok true,steps))
    (firstPath : follow firstFuel left path = some (leftBinders,first))
    (secondPath : follow secondFuel right path = some (rightBinders,second))
    (firstKept : ∀ binding ∈ leftBinders,FullyRetained binding.ty)
    (secondKept : ∀ binding ∈ rightBinders,FullyRetained binding.ty) : leftBinders = rightBinders := by
  have same := (NativeCoreIdentical.runArena_refines firstRep secondRep compared).mp rfl
  have leftSeen := follow_scope firstPath
  have rightSeen := follow_scope secondPath
  rw [same] at leftSeen
  exact same_scope (Option.some.inj (leftSeen.symm.trans rightSeen)) firstKept secondKept


/-- With a common starting context, the accepted graph identity supplies
both scope alignment and the common proposition for the omitted proofs. -/
theorem live_identity_path_common_proposition_in_context
    (wf : UnifiedProgram.EnvWellFormed env)
    (firstRep : Represents arena leftRoot left) (secondRep : Represents arena rightRoot right)
    (compared : NativeCoreIdentical.runArena arena limit depth initial leftRoot rightRoot = (.ok true,steps))
    (firstPath : follow firstFuel left path = some (leftBinders,.node firstOp [a,b,firstProof]))
    (secondPath : follow secondFuel right path = some (rightBinders,.node secondOp [a',b',secondProof]))
    (firstTyped : HasType env leftLoans ctx leftMode left leftType)
    (secondTyped : HasType env rightLoans ctx rightMode right rightType)
    (leftDomains : ∀ binding ∈ leftBinders,FullyRetained binding.ty)
    (rightDomains : ∀ binding ∈ rightBinders,FullyRetained binding.ty)
    (firstField : IgnoredProposition firstOp a b A) (secondField : IgnoredProposition secondOp a' b' B)
    (firstKept : FullyRetained a ∧ FullyRetained b) (secondKept : FullyRetained a' ∧ FullyRetained b') :
    A = B ∧ HasEvidence env (leftBinders ++ ctx) A firstProof ∧
      HasType env [] (leftBinders ++ ctx) true secondProof A := by
  have shared := live_identity_path_scope firstRep secondRep compared firstPath secondPath leftDomains rightDomains
  subst rightBinders
  exact live_identity_path_common_proposition wf firstRep secondRep compared firstPath secondPath firstTyped secondTyped
    (Ghost.ContextConversion.refl env _) firstField secondField firstKept secondKept

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence.Examples

open NativeArena
open NativeCoreCompare (FullyRetained)

private def zeroWord : Term := .natural 0
private def oneWord : Term := .natural 1
private def linearProof : Term := .zeroLe zeroWord
private def computedProof : Term := .decide zeroWord oneWord
private def subtraction (evidence : Term) : Term := .usub zeroWord zeroWord evidence
private def sizeBound : Term := .lt zeroWord (.uadd zeroWord oneWord)

private def bufferArena : Arena := #[
  .node (.natural 0) [],.node (.natural 1) [],.node .zeroLe [0],.node .decide [0,1],
  .node .usub [0,0,2],.node .usub [0,0,3],.node .buffer [4],.node .buffer [5]]

/-- The real comparison skips the two different proofs in the retained
dependent Buffer length. The checked path recovers their same bound. -/
theorem checked_buffer_lengths_share_bound :
    NativeCoreIdentical.runArena bufferArena 4 16 0 6 7 = (.ok true,4) ∧
      HasEvidence .empty [] sizeBound linearProof ∧
      HasType .empty [] [] true computedProof sizeBound := by
  have compared : NativeCoreIdentical.runArena bufferArena 4 16 0 6 7 = (.ok true,4) := by cbv
  have left : HasType .empty [] [] true (.buffer (subtraction linearProof)) (.univ 0) :=
    Checker.infer_sound (fuel := 64) (by cbv)
  have right : HasType .empty [] [] true (.buffer (subtraction computedProof)) (.univ 0) :=
    Checker.infer_sound (fuel := 64) (by cbv)
  have leftRep : Represents bufferArena 6 (.buffer (subtraction linearProof)) := decode_sound (fuel := 12) rfl
  have rightRep : Represents bufferArena 7 (.buffer (subtraction computedProof)) := decode_sound (fuel := 12) rfl
  have kept : FullyRetained zeroWord := .node (by decide) rfl rfl (by simp)
  obtain ⟨_,first,second⟩ := live_identity_path_common_proposition_in_context
    UnifiedProgram.EnvWellFormed.empty leftRep rightRep compared
    (firstFuel := 2) (secondFuel := 2) (path := [0]) (leftBinders := []) (rightBinders := [])
    rfl rfl left right (by simp) (by simp) IgnoredProposition.subtract IgnoredProposition.subtract
    ⟨kept,kept⟩ ⟨kept,kept⟩
  exact ⟨compared,first,second⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence.Examples
