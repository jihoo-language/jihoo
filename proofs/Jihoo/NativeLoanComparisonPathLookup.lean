import Jihoo.NativeLoanComparisonBinderPaths

/-! A native comparison path selects typed retained occurrences under
products, lambdas, applications, and erased Strict prefixes. Selection
uses child positions in the compared shape and recovers source binders. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

open NativeArena
open NativeCoreCompare (Shape project projectArgs syntaxView conversionChildren FullyRetained)

private def chooseChild : Nat → Term → Option (Term × Option Binding)
  | 0,.pi _ domain _ | 0,.lam _ domain _ => some (domain,none)
  | 1,.pi erased domain body | 1,.lam erased domain body => some (body,some ⟨domain,erased⟩)
  | 0,.app function _ => some (function,none)
  | 1,.app _ argument => some (argument,none)
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

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence
