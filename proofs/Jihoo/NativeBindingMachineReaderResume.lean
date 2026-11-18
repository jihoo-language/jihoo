import Jihoo.NativeBindingMachineLendResources

namespace Jihoo.NativeKernel

private theorem resume_subst_strict (first rest : Term) (values : Nat → Term) :
    (Term.strict first rest).subst values = .strict (first.subst values) (rest.subst values) := by
  simp only [Term.subst,substArgs,Op.binders,liftSub]

end Jihoo.NativeKernel

/-! Resume a named outer Borrow after an inner reader returns. The actual
dependent resource check supplies the specialized continuation's source
permission; the old slots and reachable reader inventory supply its concrete
owner and still-live outer token. No post-close slot or heap-guard certificate
is assumed. This local result does not reconstruct every input invariant from
closed mixed-program admission. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def StrictFirst (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .strict first _ => ∃ type, HasType env loans ctx mode first type
  | _ => True

theorem HasType.strict_first (typed : HasType env loans ctx mode (.strict first rest) type) :
    ∃ firstType, HasType env loans ctx mode first firstType := by
  have general : ∀ {term type}, HasType env loans ctx mode term type →
      StrictFirst env loans ctx mode term := by
    intro term type source
    apply HasType.rec (t := source)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack context ghost expression _ _ => StrictFirst env stack context ghost expression)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | assumption | skip
    case strict => exact ⟨_,by assumption⟩
    case dataElim => split <;> trivial
  exact general typed

theorem HasType.strict_tail (typed : HasType env loans ctx mode (.strict first rest) type) :
    HasType env loans ctx mode rest type := by
  obtain ⟨result,restTyped,converted⟩ := typed.principalView
  exact restTyped.convert converted

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Source permission comes from the actual specialized checked body, including
the two retained continuation binders. No generic callback typing is requested. -/
theorem checked_continuation_outer_borrow
    (entered : Loans.Entered ctx.length loans)
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.strict (.borrow (.var (outer+2))) tail)))) = some control) :
    Loans.active ctx.length loans outer = true := by
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := dependent_project_contract checked
  have original : (Term.var (outer+2)).subst (single ((Term.var owner).rename Nat.succ)) =
      .var (outer+1) := by simp only [Term.subst,single]
  rw [resume_subst_strict,subst_borrow,original] at bodyTyped
  obtain ⟨firstType,borrowTyped⟩ := bodyTyped.strict_first
  obtain ⟨index,same,active⟩ := borrowTyped.code_borrow_named
  have indexSame : outer+1 = index := Term.var.inj same
  rw [← indexSame] at active
  simpa only [List.length_cons,Loans.active_weaken entered] using active

theorem checked_continuation_returned_owner_borrow
    (entered : Loans.Entered ctx.length loans)
    (checked : project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.strict (.borrow (.var 0)) tail)))) = some control) :
    Loans.active ctx.length loans owner = true := by
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := dependent_project_contract checked
  rw [resume_subst_strict,subst_borrow,restored_returned_owner] at bodyTyped
  obtain ⟨firstType,borrowTyped⟩ := bodyTyped.strict_first
  obtain ⟨index,same,active⟩ := borrowTyped.code_borrow_named
  have indexSame : owner+1 = index := Term.var.inj same
  rw [← indexSame] at active
  simpa only [List.length_cons,Loans.active_weaken entered] using active

/-- Returning the owner creates no new code-Borrow authority. In particular,
closing its final source reader rejects reborrowing through either alias. -/
theorem no_checked_continuation_reborrow
    (entered : Loans.Entered ctx.length loans)
    (inactive : Loans.active ctx.length loans owner = false)
    (selected : index = 0 ∨ index = owner+2) :
    project (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.strict (.borrow (.var index)) tail)))) ≠ some control := by
  intro checked
  have active : Loans.active ctx.length loans owner = true := by
    rcases selected with rfl | rfl
    · exact checked_continuation_returned_owner_borrow entered checked
    · exact checked_continuation_outer_borrow entered checked
  rw [inactive] at active
  cases active

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

set_option linter.unusedSimpArgs false in
private theorem close_resume_eight_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object)
    (stored : code.values[outer]? = some (some (.owner outerObject)))
    (found : activeLease (code.context.length-outer) outerObject stack = some outerToken)
    (outerLease : (SizedBufferHeap.close heap token).heap.lease outerToken = some outerObject)
    (first again tail ownerOrigin resultOrigin : Term) (result : Value) (name : Option Nat) :
    let body := Term.strict (.borrow (.var (outer+2))) tail
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object result
    run 8 ⟨heap,.returned result,
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      ⟨⟨SizedBufferHeap.close heap token,.evaluate (bodyCode.child tail),stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,
          .activate false body ownerOrigin],8⟩ := by
  have key : code.context.length+1+1-(outer+2) = code.context.length-outer := by omega
  simp only [run,step,action,returnAction,execute,leased,↓reduceIte,evaluateAction,
    Code.child,applyValue,enter,restoredContinuation,Option.map_some,List.getElem?_cons_succ,
    List.length_cons,key,stored,borrowLease,Option.orElse_some,activeLease,readerFor,Frame.reader?,bind,Option.bind,
    Option.orElse_none,found,outerLease]
  rfl

/-- An actual inner-reader return resumes source-authorized outer borrowing.
The outer token is distinct and survives the close; both binding activations
and Borrow execute, then the original-type continuation tail is entered. -/
theorem reachable_checked_reader_resume (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again (.strict (.borrow (.var (outer+2))) tail))))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned result)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        ((Lending.read (.var owner) readerBody).subst code.origins)
        (code.child (.lam false first (.lam false again (.strict (.borrow (.var (outer+2))) tail)))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let body := Term.strict (.borrow (.var (outer+2))) tail
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (Lending.read (.var owner) readerBody).subst code.origins
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object result
    ∃ outerToken outerObject,
      outerToken ≠ token ∧
      (SizedBufferHeap.close heap token).heap.lease outerToken = some outerObject ∧
      (SizedBufferHeap.close heap token).heap.live outerObject = true ∧
      LoanSlots (bodyCode.child tail) loans stack ∧
      LoanTyping.HasType env [] [] true (bodyCode.child tail).origin type ∧
      run 8 (run fuel (initial term)).state =
        ⟨⟨SizedBufferHeap.close heap token,.evaluate (bodyCode.child tail),stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin],8⟩ := by
  have permitted := LoanTyping.ResourceQuantity.checked_continuation_outer_borrow entered (shape ▸ checked)
  obtain ⟨outerObject,stored,present⟩ := slots outer permitted
  obtain ⟨outerToken,found⟩ := activeLease_complete present
  obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have remaining := inventory.finish.2
  have outerLease := remaining.live _ (List.mem_filterMap.mpr ⟨frame,member,descriptor⟩)
  have different : outerToken ≠ token := by
    intro same
    subst outerToken
    simp [SizedBufferHeap.close,HeapLeases.put] at outerLease
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  have original := typed_explicit_continuation_origin history typed shape object result
  change LoanTyping.HasType env [] [] true
    ((Term.strict (.borrow (.var (outer+2))) tail).subst
      (consValues ((Term.var owner).subst code.origins)
        (consValues ((Lending.read (.var owner) readerBody).subst code.origins) code.origins))) type at original
  rw [resume_subst_strict] at original
  refine ⟨outerToken,outerObject,different,outerLease,(valid.leased _ _ outerLease).2,
    (restored_continuation_loans code slots entered _ _ _ _ _ _ _).child tail,original.strict_tail,?_⟩
  have executed := close_resume_eight_steps (run fuel (initial term)).state.heap code
    leased stored found outerLease first again tail ((Term.var owner).subst code.origins)
    ((Lending.read (.var owner) readerBody).subst code.origins) result name
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned result,
        .lendFinish token object name ((Term.var owner).subst code.origins)
          ((Lending.read (.var owner) readerBody).subst code.origins)
          (code.child (.lam false first (.lam false again (.strict (.borrow (.var (outer+2))) tail)))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  dsimp only at executed
  rw [← stateShape] at executed
  exact executed

end Jihoo.NativeKernel.Environment.BindingMachine
