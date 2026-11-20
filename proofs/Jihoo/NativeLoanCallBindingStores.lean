import Jihoo.NativeLoanQuantityOrigins
import Jihoo.NativeBindingMachineLoanTyping
import Jihoo.NativeCallResourceContracts
import Jihoo.NativeExactClosing
import Jihoo.NativeLoanBorrowedBudget

/-! The actual loan resource projection retains both the complete leading
source telescope and the replay that authenticates its supplied arguments.
Closing the telescope keeps the binder context of the original body. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes
variable {control : Control}

/-- The source lambdas taken by `openHead` have their written domains and
resolved modes. The unapplied tail may be a computed function expression. -/
inductive OpenedLambdas (env : Environment) (loans : Loans.Stack) :
    Context → Term → List Term → Opened → Prop where
  | done : OpenedLambdas env loans ctx head supplied ⟨ctx,[],head⟩
  | cons : Resolved env loans ctx erased domain mode →
      OpenedLambdas env loans (⟨domain,erased⟩ :: ctx) body arguments rest →
      OpenedLambdas env loans ctx (.lam erased domain body) (argument :: arguments)
        ⟨rest.context,mode :: rest.modes,rest.body⟩

theorem openHead_lambdas (opened : openHead fuel env loans ctx head supplied = some result) :
    OpenedLambdas env loans ctx head supplied result := by
  induction fuel generalizing ctx head supplied result with
  | zero => simp [openHead] at opened
  | succ fuel ih =>
    simp only [openHead] at opened
    split at opened
    · split at opened
      · contradiction
      · obtain ⟨mode,resolved,opened⟩ := Option.bind_eq_some_iff.mp opened
        obtain ⟨rest,found,same⟩ := Option.bind_eq_some_iff.mp opened
        cases same
        exact .cons (resolve_sound resolved) (ih found)
    · cases opened
      exact .done

theorem OpenedLambdas.context_length (opening : OpenedLambdas env loans ctx head supplied opened) :
    opened.context.length = ctx.length + opened.modes.length := by
  induction opening with
  | done => simp
  | cons _ _ ih => simpa only [List.length_cons,Nat.add_right_comm _ 1,Nat.add_assoc] using ih

/-- The original application projection supplies every relevant argument
receipt in source order and the actual opened body receipt. -/
theorem projectRaw_app_origin
    (checked : projectRaw (fuel+1) env loans ctx (.app function argument) = some control) :
    ∃ head supplied entries result opened runtime body,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ResourceReplay.checked fuel env loans ctx false head supplied = some (entries,result) ∧
      openHead fuel env loans ctx head supplied = some opened ∧
      (ResourceReplay.runtimeArguments entries).mapM (projectRaw fuel env loans ctx) = some runtime ∧
      projectRaw fuel env loans opened.context opened.body = some body ∧
      control = if opened.modes.isEmpty then .seq body (sequence runtime)
        else .seq (sequence runtime) (.scopes opened.modes body) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨⟨head,supplied⟩,spine,checked⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨⟨entries,result⟩,replayed,checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · contradiction
  · obtain ⟨opened,openedHead,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨runtime,arguments,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨body,bodyProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    exact ⟨head,supplied,entries,result,opened,runtime,body,spine,replayed,openedHead,
      arguments,bodyProjected,(Option.some.inj same).symm⟩

open CodeKinds (consValues pushValues subst_lift_consValues)

/-- Closing the leading source binders uses the original ordered application
replay. Every consumed argument is checked in the caller context and enters
the capture context at its original dependent domain. The result retains the
remaining replay and the exact closed body type at that boundary. -/
theorem OpenedLambdas.close_source
    (opening : OpenedLambdas env loans ctx head supplied opened)
    (wf : UnifiedProgram.EnvWellFormed env)
    (captured : Ghost.Substitution env ctx [] values)
    (caller : Ghost.Substitution env callerContext [] callerValues)
    (typed : HasType env loans ctx false head type)
    (replay : ResourceReplay.Steps env callerLoans callerContext false signature supplied entries result)
    (aligned : Conversion.Conv env (type.subst values) (signature.subst callerValues)) :
    let consumed := opened.modes.length
    let closedValues := pushValues values ((supplied.take consumed).map (Term.subst callerValues))
    ∃ bodyType remaining,
      Ghost.Substitution env opened.context [] closedValues ∧
      HasType env loans opened.context false opened.body bodyType ∧
      Conversion.Conv env (bodyType.subst closedValues) (remaining.subst callerValues) ∧
      ResourceReplay.Steps env callerLoans callerContext false remaining (supplied.drop consumed)
        (entries.drop consumed) result := by
  induction opening generalizing values type signature entries with
  | done => exact ⟨type,signature,captured,typed,aligned,replay⟩
  | @cons ctx erased domain mode body arguments rest argument resolved opening ih =>
    obtain ⟨sort,bodyType,binder,bodyTyped,actualPi⟩ := typed.lamView
    cases replay with
    | cons normalized argumentChecked allowed safe tail =>
      have compared := (actualPi.substitution values wf.closed).trans
        (aligned.trans ((Conversion.normalize?_sound normalized).substitution callerValues wf.closed))
      simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] at compared
      obtain ⟨_,domainConverted,bodyConverted⟩ := compared.pi_injective wf.admissible
      have argumentTyped := ((Checker.check_sound argumentChecked).ghostSubstitution wf caller).convert
        domainConverted.symm
      have inner := captured.consValues (erased := erased) argumentTyped
      refine ih inner bodyTyped tail ?_
      simpa only [subst_lift_consValues, Term.subst_instantiate] using
        bodyConverted.substitution (single (argument.subst callerValues)) wf.closed

/-- The complete loan-aware application projection authenticates the original
typed application and its source-ordered binder closing. Its body and runtime
operand receipts are the ones returned by the original resource query. -/
theorem project_app_binding_store (wf : UnifiedProgram.EnvWellFormed env)
    (closing : Ghost.Substitution env ctx [] values)
    (checked : project fuel env loans ctx (.app function argument) = some control) :
    ∃ prefixFuel head supplied entries result opened runtime body bodyType remaining,
      fuel = prefixFuel+1 ∧
      splitSpine prefixFuel (.app function argument) [] = some (head,supplied) ∧
      ResourceReplay.checked prefixFuel env loans ctx false head supplied = some (entries,result) ∧
      HasType env loans ctx false (.app function argument) result ∧
      openHead prefixFuel env loans ctx head supplied = some opened ∧
      HasType env loans opened.context false opened.body bodyType ∧
      projectRaw prefixFuel env loans opened.context opened.body = some body ∧
      (ResourceReplay.runtimeArguments entries).mapM (projectRaw prefixFuel env loans ctx) = some runtime ∧
      (let consumed := opened.modes.length
       let closedValues := pushValues values ((supplied.take consumed).map (Term.subst values))
       Ghost.Substitution env opened.context [] closedValues ∧
         Conversion.Conv env (bodyType.subst closedValues) (remaining.subst values) ∧
         ResourceReplay.Steps env loans ctx false remaining (supplied.drop consumed) (entries.drop consumed) result) ∧
      control = if opened.modes.isEmpty then .seq body (sequence runtime)
        else .seq (sequence runtime) (.scopes opened.modes body) := by
  have raw := project_origin checked
  cases fuel with
  | zero => simp [projectRaw] at raw
  | succ fuel =>
    obtain ⟨head,supplied,entries,result,opened,runtime,body,spine,accepted,entered,arguments,bodyProjected,same⟩ :=
      projectRaw_app_origin raw
    obtain ⟨signature,typed,replayed,applied⟩ :=
      ResourceReplay.infer_sound (ResourceReplay.checked_origin accepted).2.2.2
    obtain ⟨bodyType,remaining,store,bodyTyped,converted,tail⟩ :=
      (openHead_lambdas entered).close_source wf closing closing typed replayed (.refl _)
    have application := NativeQuantity.splitSpine_reassembles spine
    rw [application] at applied
    exact ⟨fuel,head,supplied,entries,result,opened,runtime,body,bodyType,remaining,rfl,spine,accepted,applied,
      entered,bodyTyped,bodyProjected,arguments,⟨store,converted,tail⟩,same⟩

theorem LoanBudget.scopes (budget : LoanBudget depth loans (.scopes modes body))
    (entered : Loans.Entered depth loans) : LoanBudget (depth + modes.length) loans body := by
  induction modes generalizing depth with
  | nil => exact budget
  | cons mode tail ih =>
    have enteredBody : Loans.Entered (depth+1) loans :=
      fun frame member => Nat.le_trans (entered frame member) (Nat.le_succ _)
    simpa only [List.length_cons,Nat.add_right_comm _ 1,Nat.add_assoc] using ih (budget.scope entered) enteredBody

private theorem local_scope_inner (valid : LocalScopes (.scope mode body)) : LocalScopes body := by
  cases mode
  · exact valid.2
  · exact valid.2
  · exact valid
  · exact valid

private theorem local_scopes_body (valid : LocalScopes (.scopes modes body)) : LocalScopes body := by
  induction modes with
  | nil => exact valid
  | cons mode tail ih => exact ih (local_scope_inner valid)

/-- The source-order mode of a consumed binder determines the exact use
count of its de Bruijn slot in the fully opened body. -/
theorem scopes_bound_demand (valid : LocalScopes (.scopes modes body))
    (selected : modes[position]? = some mode) (checked : mode = .linear ∨ mode = .erased) :
    body.demand (modes.length-position-1) = some (if mode = .linear then 1 else 0) := by
  induction modes generalizing position with
  | nil => cases selected
  | cons head tail ih =>
    cases position with
    | zero =>
      have same : head = mode := Option.some.inj selected
      subst head
      have index : (mode::tail).length-0-1 = 0+tail.length := by simp
      rw [index]
      rcases checked with rfl | rfl
      · exact Jihoo.Quantity.scopes_outer (modes := tail) (n := 1) valid.1
      · exact Jihoo.Quantity.scopes_outer (modes := tail) (n := 0) valid.1
    | succ position =>
      have index : (head::tail).length-(position+1)-1 = tail.length-position-1 := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact ih (local_scope_inner valid) selected

private theorem runtime_budgets (budget : LoanBudget depth loans (sequence operands))
    (valid : LocalScopes (sequence operands)) :
    ∀ operand ∈ operands, LoanBudget depth loans operand ∧ LocalScopes operand := by
  induction operands with
  | nil => intro _ impossible; cases impossible
  | cons first tail ih =>
    intro operand member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨budget.sequence.1,valid.1⟩
    · exact ih budget.sequence.2 valid.2 operand later

/-- Every relevant operand and the entire opened CODE body have zero
ownership demand for each active loan. The body's budget uses the actual
context depth after opening the complete dependent telescope. -/
theorem projectRaw_app_loan_budgets
    (checked : projectRaw (fuel+1) env loans ctx (.app function argument) = some control)
    (budget : LoanBudget ctx.length loans control) (valid : LocalScopes control)
    (entered : Loans.Entered ctx.length loans) :
    ∃ head supplied entries result opened runtime body,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ResourceReplay.checked fuel env loans ctx false head supplied = some (entries,result) ∧
      openHead fuel env loans ctx head supplied = some opened ∧
      (ResourceReplay.runtimeArguments entries).mapM (projectRaw fuel env loans ctx) = some runtime ∧
      projectRaw fuel env loans opened.context opened.body = some body ∧
      LoanBudget opened.context.length loans body ∧ LocalScopes body ∧
      ∀ operand ∈ runtime, LoanBudget ctx.length loans operand ∧ LocalScopes operand := by
  obtain ⟨head,supplied,entries,result,opened,runtime,body,spine,replayed,opening,operands,projected,same⟩ :=
    projectRaw_app_origin checked
  have parts : LoanBudget ctx.length loans (.scopes opened.modes body) ∧ LocalScopes (.scopes opened.modes body) ∧
      LoanBudget ctx.length loans (sequence runtime) ∧ LocalScopes (sequence runtime) := by
    rw [same] at budget valid
    cases modes : opened.modes with
    | nil =>
      simp only [modes,List.isEmpty,ite_true] at budget valid ⊢
      exact ⟨budget.sequence.1,valid.1,budget.sequence.2,valid.2⟩
    | cons mode rest =>
      simp only [modes,List.isEmpty,Bool.false_eq_true,ite_false] at budget valid ⊢
      exact ⟨budget.sequence.2,valid.2,budget.sequence.1,valid.1⟩
  have bodyBudget := parts.1.scopes entered
  rw [← (openHead_lambdas opening).context_length] at bodyBudget
  exact ⟨head,supplied,entries,result,opened,runtime,body,spine,replayed,opening,operands,projected,
    bodyBudget,local_scopes_body parts.2.1,runtime_budgets parts.2.2.1 parts.2.2.2⟩

/-- For an admitted application, the actual opened mode telescope records one
use for each owned argument and none for erased arguments. The same counts
bound every finite body prefix, and are exact for completed bodies. -/
theorem projectRaw_app_checked_binder_usage
    (checked : projectRaw (fuel+1) env loans ctx (.app function argument) = some control)
    (valid : LocalScopes control) :
    ∃ head supplied entries result opened body,
      ResourceReplay.checked fuel env loans ctx false head supplied = some (entries,result) ∧
      openHead fuel env loans ctx head supplied = some opened ∧
      projectRaw fuel env loans opened.context opened.body = some body ∧
      ∀ {position mode}, opened.modes[position]? = some mode → (mode = .linear ∨ mode = .erased) →
        let index := opened.modes.length-position-1
        let uses := if mode = .linear then 1 else 0
        body.demand index = some uses ∧
          (∀ events, Prefix body events → events.count index ≤ uses) ∧
          (∀ events, Finishes body events → events.count index = uses) := by
  obtain ⟨head,supplied,entries,result,opened,runtime,body,_,replayed,opening,_,projected,shape⟩ :=
    projectRaw_app_origin checked
  have scopeValid : LocalScopes (.scopes opened.modes body) := by
    rw [shape] at valid
    cases modes : opened.modes with
    | nil =>
      simp only [modes,List.isEmpty,ite_true] at valid
      exact valid.1
    | cons mode rest =>
      simp only [modes,List.isEmpty,Bool.false_eq_true,ite_false] at valid
      exact valid.2
  refine ⟨head,supplied,entries,result,opened,body,replayed,opening,projected,?_⟩
  intro position mode selected verified
  have count := scopes_bound_demand scopeValid selected verified
  exact ⟨count,fun _ started => started.count_le count,fun _ finished => finished.count_eq count⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
