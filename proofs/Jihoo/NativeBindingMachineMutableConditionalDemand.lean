import Jihoo.NativeBindingMachineDynamicIndex
import Jihoo.NativeBindingMachineValueKinds
import Jihoo.NativeBindingMachineMutableNumeric
import Jihoo.NativeBindingMachineMutableReaderReturnDemand

/-! A checked conditional has equal ownership demand in both alternatives.
The actual positive branch extends the binding machine with an erased
proof slot and transfers ownership and existing reader authority. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity NativeQuantity
open LoanTyping.ResourceQuantity (projectRaw LoanBudget)

private theorem branch_counts (known : (Jihoo.Quantity.Control.branch yes no).demand index = some count) :
    yes.demand index = some count ∧ no.demand index = some count := by
  simp only [Jihoo.Quantity.Control.demand] at known
  obtain ⟨left,leftCount,later⟩ := Option.bind_eq_some_iff.mp known
  obtain ⟨right,rightCount,returned⟩ := Option.bind_eq_some_iff.mp later
  split at returned
  · rename_i same
    cases returned
    exact ⟨leftCount,same ▸ rightCount⟩
  · cases returned

/-- Neither branch can add authority which the original branch receipt
omits, including a positive demand through a different alias of an owner. -/
theorem OwnerDemandWorld.branch
    (world : OwnerDemandWorld heap code (.branch yes no)) (total : OwnerDemandWorld.Total code (.branch yes no)) :
    (OwnerDemandWorld heap code yes ∧ OwnerDemandWorld.Total code yes) ∧
    (OwnerDemandWorld heap code no ∧ OwnerDemandWorld.Total code no) := by
  have project (part : Jihoo.Quantity.Control)
      (counts : ∀ {index count}, (Jihoo.Quantity.Control.branch yes no).demand index = some count →
        part.demand index = some count) : OwnerDemandWorld heap code part ∧ OwnerDemandWorld.Total code part := by
    have complete {index object} (stored : code.values[index]? = some (some (.owner object))) :
        ∃ count, (Jihoo.Quantity.Control.branch yes no).demand index = some count ∧ part.demand index = some count := by
      obtain ⟨count,known⟩ := total index object stored
      exact ⟨count,known,counts known⟩
    have lift {index object uses} (stored : code.values[index]? = some (some (.owner object)))
        (used : part.demand index = some (uses+1)) :
        (Jihoo.Quantity.Control.branch yes no).demand index = some (uses+1) := by
      obtain ⟨count,known,partCount⟩ := complete stored
      rw [used] at partCount
      cases partCount
      exact known
    exact ⟨⟨fun index object uses stored used => world.live_once index object uses stored (lift stored used),
      fun index alias object uses different stored aliased used =>
        counts (world.exclusive index alias object uses different stored aliased (lift stored used))⟩,
      fun _ _ stored => let ⟨count,_,selected⟩ := complete stored; ⟨count,selected⟩⟩
  exact ⟨project yes (fun read => (branch_counts read).1),project no (fun read => (branch_counts read).2)⟩

private def comparisonType (equality : Bool) (first second : Term) : Term :=
  if equality then .eq first second else .lt first second

private def conditionalTerm (equality : Bool) (first second yes no : Term) : Term :=
  if equality then .ifEq first second yes no else .ifLt first second yes no

private def leftTaken (equality : Bool) (left right : Nat) : Bool :=
  if equality then left == right else decide (left < right)

/-- Recover the two branch receipts from the actual source query, under
exactly the context the machine uses after taking the positive branch. -/
theorem conditional_receipts
    (checked : projectRaw (fuel+1) env loans ctx (conditionalTerm equality first second yes no) = some receipt) :
    ∃ comparison yesReceipt noReceipt,
      fields (projectRaw fuel env loans ctx) [first,second,yes,no] [0,1] = some comparison ∧
      projectRaw fuel env loans (⟨comparisonType equality first second,true⟩ :: ctx) yes = some yesReceipt ∧
      projectRaw fuel env loans ctx no = some noReceipt ∧
      receipt = .seq comparison (.branch (.scope .erased yesReceipt) noReceipt) := by
  cases equality <;>
    simp only [conditionalTerm,comparisonType,Bool.false_eq_true,ite_false,ite_true,
      Term.ifEq,Term.ifLt,projectRaw,Op.arity,List.length_cons,List.length_nil,reduceCtorEq] at checked ⊢
  all_goals
    obtain ⟨comparison,foundComparison,rest⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨yesReceipt,foundYes,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨noReceipt,foundNo,same⟩ := Option.bind_eq_some_iff.mp rest
    exact ⟨comparison,yesReceipt,noReceipt,foundComparison,foundYes,foundNo,(Option.some.inj same).symm⟩

private theorem step_branch {code : Code} (returning : state.control = .returned (.natural right))
    (pendingComparison : state.stack = .branchRight equality left (code.child yes) (code.child no) first second :: stack) :
    let next := if leftTaken equality left right then branchCode equality (code.child yes) first second else code.child no
    step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,none) := by
  cases state with
  | mk heap control before pending =>
    cases returning
    change before = _ at pendingComparison
    subst before
    cases equality <;> simp only [leftTaken,Bool.false_eq_true,ite_false,ite_true,step,returnAction]
    all_goals split <;> rfl

/-- Once the computed operands are in the comparison frame, the next
machine step enters the source branch with its exact checked receipt.
The selected body keeps every existing loan and the same physical heap.
Demand for the alternatives is the invariant at the end of the operands. -/
theorem checked_branch_handoff
    (returning : state.control = .returned (.natural right))
    (pendingComparison : state.stack = .branchRight equality left (code.child yes) (code.child no) first second :: stack)
    (checked : projectRaw (fuel+1) env loans code.context (conditionalTerm equality first second yes no) = some receipt)
    (rest : receipt = .seq compared alternatives)
    (world : OwnerDemandWorld state.heap.metadata code alternatives)
    (total : OwnerDemandWorld.Total code alternatives)
    (valid : LocalScopes receipt)
    (budget : LoanBudget code.context.length loans receipt)
    (entered : Loans.Entered code.context.length loans) :
    ∃ next bodyReceipt, step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,none) ∧
      projectRaw fuel env loans next.context next.term = some bodyReceipt ∧
      OwnerDemandWorld state.heap.metadata next bodyReceipt ∧ OwnerDemandWorld.Total next bodyReceipt ∧
      LoanBudget next.context.length loans bodyReceipt := by
  obtain ⟨compared',yesReceipt,noReceipt,_,yesChecked,noChecked,shape⟩ := conditional_receipts checked
  have splitReceipt := Jihoo.Quantity.Control.seq.inj (rest.symm.trans shape)
  rw [splitReceipt.2] at world total
  obtain ⟨⟨yesWorld,yesTotal⟩,⟨noWorld,noTotal⟩⟩ := world.branch total
  rw [shape] at valid budget
  change LocalScopes compared' ∧ LocalScopes (.scope .erased yesReceipt) ∧ LocalScopes noReceipt at valid
  have budgets := budget.sequence.2.branch
  have ran := step_branch returning pendingComparison
  dsimp only at ran
  by_cases taken : leftTaken equality left right = true
  · rw [ite_eq_left taken] at ran
    let next := branchCode equality (code.child yes) first second
    have use : OwnerDemandWorld state.heap.metadata (code.child yes) (.scope .erased yesReceipt) := ⟨yesWorld.live_once,yesWorld.exclusive⟩
    have allUses : OwnerDemandWorld.Total (code.child yes) (.scope .erased yesReceipt) := yesTotal
    have transferred := use.enter_nonowner_scope (erased := true) (value := none)
      allUses valid.2.1 (comparisonType equality first second) yes
      (if equality then Term.refl (first.subst code.origins)
       else Term.decide (first.subst code.origins) (second.subst code.origins))
      (by intro _ impossible; cases impossible)
    change OwnerDemandWorld state.heap.metadata next yesReceipt ∧ OwnerDemandWorld.Total next yesReceipt at transferred
    exact ⟨next,yesReceipt,ran,yesChecked,transferred.1,transferred.2,budgets.1.scope entered⟩
  · rw [ite_eq_right taken] at ran
    exact ⟨code.child no,noReceipt,ran,noChecked,⟨noWorld.live_once,noWorld.exclusive⟩,noTotal,budgets.2⟩


/-- The machine's selected branch also retains the physical owner slot and
reader descriptor of every active source loan. The erased input shifts
slot indices while leaving their lexical reader keys unchanged. -/
theorem checked_branch_retains_loan_slots
    (returning : state.control = .returned (.natural right))
    (pendingComparison : state.stack = .branchRight equality left (code.child yes) (code.child no) first second :: stack)
    (slots : LoanSlots code loans state.activeStack) (entered : Loans.Entered code.context.length loans) :
    let next := if leftTaken equality left right then branchCode equality (code.child yes) first second else code.child no
    let after : State := ⟨state.heap,.evaluate next,stack,state.pending⟩
    step state = some (after,none) ∧ LoanSlots next loans after.activeStack := by
  dsimp only
  refine ⟨step_branch returning pendingComparison,?_⟩
  have active : state.activeStack =
      .branchRight equality left (code.child yes) (code.child no) first second ::
        (stack ++ state.pending.flatMap Prod.snd) := by
    simp only [State.activeStack,pendingComparison,List.cons_append]
  rw [active] at slots
  have suffix : LoanSlots code loans (stack ++ state.pending.flatMap Prod.snd) := by
    intro index borrowed
    obtain ⟨object,stored,frame,member,token,reader⟩ := slots index borrowed
    rcases List.mem_cons.mp member with rfl | remains
    · cases reader
    · exact ⟨object,stored,frame,remains,token,reader⟩
  split
  · exact suffix.enter entered true (comparisonType equality first second) yes
      (if equality then Term.refl (first.subst code.origins)
       else Term.decide (first.subst code.origins) (second.subst code.origins)) none
  · exact suffix.child no


open CodeKinds

private def EqualityInputs (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .ifEq left right yes no => ∃ result,
      LoanTyping.HasType env loans ctx mode left .u64 ∧ LoanTyping.HasType env loans ctx mode right .u64 ∧
      LoanTyping.HasType env loans (⟨.eq left right,true⟩ :: ctx) mode yes (result.rename Nat.succ) ∧
      LoanTyping.HasType env loans ctx mode no result
  | _ => True

private theorem equality_inputs (typed : LoanTyping.HasType env loans ctx mode term type) :
    EqualityInputs env loans ctx mode term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => EqualityInputs env loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case ifEq => exact ⟨_,by assumption,by assumption,by assumption,by assumption⟩
  case dataElim => split <;> trivial

private theorem typed_branches (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode (conditionalTerm equality first second yes no) type) :
    ∃ result, LoanTyping.HasType env loans (⟨comparisonType equality first second,true⟩ :: ctx)
        mode yes (result.rename Nat.succ) ∧
      LoanTyping.HasType env loans ctx mode no result ∧ RawLend.Conv env result type := by
  cases equality
  · obtain ⟨result,left,right,positive,negative⟩ := typed.ifLt_inputs
    exact ⟨result,positive,negative,(LoanTyping.HasType.ifLt left right positive negative).unique wf typed⟩
  · obtain ⟨result,left,right,positive,negative⟩ : EqualityInputs env loans ctx mode (.ifEq first second yes no) :=
      equality_inputs typed
    exact ⟨result,positive,negative,(LoanTyping.HasType.ifEq left right positive negative).unique wf typed⟩

private theorem branch_context
    (context : ValueContext env code meanings)
    (proofTyped : LoanTyping.HasType env [] [] true proof ((comparisonType equality first second).subst meanings)) :
    ValueContext env (branchCode equality (code.child yes) first second) (consValues proof meanings) := by
  simpa only [branchCode,Code.child,enter,comparisonType] using
    context.enter_erased (comparisonType equality first second) yes
      (if equality then Term.refl (first.subst code.origins)
        else Term.decide (first.subst code.origins) (second.subst code.origins)) proofTyped

private theorem comparison_witness
    (leftMeaning : RawLend.Conv env (first.subst meanings) (.natural left))
    (rightMeaning : RawLend.Conv env (second.subst meanings) (.natural right))
    (leftBound : left < 2^64) (rightBound : right < 2^64)
    (taken : leftTaken equality left right = true) :
    ∃ proof, LoanTyping.HasType env [] [] true proof ((comparisonType equality first second).subst meanings) := by
  cases equality
  · have ordered : left < right := of_decide_eq_true taken
    refine ⟨.decide (.natural left) (.natural right),?_⟩
    have converted : RawLend.Conv env (.lt (.natural left) (.natural right))
        (.lt (first.subst meanings) (second.subst meanings)) :=
      .node .lt (.cons leftMeaning.symm (.cons rightMeaning.symm .nil))
    apply (LoanTyping.HasType.decide leftBound rightBound ordered).convert
    simpa only [comparisonType,Bool.false_eq_true,ite_false,Term.lt,Term.subst,substArgs,Op.binders,liftSub] using converted
  · have same : left = right := beq_iff_eq.mp taken
    subst right
    refine ⟨.refl (.natural left),?_⟩
    have converted : RawLend.Conv env (.eq (.natural left) (.natural left))
        (.eq (first.subst meanings) (second.subst meanings)) :=
      .node .eq (.cons leftMeaning.symm (.cons rightMeaning.symm .nil))
    apply (LoanTyping.HasType.refl (.natural leftBound)).convert
    simpa only [comparisonType,ite_true,Term.eq,Term.subst,substArgs,Op.binders,liftSub] using converted

/-- At the actual comparison frame, value interpretations of the evaluated
operands give closed evidence for the selected positive branch. Both branches
retain the original dependent result type and the interpretation of old slots. -/
theorem checked_branch_closing
    (wf : UnifiedProgram.EnvWellFormed env)
    (returning : state.control = .returned (.natural right))
    (pendingComparison : state.stack = .branchRight equality left (code.child yes) (code.child no) first second :: stack)
    (typed : LoanClosingTyped env loans false (code.child (conditionalTerm equality first second yes no)) meanings type)
    (context : ValueContext env code meanings)
    (leftMeaning : RawLend.Conv env (first.subst meanings) (.natural left))
    (rightMeaning : RawLend.Conv env (second.subst meanings) (.natural right))
    (leftBound : left < 2^64) (rightBound : right < 2^64) :
    ∃ next actualMeanings, step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,none) ∧
      LoanClosingTyped env loans false next actualMeanings type ∧ ValueContext env next actualMeanings := by
  obtain ⟨closing,localType,source,expected⟩ := typed
  obtain ⟨result,positive,negative,converted⟩ := typed_branches wf source
  have resultType := (converted.substitution meanings wf.closed).trans expected
  have stepped := step_branch returning pendingComparison
  dsimp only at stepped
  by_cases taken : leftTaken equality left right = true
  · rw [ite_eq_left taken] at stepped
    obtain ⟨proof,proofTyped⟩ := comparison_witness leftMeaning rightMeaning leftBound rightBound taken
    have continued := branch_context (yes := yes) context proofTyped
    refine ⟨_,_,stepped,⟨continued.closing,result.rename Nat.succ,positive,?_⟩,continued⟩
    simpa only [shift_subst_consValues] using resultType
  · rw [ite_eq_right taken] at stepped
    exact ⟨_,_,stepped,⟨closing,result,negative,resultType⟩,context.child no⟩

/-- Both comparison operands have word range by actual machine
reachability. The original resource and ownership receipts transfer to
the same uniquely selected and value-typed branch. -/
theorem reachable_checked_branch_handoff (term : Term) (ticks : Nat)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (returning : (run ticks (initial term)).state.control = .returned (.natural right))
    (pendingComparison : (run ticks (initial term)).state.stack =
      .branchRight equality left (code.child yes) (code.child no) first second :: stack)
    (typed : LoanClosingTyped env loans false (code.child (conditionalTerm equality first second yes no)) meanings type)
    (context : ValueContext env code meanings)
    (leftMeaning : RawLend.Conv env (first.subst meanings) (.natural left))
    (rightMeaning : RawLend.Conv env (second.subst meanings) (.natural right))
    (checked : projectRaw (fuel+1) env loans code.context (conditionalTerm equality first second yes no) = some receipt)
    (rest : receipt = .seq compared alternatives)
    (world : OwnerDemandWorld (run ticks (initial term)).state.heap.metadata code alternatives)
    (total : OwnerDemandWorld.Total code alternatives)
    (valid : LocalScopes receipt) (budget : LoanBudget code.context.length loans receipt)
    (entered : Loans.Entered code.context.length loans)
    (slots : LoanSlots code loans (run ticks (initial term)).state.activeStack) :
    let state := (run ticks (initial term)).state
    ∃ next actualMeanings bodyReceipt,
      step state = some (⟨state.heap,.evaluate next,stack,state.pending⟩,none) ∧
      LoanClosingTyped env loans false next actualMeanings type ∧ ValueContext env next actualMeanings ∧
      projectRaw fuel env loans next.context next.term = some bodyReceipt ∧
      OwnerDemandWorld state.heap.metadata next bodyReceipt ∧ OwnerDemandWorld.Total next bodyReceipt ∧
      LoanBudget next.context.length loans bodyReceipt ∧
      LoanSlots next loans (⟨state.heap,.evaluate next,stack,state.pending⟩ : State).activeStack := by
  have numeric := (initial_run_numbers term ticks).legacy
  have rightBound := numeric.2.1
  change ControlNumbers (run ticks (initial term)).state.control at rightBound
  rw [returning] at rightBound
  have leftFrame := numeric.2.2
  change StackNumbers (run ticks (initial term)).state.stack at leftFrame
  rw [pendingComparison] at leftFrame
  have leftBound := leftFrame.head.1
  obtain ⟨next,actual,stepTyped,closing,values⟩ := checked_branch_closing history.wellFormed
    returning pendingComparison typed context leftMeaning rightMeaning leftBound rightBound.naturalBound
  obtain ⟨resource,body,stepResource,projected,owners,allOwners,loans⟩ :=
    checked_branch_handoff returning pendingComparison checked rest world total valid budget entered
  have outcome := Option.some.inj (stepResource.symm.trans stepTyped)
  have same := Control.evaluate.inj (congrArg (fun state : State × Option Event => state.1.control) outcome)
  subst resource
  obtain ⟨stepSlots,keptSlots⟩ := checked_branch_retains_loan_slots returning pendingComparison slots entered
  have slotOutcome := Option.some.inj (stepSlots.symm.trans stepTyped)
  have sameSlots := Control.evaluate.inj (congrArg (fun state : State × Option Event => state.1.control) slotOutcome)
  exact ⟨next,actual,body,stepTyped,closing,values,projected,owners,allOwners,loans,sameSlots ▸ keptSlots⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
