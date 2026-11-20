import Jihoo.NativeBindingMachineMutableTelescopeDemand
import Jihoo.NativeBindingMachineMutableFreeContinuation

/-! A saturated application enters its original leading lambda telescope
in source order. This relation uses the actual evaluation of each relevant
operand in its saved argument frame. The argument frame enforces the
boundary before the next activation, even across mutable buffer actions. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity NativeQuantity CodeKinds
open LoanTyping.ResourceQuantity (Opened OpenedLambdas)
open LoanTyping.ResourceModes (Resolved)

def functionFrames (caller : Code) (supplied : List Term) (stack : List Frame) : List Frame :=
  supplied.map (fun argument => .function (caller.child argument)) ++ stack

def callState (heap : SizedBufferHeap.IndexedState) (code caller : Code)
    (supplied : List Term) (stack : List Frame) (pending : List (BufferFrame × List Frame)) : State :=
  ⟨heap,.evaluate code,functionFrames caller supplied stack,pending⟩

/-- Relevant operands use the original caller code and a saved copy of the
currently evaluated lambda. Erased operands have no operand computation. -/
inductive CallEntry (env : Environment) (loans : Loans.Stack) (caller : Code)
    (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    Code → List Term → Opened → SizedBufferHeap.IndexedState → Nat → List Event →
      List (Option Value) → SizedBufferHeap.IndexedState → Code → Prop where
  | done : CallEntry env loans caller stack pending code supplied ⟨code.context,[],code.term⟩
      heap 0 [] [] heap code
  | erased (resolved : Resolved env loans code.context true domain mode)
      (written : code.term = .lam true domain body)
      (tail : CallEntry env loans caller stack pending
        (enter true domain body code.context code.origins code.values (caller.child argument).origin none)
        rest opened heap fuel events slots finalHeap finalCode) :
      CallEntry env loans caller stack pending code (argument :: rest)
        ⟨opened.context,mode :: opened.modes,opened.body⟩ heap (2+fuel)
        (.legacy (.activate true body (caller.child argument).origin) :: events) (none :: slots) finalHeap finalCode
  | relevant (resolved : Resolved env loans code.context false domain mode)
      (written : code.term = .lam false domain body)
      (evaluated :
        let origin := (caller.child argument).origin
        let saved := Frame.argument (.closure false domain body code.context code.origins code.values) origin
        let frames := saved :: functionFrames caller rest stack
        run argFuel ⟨heap,.evaluate (caller.child argument),frames,pending⟩ =
          ⟨⟨afterArgument,.returned value,frames,pending⟩,argEvents,argFuel⟩)
      (tail : CallEntry env loans caller stack pending
        (enter false domain body code.context code.origins code.values (caller.child argument).origin (some value))
        rest opened afterArgument fuel events slots finalHeap finalCode) :
      CallEntry env loans caller stack pending code (argument :: rest)
        ⟨opened.context,mode :: opened.modes,opened.body⟩ heap (2+(argFuel+(1+fuel)))
        (argEvents ++ .legacy (.activate false body (caller.child argument).origin) :: events)
        (some value :: slots) finalHeap finalCode

/-- The entered code uses the original written domains and body, with one
runtime slot per consumed source binder. Its origin substitution and its
physical values preserve the separate caller and capture stores. -/
theorem CallEntry.retains_original_bindings
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode) :
    OpenedLambdas env loans code.context code.term supplied opened ∧
    finalCode.context = opened.context ∧ finalCode.term = opened.body ∧
    slots.length = opened.modes.length ∧
    finalCode.values = slots.reverse ++ code.values ∧
    finalCode.origins = pushValues code.origins ((supplied.take slots.length).map (fun term => (caller.child term).origin)) := by
  induction entry with
  | done => exact ⟨.done,rfl,rfl,rfl,rfl,rfl⟩
  | erased resolved written _ ih =>
    obtain ⟨lambdas,ctx,term,length,values,origins⟩ := ih
    refine ⟨?_,ctx,term,by simpa only [List.length_cons] using congrArg Nat.succ length,?_,?_⟩
    · rw [written]
      exact .cons resolved lambdas
    · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,enter] using values
    · simpa only [List.length_cons,List.take_succ_cons,List.map_cons,pushValues_cons,enter] using origins
  | relevant resolved written _ _ ih =>
    obtain ⟨lambdas,ctx,term,length,values,origins⟩ := ih
    refine ⟨?_,ctx,term,by simpa only [List.length_cons] using congrArg Nat.succ length,?_,?_⟩
    · rw [written]
      exact .cons resolved lambdas
    · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,enter] using values
    · simpa only [List.length_cons,List.take_succ_cons,List.map_cons,pushValues_cons,enter] using origins

/-- The actual mutable machine runs the complete entry, with one activation
per source binder. The unused source suffix stays on the original stack. -/
theorem CallEntry.executes
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode) :
    run fuel (callState heap code caller supplied stack pending) =
      ⟨callState finalHeap finalCode caller (supplied.drop slots.length) stack pending,events,fuel⟩ := by
  induction entry with
  | done => rfl
  | erased resolved written tail ih =>
    simp only [callState,functionFrames,List.map_cons,List.cons_append,List.length_cons,
      List.drop_succ_cons] at ih ⊢
    rw [run_add]
    simp only [run,step,written,evaluateAction,returnAction,applyValue,executeLegacy,execute,Option.map_none,
      Option.map_some,Option.toList,List.nil_append,List.singleton_append]
    rw [ih]
  | relevant resolved written evaluated tail ih =>
    simp only [callState,functionFrames,List.map_cons,List.cons_append,List.length_cons,
      List.drop_succ_cons] at ih ⊢
    simp only [functionFrames] at evaluated
    rw [run_add]
    simp only [run,step,written,evaluateAction,returnAction,executeLegacy,execute,Option.map_none,
      Option.toList,List.nil_append]
    rw [run_add,evaluated]
    dsimp only
    rw [Nat.one_add]
    simp only [run,step,returnAction,applyValue,executeLegacy,execute,Option.map_some,Option.toList,
      List.singleton_append]
    rw [ih]

private theorem splitSpine_enters {caller : Code} {heap : SizedBufferHeap.IndexedState}
    {stack : List Frame} {pending : List (BufferFrame × List Frame)}
    (selected : splitSpine splitFuel source staged = some (head,supplied)) :
    staged.length ≤ supplied.length ∧
      run (supplied.length-staged.length) (callState heap (caller.child source) caller staged stack pending) =
        ⟨callState heap (caller.child head) caller supplied stack pending,[],supplied.length-staged.length⟩ := by
  induction splitFuel generalizing source staged with
  | zero => simp [splitSpine] at selected
  | succ splitFuel ih =>
    cases source with
    | var index =>
      simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
      obtain ⟨rfl,rfl⟩ := selected
      exact ⟨Nat.le_refl _,by simp only [Nat.sub_self,run]⟩
    | node op args =>
      cases op <;> try
        (simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
         obtain ⟨rfl,rfl⟩ := selected
         exact ⟨Nat.le_refl _,by simp only [Nat.sub_self,run]⟩)
      case app =>
        rcases args with _ | ⟨function,_ | ⟨argument,_ | ⟨_,_⟩⟩⟩
        all_goals try
          (simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
           obtain ⟨rfl,rfl⟩ := selected
           exact ⟨Nat.le_refl _,by simp only [Nat.sub_self,run]⟩)
        simp only [splitSpine] at selected
        obtain ⟨stagedFits,descended⟩ := ih selected
        simp only [List.length_cons] at stagedFits
        have count : supplied.length - staged.length = (supplied.length - (argument :: staged).length) + 1 := by
          simp only [List.length_cons]
          omega
        refine ⟨by omega,?_⟩
        rw [count]
        simp only [run,callState,step,Code.child,evaluateAction,executeLegacy,execute,Option.map_none,
          Option.toList,List.nil_append]
        simp only [callState,Code.child,functionFrames,List.map_cons,List.cons_append] at descended ⊢
        rw [descended]

/-- From the exact source application, the machine builds the original
spine frames, enters each evaluated or erased argument, and keeps the
unconsumed suffix available for the checked residual procedure. -/
theorem CallEntry.executes_from_source
    (selected : splitSpine splitFuel caller.term [] = some (head,supplied))
    (entry : CallEntry env loans caller stack pending (caller.child head) supplied opened heap fuel events slots finalHeap finalCode) :
    run (supplied.length+fuel) ⟨heap,.evaluate caller,stack,pending⟩ =
      ⟨callState finalHeap finalCode caller (supplied.drop slots.length) stack pending,events,supplied.length+fuel⟩ := by
  have descended := (splitSpine_enters (caller := caller) (heap := heap) (stack := stack) (pending := pending) selected).2
  have original : caller.child caller.term = caller := by cases caller; rfl
  simp only [List.length_nil,Nat.sub_zero,original,callState,functionFrames,List.map_nil,List.nil_append] at descended
  rw [run_add,descended]
  have entered := entry.executes
  simp only [callState,functionFrames] at entered
  simp only [entered,callState,functionFrames,List.nil_append]

/-- The actual entered body's original annotation and residual application
are determined by the same source replay that checked the caller's
arguments. Runtime slot entry therefore retains the dependent closing store. -/
theorem CallEntry.closed_source_body
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode)
    (wf : UnifiedProgram.EnvWellFormed env)
    (captureClosing : LoanTyping.Ghost.Substitution env code.context [] code.origins)
    (callerClosing : LoanTyping.Ghost.Substitution env caller.context [] caller.origins)
    (typed : LoanTyping.HasType env loans code.context false code.term headType)
    (replay : LoanTyping.ResourceReplay.Steps env callerLoans caller.context false signature supplied entries result)
    (aligned : RawLend.Conv env (headType.subst code.origins) (signature.subst caller.origins)) :
    ∃ bodyType remaining,
      LoanTyping.Ghost.Substitution env finalCode.context [] finalCode.origins ∧
      LoanTyping.HasType env loans finalCode.context false finalCode.term bodyType ∧
      RawLend.Conv env (bodyType.subst finalCode.origins) (remaining.subst caller.origins) ∧
      LoanTyping.ResourceReplay.Steps env callerLoans caller.context false remaining (supplied.drop slots.length)
        (entries.drop slots.length) result := by
  obtain ⟨lambdas,context,term,length,_,origins⟩ := entry.retains_original_bindings
  obtain ⟨bodyType,remaining,closed,body,converted,rest⟩ :=
    lambdas.close_source wf captureClosing callerClosing typed replay aligned
  refine ⟨bodyType,remaining,?_,?_,?_,?_⟩
  · simpa only [context,origins,length,Code.child,Code.origin] using closed
  · simpa only [context,term] using body
  · simpa only [origins,length,Code.child,Code.origin] using converted
  · simpa only [length] using rest

/-- Even if relevant arguments allocate, the physical final slot list is
derived from the steps that entered them. Demand transfers in that final
heap, with the checked caller's owner retirement as the local premise. -/
theorem CallEntry.transfers_owner_demand
    (entry : CallEntry env loans caller stack pending code supplied opened heap fuel events slots finalHeap finalCode)
    (world : OwnerDemandWorld finalHeap.metadata code (.scopes opened.modes body))
    (total : OwnerDemandWorld.Total code (.scopes opened.modes body))
    (valid : LocalScopes (.scopes opened.modes body))
    (installed : ∀ (position object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      opened.modes[opened.modes.length-position-1]? = some .linear ∧ finalHeap.metadata.heap.live object = true)
    (different : ∀ (position alias object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      slots.reverse[alias]? = some (some (Value.owner object)) → position = alias)
    (retired : ∀ (position index object : Nat), slots.reverse[position]? = some (some (Value.owner object)) →
      code.values[index]? = some (some (Value.owner object)) →
      (.scopes opened.modes body : Jihoo.Quantity.Control).demand index = some 0) :
    OwnerDemandWorld finalHeap.metadata finalCode body ∧ OwnerDemandWorld.Total finalCode body := by
  obtain ⟨_,_,_,length,values,_⟩ := entry.retains_original_bindings
  exact world.opened_telescope total valid values (by simpa only [List.length_reverse] using length.symm)
    installed different retired

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
