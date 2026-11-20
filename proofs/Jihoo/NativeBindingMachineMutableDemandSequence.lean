import Jihoo.NativeBindingMachineMutableOwnerDemand

/-! A complete demand receipt for captured owners splits at sequential
evaluation. If the first component consumes a physical owner, the later
component has zero demand through every retained alias. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity

def OwnerDemandWorld.Total (code : Code) (receipt : Jihoo.Quantity.Control) : Prop :=
  ∀ index object, code.values[index]? = some (some (.owner object)) →
    ∃ uses, receipt.demand index = some uses

private theorem sequence_counts (found : (Jihoo.Quantity.Control.seq first second).demand index = some uses) :
    ∃ left right, first.demand index = some left ∧ second.demand index = some right ∧ left+right = uses := by
  change (first.demand index).bind (fun left => (second.demand index).bind (fun right => some (left+right))) =
    some uses at found
  obtain ⟨left,firstDemand,rest⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨right,secondDemand,same⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨left,right,firstDemand,secondDemand,Option.some.inj same⟩

private theorem project_world (wholeWorld : OwnerDemandWorld heap code whole)
    (accounted : ∀ index object, code.values[index]? = some (some (.owner object)) →
      ∃ selected extra, part.demand index = some selected ∧ whole.demand index = some (selected+extra)) :
    OwnerDemandWorld heap code part ∧ OwnerDemandWorld.Total code part := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro index object uses stored positive
    obtain ⟨selected,extra,demand,full⟩ := accounted index object stored
    rw [positive] at demand
    cases demand
    have fullPositive : whole.demand index = some ((uses+extra)+1) := by
      have reordered : uses+1+extra = uses+extra+1 := by omega
      rw [reordered] at full
      exact full
    obtain ⟨live,unit⟩ := wholeWorld.live_once index object (uses+extra) stored fullPositive
    exact ⟨live,by omega⟩
  · intro index alias object uses different stored aliased positive
    obtain ⟨selected,extra,demand,full⟩ := accounted index object stored
    rw [positive] at demand
    cases demand
    have fullPositive : whole.demand index = some ((uses+extra)+1) := by
      have reordered : uses+1+extra = uses+extra+1 := by omega
      rw [reordered] at full
      exact full
    have unused := wholeWorld.exclusive index alias object (uses+extra) different stored aliased fullPositive
    obtain ⟨aliasUses,aliasExtra,aliasDemand,aliasFull⟩ := accounted alias object aliased
    rw [unused] at aliasFull
    have zero : aliasUses = 0 := by
      have same := Option.some.inj aliasFull
      omega
    exact zero ▸ aliasDemand
  · intro index object stored
    obtain ⟨uses,_,demand,_⟩ := accounted index object stored
    exact ⟨uses,demand⟩

/-- Ownership units partition across both executable sides of a sequence.
The two worlds retain exact availability and exclude consumption of the
same allocation through distinct slot names. -/
theorem OwnerDemandWorld.sequence
    (world : OwnerDemandWorld heap code (.seq first second))
    (complete : OwnerDemandWorld.Total code (.seq first second)) :
    OwnerDemandWorld heap code first ∧ OwnerDemandWorld.Total code first ∧
      OwnerDemandWorld heap code second ∧ OwnerDemandWorld.Total code second ∧
      ∀ index alias object uses, code.values[index]? = some (some (.owner object)) →
        code.values[alias]? = some (some (.owner object)) → first.demand index = some (uses+1) →
        second.demand alias = some 0 := by
  have amount (index object : Nat) (stored : code.values[index]? = some (some (.owner object))) :
      ∃ left right, first.demand index = some left ∧ second.demand index = some right ∧
        (Jihoo.Quantity.Control.seq first second).demand index = some (left+right) := by
    obtain ⟨uses,observed⟩ := complete index object stored
    obtain ⟨left,right,firstCount,secondCount,total⟩ := sequence_counts observed
    exact ⟨left,right,firstCount,secondCount,total.symm ▸ observed⟩
  obtain ⟨firstWorld,firstTotal⟩ := project_world (part := first) world (by
    intro index object stored
    obtain ⟨left,right,demand,_,full⟩ := amount index object stored
    exact ⟨left,right,demand,full⟩)
  obtain ⟨secondWorld,secondTotal⟩ := project_world (part := second) world (by
    intro index object stored
    obtain ⟨left,right,_,demand,full⟩ := amount index object stored
    exact ⟨right,left,demand,by simpa only [Nat.add_comm] using full⟩)
  refine ⟨firstWorld,firstTotal,secondWorld,secondTotal,?_⟩
  intro index alias object uses stored aliased positive
  obtain ⟨left,right,firstCount,secondCount,full⟩ := amount index object stored
  rw [positive] at firstCount
  cases firstCount
  have liveDemand : (Jihoo.Quantity.Control.seq first second).demand index = some ((uses+right)+1) := by
    simpa only [Nat.add_right_comm uses 1 right] using full
  by_cases same : alias = index
  · subst alias
    have unit := (world.live_once index object (uses+right) stored liveDemand).2
    have none : right = 0 := by omega
    exact none ▸ secondCount
  · have unused := world.exclusive index alias object (uses+right) (Ne.symm same) stored aliased liveDemand
    obtain ⟨aliasFirst,aliasSecond,_,aliasCount,aliasFull⟩ := amount alias object aliased
    rw [unused] at aliasFull
    have none : aliasSecond = 0 := by
      have sum := Option.some.inj aliasFull
      omega
    exact none ▸ aliasCount

theorem OwnerDemandWorld.total_initial (term : Term) (receipt : Jihoo.Quantity.Control) :
    OwnerDemandWorld.Total (.initial term) receipt := by
  intro index object stored
  cases stored

private theorem named_reader_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain readBody) continuation)
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true) :
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let entered := enter false domain readBody code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let stack := .lendFinish token object (some (code.context.length-owner))
      origin entered.origin (code.child continuation) :: state.stack
    let heap : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.lend state.heap.metadata object,state.heap.cell⟩
    run 5 state = ⟨⟨heap,.evaluate entered,stack,state.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin))],5⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,returnAction,
    Term.subst,live,ite_true,Option.map_none,Option.map_some,applyValue]
  rfl

/-- The specialized read's genuine receipt is the first component of the
checked Lend. Five actual transitions enter the reader and bind the fresh
token. The borrowed owner has zero demand in the read, and any other
retained physical owners keep their live, exclusive units. -/
theorem reachable_named_reader_entry_demand (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false domain readBody)
      (.lam false first (.lam false again body)))
    (typed : LoanSourceTyped env loans false code type)
    (slots : LoanSlots code loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial term)).state
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let enteredCode := enter false domain readBody code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let continuation := code.child (.lam false first (.lam false again body))
    let stack := .lendFinish token object (some (code.context.length-owner))
      origin enteredCode.origin continuation :: state.stack
    let result := run 5 state
    result.state.control = .evaluate enteredCode ∧ result.state.stack = stack ∧
      result.state.pending = state.pending ∧ result.steps = 5 ∧
      result.events = [.legacy (.heap (.beginLease token object)),.legacy (.activate false readBody (.borrow origin))] ∧
      result.state.heap.metadata.heap.lease token = some object ∧
      LoanSlots enteredCode (Loans.enter code.context.length owner loans) result.state.activeStack ∧
      (∃ valueType, LoanTyping.HasType env [] [] true enteredCode.origin (valueType.subst code.origins) ∧
        LoanTyping.Outlived env valueType) ∧
      ∃ reader,
        let specialized := Lending.read (.var owner) readBody
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans)
          code.context specialized = some reader ∧ reader.demand owner = some 0 ∧
        OwnerDemandWorld result.state.heap.metadata (code.child specialized) reader ∧
        OwnerDemandWorld.Total (code.child specialized) reader := by
  let state := (run fuel (initial term)).state
  let continuation := code.child (.lam false first (.lam false again body))
  let origin := (Term.var owner).subst code.origins
  let token := state.heap.metadata.heap.nextLease
  let enteredCode := enter false domain readBody code.context code.origins code.values
    (.borrow origin) (some (.reference token))
  rw [shape] at checked
  obtain ⟨_,_,_,reader,_,_,_,_,_,_,_,_,_,_,projected,_,readerZero,_,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checked
  have one := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checked
  have live := (world.live_once owner object 0 stored one).1
  rw [receiptShape] at world complete
  obtain ⟨readerWorld,readerTotal,_,_,_⟩ := world.sequence complete
  have ran := named_reader_steps state evaluating shape stored live
  have closed := typed_explicit_reader_origin history typed shape token
  have permission := named_reader_body_slots code slots entered stored domain readBody token
    (code.child (.lam false domain readBody)).origin continuation
  have lease : (SizedBufferHeap.lend state.heap.metadata object).heap.lease token = some object := by
    simp [SizedBufferHeap.lend,HeapLeases.put,token]
  have laterWorld : OwnerDemandWorld (SizedBufferHeap.lend state.heap.metadata object)
      (code.child (Lending.read (.var owner) readBody)) reader := by
    refine ⟨?_,readerWorld.exclusive⟩
    intro index actual uses captured positive
    exact readerWorld.live_once index actual uses captured positive
  dsimp only at ran ⊢
  rw [ran]
  exact ⟨rfl,rfl,rfl,rfl,rfl,lease,permission,closed,reader,projected,readerZero,laterWorld,readerTotal⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
