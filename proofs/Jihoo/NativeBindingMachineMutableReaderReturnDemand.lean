import Jihoo.NativeBindingMachineMutableDemandSequence
import Jihoo.NativeBindingMachineMutableNumeric
import Jihoo.NativeBindingMachineReferenceIndex
import Jihoo.NativeBindingMachineScalarReaderShape

/-! A named reader can read the current indexed cell and restore the
original continuation. The same resource receipt accounts for the
physical owner before the loan and in the canonical restored context. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

private theorem demand_under_checked_scope (valid : LocalScopes (.scope mode receipt)) (index : Nat) :
    (Jihoo.Quantity.Control.scope mode receipt).demand index = receipt.demand (index+1) := by
  cases mode with
  | linear =>
      change receipt.demand 0 = some 1 ∧ LocalScopes receipt at valid
      simp [Jihoo.Quantity.Control.demand,valid.1]
  | erased =>
      change receipt.demand 0 = some 0 ∧ LocalScopes receipt at valid
      simp [Jihoo.Quantity.Control.demand,valid.1]
  | unrestricted => rfl
  | borrowed => rfl

/-- Entering a scalar continuation under its actual checked scope shifts
every owned capture, preserving both the unique physical unit and defined
demand for unused owners. -/
theorem OwnerDemandWorld.enter_integer_scope
    (world : OwnerDemandWorld heap code (.scope mode receipt))
    (complete : OwnerDemandWorld.Total code (.scope mode receipt))
    (valid : LocalScopes (.scope mode receipt))
    (domain body origin : Term) (integer : Int) :
    let next := enter false domain body code.context code.origins code.values origin (some (.integer integer))
    OwnerDemandWorld heap next receipt ∧ OwnerDemandWorld.Total next receipt := by
  dsimp only
  have demanded := demand_under_checked_scope valid
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro index object uses stored positive
    cases index with
    | zero => cases stored
    | succ index =>
        exact world.live_once index object uses stored ((demanded index).trans positive)
  · intro index alias object uses different stored aliased positive
    cases index with
    | zero => cases stored
    | succ index =>
        cases alias with
        | zero => cases aliased
        | succ alias =>
            have notSame : index ≠ alias := fun same => different (congrArg Nat.succ same)
            exact (demanded alias).symm.trans
              (world.exclusive index alias object uses notSame stored aliased ((demanded index).trans positive))
  · intro index object stored
    cases index with
    | zero => cases stored
    | succ index =>
        obtain ⟨uses,count⟩ := complete index object stored
        exact ⟨uses,(demanded index).symm.trans count⟩

private theorem reader_close_metadata (heap : SizedBufferHeap.State) (object : Nat) :
    let token := heap.heap.nextLease
    let closed := SizedBufferHeap.close (SizedBufferHeap.lend heap object) token
    closed.heap.lease token = none ∧ closed.heap.nextLease = token+1 ∧
      closed.heap.live = heap.heap.live ∧ closed.length = heap.length ∧
      ∀ outer < token, closed.heap.lease outer = heap.heap.lease outer := by
  dsimp only
  refine ⟨by simp [SizedBufferHeap.close,HeapLeases.put],rfl,rfl,rfl,?_⟩
  intro outer old
  simp [SizedBufferHeap.close,SizedBufferHeap.lend,HeapLeases.put,Nat.ne_of_lt old]

private theorem named_index_complete_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again body)))
    (stored : code.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (offsetBound : offset < 2^64) (within : offset < state.heap.metadata.length object) :
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let reader := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let readerCode := enter false domain reader code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let payload := state.heap.cell object offset
    let next := restoredContinuation code first again body origin readerCode.origin object (.integer (decodeInteger payload))
    let closed : SizedBufferHeap.IndexedState :=
      ⟨SizedBufferHeap.close (SizedBufferHeap.lend state.heap.metadata object) token,state.heap.cell⟩
    run 15 state = ⟨⟨closed,.evaluate next,state.stack,state.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader (.borrow origin)),
        .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
        .legacy (.activate false (.lam false again body) readerCode.origin),.legacy (.activate false body origin)],15⟩ := by
  let opened : SizedBufferHeap.IndexedState :=
    ⟨SizedBufferHeap.lend state.heap.metadata object,state.heap.cell⟩
  have leased : opened.metadata.heap.lease state.heap.metadata.heap.nextLease = some object := by
    simp [opened,SizedBufferHeap.lend,HeapLeases.put]
  have read : opened.read state.heap.metadata.heap.nextLease offset = some (state.heap.cell object offset) := by
    unfold SizedBufferHeap.IndexedState.read
    rw [leased]
    change (if offset < state.heap.metadata.length object then some (state.heap.cell object offset) else none) = _
    rw [ite_eq_left within]
  change (SizedBufferHeap.lend state.heap.metadata object).heap.lease state.heap.metadata.heap.nextLease =
    some object at leased
  change (SizedBufferHeap.IndexedState.mk (SizedBufferHeap.lend state.heap.metadata object) state.heap.cell).read
    state.heap.metadata.heap.nextLease offset = some (state.heap.cell object offset) at read
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,returnAction,
    Term.subst,live,offsetBound,read,leased,ite_true,Option.map_none,Option.map_some,applyValue,enter,
    List.getElem?_cons_zero,restoredContinuation]
  rfl

private theorem typed_canonical_scalar_restore
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (readerShape : LoanTyping.ScalarReadShape readerBody)
    (readerTyped : LoanTyping.HasType env (Loans.enter code.context.length owner loans) code.context false
      (Lending.read (.var owner) readerBody) first)
    (binder : LoanTyping.Binder env loans code.context false first sort)
    (bodyTyped : LoanTyping.HasType env loans (⟨first,false⟩ :: code.context) false
      (body.subst (single ((Term.var owner).rename Nat.succ))) returnType)
    (stored : code.values[owner]? = some (some (.owner object)))
    (bounded : ValueReduction.signed64 number) (resultOrigin : Term) :
    let next := canonicalContinuation code owner first body resultOrigin (.integer number)
    let extended := consValues (.integer number) meanings
    LoanClosingTyped env loans false next extended type ∧ ValueContext env next extended := by
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at bodyTyped
  let normalized := body.rename (Jihoo.Quantity.openOwner (owner+1))
  have firstKind := (readerShape.read (.var owner)).result_conversion history.wellFormed readerTyped
  have closedFirst : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    simpa only [Term.subst,substArgs] using firstKind.substitution meanings history.wellFormed.closed
  have closureTyped : LoanClosingTyped env loans false (code.child (.lam false first normalized)) meanings
      (.pi false .i64 (returnType.subst (liftSubOne meanings))) := by
    refine ⟨context.closing,.pi false first returnType,.lam binder bodyTyped,?_⟩
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (RawLend.Conv.node (.pi false) (.cons closedFirst.symm (.cons
        (.refl (returnType.subst (liftSubOne meanings))) .nil)))
  have canonicalTyped := enter_integer_closing history closureTyped bounded resultOrigin
  have canonicalContext := (context.child (.lam false first normalized)).enter_integer history
    closureTyped bounded resultOrigin
  have closedSource := typed.closed history
  simp only [shape,Term.subst,substArgs,Op.binders,liftSub] at closedSource
  have finished := LoanTyping.actual_scalar_shape_finish history.wellFormed closedSource
    (readerShape.substitution (liftSubOne meanings)) bounded
  let actual := restoredContinuation code first again body ((Term.var owner).subst code.origins)
    resultOrigin object (.integer number)
  let allMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer number) meanings)
  have actualTyped : LoanTyping.HasType env [] [] true (actual.term.subst allMeanings) type := by
    change LoanTyping.HasType env [] [] true
      (body.subst (consValues ((Term.var owner).subst meanings) (consValues (.integer number) meanings))) type
    rw [continuation_actual_substitution]
    simpa only [Term.subst,liftSub] using finished
  have sourceView := restored_canonical_view code stored first again body resultOrigin (.integer number)
  have related : ∀ index, allMeanings index =
      consValues (.integer number) meanings (Jihoo.Quantity.openOwner (owner+1) index) := by
    intro index
    cases index with
    | zero => simp only [allMeanings,consValues,Term.subst,Jihoo.Quantity.openOwner]
    | succ index => rfl
  rw [sourceView.closed related] at actualTyped
  have converted := (canonicalTyped.closed history).unique history.wellFormed actualTyped
  obtain ⟨closing,localType,localTyped,localConverted⟩ := canonicalTyped
  exact ⟨⟨closing,localType,localTyped,localConverted.trans converted⟩,canonicalContext⟩

/-- A named Index reader opens a fresh lease, reads the actual indexed cell,
closes that lease, and enters both real continuation bindings in 15 steps.
The original Lend projection supplies the canonical continuation's exact
receipt. The read leaves physical owner demand and captured sizes intact,
and all preexisting reader tokens keep their original leases. -/
theorem reachable_named_index_reader_restore_demand (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial term)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial term)).state
    let origin := (Term.var owner).subst code.origins
    let token := state.heap.metadata.heap.nextLease
    let reader := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let readerCode := enter false domain reader code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    let payload := state.heap.cell object offset
    let number := decodeInteger payload
    let next := restoredContinuation code first again body origin readerCode.origin object (.integer number)
    let restored := canonicalContinuation code owner first body readerCode.origin (.integer number)
    let nextMeanings := consValues (.integer number) meanings
    let closed : SizedBufferHeap.IndexedState :=
      ⟨SizedBufferHeap.close (SizedBufferHeap.lend state.heap.metadata object) token,state.heap.cell⟩
    let result := run 15 state
    result = ⟨⟨closed,.evaluate next,state.stack,state.pending⟩,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false reader (.borrow origin)),
        .legacy (.heap (.read token offset payload)),.legacy (.heap (.close token)),
        .legacy (.activate false (.lam false again body) readerCode.origin),.legacy (.activate false body origin)],15⟩ ∧
    result.state.heap.metadata.heap.lease token = none ∧
    result.state.heap.metadata.heap.nextLease = token+1 ∧
    (∀ outer < token, result.state.heap.metadata.heap.lease outer = state.heap.metadata.heap.lease outer) ∧
    ReaderInventory result.state.heap.metadata (readerFrames state.activeStack) ∧
    CanonicalView next restored (Jihoo.Quantity.openOwner (owner+1)) ∧
    LoanClosingTyped env loans false restored nextMeanings type ∧ ValueContext env restored nextMeanings ∧
    OwnerSizes env result.state.heap.metadata restored nextMeanings ∧
    LoanSlots restored loans result.state.activeStack ∧ LoanCoverage restored loans result.state.activeStack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans restored.context restored.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget restored.context.length loans rest ∧
      rest.demand (owner+1) = some 1 ∧ OwnerDemandWorld result.state.heap.metadata restored rest ∧
      OwnerDemandWorld.Total restored rest ∧
      ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  let state := (run fuel (initial term)).state
  let token := state.heap.metadata.heap.nextLease
  let origin := (Term.var owner).subst code.origins
  let reader := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
  let readerCode := enter false domain reader code.context code.origins code.values
    (.borrow origin) (some (.reference token))
  let number := decodeInteger (state.heap.cell object offset)
  let restored := canonicalContinuation code owner first body readerCode.origin (.integer number)
  have widths := typed.reference_index_heap history sizes shape stored
  obtain ⟨_,_,offsetBound,within,length,_,_⟩ := widths
  rw [shape] at checked
  obtain ⟨_,sort,returnType,readerReceipt,mode,rest,_,_,_,_,readerTyped,binder,bodyTyped,_,
    _,restProjected,_,ownerOne,receiptShape⟩ := LoanTyping.ResourceQuantity.dependent_raw_project_contract checked
  have one := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checked
  have live := (world.live_once owner object 0 stored one).1
  have ran := named_index_complete_steps state evaluating shape stored live offsetBound (length.symm ▸ within)
  rw [receiptShape] at world complete budget
  obtain ⟨_,_,restWorld,restTotal,_⟩ := world.sequence complete
  have scopeValid := NativeQuantity.demand_localScopes _ ownerOne
  obtain ⟨newWorld,newTotal⟩ := restWorld.enter_integer_scope restTotal scopeValid first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) readerCode.origin number
  have demand := demand_under_checked_scope scopeValid owner
  have restoredOne : rest.demand (owner+1) = some 1 := demand.symm.trans ownerOne
  have aliases : ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) →
      rest.demand (alias+1) = some 0 := by
    intro alias other found
    have unused := restWorld.exclusive owner alias object 0 (Ne.symm other) stored found ownerOne
    exact (demand_under_checked_scope scopeValid alias).symm.trans unused
  have bounded : ValueReduction.signed64 number :=
    decode_integer_bound ((initial_run_numbers term fuel).cells object offset)
  obtain ⟨nextTyped,nextContext⟩ := typed_canonical_scalar_restore history typed context shape .index
    readerTyped binder bodyTyped stored bounded readerCode.origin
  have nextSizes := (reachable_run_owner_sizes term fuel 15 sizes).enter_integer first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) readerCode.origin number
  have nextSlots := slots.enter entered false first (body.rename (Jihoo.Quantity.openOwner (owner+1)))
    readerCode.origin (some (.integer number))
  have nextCoverage := coverage.enter_nonowner entered false first
    (body.rename (Jihoo.Quantity.openOwner (owner+1))) readerCode.origin (some (.integer number))
    (by intro queried impossible; cases impossible)
  have inventory := (run_invariant 15 (initial_run_invariant term fuel)).2
  have view := restored_canonical_view code stored first again body readerCode.origin (.integer number)
  obtain ⟨lease,fresh,liveSame,_,outer⟩ := reader_close_metadata state.heap.metadata object
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at restProjected
  refine ⟨ran,?_⟩
  dsimp only at ran ⊢
  rw [ran] at nextSizes inventory ⊢
  refine ⟨lease,fresh,outer,inventory,view,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,
    rest,restProjected,budget.sequence.2.scope entered,restoredOne,?_,newTotal,aliases⟩
  exact ⟨fun index object uses selected demanded => by
    rw [liveSame]
    exact newWorld.live_once index object uses selected demanded,newWorld.exclusive⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
