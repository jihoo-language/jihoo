import Jihoo.NativeBindingMachineMutableCalleeCleanup

/-! A checked Store returns its same physical Buffer through the actual
machine. A subsequent Free can consume that result while unrelated pending
owners retain their resource, length, and indexed cell interpretations. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity

theorem projectRaw_free_operands
    (checked : projectRaw (fuel+1) env loans ctx (.free argument tail) = some receipt) :
    ∃ argumentReceipt tailReceipt,
      projectRaw fuel env loans ctx argument = some argumentReceipt ∧
      projectRaw fuel env loans ctx tail = some tailReceipt ∧
      receipt = .seq argumentReceipt (.seq tailReceipt .pure) := by
  have same : projectRaw (fuel+1) env loans ctx (.free argument tail) =
      projectRaw (fuel+1) env loans ctx (.strict argument tail) := by
    rfl
  exact strict_projection (same ▸ checked)

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

/-- The checked named Store selects its physical owner and preserves the
original allocation, value annotation and reader inventory. The result is
available to a real pending operation under its original Buffer type. -/
theorem reachable_named_store_owned_result (program : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .store (.var owner) (.natural offset) (.integer value)
      (.decide (.natural offset) (.natural count)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt) :
    let state := (run fuel (initial program)).state
    ∃ object heap, code.values[owner]? = some (some (.owner object)) ∧ receipt.demand owner = some 1 ∧
      run 7 state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
        [.store object offset (encodeInteger value)],7⟩ ∧
      heap.metadata = state.heap.metadata ∧
      OwnedResult env heap.metadata state.activeStack object (code.term.subst meanings) type ∧
      decodeInteger (heap.cell object offset) = value ∧
      (∀ queried index, queried ≠ object ∨ index ≠ offset → heap.cell queried index = state.heap.cell queried index) := by
  let state := (run fuel (initial program)).state
  have ⟨closing,_,source,_⟩ := typed
  rw [shape] at source
  obtain ⟨size,sourceOwner,_,_,_,_⟩ := source.store_inputs
  have checkedOwner : LoanClosingTyped env loans false (code.child (.var owner)) meanings ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,sourceOwner,.refl _⟩
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  obtain ⟨actual,stored,kind⟩ := (context.child (.var owner)).variable_kind history checkedOwner aligned rfl
  have buffer : ValueKind env actual (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  obtain ⟨used,inactive⟩ := LoanTyping.ResourceQuantity.projectRaw_literal_store_inactive (shape ▸ checked) budget
  have live := (world.live_once owner object 0 stored used).1
  have invariant := initial_run_invariant program fuel
  obtain ⟨heap,written,metadata,length,offsetBound,valueBound,resultType,newCell,otherCells⟩ :=
    canonical_store_cell history state.heap invariant.1 invariant.2 (CanonicalView.identity code) typed sizes shape stored
      live coverage checked budget
  have older := invariant.1.allocated object live
  have resultSize : OwnerSize env heap.metadata object type := by
    rw [metadata]
    exact ⟨older,count,length,resultType⟩
  have owned : OwnedResult env heap.metadata state.activeStack object (code.term.subst meanings) type :=
    ⟨typed.closed history,resultSize,metadata.symm ▸ live,coverage.inactive stored inactive⟩
  exact ⟨object,heap,stored,used,literal_store_steps state evaluating shape stored offsetBound valueBound written,
    metadata,owned,newCell,otherCells⟩

/-- The Pending Free frame consumes a previously checked owned result.
Liveness and the exclusion of an active physical reader discharge the exact
native release guard, preserving the indexed cells and suspended frames. -/
theorem free_owned_result_step (state : State) (invariant : Invariant state)
    (owned : OwnedResult env state.heap.metadata state.activeStack object source type)
    (returned : state.control = .returned (.owner object)) (shape : state.stack = .free tail :: stack) :
    let released : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩
    step state = some (⟨released,.evaluate tail,stack,state.pending⟩,some (.legacy (.heap (.free object)))) := by
  have guard := (invariant.2.free_guard_iff invariant.1).mpr owned.noReaders
  simp only [step,returned,shape,returnAction,executeLegacy,execute,owned.live,guard,ite_true,Option.map_some]

/-- A checked Store can supply the actual operand of Free. The resulting
tail keeps its dependent type and complete resource receipt. The whole
prefix preserves the sizes, leases and indexed cells of every physical
owner with positive demand in the separated sibling receipt. -/
theorem reachable_store_then_free_preserves_sibling (program : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .free
      (.store (.var owner) (.natural offset) (.integer value) (.decide (.natural offset) (.natural count))) tail)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt)
    (sibling : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code later)
    (separated : OwnerDemandSeparation code receipt later) :
    let state := (run fuel (initial program)).state
    let result := run 9 state
    let next := code.child tail
    ∃ object residual,
      code.values[owner]? = some (some (.owner object)) ∧
      result.state.heap.metadata = SizedBufferHeap.release state.heap.metadata object ∧
      result.state.control = .evaluate next ∧ result.state.stack = state.stack ∧
      result.state.pending = state.pending ∧ result.steps = 9 ∧
      result.events = [.store object offset (encodeInteger value),.legacy (.heap (.free object))] ∧
      decodeInteger (result.state.heap.cell object offset) = value ∧
      LoanClosingTyped env loans false next meanings type ∧ ValueContext env next meanings ∧
      OwnerSizes env result.state.heap.metadata code meanings ∧
      LoanSlots code loans result.state.activeStack ∧ LoanCoverage code loans result.state.activeStack ∧
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans next.context next.term = some residual ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans residual ∧
      OwnerDemandWorld result.state.heap.metadata next residual ∧ OwnerDemandWorld.Total next residual ∧
      (∀ alias, code.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0) ∧
      OwnerDemandWorld result.state.heap.metadata code later ∧
      ∀ slot wanted uses, code.values[slot]? = some (some (.owner wanted)) → later.demand slot = some (uses+1) →
        .free wanted ∉ result.events.filterMap Event.lifecycle? ∧
        ∀ index, result.state.heap.cell wanted index = state.heap.cell wanted index := by
  let state := (run fuel (initial program)).state
  let storeTerm := Term.store (.var owner) (.natural offset) (.integer value) (.decide (.natural offset) (.natural count))
  let next := code.child tail
  have sourceShape : code.term = .free storeTerm tail := shape
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [sourceShape] at source
  obtain ⟨length,storeSource⟩ := source.free_owner_inputs
  have storeTyped : LoanClosingTyped env loans false (code.child storeTerm) meanings ((Term.buffer length).subst meanings) :=
    ⟨closing,.buffer length,storeSource,.refl _⟩
  have tailTyped : LoanClosingTyped env loans false next meanings type :=
    ⟨closing,localType,source.free_tail,converted⟩
  obtain ⟨storeReceipt,residual,storeChecked,tailChecked,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_free_operands (sourceShape ▸ checked)
  obtain ⟨storeWorld,_,restWorld,restTotal,disjoint⟩ :=
    (receiptShape ▸ world).sequence (receiptShape ▸ complete)
  obtain ⟨tailWorld,tailTotal,_,_,_⟩ := restWorld.sequence restTotal
  have fullBudget := receiptShape ▸ budget
  let entered := (run (fuel+1) (initial program)).state
  have enterRun : run 1 state = ⟨⟨state.heap,.evaluate (code.child storeTerm),
      .free next :: state.stack,state.pending⟩,[],1⟩ := by
    change state.control = .evaluate code at evaluating
    have enterStep : step state = some (⟨state.heap,.evaluate (code.child storeTerm),
        .free next :: state.stack,state.pending⟩,none) := by
      rw [step,evaluating]
      dsimp only
      rw [sourceShape]
      simp only [evaluateAction,sourceShape,executeLegacy,execute,Option.map_none]
      rfl
    rw [run,enterStep]
    rfl
  have reached : entered = (run 1 state).state := by
    have fields := congrArg Result.state (run_add fuel 1 (initial program))
    exact fields
  have storeEvaluating : entered.control = .evaluate (code.child storeTerm) := by rw [reached,enterRun]
  have enterHeap : entered.heap = state.heap := by rw [reached,enterRun]
  have enterFrames : readerFrames entered.activeStack = readerFrames state.activeStack := by
    rw [reached,enterRun]
    rfl
  have storeStart : OwnerDemandWorld state.heap.metadata (code.child storeTerm) storeReceipt :=
    ⟨storeWorld.live_once,storeWorld.exclusive⟩
  obtain ⟨object,heap,stored,used,storeRun,metadata,owned,newCell,otherCells⟩ :=
    reachable_named_store_owned_result program (fuel+1) history storeEvaluating rfl storeTyped
      (context.child _) (enterHeap.symm ▸ sizes.child _)
      ((coverage.child _).same_frames enterFrames.symm) storeChecked fullBudget.sequence.1 (enterHeap.symm ▸ storeStart)
  change run 7 entered = ⟨⟨heap,.returned (.owner object),entered.stack,entered.pending⟩,
    [.store object offset (encodeInteger value)],7⟩ at storeRun
  have ownedAtReturn : OwnedResult env (run 7 entered).state.heap.metadata (run 7 entered).state.activeStack
      object ((code.child storeTerm).term.subst meanings) ((Term.buffer length).subst meanings) := by
    rw [storeRun]
    exact owned
  have returned : (run 7 entered).state.control = .returned (.owner object) := by rw [storeRun]
  have frame : (run 7 entered).state.stack = .free next :: state.stack := by
    rw [storeRun]
    change entered.stack = _
    rw [reached,enterRun]
  have release := free_owned_result_step (run 7 entered).state
    (run_invariant 7 (initial_run_invariant program (fuel+1))) ownedAtReturn returned frame
  have afterStore : run 8 entered = ⟨⟨⟨SizedBufferHeap.release state.heap.metadata object,heap.cell⟩,
      .evaluate next,state.stack,state.pending⟩,
      [.store object offset (encodeInteger value),.legacy (.heap (.free object))],8⟩ := by
    have combined := run_add 7 1 entered
    dsimp only at combined release
    have one : run 1 (run 7 entered).state =
        ⟨⟨⟨SizedBufferHeap.release (run 7 entered).state.heap.metadata object,(run 7 entered).state.heap.cell⟩,
          .evaluate next,state.stack,(run 7 entered).state.pending⟩,[.legacy (.heap (.free object))],1⟩ := by
      rw [run,release]
      rfl
    rw [one,storeRun] at combined
    change heap.metadata = entered.heap.metadata at metadata
    rw [metadata,enterHeap] at combined
    have pending : entered.pending = state.pending := by rw [reached,enterRun]
    rw [pending] at combined
    exact combined
  have fullRun : run 9 state = ⟨⟨⟨SizedBufferHeap.release state.heap.metadata object,heap.cell⟩,
      .evaluate next,state.stack,state.pending⟩,
      [.store object offset (encodeInteger value),.legacy (.heap (.free object))],9⟩ := by
    have combined := run_add 1 8 state
    dsimp only at combined
    rw [← reached,afterStore] at combined
    have enterEvents := congrArg Result.events enterRun
    have enterSteps := congrArg Result.steps enterRun
    rw [enterEvents,enterSteps] at combined
    exact combined
  have noneAfterStore (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      (Control.seq residual .pure).demand alias = some 0 :=
    disjoint owner alias object 0 stored found used
  have noTail (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      residual.demand alias = some 0 := by
    have zero := noneAfterStore alias found
    cases observed : residual.demand alias with
    | none => simp [Control.demand,observed] at zero
    | some amount => simpa [Control.demand,observed] using zero
  have wholeUsed : receipt.demand owner = some 1 := by
    rw [receiptShape]
    simp [Control.demand,used,noTail owner stored]
  have siblingAlias (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      later.demand alias = some 0 :=
    separated owner alias object 0 stored found wholeUsed
  have distinct {uses : Nat} {control : Jihoo.Quantity.Control}
      (zero : ∀ alias, code.values[alias]? = some (some (.owner object)) → control.demand alias = some 0)
      {slot wanted : Nat} (found : code.values[slot]? = some (some (.owner wanted)))
      (wantedUse : control.demand slot = some (uses+1)) : wanted ≠ object := by
    intro same
    subst wanted
    rw [zero slot found] at wantedUse
    cases wantedUse
  have noRelease (wanted : Nat) (different : wanted ≠ object) :
      .free wanted ∉ (run 9 state).events.filterMap Event.lifecycle? := by
    rw [fullRun]
    change SizedBufferHeap.Event.free wanted ∉ [SizedBufferHeap.Event.free object]
    exact fun member => different (SizedBufferHeap.Event.free.inj (List.mem_singleton.mp member))
  have tailStart : OwnerDemandWorld state.heap.metadata next residual :=
    ⟨tailWorld.live_once,tailWorld.exclusive⟩
  have tailAfter := OwnerDemandWorld.run_without_demanded_free program fuel 9 tailStart
    (fun _ wanted _ found demand => noRelease wanted (distinct noTail found demand))
  have siblingAfter := OwnerDemandWorld.run_without_demanded_free program fuel 9 sibling
    (fun _ wanted _ found demand => noRelease wanted (distinct siblingAlias found demand))
  have finalFrames : readerFrames (run 9 state).state.activeStack = readerFrames state.activeStack := by
    rw [fullRun]
    rfl
  refine ⟨object,residual,stored,?_,?_,?_,?_,?_,?_,?_,tailTyped,context.child tail,
    reachable_run_owner_sizes program fuel 9 sizes,slots.same_frames finalFrames.symm,
    coverage.same_frames finalFrames.symm,tailChecked,fullBudget.sequence.2.sequence.1,
    tailAfter,tailTotal,noTail,siblingAfter,?_⟩
  · rw [fullRun]
  · rw [fullRun]
  · rw [fullRun]
  · rw [fullRun]
  · rw [fullRun]
  · rw [fullRun]
  · rw [fullRun]
    exact newCell
  · intro slot wanted uses found demand
    have different := distinct siblingAlias found demand
    refine ⟨noRelease wanted different,fun index => ?_⟩
    rw [fullRun]
    exact (otherCells wanted index (.inl different)).trans (congrArg (fun h : SizedBufferHeap.IndexedState => h.cell wanted index) enterHeap)

namespace Examples

private def ownedAfterStoreCleanup : Term :=
  let temporary := Term.buffer (.natural 1)
  let target := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let store := Term.store (.var 1) (.natural 0) (.integer 41) (.decide (.natural 0) (.natural 1))
  let cleanup := Term.free store (.integer 0)
  let release := Term.lam false .i64 (.lam false target (.free (.var 0) (.var 1)))
  let body := Term.load (.var 0) (.natural 1) bound release
  let call := Term.app (.strict cleanup (.lam false target body)) (.var 0)
  let written := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) bound
  let withTarget := Term.app (.lam false target call) written
  .app (.lam false temporary withTarget) (.alloc (.natural 1) (.integer 0))

set_option maxRecDepth 4096 in
/-- A checked computed callee updates and frees its captured Buffer before
the pending argument loads the original value from its own distinct cell. -/
theorem computed_callee_stores_and_frees_unrelated_capture :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,ownedAfterStoreCleanup⟩ =
      some ⟨.i64,ownedAfterStoreCleanup⟩ ∧
    let result := run 80 (initial ownedAfterStoreCleanup)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.nextObject = 2 ∧
      result.state.heap.metadata.heap.live 0 = false ∧ result.state.heap.metadata.heap.live 1 = false ∧
      decodeInteger (result.state.heap.cell 0 0) = 41 ∧ decodeInteger (result.state.heap.cell 1 1) = 7 := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
