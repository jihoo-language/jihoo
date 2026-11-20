import Jihoo.NativeBindingMachineMutableArithmeticReaderHandoff

/-! A checked reader can select an indexed read using actual captures and
the erased comparison evidence. Failed guards recursively select another
guard or the ordinary signed arithmetic fragment. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

inductive GuardedReader where
  | arithmetic (reader : ArithmeticReader)
  | less (offsetSlot countSlot : Nat) (fallback : GuardedReader)

namespace GuardedReader

private def yesRead (offsetSlot : Nat) : Term := .index (.var 1) (.var (offsetSlot+2)) (.var 0)

def term : GuardedReader → Term
  | .arithmetic reader => reader.term
  | .less offsetSlot countSlot fallback =>
      .ifLt (.var (offsetSlot+1)) (.var (countSlot+1)) (yesRead offsetSlot) fallback.term

def Ready (values : List (Option Value)) (length : Nat) : GuardedReader → Prop
  | .arithmetic reader => reader.Ready length
  | .less offsetSlot countSlot fallback =>
      ∃ offset count,
        values[offsetSlot+1]? = some (some (.natural offset)) ∧
        values[countSlot+1]? = some (some (.natural count)) ∧
        (offset < count → offset < length) ∧ fallback.Ready values length

private def capture (code : Code) (slot : Nat) : Nat :=
  match code.values[slot]? with | some (some (.natural number)) => number | _ => 0

def replay (code : Code) (heap : SizedBufferHeap.IndexedState) (token object : Nat)
    (stack : List Frame) : GuardedReader → ArithmeticReader.Trace
  | .arithmetic reader => reader.replay code heap token object stack
  | .less offsetSlot countSlot fallback =>
      let offset := capture code (offsetSlot+1)
      let count := capture code (countSlot+1)
      if offset < count then
        let payload := heap.cell object offset
        ⟨.integer (decodeInteger payload),[.legacy (.heap (.read token offset payload))],10⟩
      else
        let rest := replay code heap token object stack fallback
        {rest with ticks := 5+rest.ticks}

set_option linter.unusedSimpArgs false in
private theorem true_guard_steps (heap : SizedBufferHeap.IndexedState) (code : Code) (stack : List Frame)
    (pending : List (BufferFrame × List Frame)) (fallback : GuardedReader)
    (boundReference : code.values[0]? = some (some (.reference token)))
    (storedOffset : code.values[offsetSlot+1]? = some (some (.natural offset)))
    (storedCount : code.values[countSlot+1]? = some (some (.natural count)))
    (compared : offset < count) (read : heap.read token offset = some (heap.cell object offset)) :
    run 10 ⟨heap,.evaluate (code.child (term (.less offsetSlot countSlot fallback))),stack,pending⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.cell object offset))),stack,pending⟩,
        [.legacy (.heap (.read token offset (heap.cell object offset)))],10⟩ := by
  simp only [run,step,term,yesRead,evaluateAction,Code.child,returnAction,executeLegacy,execute,branchCode,
    storedOffset,storedCount,boundReference,List.getElem?_cons_succ,read,compared,decide_true,
    Bool.false_eq_true,↓reduceIte,Option.map_none,Option.map_some]
  rfl

set_option linter.unusedSimpArgs false in
private theorem false_guard_steps (heap : SizedBufferHeap.IndexedState) (code : Code) (stack : List Frame)
    (pending : List (BufferFrame × List Frame)) (fallback : GuardedReader)
    (storedOffset : code.values[offsetSlot+1]? = some (some (.natural offset)))
    (storedCount : code.values[countSlot+1]? = some (some (.natural count))) (compared : ¬ offset < count) :
    run 5 ⟨heap,.evaluate (code.child (term (.less offsetSlot countSlot fallback))),stack,pending⟩ =
      ⟨⟨heap,.evaluate (code.child fallback.term),stack,pending⟩,[],5⟩ := by
  simp only [run,step,term,evaluateAction,Code.child,returnAction,executeLegacy,execute,storedOffset,storedCount,
    compared,decide_false,Bool.false_eq_true,↓reduceIte,Option.map_none]
  rfl

/-- Every failed guard contributes exactly its five real transitions with
no read. The selected comparison enters its erased binder and reads the
current indexed cell. An arithmetic fallback retains its precise fault trace. -/
theorem replay_executes (reader : GuardedReader) (heap : SizedBufferHeap.IndexedState) (code : Code)
    (stack : List Frame) (pending : List (BufferFrame × List Frame))
    (argument : code.values[0]? = some (some (.reference token)))
    (leased : heap.metadata.heap.lease token = some object) (ready : reader.Ready code.values (heap.metadata.length object)) :
    let trace := reader.replay code heap token object stack
    run trace.ticks ⟨heap,.evaluate (code.child reader.term),stack,pending⟩ = trace.result heap stack pending := by
  induction reader with
  | arithmetic reader => exact reader.replay_executes heap pending code stack argument leased ready
  | less offsetSlot countSlot fallback ih =>
      obtain ⟨offset,count,storedOffset,storedCount,within,fallbackReady⟩ := ready
      by_cases compared : offset < count
      · have read : heap.read token offset = some (heap.cell object offset) := by
          unfold SizedBufferHeap.IndexedState.read
          rw [leased]
          change (if offset < heap.metadata.length object then some (heap.cell object offset) else none) = _
          rw [ite_eq_left (within compared)]
        simp only [replay,capture,storedOffset,storedCount,compared,↓reduceIte,ArithmeticReader.Trace.result]
        exact true_guard_steps heap code stack pending fallback argument storedOffset storedCount compared read
      · have earlier := false_guard_steps heap code stack pending fallback storedOffset storedCount compared
        have later := ih fallbackReady
        simp only [replay,capture,storedOffset,storedCount,compared,↓reduceIte]
        rw [run_add 5,earlier]
        dsimp only
        rw [later]
        cases outcome : (fallback.replay code heap token object stack).outcome <;>
          simp [ArithmeticReader.Trace.result,outcome]

private theorem observed_natural_slot
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (closing : LoanTyping.Ghost.Substitution env original.context [] meanings)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (typed : LoanTyping.HasType env loans original.context false (.var slot) .u64) :
    ∃ number, original.values[slot]? = some (some (.natural number)) ∧
      meanings slot = .natural number ∧ number < 2^64 := by
  have variableType : LoanClosingTyped env loans false (original.child (.var slot)) meanings .u64 :=
    ⟨closing,.u64,typed,by simp only [Term.subst,substArgs]; exact .refl _⟩
  obtain ⟨value,found,kind⟩ := (context.child (.var slot)).variable_kind history variableType aligned rfl
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have meaning := context.scalars.1 slot number found
  have numeral : LoanTyping.HasType env [] [] true (.natural number) .u64 := by
    simpa only [Term.subst,substArgs,meaning] using typed.ghostSubstitution history.wellFormed closing
  exact ⟨number,found,meaning,numeral.natural_bound⟩

private theorem true_guard_within
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (closing : LoanTyping.Ghost.Substitution env original.context [] meanings)
    (sizes : OwnerSizes env heap original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (yes : LoanTyping.HasType env loans (⟨.lt (.var offsetSlot) (.var countSlot),true⟩ :: original.context)
      false (dynamicRead owner offsetSlot) type)
    (offsetMeaning : meanings offsetSlot = .natural offset) (countMeaning : meanings countSlot = .natural count)
    (offsetBound : offset < 2^64) (countBound : count < 2^64) (compared : offset < count) :
    offset < heap.length object := by
  let proof := Term.decide (.natural offset) (.natural count)
  let yesMeanings := consValues proof meanings
  let branch := branchCode false (original.child (dynamicRead owner offsetSlot)) (.var offsetSlot) (.var countSlot)
  have comparison : LoanTyping.HasType env [] [] true proof
      ((Term.lt (.var offsetSlot) (.var countSlot)).subst meanings) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,offsetMeaning,countMeaning] using
      (show LoanTyping.HasType env [] [] true proof (.lt (.natural offset) (.natural count)) from
        .decide offsetBound countBound compared)
  have extended : LoanTyping.Ghost.Substitution env branch.context [] yesMeanings := closing.consValues comparison
  obtain ⟨size,ownerTyped,_,evidence⟩ := yes.named_index_owner history.wellFormed
  have branchSizes : OwnerSizes env heap branch yesMeanings := sizes.branch false _ _ _ _
  have ownerStored : branch.values[owner+1]? = some (some (.owner object)) := by
    simpa only [branch,branchCode,Code.child,List.getElem?_cons_succ] using stored
  have sizeTyped := branchSizes.typed_variable history ownerTyped ownerStored
  have bufferSize : OwnerSize env heap object (.buffer (size.subst yesMeanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizeTyped
  have proofChecked := evidence.ghostSubstitution history.wellFormed extended
  have proofTyped : LoanTyping.HasType env [] [] true proof (.lt (.natural offset) (size.subst yesMeanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,yesMeanings,consValues,offsetMeaning] using proofChecked
  have expected := (proofTyped.principalView.lt_injective history.wellFormed.admissible).2
  have length := ((bufferSize.buffer_length history).trans expected.symm).natural_injective history.wellFormed.admissible
  exact length.symm ▸ compared

/-- CODE typing of the real specialized reader selects the runtime captures.
The true branch's erased binder receives the observed comparison proof and
its checked Index type identifies the physical Buffer length. -/
theorem checked_ready (reader : GuardedReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (closing : LoanTyping.Ghost.Substitution env original.context [] meanings)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (sizes : OwnerSizes env heap original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (typed : LoanTyping.HasType env loans original.context false (Lending.read (.var owner) reader.term) type)
    (domain origin : Term) (token : Nat) :
    let entry := enter false domain reader.term original.context original.origins original.values
      (.borrow origin) (some (.reference token))
    reader.Ready entry.values (heap.length object) ∧ LoanTyping.Conversion.Conv env .i64 type := by
  induction reader generalizing type with
  | arithmetic reader => exact reader.checked_ready history closing sizes stored (typed.ghost [])
  | less offsetSlot countSlot fallback ih =>
      simp only [term,Lending.read,Term.subst,substArgs,Op.binders,liftSub,liftSubOne,single,
        yesRead,Term.rename,renameArgs,liftRenaming] at typed
      obtain ⟨result,left,right,yes,no⟩ := typed.ifLt_inputs
      obtain ⟨offset,storedOffset,meaningOffset,boundedOffset⟩ := observed_natural_slot history closing context aligned left
      obtain ⟨count,storedCount,meaningCount,boundedCount⟩ := observed_natural_slot history closing context aligned right
      obtain ⟨fallbackReady,fallbackType⟩ := ih no
      have originalType := (LoanTyping.HasType.ifLt left right yes no).unique history.wellFormed typed
      exact ⟨⟨offset,count,storedOffset,storedCount,true_guard_within history closing sizes stored yes
        meaningOffset meaningCount boundedOffset boundedCount,fallbackReady⟩,fallbackType.trans originalType⟩

end GuardedReader

/-- The exact original checked Lend resource projection supplies the guarded
reader's CODE typing. Actual capture alignment and the indexed lease turn the
selected branch into an exact replay. The observed scalar closes at the
original continuation annotation, while overflow preserves its active lease. -/
theorem reachable_guarded_lend_close (term : Term) (fuel : Nat) (reader : GuardedReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false original meanings type)
    (context : ValueContext env original meanings)
    (originalShape : original.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans original.context original.term = some receipt)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate (enter false domain reader.term
      original.context original.origins original.values (.borrow ((Term.var owner).subst original.origins))
      (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack = .lendFinish token object
      (some (original.context.length-owner)) ((Term.var owner).subst original.origins) resultOrigin
      (original.child (.lam false first (.lam false again body))) :: stack) :
    let state := (run fuel (initial term)).state
    let entry := enter false domain reader.term original.context original.origins original.values
      (.borrow ((Term.var owner).subst original.origins)) (some (.reference token))
    let trace := reader.replay entry state.heap token object state.stack
    let result := run trace.ticks state
    result = trace.result state.heap state.stack state.pending ∧
    match trace.outcome with
    | .integer number =>
        let closed := SizedBufferHeap.close state.heap.metadata token
        let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate (original.child (.lam false first (.lam false again body))),
          .lendContinuation object ((Term.var owner).subst original.origins) resultOrigin (.integer number) :: stack,
          state.pending⟩
        LoanTyping.HasType env [] [] true (.integer number) (first.subst meanings) ∧
          step result.state = some (next,some (.legacy (.heap (.close token)))) ∧
          ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
          (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
          ReaderInventory closed (readerFrames next.activeStack)
    | .overflow _ =>
        step result.state = none ∧ result.state.heap.metadata.heap.lease token = some object := by
  let state := (run fuel (initial term)).state
  let origin := (Term.var owner).subst original.origins
  let entry := enter false domain reader.term original.context original.origins original.values
    (.borrow origin) (some (.reference token))
  let trace := reader.replay entry state.heap token object state.stack
  rw [originalShape] at checked
  obtain ⟨_,_,_,_,_,_,_,_,_,_,readerTyped,_,_,_,_,_,_,_,_⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checked
  have entryAligned := initial_run_code_aligned term fuel SizedBufferHeap.empty evaluating
  have aligned : CodeAligned original := by
    change SlotsAligned (⟨domain,false⟩ :: original.context) (some (.reference token) :: original.values) at entryAligned
    cases entryAligned with | retained _ previous => exact previous
  obtain ⟨ready,firstType⟩ := reader.checked_ready history typed.1 context aligned sizes stored readerTyped domain origin token
  have observedType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    simpa only [Term.subst,substArgs] using firstType.substitution meanings history.wellFormed.closed
  have entries : ReaderInventory state.heap.metadata
      ((token,object,some (original.context.length-owner)) :: readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
    simpa only [state,State.activeStack,stackShape,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?]
      using (initial_run_invariant term fuel).2
  have leased := entries.live _ List.mem_cons_self
  have executed := reader.replay_executes state.heap entry state.stack state.pending (by rfl) leased ready
  change run trace.ticks ⟨state.heap,.evaluate entry,state.stack,state.pending⟩ =
    trace.result state.heap state.stack state.pending at executed
  change state.control = .evaluate entry at evaluating
  rw [← evaluating] at executed
  exact ⟨executed,reachable_replayed_integer_close term fuel trace history typed originalShape observedType
    stackShape leased executed⟩

/-- After a successful guarded reader, the exact close and both retained
activations restore the continuation type and the checked owner demand.
The original erased comparison proof does not become a runtime capture. -/
theorem reachable_guarded_reader_restore_demand (term : Term) (fuel : Nat) (reader : GuardedReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false original meanings type) (context : ValueContext env original meanings)
    (originalShape : original.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans original.context original.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget original.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata original receipt)
    (complete : OwnerDemandWorld.Total original receipt)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate (enter false domain reader.term
      original.context original.origins original.values (.borrow ((Term.var owner).subst original.origins))
      (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack = .lendFinish token object
      (some (original.context.length-owner)) ((Term.var owner).subst original.origins) resultOrigin
      (original.child (.lam false first (.lam false again body))) :: stack)
    (slots : LoanSlots original loans (stack ++ (run fuel (initial term)).state.pending.flatMap Prod.snd))
    (coverage : LoanCoverage original loans (stack ++ (run fuel (initial term)).state.pending.flatMap Prod.snd))
    (entered : Loans.Entered original.context.length loans) :
    let state := (run fuel (initial term)).state
    let origin := (Term.var owner).subst original.origins
    let entry := enter false domain reader.term original.context original.origins original.values
      (.borrow origin) (some (.reference token))
    let trace := reader.replay entry state.heap token object state.stack
    trace.outcome = .integer number →
    let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close state.heap.metadata token,state.heap.cell⟩
    let actual := restoredContinuation original first again body origin resultOrigin object (.integer number)
    let canonical := canonicalContinuation original owner first body resultOrigin (.integer number)
    let nextMeanings := consValues (.integer number) meanings
    let result := run (trace.ticks+5) state
    result = ⟨⟨closed,.evaluate actual,stack,state.pending⟩,
      trace.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) resultOrigin),
        .legacy (.activate false body origin)],trace.ticks+5⟩ ∧
    closed.metadata.heap.lease token = none ∧
    (∀ other, other ≠ token → closed.metadata.heap.lease other = state.heap.metadata.heap.lease other) ∧
    ¬ StateReferenceOccurs token result.state ∧ ReaderInventory closed.metadata (readerFrames result.state.activeStack) ∧
    CanonicalView actual canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
    LoanClosingTyped env loans false canonical nextMeanings type ∧ ValueContext env canonical nextMeanings ∧
    OwnerSizes env closed.metadata canonical nextMeanings ∧ LoanSlots canonical loans result.state.activeStack ∧
    LoanCoverage canonical loans result.state.activeStack ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans canonical.context canonical.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget canonical.context.length loans rest ∧ rest.demand (owner+1) = some 1 ∧
      OwnerDemandWorld closed.metadata canonical rest ∧ OwnerDemandWorld.Total canonical rest ∧
      ∀ alias, alias ≠ owner → original.values[alias]? = some (some (.owner object)) → rest.demand (alias+1) = some 0 := by
  let state := (run fuel (initial term)).state
  let origin := (Term.var owner).subst original.origins
  let entry := enter false domain reader.term original.context original.origins original.values
    (.borrow origin) (some (.reference token))
  let trace := reader.replay entry state.heap token object state.stack
  let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close state.heap.metadata token,state.heap.cell⟩
  let actual := restoredContinuation original first again body origin resultOrigin object (.integer number)
  dsimp only
  intro success
  obtain ⟨executed,exit⟩ := reachable_guarded_lend_close term fuel reader history typed context originalShape
    checked sizes stored evaluating stackShape
  change trace.outcome = .integer number at success
  rw [success] at exit
  dsimp only at exit
  obtain ⟨argument,closedStep,_,retired,otherLeases,inventory⟩ := exit
  have afterReplay := resume_lend_continuation_steps _ closed original first again body origin resultOrigin number
    token object stack state.pending closedStep
  have finished : run (trace.ticks+5) state = ⟨⟨closed,.evaluate actual,stack,state.pending⟩,
      trace.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) resultOrigin),
        .legacy (.activate false body origin)],trace.ticks+5⟩ := by
    rw [run_add trace.ticks]
    dsimp only
    rw [afterReplay,executed]
    rfl
  obtain ⟨savedReady,stackReady,pendingReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  have actualReady : CodeReferences token actual := ValuesReferences.retained .owner (.retained .integer savedReady)
  have absent : ¬ StateReferenceOccurs token ⟨closed,.evaluate actual,stack,state.pending⟩ := by
    intro occurs
    rcases occurs with (control | ⟨frame,member,occurs⟩) | pending
    · exact actualReady.fresh_absent control
    · exact stackReady.fresh_absent member occurs
    · exact pendingReady.fresh_absent pending
  have closedSizes := reachable_run_owner_sizes term fuel (trace.ticks+5) sizes
  rw [finished] at closedSizes
  have closedWorld : OwnerDemandWorld closed.metadata original receipt := ⟨world.live_once,world.exclusive⟩
  obtain ⟨nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,rest⟩ :=
    canonical_integer_restore_demand history originalShape typed context argument closedSizes slots coverage entered stored
      (originalShape ▸ checked) budget closedWorld complete resultOrigin
  refine ⟨finished,retired,otherLeases,?_,?_,restored_canonical_view original stored first again body resultOrigin _,
    nextTyped,nextContext,nextSizes,?_,?_,rest⟩
  · exact finished.symm ▸ absent
  · exact finished.symm ▸ inventory
  · exact finished.symm ▸ nextSlots
  · exact finished.symm ▸ nextCoverage

namespace Examples

private def guardedCaptures : Term :=
  let reader := GuardedReader.less 2 3 (.less 1 3 (.arithmetic (.literal 5)))
  let lend := Term.lend (.var 0) (.lam false (.ref (.buffer (.var 3))) reader.term)
    (.lam false .i64 (.lam false (.buffer (.var 4)) (.free (.var 0) (.var 1))))
  let allocated := Term.app (.lam false (.buffer (.var 2)) lend) (.alloc (.var 2) (.integer 7))
  let second := Term.app (.lam false .u64 allocated) (.natural 1)
  let first := Term.app (.lam false .u64 second) (.natural 3)
  .app (.lam false .u64 first) (.natural 2)

private def guardedReadOffsets (events : List Event) : List Nat :=
  events.filterMap fun event => match event with
    | .legacy (.heap (.read _ offset _)) => some offset
    | _ => none

set_option maxRecDepth 4096 in
/-- A Buffer whose length is a captured U64 rejects the first dynamic
offset. The second guard's checked proof allows its one actual read, then
the original continuation releases the owner. -/
theorem guarded_reader_uses_second_capture :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,guardedCaptures⟩ =
      some ⟨.i64,guardedCaptures⟩ ∧
    let result := run 70 (initial guardedCaptures)
    guardedReadOffsets result.events = [1] ∧ observe result = .integer 7 ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
