import Jihoo.NativeBindingMachineReturnedBufferRead
import Jihoo.NativeBindingMachineRunAlgebra

/-! Original-result typing and actual complete two-owner cleanup after the
fresh returned Buffer's second reader. General source/control/resource
fundamental preservation and arbitrary callbacks remain separate obligations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

def returnedReadRelease : Term := .free (.var 0) (.free (.var 2) (.var 1))

/-- The actual scalar can close the inner continuation at the original outer
Lend result type, including specialized source rules and result conversions. -/
theorem LoanSourceTyped.returned_read_result_type
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false first (.lam false again
        (returnedBufferRead readDomain offset count innerFirst innerAgain returnedReadRelease)))) :
    LoanTyping.HasType env [] [] true (.integer fill) type := by
  obtain ⟨countBound,fillBound,indexBound,bound,readerType,outlived,originTyped,valueTyped⟩ :=
    typed.returned_read_limits history shape
  have nested := typed_explicit_continuation_origin history typed shape 0 (.owner 0)
  simp only [Code.origin,enter,returnedBufferRead,Term.subst,substArgs,Op.binders,liftSub] at nested
  have finished := LoanTyping.actual_scalar_finish history.wellFormed nested fillBound
  simp only [Lending.finish,returnedReadRelease,Term.subst,substArgs,Op.binders,liftSub] at finished
  simpa only [liftSubOne,Term.rename,Term.subst,single] using finished.free_tail.free_tail

private theorem frame_reader_owner_bound (ready : FrameOwners limit frame)
    (descriptor : frame.reader? = some (token,object,name)) : object < limit := by
  cases frame <;> simp_all [Frame.reader?,FrameOwners]

private theorem stack_no_fresh_reader (ready : StackOwners limit stack) : ¬ ObjectReader limit stack := by
  rintro ⟨frame,member,token,name,descriptor⟩
  have before := frame_reader_owner_bound (ready frame member) descriptor
  omega

private theorem completion_close_live (heap : SizedBufferHeap.State) (token : Nat) :
    (SizedBufferHeap.close heap token).heap.live = heap.heap.live := rfl

private theorem completion_release_guard (heap : SizedBufferHeap.State) (released object : Nat) :
    freeGuard (SizedBufferHeap.release heap released) object = freeGuard heap object := rfl

set_option linter.unusedSimpArgs false in
private theorem close_release_return_twelve_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some fresh) (freshLive : heap.heap.live fresh = true)
    (stored : code.values[0]? = some (some (.owner object))) (oldLive : heap.heap.live object = true)
    (different : fresh ≠ object) (freshGuard : freeGuard (SizedBufferHeap.close heap token) fresh = true)
    (first again ownerOrigin resultOrigin : Term) (fill : Int) (name : Option Nat) (stack : List Frame) :
    let closed := SizedBufferHeap.close heap token
    let freed := SizedBufferHeap.release closed fresh
    run 12 ⟨heap,.returned (.integer fill),
      .lendFinish token fresh name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again returnedReadRelease))) :: stack⟩ =
      if freeGuard closed object then
        ⟨⟨SizedBufferHeap.release freed object,.returned (.integer fill),stack⟩,
          [.heap (.close token),.activate false (.lam false again returnedReadRelease) resultOrigin,
            .activate false returnedReadRelease ownerOrigin,.heap (.free fresh),.heap (.free object)],12⟩
      else
        ⟨⟨freed,.fault .borrowedOwner,stack⟩,
          [.heap (.close token),.activate false (.lam false again returnedReadRelease) resultOrigin,
            .activate false returnedReadRelease ownerOrigin,.heap (.free fresh)],11⟩ := by
  have afterLive : (SizedBufferHeap.release (SizedBufferHeap.close heap token) fresh).heap.live object = true := by
    simp only [SizedBufferHeap.release,HeapLeases.put,Ne.symm different,↓reduceIte,completion_close_live,oldLive]
  simp only [run,step,action,returnAction,execute,evaluateAction,Code.child,returnedReadRelease,
    applyValue,enter,Option.map_some,List.getElem?_cons_zero,List.getElem?_cons_succ,stored,
    leased,completion_close_live,freshLive,freshGuard,afterLive,completion_release_guard,↓reduceIte]
  by_cases guarded : freeGuard (SizedBufferHeap.close heap token) object = true
  all_goals simp only [guarded,Bool.false_eq_true,↓reduceIte,run,step,action,returnAction,
    execute,evaluateAction,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.map_some]
  all_goals rfl

/-- Actual complete fresh-result read and cleanup at the original input type.
The fresh Free guard follows from all-prefix owner provenance and the actual
reader inventory. Byte overflow and an outstanding reader of the original
owner remain explicit outcomes, not caller-supplied success assumptions. -/
theorem reachable_returned_buffer_completion (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false (.buffer size) (.lam false again
        (returnedBufferRead readDomain offset count innerFirst innerAgain returnedReadRelease))))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (evaluating : (run fuel (initial term)).state.control = .evaluate
      (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
        (code.child (.lam false (.buffer size) (.lam false again
          (returnedBufferRead readDomain offset count innerFirst innerAgain returnedReadRelease)))) :: stack) :
    let state := (run fuel (initial term)).state
    let fresh := state.heap.heap.nextObject
    let nextToken := state.heap.heap.nextLease
    let allocated := SizedBufferHeap.allocate state.heap count (encodeInteger fill)
    let readHeap := SizedBufferHeap.lend (SizedBufferHeap.close allocated token) fresh
    let closed := SizedBufferHeap.close readHeap nextToken
    let freed := SizedBufferHeap.release closed fresh
    let body := returnedBufferRead readDomain offset count innerFirst innerAgain returnedReadRelease
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))).origin
    let bodyCode := restoredContinuation code (.buffer size) again body ownerOrigin resultOrigin object (.owner fresh)
    let indexCode := returnedIndexCode bodyCode readDomain offset count nextToken
    LoanTyping.HasType env [] [] true (.integer fill) type ∧
      if count*8+8 < 2^64 then
        (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
        run 32 state =
          if freeGuard closed object then
            ⟨⟨SizedBufferHeap.release freed object,.returned (.integer fill),stack⟩,
              (run 20 state).events ++
                [.heap (.close nextToken),.activate false (.lam false innerAgain returnedReadRelease) indexCode.origin,
                  .activate false returnedReadRelease ((Term.var 1).subst bodyCode.origins),
                  .heap (.free fresh),.heap (.free object)],32⟩
          else
            ⟨⟨freed,.fault .borrowedOwner,stack⟩,
              (run 20 state).events ++
                [.heap (.close nextToken),.activate false (.lam false innerAgain returnedReadRelease) indexCode.origin,
                  .activate false returnedReadRelease ((Term.var 1).subst bodyCode.origins),
                  .heap (.free fresh)],31⟩
      else run 32 state = ⟨⟨state.heap,.fault .allocationOverflow,state.stack⟩,[],5⟩ := by
  have resultTyped := typed.returned_read_result_type history shape
  obtain ⟨readerType,outlived,valueTyped,different,executed⟩ :=
    reachable_returned_buffer_read term fuel code history typed shape checked evaluating stackShape
  refine ⟨resultTyped,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at executed ⊢
    obtain ⟨bufferValue,originTyped,tokenDifferent,oldClosed,newLease,twenty⟩ := executed
    let state := (run fuel (initial term)).state
    let fresh := state.heap.heap.nextObject
    let nextToken := state.heap.heap.nextLease
    let allocated := SizedBufferHeap.allocate state.heap count (encodeInteger fill)
    let readHeap := SizedBufferHeap.lend (SizedBufferHeap.close allocated token) fresh
    let closed := SizedBufferHeap.close readHeap nextToken
    let body := returnedBufferRead readDomain offset count innerFirst innerAgain returnedReadRelease
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))).origin
    let bodyCode := restoredContinuation code (.buffer size) again body ownerOrigin resultOrigin object (.owner fresh)
    let indexCode := returnedIndexCode bodyCode readDomain offset count nextToken
    have valid := initial_run_heap_valid term fuel
    have readValid := run_heap_valid valid 20
    rw [twenty] at readValid
    change SizedBufferHeap.Valid readHeap at readValid
    have inventory := run_reader_inventory valid (initial_reader_inventory term fuel) 20
    rw [twenty] at inventory
    change ReaderInventory readHeap ((nextToken,fresh,some (bodyCode.context.length-1)) :: readerFrames stack) at inventory
    have leased := inventory.live _ List.mem_cons_self
    have remaining := inventory.finish.2
    have closedValid := SizedBufferHeap.step_valid readValid (.close leased)
    have oldInventory := initial_reader_inventory term fuel
    rw [stackShape] at oldInventory
    change ReaderInventory state.heap ((token,object,name) :: readerFrames stack) at oldInventory
    have oldLive := (valid.leased token object (oldInventory.live _ List.mem_cons_self)).2
    have oldDifferent : object ≠ state.heap.heap.nextObject := Ne.symm different
    have stillLive : readHeap.heap.live object = true := by
      simpa only [readHeap,allocated,SizedBufferHeap.lend,SizedBufferHeap.close,SizedBufferHeap.allocate,
        HeapLeases.put,oldDifferent,↓reduceIte] using oldLive
    have oldOwners := (initial_run_owners term fuel).2
    rw [stackShape] at oldOwners
    have freshAbsent : ¬ ObjectReader fresh stack := stack_no_fresh_reader oldOwners.tail
    have freshGuard := (remaining.free_guard_iff (object := fresh) closedValid).mpr freshAbsent
    have oldGuard := remaining.free_guard_iff (object := object) closedValid
    refine ⟨oldGuard,?_⟩
    have twelve := close_release_return_twelve_steps readHeap bodyCode leased
      (readValid.leased _ _ leased).2 rfl stillLive different freshGuard innerFirst innerAgain
      ((Term.var 1).subst bodyCode.origins) indexCode.origin fill (some (bodyCode.context.length-1)) stack
    have composed := run_add 20 12 state
    rw [twenty] at composed
    dsimp only at composed
    rw [twelve] at composed
    dsimp only [closed,readHeap,allocated,state,fresh,nextToken,bodyCode,indexCode,body,ownerOrigin,resultOrigin] at composed ⊢
    by_cases canFree : freeGuard closed object = true
    all_goals dsimp only [closed,readHeap,allocated,state,fresh,nextToken] at canFree
    all_goals simpa only [twenty,canFree,Bool.false_eq_true,↓reduceIte] using composed
  · simp only [fits,↓reduceIte] at executed ⊢
    have composed := run_add 5 27 (run fuel (initial term)).state
    rw [executed] at composed
    simp only [run_stopped (show step
      ⟨(run fuel (initial term)).state.heap,.fault .allocationOverflow,(run fuel (initial term)).state.stack⟩ = none from rfl)] at composed
    exact composed

end Jihoo.NativeKernel.Environment.BindingMachine
