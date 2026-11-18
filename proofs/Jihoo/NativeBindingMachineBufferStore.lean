import Jihoo.NativeBindingMachineCanonicalIndex
import Jihoo.NativeBindingMachineCanonicalView

/-! Store requires indexed contents. The read-only binding machine supplies
allocation and reader metadata; the indexed heap supplies mutable cells. A
canonical Store command with a named owner and literal inputs derives the
write's numerical and lease guards from authentic source typing and quantity
checking. An evaluator with Store control frames remains a separate step. -/
namespace Jihoo.SizedBufferHeap
open NativeKernel.Environment.BindingMachine

structure IndexedState where
  metadata : State
  cell : Nat → Nat → Nat

def IndexedState.read (s : IndexedState) (token index : Nat) : Option Nat := do
  let object ← s.metadata.heap.lease token
  if index < s.metadata.length object then some (s.cell object index) else none

def IndexedState.store (s : IndexedState) (object index value : Nat) : Option IndexedState :=
  if s.metadata.heap.live object = true ∧ freeGuard s.metadata object = true ∧
      index < s.metadata.length object then
    some { s with cell := HeapLeases.put s.cell object (HeapLeases.put (s.cell object) index value) }
  else none

/-- A write changes the selected cell and preserves every other cell and the
allocation, length and lease metadata. It cannot write through a live lease. -/
theorem IndexedState.store_spec
    {s next : IndexedState} (valid : Valid s.metadata)
    (written : s.store object index value = some next) :
    s.metadata.heap.live object = true ∧ HeapLeases.Unborrowed s.metadata.heap object ∧
    index < s.metadata.length object ∧ next.metadata = s.metadata ∧
    next.cell object index = value ∧
    ∀ queried offset, queried ≠ object ∨ offset ≠ index → next.cell queried offset = s.cell queried offset := by
  unfold IndexedState.store at written
  split at written
  · rename_i guarded
    obtain ⟨live,canWrite,inBounds⟩ := guarded
    cases written
    refine ⟨live,freeGuard_unborrowed valid canWrite,inBounds,rfl,by simp [HeapLeases.put],?_⟩
    intro queried offset other
    rcases other with objectNe | indexNe
    · simp [HeapLeases.put,objectNe]
    · by_cases same : queried = object <;> simp [HeapLeases.put,same,indexNe]
  · contradiction

theorem IndexedState.read_spec {s : IndexedState} (valid : Valid s.metadata)
    (read : s.read token index = some value) :
    ∃ object, s.metadata.heap.lease token = some object ∧ s.metadata.heap.live object = true ∧
      index < s.metadata.length object ∧ value = s.cell object index := by
  unfold IndexedState.read at read
  obtain ⟨object,leased,read⟩ := Option.bind_eq_some_iff.mp read
  split at read
  · rename_i inBounds
    exact ⟨object,leased,(valid.leased _ _ leased).2,inBounds,(Option.some.inj read).symm⟩
  · contradiction

/-- An indexed write preserves the observation of every pre-existing lease.
The observed object differs from the written object by the physical guard. -/
theorem IndexedState.store_keeps_reader {s next : IndexedState} (valid : Valid s.metadata)
    (written : s.store object index value = some next) (token offset : Nat) :
    next.read token offset = s.read token offset := by
  obtain ⟨_,unborrowed,_,sameMetadata,_,sameCell⟩ := store_spec valid written
  unfold IndexedState.read
  rw [sameMetadata]
  cases leased : s.metadata.heap.lease token with
  | none => rfl
  | some observed =>
      have different : observed ≠ object := by
        intro equal
        exact unborrowed token (equal ▸ leased)
      change (if offset < s.metadata.length observed then some (next.cell observed offset) else none) =
        (if offset < s.metadata.length observed then some (s.cell observed offset) else none)
      rw [sameCell observed offset (Or.inl different)]

end Jihoo.SizedBufferHeap

namespace Jihoo.NativeKernel.Environment.LoanTyping

private def StoreInputs (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Term → Prop
  | .store owner index value guard, result => ∃ count,
      HasType env loans ctx mode owner (.buffer count) ∧ HasType env loans ctx mode index .u64 ∧
      HasType env loans ctx mode value .i64 ∧ HasType env loans ctx true guard (.lt index count) ∧
      Conversion.Conv env (.buffer count) result
  | _, _ => True

theorem HasType.store_inputs {owner offset value evidence result : Term}
    (typed : HasType env loans ctx mode (.store owner offset value evidence) result) :
    ∃ count, HasType env loans ctx mode owner (.buffer count) ∧ HasType env loans ctx mode offset .u64 ∧
      HasType env loans ctx mode value .i64 ∧ HasType env loans ctx true evidence (.lt offset count) ∧
      Conversion.Conv env (.buffer count) result := by
  have general : ∀ {term result}, HasType env loans ctx mode term result → StoreInputs env loans ctx mode term result := by
    intro term result source
    apply HasType.rec (t := source)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack context ghost term type _ => StoreInputs env stack context ghost term type)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | skip
    case store => exact ⟨_,by assumption,by assumption,by assumption,by assumption,.refl _⟩
    case dataElim => split <;> trivial
    case convert =>
      rename_i stack context ghost input first second source converted ih
      fun_cases StoreInputs env stack context ghost input first <;> simp only [StoreInputs] at ih ⊢
      obtain ⟨count,ownerTyped,indexTyped,valueTyped,evidence,original⟩ := ih
      exact ⟨count,ownerTyped,indexTyped,valueTyped,evidence,original.trans converted⟩
  exact general typed

namespace ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control}

/-- A literal Store consumes its owner exactly once. An enclosing loan's zero
ownership budget therefore excludes that owner from active source loans. -/
theorem projectRaw_literal_store_inactive
    (checked : projectRaw (fuel+2) env loans ctx
      (.store (.var owner) (.natural index) (.integer value) evidence) = some control)
    (budget : LoanBudget ctx.length loans control) :
    control.demand owner = some 1 ∧ Loans.active ctx.length loans owner = false := by
  simp only [projectRaw,Term.natural,Term.integer,Op.arity,runtimeFields,erasedNode,fields,fetch,
    List.length_cons,List.length_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    bind,Option.bind,Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      cases erased : binding.erased with
      | true => simp [selected,erased] at checked
      | false =>
          have demand : control.demand owner = some 1 := by
            simp [selected,erased] at checked
            rw [← checked]
            simp [Control.demand]
          refine ⟨demand,Bool.eq_false_iff.mpr ?_⟩
          intro active
          have zero := budget owner active
          rw [demand] at zero
          contradiction

end ResourceQuantity
end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- For Store at a reachable heap snapshot, original typing and its checked
quantity receipt supply the signed value width, physical index bound and
absence of a reader. Ambient ownership supplies the owner's current liveness.
The indexed heap writes that exact cell and retains the Loan64 result type. -/
theorem reachable_canonical_store_cell (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (heap : SizedBufferHeap.IndexedState) (metadata : heap.metadata = (run fuel (initial term)).state.heap)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env heap.metadata source meanings)
    (shape : actual.term = .store (.var owner) (.natural offset) (.integer value)
      (.decide (.natural offset) (.natural count)))
    (stored : actual.values[owner]? = some (some (.owner object)))
    (live : heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.stack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans control) :
    ∃ next, heap.store object offset (encodeInteger value) = some next ∧
      next.metadata = heap.metadata ∧ heap.metadata.length object = count ∧
      LoanTyping.Conversion.Conv env (.buffer (.natural count)) type ∧
      decodeInteger (next.cell object offset) = value ∧
      ∀ queried index, queried ≠ object ∨ index ≠ offset → next.cell queried index = heap.cell queried index := by
  have sourceShape : source.term = .store (.var (indices owner)) (.natural offset) (.integer value)
      (.decide (.natural offset) (.natural count)) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped checked
  obtain ⟨size,ownerTyped,offsetTyped,valueTyped,evidence,principal⟩ := sourceTyped.store_inputs
  have sourceStored := (view.values owner).symm.trans stored
  have physicalTyped : OwnerSize env heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      sizes.typed_variable history ownerTyped sourceStored
  have physical := physicalTyped.buffer_length history
  have closedEvidence : LoanTyping.HasType env [] [] true
      (.decide (.natural offset) (.natural count)) (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      evidence.ghostSubstitution history.wellFormed closing
  have sizeConverted := (closedEvidence.principalView.lt_injective history.wellFormed.admissible).2
  have length := (physical.trans sizeConverted.symm).natural_injective history.wellFormed.admissible
  have ordered := (evidence.literal_decide_limits history.wellFormed).2.2
  have outside := (LoanTyping.ResourceQuantity.projectRaw_literal_store_inactive checked budget).2
  have noReader := coverage.inactive sourceStored outside
  have guard := (ReaderInventory.free_guard_iff (initial_run_heap_valid term fuel)
    (initial_reader_inventory term fuel)).mpr noReader
  rw [← metadata] at guard
  have valid : SizedBufferHeap.Valid heap.metadata := metadata ▸ initial_run_heap_valid term fuel
  have within : offset < heap.metadata.length object := by rwa [length]
  have written : heap.store object offset (encodeInteger value) = some
      { heap with cell := HeapLeases.put heap.cell object (HeapLeases.put (heap.cell object) offset (encodeInteger value)) } := by
    simp [SizedBufferHeap.IndexedState.store,live,guard,within]
  obtain ⟨_,_,_,metadataEq,cell,otherCells⟩ := SizedBufferHeap.IndexedState.store_spec valid written
  have outsideTyped : LoanTyping.Conversion.Conv env (.buffer (size.subst meanings)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (principal.substitution meanings history.wellFormed.closed).trans converted
  have resultType := (RawLend.Conv.node .buffer (.cons sizeConverted .nil)).trans outsideTyped
  refine ⟨_,written,metadataEq,length,resultType,?_,otherCells⟩
  rw [cell]
  exact encode_decode_integer valueTyped.integer_bound

end Jihoo.NativeKernel.Environment.BindingMachine
