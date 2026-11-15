import Jihoo.NativeBindingMachineReaderClosing

/-! Captured owner types interpret immutable allocation lengths, including
released aliases. This is size/provenance information, not liveness or an
exclusive capability. Actual reader inventory supplies live lease authority. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- A source Buffer type describes this allocated identity's actual length.
Released owners deliberately remain interpretable. -/
def OwnerSize (env : Environment) (heap : SizedBufferHeap.State) (object : Nat) (type : Term) : Prop :=
  object < heap.heap.nextObject ∧ ∃ count, heap.length object = count ∧
    LoanTyping.Conversion.Conv env (.buffer (.natural count)) type

theorem OwnerSize.convert (size : OwnerSize env heap object type)
    (converted : LoanTyping.Conversion.Conv env type other) : OwnerSize env heap object other := by
  obtain ⟨bound,count,length,typed⟩ := size
  exact ⟨bound,count,length,typed.trans converted⟩

theorem OwnerSize.steps (size : OwnerSize env before object type)
    (steps : SizedBufferHeap.Steps before events after) : OwnerSize env after object type := by
  obtain ⟨bound,count,length,converted⟩ := size
  obtain ⟨later,preserved⟩ := SizedBufferHeap.lengths_preserved bound steps
  exact ⟨later,count,preserved.trans length,converted⟩

theorem OwnerSize.allocate
    (converted : LoanTyping.Conversion.Conv env (.buffer (.natural count)) type) :
    OwnerSize env (SizedBufferHeap.allocate heap count fill) heap.heap.nextObject type := by
  exact ⟨by simp only [SizedBufferHeap.allocate]; omega,
    count,SizedBufferHeap.allocation_length,converted⟩

theorem OwnerSize.buffer_length (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (size : OwnerSize env heap object (.buffer count)) :
    LoanTyping.Conversion.Conv env (.natural (heap.length object)) count := by
  obtain ⟨bound,actual,length,converted⟩ := size
  rw [length]
  exact converted.buffer_injective history.wellFormed.admissible

/-- Every retained owner slot has its original dependent Buffer length.
No live/exclusive authority is assigned to all saved captures. -/
def OwnerSizes (env : Environment) (heap : SizedBufferHeap.State) (code : Code) (meanings : Nat → Term) : Prop :=
  ∀ index binding object, lookup code.context index = some binding →
    code.values[index]? = some (some (.owner object)) → OwnerSize env heap object (binding.ty.subst meanings)

theorem OwnerSizes.initial (env : Environment) (heap : SizedBufferHeap.State) (term : Term) :
    OwnerSizes env heap (.initial term) Term.var := by
  intro index binding object selected
  cases selected

theorem OwnerSizes.child (sizes : OwnerSizes env heap code meanings) (term : Term) :
    OwnerSizes env heap (code.child term) meanings := sizes

theorem OwnerSizes.steps (sizes : OwnerSizes env before code meanings)
    (steps : SizedBufferHeap.Steps before events after) : OwnerSizes env after code meanings := by
  intro index binding object selected stored
  exact (sizes index binding object selected stored).steps steps

theorem OwnerSizes.allocate (sizes : OwnerSizes env heap code meanings) (count fill : Nat) :
    OwnerSizes env (SizedBufferHeap.allocate heap count fill) code meanings :=
  sizes.steps (.cons .alloc .nil)

/-- Actual execution preserves the sizes of these captured identities through
allocation, Free, all reader actions, faults and exhausted fuel. -/
theorem OwnerSizes.run (sizes : OwnerSizes env state.heap code meanings)
    (valid : SizedBufferHeap.Valid state.heap) (fuel : Nat) :
    OwnerSizes env (run fuel state).state.heap code meanings := sizes.steps (run_heap_steps valid fuel)

theorem OwnerSizes.typed_variable (sizes : OwnerSizes env heap code meanings)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans code.context mode (.var index) type)
    (stored : code.values[index]? = some (some (.owner object))) :
    OwnerSize env heap object (type.subst meanings) := by
  obtain ⟨binding,selected,converted⟩ := typed.principalView
  exact (sizes index binding object selected stored).convert
    (converted.substitution meanings history.wellFormed.closed)

private theorem owner_sizes_enter_other (sizes : OwnerSizes env heap code meanings)
    (other : ∀ object, value ≠ Value.owner object) (domain body origin source : Term) :
    OwnerSizes env heap (enter false domain body code.context code.origins code.values origin (some value))
      (consValues source meanings) := by
  intro index binding object selected stored
  cases index with
  | zero => exact False.elim (other object (Option.some.inj (Option.some.inj stored)))
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using sizes index previous object found stored

theorem OwnerSizes.enter_natural (sizes : OwnerSizes env heap code meanings)
    (domain body origin : Term) (number : Nat) :
    OwnerSizes env heap (enter false domain body code.context code.origins code.values origin (some (.natural number)))
      (consValues (.natural number) meanings) :=
  owner_sizes_enter_other sizes (by intro object same; cases same) domain body origin (.natural number)

theorem OwnerSizes.enter_integer (sizes : OwnerSizes env heap code meanings)
    (domain body origin : Term) (number : Int) :
    OwnerSizes env heap (enter false domain body code.context code.origins code.values origin (some (.integer number)))
      (consValues (.integer number) meanings) :=
  owner_sizes_enter_other sizes (by intro object same; cases same) domain body origin (.integer number)

theorem OwnerSizes.enter_reference (sizes : OwnerSizes env heap code meanings)
    (domain body origin source : Term) (token : Nat) :
    OwnerSizes env heap (enter false domain body code.context code.origins code.values origin (some (.reference token)))
      (consValues source meanings) :=
  owner_sizes_enter_other sizes (by intro object same; cases same) domain body origin source

theorem OwnerSizes.branch (sizes : OwnerSizes env heap code meanings)
    (equal : Bool) (yes left right proof : Term) :
    OwnerSizes env heap (branchCode equal (code.child yes) left right) (consValues proof meanings) := by
  intro index binding object selected stored
  cases index with
  | zero => cases stored
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using sizes index previous object found stored

private theorem owner_sizes_enter_owner (sizes : OwnerSizes env heap code meanings)
    (argument : OwnerSize env heap object (domain.subst meanings)) (body origin source : Term) :
    OwnerSizes env heap (enter false domain body code.context code.origins code.values origin (some (.owner object)))
      (consValues source meanings) := by
  intro index binding actual selected stored
  cases index with
  | zero =>
      simp only [enter,lookup,Option.some.injEq] at selected
      subst binding
      have same : object = actual := Value.owner.inj (Option.some.inj (Option.some.inj stored))
      subst actual
      simpa only [shift_subst_consValues] using argument
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using sizes index previous actual found stored

/-- The stronger heap-size context is constructed from the same source
allocation and pending function as actual owner entry. It is not a caller-
supplied output interpretation; old aliases retain their immutable lengths. -/
theorem reachable_allocated_argument_sizes (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (allocationTyped : LoanClosingTyped env allocationLoans false code allocationMeanings argumentType)
    (allocationContext : ValueContext env code allocationMeanings)
    (shape : code.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false argumentType result))
    (functionContext : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (functionSizes : OwnerSizes env (run fuel (initial term)).state.heap
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let bodyCode := enter false domain body ctx origins captured argumentOrigin (some (.owner heap.heap.nextObject))
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      if count*8+8 < 2^64 then
        OwnerSizes env (SizedBufferHeap.allocate heap count (encodeInteger fill)) bodyCode bodyMeanings ∧
        ValueContext env bodyCode bodyMeanings ∧
        LoanClosingTyped env loans false bodyCode bodyMeanings
          (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.evaluate bodyCode,stack⟩,
            [.heap (.alloc heap.heap.nextObject count (encodeInteger fill)),.activate false body argumentOrigin],6⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,
          .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack⟩,[],5⟩ := by
  obtain ⟨count,fill,countMeaning,fillMeaning,entry⟩ := reachable_allocated_argument_entry term fuel history
    evaluating allocationTyped allocationContext shape functionTyped functionContext stackShape
  have canonicalTyped : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill)) argumentType := by
    simpa only [shape,Term.subst,substArgs,Op.binders,liftSub,countMeaning,fillMeaning] using allocationTyped.closed history
  obtain ⟨closing,localType,source,converted⟩ := functionTyped
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := source.lamView
  have functionConverted := (sourceType.substitution meanings history.wellFormed.closed).trans converted
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false argumentType result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using functionConverted
  have domainConverted := (convertedPi.pi_injective history.wellFormed.admissible).2.1
  have bufferConverted := canonicalTyped.principalView.trans domainConverted.symm
  have enteredSizes := owner_sizes_enter_owner (functionSizes.allocate count (encodeInteger fill))
    (OwnerSize.allocate bufferConverted) body argumentOrigin (.alloc (.natural count) (.integer fill))
  refine ⟨count,fill,countMeaning,fillMeaning,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at entry ⊢
    obtain ⟨buffer,bodyTyped,bodyContext,origin,executed⟩ := entry
    exact ⟨enteredSizes,bodyContext,bodyTyped,executed⟩
  · simpa only [fits,↓reduceIte] using entry

end Jihoo.NativeKernel.Environment.BindingMachine
