import Jihoo.NativeBindingMachineComputedAllocation

/-! Type-directed representation of captured values. This interpretation records
only type heads, not closure-body correctness, live heap ownership or exclusive
resource authority. Scalar entry constructs it; reachable variable lookup uses
it together with the unconditional machine alignment invariant. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- A runtime representation must agree with its source type head. -/
def ValueKind (env : Environment) (value : Value) (type : Term) : Prop :=
  match value with
  | .natural _ => LoanTyping.Conversion.Conv env .u64 type
  | .integer _ => LoanTyping.Conversion.Conv env .i64 type
  | .owner _ => ∃ size, LoanTyping.Conversion.Conv env (.buffer size) type
  | .reference _ => ∃ domain, LoanTyping.Conversion.Conv env (.ref domain) type
  | .closure erased _ _ _ _ _ => ∃ domain body, LoanTyping.Conversion.Conv env (.pi erased domain body) type
  | .typeCode _ => ∃ sort : SortTag, LoanTyping.Conversion.Conv env sort.term type

theorem ValueKind.convert (kind : ValueKind env value type)
    (converted : LoanTyping.Conversion.Conv env type other) : ValueKind env value other := by
  cases value with
  | natural => exact kind.trans converted
  | integer => exact kind.trans converted
  | owner => obtain ⟨size,kind⟩ := kind; exact ⟨size,kind.trans converted⟩
  | reference => obtain ⟨domain,kind⟩ := kind; exact ⟨domain,kind.trans converted⟩
  | closure => obtain ⟨domain,body,kind⟩ := kind; exact ⟨domain,body,kind.trans converted⟩
  | typeCode => obtain ⟨sort,kind⟩ := kind; exact ⟨sort,kind.trans converted⟩

theorem ValueKind.natural_shape (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value .u64) : ∃ number, value = .natural number := by
  cases value with
  | natural number => exact ⟨number,rfl⟩
  | integer => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | owner =>
      obtain ⟨size,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | reference =>
      obtain ⟨domain,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | closure =>
      obtain ⟨domain,body,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | typeCode =>
      obtain ⟨sort,kind⟩ := kind
      cases sort <;> exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)

theorem ValueKind.integer_shape (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value .i64) : ∃ number, value = .integer number := by
  cases value with
  | integer number => exact ⟨number,rfl⟩
  | natural => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | owner =>
      obtain ⟨size,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | reference =>
      obtain ⟨domain,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | closure =>
      obtain ⟨domain,body,kind⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)
  | typeCode =>
      obtain ⟨sort,kind⟩ := kind
      cases sort <;> exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro h; cases h) kind admissible)

/-- An input value-context invariant, stronger than one-way `ScalarSlots`.
Its construction is proved below for empty contexts and actual scalar entry. -/
structure ValueContext (env : Environment) (code : Code) (meanings : Nat → Term) : Prop where
  closing : LoanTyping.Ghost.Substitution env code.context [] meanings
  scalars : ScalarSlots code meanings
  kinds : ∀ index binding value, lookup code.context index = some binding →
    code.values[index]? = some (some value) → ValueKind env value (binding.ty.subst meanings)

theorem ValueContext.initial (env : Environment) (term : Term) :
    ValueContext env (.initial term) Term.var := by
  refine ⟨?_,ScalarSlots.initial term,?_⟩
  · intro index binding selected; cases selected
  · intro index binding value selected; cases selected

theorem ValueContext.child (context : ValueContext env code meanings) (term : Term) :
    ValueContext env (code.child term) meanings := ⟨context.closing,context.scalars,context.kinds⟩

private theorem value_context_cons
    (context : ValueContext env code meanings)
    (argumentTyped : LoanTyping.HasType env [] [] true source (domain.subst meanings))
    (argumentKind : ValueKind env value (domain.subst meanings))
    (scalars : ScalarSlots (enter false domain body code.context code.origins code.values origin (some value))
      (consValues source meanings)) :
    ValueContext env (enter false domain body code.context code.origins code.values origin (some value))
      (consValues source meanings) := by
  refine ⟨context.closing.consValues argumentTyped,scalars,?_⟩
  intro index binding actual selected stored
  cases index with
  | zero =>
      simp only [enter,lookup,Option.some.injEq] at selected
      subst binding
      have same : value = actual := Option.some.inj (Option.some.inj stored)
      subst actual
      simpa only [shift_subst_consValues] using argumentKind
  | succ index =>
      obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [shift_subst_consValues] using context.kinds index previous actual found stored

/-- Function inversion supplies the domain conversion. No argument typing or
post-entry value interpretation is requested from the caller. -/
theorem ValueContext.enter_natural
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false .u64 result))
    (bounded : number < 2^64) (origin : Term) :
    ValueContext env (enter false domain body ctx origins captured origin (some (.natural number)))
      (consValues (.natural number) meanings) := by
  obtain ⟨closing,localType,source,actualType⟩ := typed
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := source.lamView
  have converted := (sourceType.substitution meanings history.wellFormed.closed).trans actualType
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false .u64 result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  have domainConverted := (convertedPi.pi_injective history.wellFormed.admissible).2.1
  exact value_context_cons context ((LoanTyping.HasType.natural bounded).convert domainConverted.symm)
    domainConverted.symm (context.scalars.enter_natural domain body origin number)

theorem ValueContext.enter_integer
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false .i64 result))
    (bounded : -(2^63) ≤ number ∧ number < 2^63) (origin : Term) :
    ValueContext env (enter false domain body ctx origins captured origin (some (.integer number)))
      (consValues (.integer number) meanings) := by
  obtain ⟨closing,localType,source,actualType⟩ := typed
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := source.lamView
  have converted := (sourceType.substitution meanings history.wellFormed.closed).trans actualType
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false .i64 result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  have domainConverted := (convertedPi.pi_injective history.wellFormed.admissible).2.1
  exact value_context_cons context ((LoanTyping.HasType.integer bounded.1 bounded.2).convert domainConverted.symm)
    domainConverted.symm (context.scalars.enter_integer domain body origin number)

/-- Source variable inversion transports its stored representation to the
required type. Alignment supplies a retained value at the selected slot. -/
theorem ValueContext.variable_kind
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (shape : code.term = .var index) :
    ∃ value, code.values[index]? = some (some value) ∧ ValueKind env value type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨binding,selected,relevant⟩ := loan_code_variable_permission source
  obtain ⟨other,selected',principal⟩ := source.principalView
  have same : binding = other := Option.some.inj (selected.symm.trans selected')
  subst other
  obtain ⟨option,stored,flag⟩ := aligned.ready index binding selected
  cases option with
  | none => simp [relevant] at flag
  | some value =>
      exact ⟨value,stored,(context.kinds index binding value selected stored).convert
        ((principal.substitution meanings history.wellFormed.closed).trans converted)⟩

/-- Full source variable typing and actual reachability select a stored value
with the required representation head. Slot readiness comes from the machine. -/
theorem reachable_variable_kind (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings) (shape : code.term = .var index) :
    ∃ value, code.values[index]? = some (some value) ∧ ValueKind env value type ∧
      step (run fuel (initial term heap)).state = some
        (⟨(run fuel (initial term heap)).state.heap,.returned value,
          (run fuel (initial term heap)).state.stack⟩,none) := by
  obtain ⟨value,stored,kind⟩ := context.variable_kind history typed
    (initial_run_code_aligned term fuel heap evaluating) shape
  refine ⟨value,stored,kind,?_⟩
  simp only [step,action,evaluating,evaluateAction,shape,stored,Option.map_some,execute,Option.map_none]

/-- A U64-typed variable returns an actual natural with its source-derived
width and canonical closing meaning. The stored value is an output. -/
theorem reachable_natural_variable (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings .u64)
    (context : ValueContext env code meanings) (shape : code.term = .var index) :
    ∃ number, code.values[index]? = some (some (.natural number)) ∧ meanings index = .natural number ∧
      number < 2^64 ∧ LoanTyping.HasType env [] [] true (.natural number) .u64 ∧
      step (run fuel (initial term heap)).state = some
        (⟨(run fuel (initial term heap)).state.heap,.returned (.natural number),
          (run fuel (initial term heap)).state.stack⟩,none) := by
  obtain ⟨value,stored,kind,next⟩ := reachable_variable_kind term fuel heap history evaluating typed context shape
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have meaning := context.scalars.1 index number stored
  have scalarTyped := typed.closed history
  have actualTyped : LoanTyping.HasType env [] [] true (.natural number) .u64 := by
    simpa only [shape,Term.subst,meaning] using scalarTyped
  exact ⟨number,stored,meaning,actualTyped.natural_bound,actualTyped,next⟩

theorem reachable_integer_variable (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings .i64)
    (context : ValueContext env code meanings) (shape : code.term = .var index) :
    ∃ number, code.values[index]? = some (some (.integer number)) ∧ meanings index = .integer number ∧
      ValueReduction.signed64 number ∧ LoanTyping.HasType env [] [] true (.integer number) .i64 ∧
      step (run fuel (initial term heap)).state = some
        (⟨(run fuel (initial term heap)).state.heap,.returned (.integer number),
          (run fuel (initial term heap)).state.stack⟩,none) := by
  obtain ⟨value,stored,kind,next⟩ := reachable_variable_kind term fuel heap history evaluating typed context shape
  obtain ⟨number,rfl⟩ := kind.integer_shape history.wellFormed.admissible
  have meaning := context.scalars.2 index number stored
  have scalarTyped := typed.closed history
  have actualTyped : LoanTyping.HasType env [] [] true (.integer number) .i64 := by
    simpa only [shape,Term.subst,meaning] using scalarTyped
  exact ⟨number,stored,meaning,actualTyped.integer_bound,actualTyped,next⟩

/-- The stronger context is constructed at actual scalar call boundaries.
Argument widths follow from reachability, rather than input scalar typing. -/
theorem reachable_natural_value_context_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false .u64 result))
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (returned : (run fuel (initial term)).state.control = .returned (.natural number))
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack) :
    let bodyCode := enter false domain body ctx origins captured argumentOrigin (some (.natural number))
    LoanClosingTyped env loans false bodyCode (consValues (.natural number) meanings)
      (result.subst (single (.natural number))) ∧
      ValueContext env bodyCode (consValues (.natural number) meanings) ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,stack⟩,
          some (.activate false body argumentOrigin)) := by
  have bounded := initial_run_natural_bound term fuel returned
  refine ⟨enter_natural_closing history typed bounded argumentOrigin,
    context.enter_natural history typed bounded argumentOrigin,?_⟩
  simp only [step,action,returned,stackShape,returnAction,applyValue,execute,Option.map_some]

theorem reachable_integer_value_context_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false .i64 result))
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (returned : (run fuel (initial term)).state.control = .returned (.integer number))
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack) :
    let bodyCode := enter false domain body ctx origins captured argumentOrigin (some (.integer number))
    LoanClosingTyped env loans false bodyCode (consValues (.integer number) meanings)
      (result.subst (single (.integer number))) ∧
      ValueContext env bodyCode (consValues (.integer number) meanings) ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,stack⟩,
          some (.activate false body argumentOrigin)) := by
  have bounded := initial_run_integer_bound term fuel returned
  refine ⟨enter_integer_closing history typed bounded argumentOrigin,
    context.enter_integer history typed bounded argumentOrigin,?_⟩
  simp only [step,action,returned,stackShape,returnAction,applyValue,execute,Option.map_some]

theorem checked_mixed_value_context_entry
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source expanded) :
    ∃ sort : SortTag,
      LoanClosingTyped env [] (Definitions.bodyMode sort) (.initial expanded.value) Term.var expanded.type ∧
      ValueContext env (.initial expanded.value) Term.var ∧
      (Definitions.bodyMode sort = false → LoanTyping.ResourceQuantity.ResourceSafe env expanded.value) := by
  obtain ⟨sort,typed,resource⟩ := checked_mixed_definition_entry checked
  exact ⟨sort,typed,ValueContext.initial _ _,resource⟩

end Jihoo.NativeKernel.Environment.BindingMachine
