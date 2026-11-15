import Jihoo.NativeBindingMachineOwnedReader

/-! Actual scalar binders close dependent source types with observed values,
while original machine origins remain unchanged as provenance. This is a local
source/value-context bridge, not a complete control-stack fundamental theorem.
No conversion of an effectful argument origin to its numeral is assumed. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- The closing map describes values, independently of the runtime provenance
map. Both the full source judgment and its input ghost substitution are kept. -/
def LoanClosingTyped (env : Environment) (loans : Loans.Stack) (mode : Bool)
    (code : Code) (meanings : Nat → Term) (type : Term) : Prop :=
  LoanTyping.Ghost.Substitution env code.context [] meanings ∧
    ∃ localType, LoanTyping.HasType env loans code.context mode code.term localType ∧
      LoanTyping.Conversion.Conv env (localType.subst meanings) type

theorem LoanClosingTyped.fromOrigins (typed : LoanSourceTyped env loans mode code type) :
    LoanClosingTyped env loans mode code code.origins type := typed

theorem LoanClosingTyped.initial (typed : LoanTyping.HasType env [] [] mode term type) :
    LoanClosingTyped env [] mode (.initial term) Term.var type := LoanSourceTyped.initial typed

theorem LoanClosingTyped.closed
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode code meanings type) :
    LoanTyping.HasType env [] [] true (code.term.subst meanings) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  exact (source.ghostSubstitution history.wellFormed closing).convert converted

/-- Direct numeric runtime slots agree with their value closing. Other value
kinds and recursive closure/heap interpretation remain separate obligations. -/
def ScalarSlots (code : Code) (meanings : Nat → Term) : Prop :=
  (∀ index value, code.values[index]? = some (some (.natural value)) → meanings index = .natural value) ∧
  (∀ index value, code.values[index]? = some (some (.integer value)) → meanings index = .integer value)

theorem ScalarSlots.initial (term : Term) : ScalarSlots (.initial term) Term.var := by
  constructor <;> intro index value stored <;> cases stored

theorem ScalarSlots.child (slots : ScalarSlots code meanings) (term : Term) :
    ScalarSlots (code.child term) meanings := slots

theorem ScalarSlots.enter_natural (slots : ScalarSlots code meanings)
    (domain body argumentOrigin : Term) (value : Nat) :
    ScalarSlots (enter false domain body code.context code.origins code.values argumentOrigin (some (.natural value)))
      (consValues (.natural value) meanings) := by
  constructor
  · intro index actual stored
    cases index with
    | zero =>
        have same : value = actual := Value.natural.inj (Option.some.inj (Option.some.inj stored))
        subst actual
        rfl
    | succ index => exact slots.1 index actual stored
  · intro index actual stored
    cases index with
    | zero => cases stored
    | succ index => exact slots.2 index actual stored

theorem ScalarSlots.enter_integer (slots : ScalarSlots code meanings)
    (domain body argumentOrigin : Term) (value : Int) :
    ScalarSlots (enter false domain body code.context code.origins code.values argumentOrigin (some (.integer value)))
      (consValues (.integer value) meanings) := by
  constructor
  · intro index actual stored
    cases index with
    | zero => cases stored
    | succ index => exact slots.1 index actual stored
  · intro index actual stored
    cases index with
    | zero =>
        have same : value = actual := Value.integer.inj (Option.some.inj (Option.some.inj stored))
        subst actual
        rfl
    | succ index => exact slots.2 index actual stored

/-- Dependent body typing uses the actual natural argument. The arbitrary
original argument term remains in `Code.origins`, not in this value closing. -/
theorem enter_natural_closing
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,context,origins,captured⟩ meanings (.pi false .u64 result))
    (bounded : value < 2^64) (argumentOrigin : Term) :
    LoanClosingTyped env loans false
      (enter false domain body context origins captured argumentOrigin (some (.natural value)))
      (consValues (.natural value) meanings) (result.subst (single (.natural value))) := by
  obtain ⟨closing,localType,source,actualType⟩ := typed
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := source.lamView
  have converted := (sourceType.substitution meanings history.wellFormed.closed).trans actualType
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings))) (.pi false .u64 result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameFlag,domainConverted,bodyConverted⟩ := convertedPi.pi_injective history.wellFormed.admissible
  have argumentTyped : LoanTyping.HasType env [] [] true (.natural value) (domain.subst meanings) :=
    (LoanTyping.HasType.natural bounded).convert domainConverted.symm
  refine ⟨closing.consValues argumentTyped,bodyType,bodyTyped,?_⟩
  simpa only [subst_lift_consValues] using
    bodyConverted.substitution (single (.natural value)) history.wellFormed.closed

/-- The same actual checked definition supplies the initial value closing and
its original resource evidence, without a chosen semantic candidate. -/
theorem checked_mixed_closing_entry
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source expanded) :
    ∃ sort : SortTag,
      LoanClosingTyped env [] (Definitions.bodyMode sort) (.initial expanded.value) Term.var expanded.type ∧
      ScalarSlots (.initial expanded.value) Term.var ∧
      (Definitions.bodyMode sort = false → LoanTyping.ResourceQuantity.ResourceSafe env expanded.value) := by
  obtain ⟨sort,typed,resource⟩ := checked_mixed_definition_entry checked
  exact ⟨sort,typed,ScalarSlots.initial _,resource⟩

/-- Numeric range comes from actual reachability. The actual closure entry
retains its body/captures, installs the canonical value closing and preserves
old named loans. No argument/output typing or execution-success oracle occurs. -/
theorem reachable_natural_closure_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,context,origins,captured⟩ meanings (.pi false .u64 result))
    (scalars : ScalarSlots ⟨.lam false domain body,context,origins,captured⟩ meanings)
    (slots : LoanSlots ⟨.lam false domain body,context,origins,captured⟩ loans stack)
    (entered : Loans.Entered context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned (.natural value))
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain body context origins captured) argumentOrigin :: stack) :
    let bodyCode := enter false domain body context origins captured argumentOrigin (some (.natural value))
    LoanClosingTyped env loans false bodyCode (consValues (.natural value) meanings)
      (result.subst (single (.natural value))) ∧
      ScalarSlots bodyCode (consValues (.natural value) meanings) ∧ LoanSlots bodyCode loans stack ∧
      bodyCode.origins 0 = argumentOrigin ∧ (consValues (.natural value) meanings) 0 = .natural value ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,stack⟩,
          some (.activate false body argumentOrigin)) := by
  have bound := initial_run_natural_bound term fuel returned
  refine ⟨enter_natural_closing history typed bound argumentOrigin,
    scalars.enter_natural _ _ _ _,slots.enter entered _ _ _ _ _,rfl,rfl,?_⟩
  simp only [step,action,returned,stackShape,returnAction,applyValue,execute,Option.map_some]

end Jihoo.NativeKernel.Environment.BindingMachine
