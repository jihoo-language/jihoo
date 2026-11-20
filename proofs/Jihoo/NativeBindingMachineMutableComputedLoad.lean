import Jihoo.NativeBindingMachineMutableCapturedLoadHandoff

/-! An effect-free U64 operand evaluates with the same successful addition
and captured words in source conversion and the mutable machine. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def UAddOperands (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .uadd left right => HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64
  | _ => True

private theorem uadd_operands (typed : HasType env loans ctx mode term type) :
    UAddOperands env loans ctx mode term := by
  apply HasType.rec (t := typed) (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack ctx mode term _ _ => UAddOperands env stack ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim => split <;> trivial

theorem HasType.uadd_runtime_inputs (typed : HasType env loans ctx mode (.uadd left right) type) :
    HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64 :=
  uadd_operands typed

/-- A checked erased comparison between a computed index and a dependent
length gives a bound for their respective concrete numerals. -/
theorem HasType.decide_converted_bound {index length : Term}
    (typed : HasType env [] [] true (.decide left right) (.lt index length))
    (admissible : EnvironmentDelta.Admissible env)
    (indexConverted : Conversion.Conv env index (.natural offset))
    (lengthConverted : Conversion.Conv env (.natural count) length) : offset < count := by
  obtain ⟨_,_,leftNumber,rightNumber,_,_,ordered⟩ := typed.decide_truth
  have operands := typed.principalView.lt_injective admissible
  have sameOffset := ((indexConverted.symm.trans operands.1.symm).trans leftNumber).natural_injective admissible
  have sameLength := ((lengthConverted.trans operands.2.symm).trans rightNumber).natural_injective admissible
  exact sameOffset ▸ sameLength ▸ ordered

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

inductive UnsignedOperand where
  | literal (number : Nat)
  | captured (slot : Nat)
  | add (left right : UnsignedOperand)

namespace UnsignedOperand

def term : UnsignedOperand → Term
  | .literal number => .natural number
  | .captured slot => .var slot
  | .add left right => .uadd left.term right.term

def ticks : UnsignedOperand → Nat
  | .literal _ | .captured _ => 1
  | .add left right => 1+(left.ticks+(1+(right.ticks+1)))

private def fit (number : Nat) : Option Nat :=
  if number < 2^64 then some number else none

def value (meanings : Nat → Term) : UnsignedOperand → Option Nat
  | .literal number => fit number
  | .captured slot =>
      match meanings slot with
      | .natural number => fit number
      | _ => none
  | .add left right => do
      let first ← value meanings left
      let second ← value meanings right
      fit (first+second)

private theorem fit_sound (observed : fit candidate = some number) :
    candidate = number ∧ number < 2^64 := by
  unfold fit at observed
  split at observed
  · cases observed
    exact ⟨rfl,by assumption⟩
  · contradiction

private theorem add_projection
    (checked : LoanTyping.ResourceQuantity.projectRaw fuel env loans ctx (.uadd left right) = some receipt) :
    ∃ depth first second,
      LoanTyping.ResourceQuantity.projectRaw depth env loans ctx left = some first ∧
      LoanTyping.ResourceQuantity.projectRaw depth env loans ctx right = some second ∧
      receipt = .seq first (.seq second .pure) := by
  cases fuel with
  | zero => cases checked
  | succ depth =>
      have same : LoanTyping.ResourceQuantity.projectRaw (depth+1) env loans ctx (.uadd left right) =
          LoanTyping.ResourceQuantity.projectRaw (depth+1) env loans ctx (.strict left right) := rfl
      obtain ⟨first,second,firstChecked,secondChecked,shape⟩ :=
        LoanTyping.ResourceQuantity.strict_projection (same ▸ checked)
      exact ⟨depth,first,second,firstChecked,secondChecked,shape⟩

/-- The actual and source values agree at the slots a word expression uses. -/
def CapturesMatch (actual source : Code) (indices : Nat → Nat) : UnsignedOperand → Prop
  | .literal _ => True
  | .captured slot => actual.values[slot]? = source.values[indices slot]?
  | .add left right => CapturesMatch actual source indices left ∧ CapturesMatch actual source indices right

/-- The successful interpretation of a typed word expression gives its
matching closed numeral and exact silent execution, even under pending
heap operations. Its authentic projection has zero demand on owner slots. -/
theorem checked_run_captures (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (captures : operand.CapturesMatch actual source indices)
    (typed : LoanClosingTyped env loans false (source.child (operand.term.rename indices)) meanings .u64)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans source.context
      (operand.term.rename indices) = some receipt)
    (observed : operand.value (meanings ∘ indices) = some number) :
    number < 2^64 ∧
    LoanTyping.Conversion.Conv env ((operand.term.rename indices).subst meanings) (.natural number) ∧
    (∀ slot object, source.values[slot]? = some (some (.owner object)) → receipt.demand slot = some 0) ∧
    ∀ (heap : SizedBufferHeap.IndexedState) (stack : List Frame) (pending : List (BufferFrame × List Frame)),
      run operand.ticks ⟨heap,.evaluate (actual.child operand.term),stack,pending⟩ =
        ⟨⟨heap,.returned (.natural number),stack,pending⟩,[],operand.ticks⟩ := by
  induction operand generalizing resourceFuel receipt number with
  | literal candidate =>
      obtain ⟨rfl,bounded⟩ := fit_sound observed
      have projection : receipt = .pure := by
        cases resourceFuel with
        | zero => cases checked
        | succ depth =>
            simp only [term,Term.rename,renameArgs] at checked
            change some Jihoo.Quantity.Control.pure = some receipt at checked
            exact (Option.some.inj checked).symm
      refine ⟨bounded,?_,?_,?_⟩
      · simp only [term,Term.rename,renameArgs,Term.subst,substArgs]
        exact .refl _
      · intros
        simp [projection,Control.demand]
      · intro heap stack pending
        simp only [term,ticks,run,step,Code.child,evaluateAction,bounded,ite_true,
          executeLegacy,execute,Option.map_none]
        rfl
  | captured slot =>
      have variableTyped : LoanClosingTyped env loans false (source.child (.var (indices slot))) meanings .u64 := by
        simpa only [term,Term.rename] using typed
      obtain ⟨actualWord,stored,kind⟩ :=
        (context.child _).variable_kind history variableTyped (aligned.child _) rfl
      obtain ⟨candidate,rfl⟩ := kind.natural_shape history.wellFormed.admissible
      change source.values[indices slot]? = some (some (.natural candidate)) at stored
      have meaning := context.scalars.1 (indices slot) candidate stored
      simp only [value,Function.comp_apply,meaning] at observed
      obtain ⟨rfl,bounded⟩ := fit_sound observed
      have actualStored := (show actual.values[slot]? = source.values[indices slot]? from captures).trans stored
      simp only [term,Term.rename] at checked
      have rawUse := LoanTyping.ResourceQuantity.raw_variable_use checked
      refine ⟨bounded,?_,?_,?_⟩
      · simp only [term,Term.rename,Term.subst,meaning]
        exact .refl _
      · intro queried object selected
        have distinct : indices slot ≠ queried := by
          intro same
          subst queried
          rw [stored] at selected
          cases selected
        simp [rawUse,Control.demand,distinct]
      · intro heap stack pending
        simp only [term,ticks,run,step,Code.child,evaluateAction,actualStored,
          executeLegacy,execute,Option.map_none]
        rfl
  | add left right leftRec rightRec =>
      let sourceLeft := left.term.rename indices
      let sourceRight := right.term.rename indices
      have renamed : (UnsignedOperand.add left right).term.rename indices = .uadd sourceLeft sourceRight := by
        simp only [term,sourceLeft,sourceRight,Term.rename,renameArgs,Op.binders,liftRenaming]
      rw [renamed] at typed checked ⊢
      obtain ⟨closing,localType,sourceTyped,resultType⟩ := typed
      change LoanTyping.HasType env loans source.context false (.uadd sourceLeft sourceRight) localType at sourceTyped
      obtain ⟨leftTyped,rightTyped⟩ := sourceTyped.uadd_runtime_inputs
      have scalarType : LoanTyping.Conversion.Conv env (Term.u64.subst meanings) .u64 := by
        simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)
      obtain ⟨depth,leftReceipt,rightReceipt,leftChecked,rightChecked,shape⟩ := add_projection checked
      change (do
        let lhs ← left.value (meanings ∘ indices)
        let rhs ← right.value (meanings ∘ indices)
        fit (lhs+rhs)) = some number at observed
      obtain ⟨lhs,leftValue,afterLeft⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨rhs,rightValue,calculated⟩ := Option.bind_eq_some_iff.mp afterLeft
      obtain ⟨rfl,bounded⟩ := fit_sound calculated
      obtain ⟨_,leftConverted,leftZero,leftRuns⟩ := leftRec captures.1 ⟨closing,.u64,leftTyped,scalarType⟩ leftChecked leftValue
      obtain ⟨_,rightConverted,rightZero,rightRuns⟩ := rightRec captures.2 ⟨closing,.u64,rightTyped,scalarType⟩ rightChecked rightValue
      refine ⟨bounded,?_,?_,?_⟩
      · have added : LoanTyping.Conversion.Conv env (.uadd (.natural lhs) (.natural rhs)) (.natural (lhs+rhs)) :=
          .old (.legacy (.add lhs rhs bounded))
        have operands : LoanTyping.Conversion.Conv env (.uadd (sourceLeft.subst meanings) (sourceRight.subst meanings))
            (.uadd (.natural lhs) (.natural rhs)) :=
          .node .uadd (.cons leftConverted (.cons rightConverted .nil))
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using operands.trans added
      · intro slot object stored
        simp [shape,Control.demand,leftZero slot object stored,rightZero slot object stored]
      · intro heap stack pending
        let leftStack := .addLeft (actual.child right.term) :: stack
        let rightStack := .addRight lhs :: stack
        have leftStart : step ⟨heap,.evaluate (actual.child (.uadd left.term right.term)),stack,pending⟩ =
            some (⟨heap,.evaluate (actual.child left.term),leftStack,pending⟩,none) := rfl
        have rightStart : step ⟨heap,.returned (.natural lhs),leftStack,pending⟩ =
            some (⟨heap,.evaluate (actual.child right.term),rightStack,pending⟩,none) := rfl
        have finish : run 1 ⟨heap,.returned (.natural rhs),rightStack,pending⟩ =
            ⟨⟨heap,.returned (.natural (lhs+rhs)),stack,pending⟩,[],1⟩ := by
          simp only [rightStack,run,step,returnAction,bounded,ite_true,executeLegacy,execute,Option.map_none]
          rfl
        exact join_runs (noevent_step_run leftStart) <|
          join_runs (leftRuns heap leftStack pending) <| join_runs (noevent_step_run rightStart) <|
            join_runs (rightRuns heap rightStack pending) finish

theorem checked_run (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false (source.child (operand.term.rename indices)) meanings .u64)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (checked : LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans source.context
      (operand.term.rename indices) = some receipt)
    (observed : operand.value (meanings ∘ indices) = some number) :
    number < 2^64 ∧
    LoanTyping.Conversion.Conv env ((operand.term.rename indices).subst meanings) (.natural number) ∧
    (∀ slot object, source.values[slot]? = some (some (.owner object)) → receipt.demand slot = some 0) ∧
    ∀ (heap : SizedBufferHeap.IndexedState) (stack : List Frame) (pending : List (BufferFrame × List Frame)),
      run operand.ticks ⟨heap,.evaluate (actual.child operand.term),stack,pending⟩ =
        ⟨⟨heap,.returned (.natural number),stack,pending⟩,[],operand.ticks⟩ := by
  have captures : operand.CapturesMatch actual source indices := by
    clear typed checked observed
    induction operand with
    | literal => trivial
    | captured slot => exact view.values slot
    | add left right leftMatch rightMatch => exact ⟨leftMatch,rightMatch⟩
  exact operand.checked_run_captures history captures typed context aligned checked observed

end UnsignedOperand

/-- A Load index that consumes no captured owner allows the two original
callback scopes to transfer exactly the selected physical unit. The
integer binding shifts the other captures before the Buffer is returned. -/
theorem OwnerDemandWorld.load_handoff_from_scopes
    (world : OwnerDemandWorld heap code receipt) (complete : OwnerDemandWorld.Total code receipt)
    (shape : receipt = .seq (.seq (.use owner) (.seq indexReceipt .pure))
      (.once (.scope firstMode (.scope .linear bodyReceipt))))
    (selected : code.values[owner]? = some (some (.owner object)))
    (indexNonowner : ∀ slot queried, code.values[slot]? = some (some (.owner queried)) →
      indexReceipt.demand slot = some 0)
    (first again body origin : Term) (number : Int) :
    let next := restoredContinuation code first again body origin (.integer number) object (.integer number)
    heap.heap.live object = true ∧
    OwnerDemandWorld heap next bodyReceipt ∧ OwnerDemandWorld.Total next bodyReceipt ∧ bodyReceipt.demand 0 = some 1 ∧
    ∀ alias, code.values[alias]? = some (some (.owner object)) → bodyReceipt.demand (alias+2) = some 0 := by
  let firstScope : Jihoo.Quantity.Control := .scope firstMode (.scope .linear bodyReceipt)
  let operands : Jihoo.Quantity.Control := .seq (.use owner) (.seq indexReceipt .pure)
  have shape : receipt = .seq operands (.once firstScope) := shape
  obtain ⟨_,_,outerWorld,outerTotal,separated⟩ := (shape ▸ world).sequence (shape ▸ complete)
  have one : operands.demand owner = some 1 := by
    simp [operands,Control.demand,indexNonowner owner object selected]
  have retired (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      firstScope.demand alias = some 0 :=
    separated owner alias object 0 selected found one
  have fullOne : receipt.demand owner = some 1 := by
    rw [shape]
    simp [Control.demand,one,retired owner selected]
  have live := (world.live_once owner object 0 selected fullOne).1
  rw [shape] at fullOne
  have firstValid : LocalScopes firstScope := (NativeQuantity.demand_localScopes _ fullOne).2
  have secondValid : LocalScopes (.scope .linear bodyReceipt) := by
    cases firstMode <;> first | exact firstValid.2 | exact firstValid
  let scalarCode := enter false first (.lam false again body) code.context code.origins code.values
    (.integer number) (some (.integer number))
  have captureWorld : OwnerDemandWorld heap code firstScope :=
    ⟨outerWorld.live_once,outerWorld.exclusive⟩
  have scalarWorld := captureWorld.enter_integer_scope (show OwnerDemandWorld.Total code firstScope from outerTotal)
    firstValid first (.lam false again body) (.integer number) number
  have inactive (alias : Nat) (found : scalarCode.values[alias]? = some (some (.owner object))) :
      (Jihoo.Quantity.Control.scope .linear bodyReceipt).demand alias = some 0 := by
    cases alias with
    | zero => cases found
    | succ alias =>
        exact (demand_under_checked_scope firstValid alias).symm.trans (retired alias found)
  obtain ⟨nextWorld,nextTotal,nextOne,aliases⟩ :=
    scalarWorld.1.enter_linear_result scalarWorld.2 secondValid live inactive again body origin
  exact ⟨live,nextWorld,nextTotal,nextOne,fun alias found => aliases (alias+1) found⟩

private theorem named_load_enter_index (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .load (.var owner) index evidence continuation)
    (stored : code.values[owner]? = some (some (.owner object))) :
    let origin := (code.child (.var owner)).origin
    run 3 state = ⟨⟨state.heap,.evaluate (code.child index),[],
      (.loadIndex object origin (code.child continuation),state.stack) :: state.pending⟩,[],3⟩ := by
  simp only [run,step,evaluating,shape,Code.child,evaluateAction,stored,executeLegacy,execute,
    returnAction,resumeBuffer,Option.map_none]
  rfl

private theorem finish_computed_load (heap : SizedBufferHeap.IndexedState) (code : Code) (stack : List Frame)
    (pending : List (BufferFrame × List Frame)) (first again body origin : Term)
    (loaded : heap.load object offset = some payload) :
    let continuation := Term.lam false first (.lam false again body)
    let number := decodeInteger payload
    let next := restoredContinuation code first again body origin (.integer number) object (.integer number)
    run 5 ⟨heap,.returned (.natural offset),[],
      (.loadIndex object origin (code.child continuation),stack) :: pending⟩ =
      ⟨⟨heap,.evaluate next,stack,pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin)],5⟩ := by
  simp only [run,step,Code.child,evaluateAction,executeLegacy,execute,returnAction,resumeBuffer,
    loaded,applyValue,enter,restoredContinuation,Option.map_none,Option.map_some]
  rfl

/-- The checked addition expression computes the actual Load offset, and
the original closed Decide evidence identifies the corresponding physical
bound. Both real callback activations retain the source type, ownership
world, shifted loan budgets and original indexed heap. -/
theorem reachable_computed_load_handoff (program : Term) (fuel : Nat) (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata source meanings)
    (slots : LoanSlots source loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage source loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (shape : actual.term = .load (.var owner) operand.term evidence (.lam false first (.lam false again body)))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (computed : operand.value (meanings ∘ indices) = some offset)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans source.context source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata source receipt)
    (complete : OwnerDemandWorld.Total source receipt) :
    let before := (run fuel (initial program)).state
    let duration := 3+(operand.ticks+5)
    let result := run duration before
    ∃ object,
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let origin := (actual.child (.var owner)).origin
      let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
      let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer number) meanings)
      actual.values[owner]? = some (some (.owner object)) ∧ offset < 2^64 ∧ offset < before.heap.metadata.length object ∧
      result = ⟨⟨before.heap,.evaluate actualNext,before.stack,before.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin)],duration⟩ ∧
      CanonicalView actualNext sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext nextMeanings type ∧ ValueContext env sourceNext nextMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceNext nextMeanings ∧
      LoanSlots sourceNext loans result.state.activeStack ∧ LoanCoverage sourceNext loans result.state.activeStack ∧
      ∃ rawReceipt,
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans sourceNext.context sourceNext.term =
          some rawReceipt ∧
        let effective := reclose (functionTail sourceNext.term rawReceipt)
        LoanTyping.ResourceQuantity.LoanBudget sourceNext.context.length loans effective ∧
        effective.demand 0 = some 1 ∧ OwnerDemandWorld result.state.heap.metadata sourceNext effective ∧
        OwnerDemandWorld.Total sourceNext effective ∧
        ∀ alias, source.values[alias]? = some (some (.owner object)) → effective.demand (alias+2) = some 0 := by
  let before := (run fuel (initial program)).state
  let duration := 3+(operand.ticks+5)
  let sourceIndex := operand.term.rename indices
  let sourceFirst := first.rename indices
  let sourceAgain := again.rename (liftRenaming 1 indices)
  let sourceBody := body.rename (liftRenaming 2 indices)
  have sourceShape : source.term = .load (.var (indices owner)) sourceIndex
      (evidence.rename indices) (.lam false sourceFirst (.lam false sourceAgain sourceBody)) := by
    rw [← view.termEq,shape]
    simp only [sourceIndex,sourceFirst,sourceAgain,sourceBody,Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [sourceShape] at sourceTyped
  obtain ⟨size,ownerTyped,indexTyped,evidenceTyped⟩ := sourceTyped.load_inputs
  have closedOwner : LoanClosingTyped env loans false (source.child (.var (indices owner))) meanings
      ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,ownerTyped,.refl _⟩
  obtain ⟨runtimeOwner,sourceStored,kind⟩ :=
    (context.child _).variable_kind history closedOwner (aligned.child _) rfl
  have buffer : ValueKind env runtimeOwner (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  have stored := (view.values owner).trans sourceStored
  obtain ⟨bodyFuel,indexReceipt,firstMode,ownerMode,bodyReceipt,fuelShape,indexChecked,resolved,bodyChecked,resourceShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_named_load_scopes (sourceShape ▸ checked)
  have fuelEq : bodyFuel = resourceFuel := by omega
  subst bodyFuel
  obtain ⟨_,_,_,ownerType,_⟩ := LoanTyping.load_retained_body history.wellFormed sourceTyped
  rw [resolved.convertible_buffer_linear history.wellFormed.admissible ownerType] at resourceShape
  have closedIndex : LoanClosingTyped env loans false (source.child sourceIndex) meanings .u64 :=
    ⟨closing,.u64,indexTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨width,indexConverted,indexNonowner,indexRun⟩ :=
    operand.checked_run history view closedIndex context aligned indexChecked computed
  have ownerSize : OwnerSize env before.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizes.typed_variable history ownerTyped sourceStored
  have physical := ownerSize.buffer_length history
  have evidenceClosed : LoanTyping.HasType env [] [] true (.decide left right)
      (.lt (sourceIndex.subst meanings) (size.subst meanings)) := by
    change evidence.subst (fun slot => meanings (indices slot)) = .decide left right at decideEvidence
    simpa only [Term.subst_rename,decideEvidence,Term.subst,substArgs,Op.binders,liftSub]
      using evidenceTyped.ghostSubstitution history.wellFormed closing
  have within := evidenceClosed.decide_converted_bound history.wellFormed.admissible indexConverted physical
  let number := decodeInteger (before.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
  let sourceNext := restoredContinuation source sourceFirst sourceAgain sourceBody origin (.integer number) object (.integer number)
  obtain ⟨live,nextWorld,nextTotal,returnedUse,aliases⟩ :=
    world.load_handoff_from_scopes complete resourceShape sourceStored indexNonowner sourceFirst sourceAgain sourceBody origin number
  have inactive := LoanTyping.ResourceQuantity.projectRaw_named_load_inactive (sourceShape ▸ checked) budget
  have noReader := coverage.inactive sourceStored inactive
  have invariant := initial_run_invariant program fuel
  have guard := (invariant.2.free_guard_iff invariant.1).mpr noReader
  have loaded : before.heap.load object offset = some (before.heap.cell object offset) := by
    unfold SizedBufferHeap.IndexedState.load
    exact ite_eq_left ⟨live,guard,within⟩
  have entry := named_load_enter_index before evaluating shape stored
  have finished := finish_computed_load before.heap actual before.stack before.pending first again body origin loaded
  have exactRun : run duration before = ⟨⟨before.heap,.evaluate actualNext,before.stack,before.pending⟩,
      [.load object offset (before.heap.cell object offset),.legacy (.activate false (.lam false again body) (.integer number)),
        .legacy (.activate false body origin)],duration⟩ :=
    join_runs entry (join_runs (indexRun before.heap []
      ((.loadIndex object origin (actual.child (.lam false first (.lam false again body))),before.stack) :: before.pending)) finished)
  have numbers := initial_run_numbers program fuel
  have nextTyped : LoanClosingTyped env loans false sourceNext
      (consValues (meanings (indices owner)) (consValues (.integer number) meanings)) type := by
    simpa only [Term.subst] using load_retained_closing history.wellFormed closing sourceTyped converted
      (decode_integer_bound (numbers.cells object offset)) origin object
  have savedClosing := nextTyped
  obtain ⟨nextClosing,_,_,_⟩ := savedClosing
  obtain ⟨nextContext,nextSizes⟩ :=
    restored_contexts history context sizes ownerTyped sourceStored sourceFirst sourceAgain sourceBody origin number nextClosing
  have nextView : CanonicalView actualNext sourceNext (liftRenaming 2 indices) :=
    (view.enter false first (.lam false again body) (.integer number)
      (some (.integer number))).enter false again body origin (some (.owner object))
  have nextSlots := source_load_slots slots entered sourceFirst sourceAgain sourceBody origin object number
  have nextCoverage := load_coverage coverage entered noReader sourceFirst sourceAgain sourceBody origin number
  have callbackBudget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans
      (.scope firstMode (.scope .linear (reclose (functionTail sourceBody bodyReceipt)))) :=
    (resourceShape ▸ budget).sequence.2
  have deeper : Loans.Entered (source.context.length+1) loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have bodyBudget := (callbackBudget.scope entered).scope deeper
  have heapEq := congrArg (fun result : Result => result.state.heap.metadata) exactRun
  have stackEq := congrArg (fun result : Result => result.state.activeStack) exactRun
  change (run duration before).state.activeStack = before.activeStack at stackEq
  exact ⟨object,stored,width,within,exactRun,nextView,nextTyped,nextContext,heapEq.symm ▸ nextSizes,
    stackEq.symm ▸ nextSlots,stackEq.symm ▸ nextCoverage,bodyReceipt,bodyChecked,bodyBudget,returnedUse,
    heapEq.symm ▸ nextWorld,nextTotal,aliases⟩

/-- After the computed read, the actual callback can consume the retained
Buffer via Free. All reader associations and remaining owner demands pass
to the original dependent tail, with no changes to indexed cells. -/
theorem reachable_computed_load_then_free (program : Term) (fuel : Nat) (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata source meanings)
    (slots : LoanSlots source loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage source loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (shape : actual.term = .load (.var owner) operand.term evidence
      (.lam false first (.lam false again (.free (.var 0) tail))))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (computed : operand.value (meanings ∘ indices) = some offset)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+5) env loans source.context source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata source receipt)
    (complete : OwnerDemandWorld.Total source receipt) :
    let before := (run fuel (initial program)).state
    let duration := (3+(operand.ticks+5))+3
    let result := run duration before
    ∃ object,
      let body := Term.free (.var 0) tail
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let origin := (actual.child (.var owner)).origin
      let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
      let sourceTail := sourceNext.child (tail.rename (liftRenaming 2 indices))
      let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer number) meanings)
      actual.values[owner]? = some (some (.owner object)) ∧ offset < before.heap.metadata.length object ∧
      result = ⟨⟨⟨SizedBufferHeap.release before.heap.metadata object,before.heap.cell⟩,
        .evaluate (actualNext.child tail),before.stack,before.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin),.legacy (.heap (.free object))],duration⟩ ∧
      result.state.heap.metadata.heap.live object = false ∧
      CanonicalView (actualNext.child tail) sourceTail (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceTail nextMeanings type ∧ ValueContext env sourceTail nextMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceTail nextMeanings ∧
      LoanSlots sourceTail loans result.state.activeStack ∧ LoanCoverage sourceTail loans result.state.activeStack ∧
      ∃ residual,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term =
          some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
        OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
        ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let before := (run fuel (initial program)).state
  let readTicks := 3+(operand.ticks+5)
  let body := Term.free (.var 0) tail
  obtain ⟨object,stored,_,within,executed,nextView,nextTyped,nextContext,nextSizes,nextSlots,nextCoverage,
    bodyReceipt,projected,bodyBudget,_,bodyWorld,bodyTotal,_⟩ :=
    reachable_computed_load_handoff (resourceFuel := resourceFuel+2) program fuel operand history evaluating view typed
      context aligned sizes slots coverage entered shape decideEvidence computed checked budget world complete
  let number := decodeInteger (before.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
  let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
    (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
  have bodyShape : sourceNext.term = .free (.var 0) (tail.rename (liftRenaming 2 indices)) := by
    change body.rename (liftRenaming 2 indices) = _
    simp only [body,Term.rename,renameArgs,Op.binders,liftRenaming]
    rfl
  have raw := projected
  change LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans sourceNext.context sourceNext.term =
    some bodyReceipt at raw
  rw [bodyShape] at raw
  have effective := LoanTyping.ResourceQuantity.projectRaw_free_callback_body raw
  change LoanTyping.ResourceQuantity.LoanBudget sourceNext.context.length loans
    (reclose (functionTail sourceNext.term bodyReceipt)) at bodyBudget
  change OwnerDemandWorld (run readTicks before).state.heap.metadata sourceNext
    (reclose (functionTail sourceNext.term bodyReceipt)) at bodyWorld
  change OwnerDemandWorld.Total sourceNext (reclose (functionTail sourceNext.term bodyReceipt)) at bodyTotal
  rw [bodyShape,effective] at bodyBudget bodyWorld bodyTotal
  have reached : (run (fuel+readTicks) (initial program)).state = (run readTicks before).state := by
    have observed := congrArg Result.state (run_add fuel readTicks (initial program))
    exact observed
  have atFree : (run (fuel+readTicks) (initial program)).state.control = .evaluate actualNext := by
    rw [reached,executed]
  obtain ⟨freed,dead,tailView,tailTyped,tailContext,tailSizes,tailCoverage,tailSlots,
    residual,tailChecked,tailBudget,tailWorld,tailTotal,noAliases⟩ :=
    reachable_canonical_free_preserves_owner_demand program (fuel+readTicks) atFree nextView (by rfl)
      nextTyped nextContext (reached.symm ▸ nextSizes) (reached.symm ▸ nextCoverage) (reached.symm ▸ nextSlots)
      (by rfl) projected bodyBudget (reached.symm ▸ bodyWorld) bodyTotal
  have finalState : (run (readTicks+3) before).state = (run 3 (run (fuel+readTicks) (initial program)).state).state := by
    rw [reached]
    have observed := congrArg Result.state (run_add readTicks 3 before)
    exact observed
  have entire := run_add readTicks 3 before
  dsimp only at entire
  rw [← reached,freed,reached,executed] at entire
  exact ⟨object,stored,within,entire,finalState.symm ▸ dead,tailView,tailTyped,tailContext,
    finalState.symm ▸ tailSizes,finalState.symm ▸ tailSlots,finalState.symm ▸ tailCoverage,residual,
    tailChecked,tailBudget,finalState.symm ▸ tailWorld,tailTotal,noAliases⟩

namespace Examples

private def computedLoadAfterStore : Term :=
  let buffer := Term.buffer (.natural 3)
  let index := fun slot => UnsignedOperand.add (.captured slot) (.add (.literal 1) (.literal 0))
  let written := Term.store (.alloc (.natural 3) (.integer 3)) (.natural 2) (.integer 46)
    (.decide (.natural 2) (.natural 3))
  let continuation := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let loaded := Term.load (.var 0) (index 2).term (.var 1) continuation
  let branch := Term.ifLt (index 0).term (.natural 3) (.app (.lam false buffer loaded) written) (.integer 0)
  .app (.lam false .u64 branch) (.natural 1)

set_option maxRecDepth 4096 in
/-- The branch provides the original bound for an actual nested addition.
That computed Load reads the prior indexed write and releases its owner. -/
theorem computed_load_reads_written_cell_then_frees :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,computedLoadAfterStore⟩ =
      some ⟨.i64,computedLoadAfterStore⟩ ∧
    let result := run 80 (initial computedLoadAfterStore)
    observe result = .integer 46 ∧
      result.events.filterMap (fun event => match event with
        | .load object offset payload => some (object,offset,payload)
        | _ => none) = [(0,2,encodeInteger 46)] ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 3 (encodeInteger 3),.free 0] ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
