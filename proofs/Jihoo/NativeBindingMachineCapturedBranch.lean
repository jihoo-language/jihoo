import Jihoo.NativeBindingMachineCapturedAllocation
import Jihoo.NativeBindingMachineDynamicIndex
import Jihoo.NativeLoanTypeUniqueness
import Jihoo.NativeBindingMachineRunAlgebra

/-! Actual captured-number comparisons construct erased source evidence and
preserve value-closing contexts for arbitrary full-source branch bodies. The
machine's provenance evidence is retained independently of the canonical proof
in the semantic closing; no typing of effectful provenance is assumed. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

private theorem natural_slot
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings .u64)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (shape : code.term = .var index) :
    ∃ number, code.values[index]? = some (some (.natural number)) ∧
      meanings index = .natural number ∧ number < 2^64 := by
  obtain ⟨value,stored,kind⟩ := context.variable_kind history typed aligned shape
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have meaning := context.scalars.1 index number stored
  have actual : LoanTyping.HasType env [] [] true (.natural number) .u64 := by
    simpa only [shape,Term.subst,meaning] using typed.closed history
  exact ⟨number,stored,meaning,actual.natural_bound⟩

private theorem less_branch_context
    (context : ValueContext env code meanings)
    (leftMeaning : meanings left = .natural first) (rightMeaning : meanings right = .natural second)
    (firstBound : first < 2^64) (secondBound : second < 2^64) (compared : first < second) :
    ValueContext env (branchCode false (code.child yes) (.var left) (.var right))
      (consValues (.decide (.natural first) (.natural second)) meanings) := by
  have proofTyped : LoanTyping.HasType env [] [] true (.decide (.natural first) (.natural second))
      ((Term.lt (.var left) (.var right)).subst meanings) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,leftMeaning,rightMeaning] using
      (show LoanTyping.HasType env [] [] true (.decide (.natural first) (.natural second))
        (.lt (.natural first) (.natural second)) from .decide firstBound secondBound compared)
  refine ⟨context.closing.consValues proofTyped,?_,?_⟩
  · constructor
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.1 index actual stored
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.2 index actual stored
  · intro index binding value selected stored
    cases index with
    | zero => cases stored
    | succ index =>
        obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
        subst binding
        simpa only [shift_subst_consValues] using context.kinds index previous value found stored

set_option linter.unusedSimpArgs false in
private theorem captured_less_five_steps (heap : SizedBufferHeap.State) (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var left) (.var right) yes no)
    (leftStored : code.values[left]? = some (some (.natural first)))
    (rightStored : code.values[right]? = some (some (.natural second))) :
    run 5 ⟨heap,.evaluate code,stack⟩ =
      if first < second then
        ⟨⟨heap,.evaluate (branchCode false (code.child yes) (.var left) (.var right)),stack⟩,[],5⟩
      else ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  by_cases compared : first < second
  all_goals simp only [run,step,action,evaluateAction,returnAction,execute,shape,Code.child,
    leftStored,rightStored,compared,↓reduceIte,decide_true,decide_false,Bool.false_eq_true,Option.map_some,Option.map_none]
  all_goals rfl

/-- Erased comparison entry shifts source owner indices but preserves their
lexical reader keys, concrete owner slots and every outer reader frame. -/
theorem LoanSlots.less_branch (slots : LoanSlots code loans stack)
    (entered : Loans.Entered code.context.length loans) (yes : Term) (left right : Nat) :
    LoanSlots (branchCode false (code.child yes) (.var left) (.var right)) loans stack := by
  exact slots.enter entered true (.lt (.var left) (.var right)) yes
    (.decide (code.origins left) (code.origins right)) none

/-- Source typing of arbitrary yes/no bodies is preserved at the actual branch
selected from captured U64 values. Both values, their ranges, canonical erased
proof, post-context and five actual transitions are constructed. -/
theorem reachable_captured_less_branch (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .ifLt (.var left) (.var right) yes no) :
    ∃ first second,
      code.values[left]? = some (some (.natural first)) ∧
      code.values[right]? = some (some (.natural second)) ∧
      meanings left = .natural first ∧ meanings right = .natural second ∧
      first < 2^64 ∧ second < 2^64 ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      if first < second then
        let branch := branchCode false (code.child yes) (.var left) (.var right)
        let branchMeanings := consValues (.decide (.natural first) (.natural second)) meanings
        LoanClosingTyped env loans false branch branchMeanings type ∧
        ValueContext env branch branchMeanings ∧
        run 5 (run fuel (initial term)).state = ⟨⟨heap,.evaluate branch,stack⟩,[],5⟩
      else
        LoanClosingTyped env loans false (code.child no) meanings type ∧
        ValueContext env (code.child no) meanings ∧
        run 5 (run fuel (initial term)).state = ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := source.ifLt_inputs
  have rebuilt : LoanTyping.HasType env loans code.context false
      (.ifLt (.var left) (.var right) yes no) result := .ifLt leftTyped rightTyped yesTyped noTyped
  have resultConverted := ((rebuilt.unique history.wellFormed source).substitution meanings
    history.wellFormed.closed).trans converted
  have leftClosing : LoanClosingTyped env loans false (code.child (.var left)) meanings .u64 :=
    ⟨closing,.u64,leftTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  have rightClosing : LoanClosingTyped env loans false (code.child (.var right)) meanings .u64 :=
    ⟨closing,.u64,rightTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  have aligned := initial_run_code_aligned term fuel _ evaluating
  obtain ⟨first,leftStored,leftMeaning,firstBound⟩ := natural_slot history leftClosing (context.child _) aligned rfl
  obtain ⟨second,rightStored,rightMeaning,secondBound⟩ := natural_slot history rightClosing (context.child _) aligned rfl
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate code,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := captured_less_five_steps (run fuel (initial term)).state.heap code
    (run fuel (initial term)).state.stack shape leftStored rightStored
  rw [← stateShape] at executed
  refine ⟨first,second,leftStored,rightStored,leftMeaning,rightMeaning,firstBound,secondBound,?_⟩
  by_cases compared : first < second
  · simp only [compared,↓reduceIte] at executed ⊢
    have branchContext := less_branch_context (yes := yes) context leftMeaning rightMeaning firstBound secondBound compared
    refine ⟨⟨branchContext.closing,result.rename Nat.succ,yesTyped,?_⟩,branchContext,executed⟩
    simpa only [shift_subst_consValues] using resultConverted
  · simp only [compared,↓reduceIte] at executed ⊢
    exact ⟨⟨closing,result,noTyped,resultConverted⟩,context.child _,executed⟩

/-- A true captured comparison enters a source-authorized Borrow and uses a
lease already present in the actual reader stack. This preserves all nested
readers: neither a token/liveness witness nor successful Borrow is an input. -/
theorem reachable_captured_less_borrow (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .ifLt (.var left) (.var right) (.borrow (.var (owner+1))) no)
    (entered : Loans.Entered code.context.length loans)
    (slots : LoanSlots code loans (run fuel (initial term)).state.stack) :
    ∃ first second,
      meanings left = .natural first ∧ meanings right = .natural second ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      if first < second then
        ∃ token object, heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
          run 6 (run fuel (initial term)).state = ⟨⟨heap,.returned (.reference token),stack⟩,[],6⟩
      else
        LoanClosingTyped env loans false (code.child no) meanings type ∧
        ValueContext env (code.child no) meanings ∧
        run 5 (run fuel (initial term)).state = ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  obtain ⟨first,second,leftStored,rightStored,leftMeaning,rightMeaning,firstBound,secondBound,selected⟩ :=
    reachable_captured_less_branch term fuel history evaluating typed context shape
  refine ⟨first,second,leftMeaning,rightMeaning,?_⟩
  by_cases compared : first < second
  · simp only [compared,↓reduceIte] at selected ⊢
    obtain ⟨branchTyped,branchContext,executed⟩ := selected
    obtain ⟨closing,localType,source,converted⟩ := branchTyped
    have branchSlots := slots.less_branch entered (.borrow (.var (owner+1))) left right
    obtain ⟨token,object,leased,live,borrowed⟩ := typed_borrow_executes
      (initial_run_heap_valid term fuel) (initial_run_readers_live term fuel) branchSlots source rfl
    have one : run 1
        ⟨(run fuel (initial term)).state.heap,
          .evaluate (branchCode false (code.child (.borrow (.var (owner+1)))) (.var left) (.var right)),
          (run fuel (initial term)).state.stack⟩ =
        ⟨⟨(run fuel (initial term)).state.heap,.returned (.reference token),
          (run fuel (initial term)).state.stack⟩,[],1⟩ := by
      simp only [run,step,action,Option.map_some,borrowed]
      rfl
    have composed := run_add 5 1 (run fuel (initial term)).state
    dsimp only at composed
    rw [executed] at composed
    dsimp only at composed
    rw [one] at composed
    exact ⟨token,object,leased,live,composed⟩
  · simpa only [compared,↓reduceIte] using selected

end Jihoo.NativeKernel.Environment.BindingMachine
