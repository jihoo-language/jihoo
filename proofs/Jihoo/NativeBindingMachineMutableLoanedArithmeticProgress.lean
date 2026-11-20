import Jihoo.NativeBindingMachineMutableLoanedArithmetic
import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeBindingMachineMutableNumeric

/-! A typed loaned reader computes its observation or reaches the exact
arithmetic overflow prefix. Runtime progress does not take a result oracle. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

namespace UnsignedOperand

open AffineSum (Expr)

/-- The mathematical sum before testing the machine-width bound. Source
typing ensures that a used capture has the expected natural head. -/
def sum (meanings : Nat → Term) : UnsignedOperand → Nat
  | .literal number => number
  | .captured slot =>
      match meanings slot with
      | .natural number => number
      | _ => 0
  | .add left right => sum meanings left + sum meanings right

def SumsFit (meanings : Nat → Term) : UnsignedOperand → Prop
  | .add left right => sum meanings left + sum meanings right < 2^64
  | _ => True

private theorem word_slot (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false (.var slot) .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original) :
    ∃ number, meanings slot = .natural number ∧ number < 2^64 := by
  have closing : LoanClosingTyped env loans false (original.child (.var slot)) meanings .u64 :=
    ⟨context.closing,.u64,typed,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨runtime,stored,kind⟩ := (context.child _).variable_kind history closing (aligned.child _) rfl
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  have meaning := context.scalars.1 slot number stored
  have numeral : LoanTyping.HasType env [] [] true (.natural number) .u64 := by
    simpa only [Code.child,Term.subst,meaning] using closing.closed history
  exact ⟨number,meaning,numeral.natural_bound⟩

/-- Literal and captured words fit by source typing. When the enclosing
nonnegative sum fits, both subtrees fit, and the checked interpretation
produces its mathematical value without a supplied result. -/
theorem checked_value (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false operand.term .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (bounded : operand.SumsFit meanings) :
    operand.value meanings = some (operand.sum meanings) := by
  induction operand with
  | literal number =>
      have width := typed.natural_bound
      change (if number < 2^64 then some number else none) = some number
      exact ite_eq_left width
  | captured slot =>
      obtain ⟨number,meaning,width⟩ := word_slot history typed context aligned
      simp only [value,sum,meaning]
      change (if number < 2^64 then some number else none) = some number
      exact ite_eq_left width
  | add left right leftRec rightRec =>
      obtain ⟨leftTyped,rightTyped⟩ := typed.uadd_runtime_inputs
      change left.sum meanings + right.sum meanings < 2^64 at bounded
      have leftFits : left.SumsFit meanings := by
        cases left <;> simp only [SumsFit] <;> first | trivial | exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bounded
      have rightFits : right.SumsFit meanings := by
        cases right <;> simp only [SumsFit] <;> first | trivial | exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bounded
      simp only [value,sum,leftRec leftTyped leftFits,rightRec rightTyped rightFits]
      change (if left.sum meanings+right.sum meanings < 2^64 then some _ else none) = _
      exact ite_eq_left bounded

private theorem closed_affine (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false operand.term .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original) :
    ∃ expression : Expr, operand.term.subst meanings = expression.toTerm ∧
      expression.eval (fun _ => 0) = operand.sum meanings := by
  induction operand with
  | literal number =>
      refine ⟨.literal number, ?_, rfl⟩
      simp only [term, Term.natural, Term.subst, substArgs, Expr.toTerm]
  | captured slot =>
      obtain ⟨number, meaning, _⟩ := word_slot history typed context aligned
      refine ⟨.literal number, ?_, by simp only [sum, meaning, Expr.eval]⟩
      simpa only [term, Term.subst, Expr.toTerm] using meaning
  | add left right leftRec rightRec =>
      obtain ⟨leftTyped, rightTyped⟩ := typed.uadd_runtime_inputs
      obtain ⟨a, leftTerm, leftValue⟩ := leftRec leftTyped
      obtain ⟨b, rightTerm, rightValue⟩ := rightRec rightTyped
      refine ⟨.add a b, ?_, ?_⟩
      · simp only [term, Term.uadd, Term.subst, substArgs, Op.binders, liftSub, Expr.toTerm, leftTerm, rightTerm]
      · simp only [sum, Expr.eval, leftValue, rightValue]

/-- The checked inequality determines the index and length numerals.
Affine conversion identifies the index with the mathematical sum of the
runtime words, and the original length converts to the upper bound. -/
theorem checked_index_bound_of_decide (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false operand.term .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (bound : LoanTyping.HasType env loans original.context true evidence (.lt operand.term count))
    (decision : ∃ left right, evidence.subst meanings = .decide left right) :
    ∃ length,
      LoanTyping.Conversion.Conv env (count.subst meanings) (.natural length) ∧
      operand.sum meanings < length ∧ length < 2^64 := by
  obtain ⟨left, right, decision⟩ := decision
  have checked : LoanTyping.HasType env [] [] true (.decide left right)
      (.lt (operand.term.subst meanings) (count.subst meanings)) := by
    simpa only [decision, Term.lt, Term.subst, substArgs, Op.binders, liftSub] using
      bound.ghostSubstitution history.wellFormed context.closing
  obtain ⟨first, second, reduces, lengthReduces, _, lengthWidth, ordered⟩ := checked.decide_truth
  have endpoints := checked.principalView.lt_injective history.wellFormed.admissible
  have normalized := endpoints.1.symm.trans reduces
  obtain ⟨expression, written, evaluated⟩ := operand.closed_affine history typed context aligned
  rw [written] at normalized
  have equal := Semantics.LoanArithmetic.affine_conversion_value history.wellFormed
    expression (.literal first) normalized (fun _ => 0)
  rw [evaluated] at equal
  change operand.sum meanings = first at equal
  exact ⟨second, endpoints.2.symm.trans lengthReduces, by rw [equal]; exact ordered, lengthWidth⟩

theorem checked_value_of_decide (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false operand.term .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (bound : LoanTyping.HasType env loans original.context true evidence (.lt operand.term count))
    (decision : ∃ left right, evidence.subst meanings = .decide left right) :
    operand.value meanings = some (operand.sum meanings) := by
  obtain ⟨_, _, within, lengthWidth⟩ := operand.checked_index_bound_of_decide history typed context aligned bound decision
  have width := Nat.lt_trans within lengthWidth
  apply operand.checked_value history typed context aligned
  cases operand with
  | literal | captured => exact True.intro
  | add => exact width

/-- The actual length interpretation and arithmetic guard certify both the
mathematical index and its corresponding executable word computation. -/
theorem checked_value_of_arithmetic_bound (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false operand.term .u64)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (bound : LoanTyping.HasType env loans original.context true evidence (.lt operand.term count))
    (supported : Semantics.LoanArithmetic.Supported (evidence.subst meanings))
    (physical : LoanTyping.Conversion.Conv env (.natural length) (count.subst meanings))
    (lengthWidth : length < 2^64) :
    operand.sum meanings < length ∧ operand.value meanings = some (operand.sum meanings) := by
  have checked : LoanTyping.HasType env [] [] true (evidence.subst meanings)
      (.lt (operand.term.subst meanings) (count.subst meanings)) := by
    simpa only [Term.lt, Term.subst, substArgs, Op.binders, liftSub] using
      bound.ghostSubstitution history.wellFormed context.closing
  obtain ⟨expression, written, evaluated⟩ := operand.closed_affine history typed context aligned
  have same : LoanTyping.Conversion.Conv env (operand.term.subst meanings) expression.toTerm := by
    rw [written]
    exact .refl _
  have within := Semantics.LoanArithmetic.supported_affine_bound history.wellFormed expression
    checked supported same physical.symm (fun _ => 0)
  rw [evaluated] at within
  have width := Nat.lt_trans within lengthWidth
  refine ⟨within, operand.checked_value history typed context aligned ?_⟩
  cases operand with
  | literal | captured => exact True.intro
  | add => exact width

end UnsignedOperand

private theorem reference_kind_shape (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value (.ref (.buffer count))) : ∃ token, value = .reference token := by
  cases value with
  | reference token => exact ⟨token,rfl⟩
  | natural => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | integer => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | array => exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) kind admissible)
  | owner =>
      obtain ⟨size,converted⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) converted admissible)
  | closure =>
      obtain ⟨domain,body,converted⟩ := kind
      exact False.elim (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) converted admissible)
  | typeCode =>
      obtain ⟨sort,converted⟩ := kind
      cases sort <;> exact False.elim
        (RawLend.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) converted admissible)

namespace LoanedArithmetic

/-- A captured read uses a checked Buffer reference. Source evidence
determines the width of each computed index. -/
def Ready (env : Environment) (loans : Loans.Stack) (ctx : Context) : LoanedArithmetic → Prop
  | .literal _ => True
  | .read .bound _ _ => True
  | .read (.captured slot) _ _ => ∃ count, LoanTyping.HasType env loans ctx false (.var slot) (.ref (.buffer count))
  | .arithmetic _ left right => Ready env loans ctx left ∧ Ready env loans ctx right

private theorem read_replay_ready (reference : ReaderReference) (word : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false (.index (reference.specialized owner) word.term evidence) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (heapNumbers : HeapNumbers heap.metadata) (sizes : OwnerSizes env heap.metadata original meanings)
    (references : ReferenceSizes env heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (freshLease : heap.metadata.heap.lease fresh = some object)
    (supported : Semantics.LoanArithmetic.Supported (evidence.subst meanings))
    (ready : (.read reference word evidence : LoanedArithmetic).Ready env loans original.context) :
    ∃ observation, (.read reference word evidence : LoanedArithmetic).replay original heap fresh meanings =
      some observation := by
  have resolution : ∃ token target, reference.token original fresh = some token ∧
      heap.metadata.heap.lease token = some target := by
    cases reference with
    | bound => exact ⟨fresh, object, rfl, freshLease⟩
    | captured slot =>
        obtain ⟨count, referenceTyped⟩ := ready
        have closed : LoanClosingTyped env loans false (original.child (.var slot)) meanings
            ((Term.ref (.buffer count)).subst meanings) :=
          ⟨context.closing,.ref (.buffer count),referenceTyped,.refl _⟩
        obtain ⟨value, selected, kind⟩ := (context.child _).variable_kind history closed (aligned.child _) rfl
        have referenceKind : ValueKind env value (.ref (.buffer (count.subst meanings))) := by
          simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
        obtain ⟨token,rfl⟩ := reference_kind_shape history.wellFormed.admissible referenceKind
        obtain ⟨target,_,lease,_,_,_⟩ := references.typed_variable history referenceTyped selected
        change original.values[slot]? = some (some (.reference token)) at selected
        exact ⟨token, target, by simp [ReaderReference.token, selected], lease⟩
  obtain ⟨token, target, selected, lease⟩ := resolution
  obtain ⟨_, indexTyped, boundTyped, physical⟩ := reference_index_typing reference word history typed
    context aligned sizes references stored freshLease selected lease
  have lengthWidth : heap.metadata.length target < 2^64 := by
    have width := heapNumbers.length target
    omega
  have offset := (word.checked_value_of_arithmetic_bound history indexTyped context aligned boundTyped
    supported physical lengthWidth).2
  let payload := heap.cell target (word.sum meanings)
  refine ⟨⟨decodeInteger payload,[.legacy (.heap (.read token (word.sum meanings) payload))]⟩,?_⟩
  simp [replay,selected,lease,offset,bind,Option.bind,payload]

theorem replay_no_lifecycle (tree : LoanedArithmetic)
    (observed : tree.replay original heap fresh meanings = some observation) :
    observation.events.filterMap Event.lifecycle? = [] := by
  induction tree generalizing observation with
  | literal number =>
      simp only [replay] at observed
      split at observed
      · cases observed
        rfl
      · contradiction
  | read reference word evidence =>
      simp only [replay] at observed
      obtain ⟨_,_,rest⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨_,_,rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_,_,same⟩ := Option.bind_eq_some_iff.mp rest
      cases same
      rfl
  | arithmetic op left right leftRec rightRec =>
      simp only [replay] at observed
      obtain ⟨lhs,leftValue,rest⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨rhs,rightValue,same⟩ := Option.bind_eq_some_iff.mp rest
      split at same
      · cases same
        simp only [List.filterMap_append,leftRec leftValue,rightRec rightValue,List.nil_append]
      · contradiction

def OverflowPrefix (state : State) (limit : Nat) : Prop :=
  ∃ ticks events remaining, ticks ≤ limit ∧
    run ticks state = ⟨⟨state.heap,.fault .arithmeticOverflow,remaining,state.pending⟩,events,ticks⟩ ∧
    events.filterMap Event.lifecycle? = []

/-- A typed reader computes its own successful observation or reaches the
precise signed overflow prefix. A left fault prevents the right read, and
a fault can neither modify the heap nor execute a lease lifecycle event. -/
theorem checked_progress (tree : LoanedArithmetic)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans original.context false (tree.specialized owner) type)
    (context : ValueContext env original meanings) (aligned : CodeAligned original)
    (heapNumbers : HeapNumbers heap.metadata)
    (sizes : OwnerSizes env heap.metadata original meanings) (references : ReferenceSizes env heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (leased : heap.metadata.heap.lease fresh = some object)
    (checked : LoanTyping.ResourceQuantity.projectRaw depth env loans original.context (tree.specialized owner) = some receipt)
    (evidence : tree.ArithmeticEvidence meanings) (ready : tree.Ready env loans original.context)
    (domain readerBody origin : Term) (stack : List Frame) (pending : List (BufferFrame × List Frame)) :
    let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
    let state : State := ⟨heap,.evaluate (entry.child tree.term),stack,pending⟩
    (∃ observation, tree.replay original heap fresh meanings = some observation ∧
      run tree.ticks state = ⟨⟨heap,.returned (.integer observation.number),stack,pending⟩,observation.events,tree.ticks⟩) ∨
      OverflowPrefix state tree.ticks := by
  let entry := enter false domain readerBody original.context original.origins original.values origin (some (.reference fresh))
  induction tree generalizing type depth receipt stack with
  | literal number =>
      have bounded := typed.integer_bound
      have observed : (LoanedArithmetic.literal number).replay original heap fresh meanings = some ⟨number,[]⟩ := by
        simp only [replay,bounded,ite_true]
      exact .inl ⟨_,observed,(LoanedArithmetic.literal number).checked_run history typed context aligned
        sizes references stored leased checked evidence observed domain readerBody origin stack pending⟩
  | read reference word bound =>
      obtain ⟨observation,observed⟩ := read_replay_ready reference word history typed context aligned
        heapNumbers sizes references stored leased evidence ready
      exact .inl ⟨observation,observed,(LoanedArithmetic.read reference word bound).checked_run history typed context
        aligned sizes references stored leased checked evidence observed domain readerBody origin stack pending⟩
  | arithmetic op left right leftRec rightRec =>
      obtain ⟨leftTyped,rightTyped⟩ := typed.arith_inputs
      obtain ⟨_,_,_,leftChecked,rightChecked,_⟩ :=
        LoanTyping.ResourceQuantity.projectRaw_arithmetic_operands checked
      let leftStack := .arithmeticLeft op (entry.child right.term) :: stack
      have leftStart : step ⟨heap,.evaluate (entry.child (.arith op left.term right.term)),stack,pending⟩ =
          some (⟨heap,.evaluate (entry.child left.term),leftStack,pending⟩,none) := rfl
      rcases leftRec leftTyped leftChecked evidence.1 ready.1 leftStack with
        ⟨lhs,leftValue,leftRun⟩ | ⟨elapsed,events,remaining,limit,faulted,onlyReads⟩
      · let rightStack := .arithmeticRight op lhs.number :: stack
        have rightStart : step ⟨heap,.returned (.integer lhs.number),leftStack,pending⟩ =
            some (⟨heap,.evaluate (entry.child right.term),rightStack,pending⟩,none) := rfl
        rcases rightRec rightTyped rightChecked evidence.2 ready.2 rightStack with
          ⟨rhs,rightValue,rightRun⟩ | ⟨elapsed,events,remaining,limit,faulted,onlyReads⟩
        · let answer := ValueReduction.arithmetic op lhs.number rhs.number
          by_cases bounded : ValueReduction.signed64 answer
          · have observed : (LoanedArithmetic.arithmetic op left right).replay original heap fresh meanings =
                some ⟨answer,lhs.events ++ rhs.events⟩ := by
              have fits : ValueReduction.signed64 (ValueReduction.arithmetic op lhs.number rhs.number) := bounded
              simp [replay,leftValue,rightValue,bind,Option.bind,fits,answer]
            exact .inl ⟨_,observed,(LoanedArithmetic.arithmetic op left right).checked_run history typed
              context aligned sizes references stored leased checked evidence observed domain readerBody origin stack pending⟩
          · have final : run 1 ⟨heap,.returned (.integer rhs.number),rightStack,pending⟩ =
                ⟨⟨heap,.fault .arithmeticOverflow,stack,pending⟩,[],1⟩ := by
              have rejects : ¬ ValueReduction.signed64 (ValueReduction.arithmetic op lhs.number rhs.number) := bounded
              simp only [rightStack,run,step,returnAction,rejects,ite_false,executeLegacy,execute,fault,Option.map_none]
              rfl
            have fullRun := join_runs (noevent_step_run leftStart) (join_runs leftRun
              (join_runs (noevent_step_run rightStart) (join_runs rightRun final)))
            refine .inr ⟨(LoanedArithmetic.arithmetic op left right).ticks,lhs.events ++ rhs.events,stack,Nat.le_refl _,?_,?_⟩
            · simpa only [term,ticks,List.nil_append,List.append_nil] using fullRun
            · simp only [List.filterMap_append,left.replay_no_lifecycle leftValue,right.replay_no_lifecycle rightValue,List.nil_append]
        · have fullRun := join_runs (noevent_step_run leftStart) (join_runs leftRun
            (join_runs (noevent_step_run rightStart) faulted))
          refine .inr ⟨1+(left.ticks+(1+elapsed)),lhs.events ++ events,remaining,?_,?_,?_⟩
          · simp only [ticks]
            omega
          · simpa only [term,List.nil_append] using fullRun
          · simp only [List.filterMap_append,left.replay_no_lifecycle leftValue,onlyReads,List.nil_append]
      · have stopped := join_runs (noevent_step_run leftStart) faulted
        refine .inr ⟨1+elapsed,events,remaining,?_,?_,onlyReads⟩
        · simp only [ticks]
          omega
        · simpa only [term,List.nil_append] using stopped

end LoanedArithmetic

/-- The actual checked Lend needs no supplied reader result. The reader
either completes and restores its original continuation, or stops at the
arithmetic overflow prefix with the lease open and no close event. -/
theorem reachable_loaned_arithmetic_progress (program : Term) (fuel : Nat) (tree : LoanedArithmetic)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .lend (.var owner) (.lam false (.ref (.buffer count)) tree.term)
      (.lam false first (.lam false again body)))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (references : ReferenceSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (evidence : tree.ArithmeticEvidence meanings)
    (ready : tree.Ready env (Loans.enter code.context.length owner loans) code.context)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let token := before.heap.metadata.heap.nextLease
    let origin := (Term.var owner).subst code.origins
    let reader := enter false (.ref (.buffer count)) tree.term code.context code.origins code.values
      (.borrow origin) (some (.reference token))
    ∃ object, code.values[owner]? = some (some (.owner object)) ∧
      let opened : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.lend before.heap.metadata object,before.heap.cell⟩
      (∃ observation, tree.replay code opened token meanings = some observation ∧
        let number := observation.number
        let closed : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.close opened.metadata token,before.heap.cell⟩
        let actual := restoredContinuation code first again body origin reader.origin object (.integer number)
        let canonical := canonicalContinuation code owner first body reader.origin (.integer number)
        let nextMeanings := consValues (.integer number) meanings
        let duration := 5+(tree.ticks+5)
        let result := run duration before
        result = ⟨⟨closed,.evaluate actual,before.stack,before.pending⟩,
          [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))] ++
            observation.events ++ [.legacy (.heap (.close token)),.legacy (.activate false (.lam false again body) reader.origin),
            .legacy (.activate false body origin)],duration⟩ ∧
        closed.metadata.heap.lease token = none ∧
        (∀ older < token, ∀ cell, closed.read older cell = before.heap.read older cell) ∧
        ¬ StateReferenceOccurs token result.state ∧
        CanonicalView actual canonical (Jihoo.Quantity.openOwner (owner+1)) ∧
        ReferenceSizes env closed.metadata canonical nextMeanings ∧
        LoanClosingTyped env loans false canonical nextMeanings type ∧ ValueContext env canonical nextMeanings ∧
        OwnerSizes env closed.metadata canonical nextMeanings ∧
        LoanSlots canonical loans before.activeStack ∧ LoanCoverage canonical loans before.activeStack ∧
        ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans canonical.context canonical.term = some rest ∧
          LoanTyping.ResourceQuantity.LoanBudget canonical.context.length loans rest ∧ rest.demand (owner+1) = some 1 ∧
          OwnerDemandWorld closed.metadata canonical rest ∧ OwnerDemandWorld.Total canonical rest ∧
          ∀ alias, alias ≠ owner → code.values[alias]? = some (some (.owner object)) →
            rest.demand (alias+1) = some 0) ∨
      ∃ ticks events remaining, ticks ≤ tree.ticks ∧ events.filterMap Event.lifecycle? = [] ∧
        let result := run (5+ticks) before
        result = ⟨⟨opened,.fault .arithmeticOverflow,remaining,before.pending⟩,
          [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))] ++ events,5+ticks⟩ ∧
        result.state.heap.metadata.heap.lease token = some object ∧ step result.state = none := by
  let before := (run fuel (initial program)).state
  let token := before.heap.metadata.heap.nextLease
  let origin := (Term.var owner).subst code.origins
  let domain := Term.ref (.buffer count)
  let reader := enter false domain tree.term code.context code.origins code.values (.borrow origin) (some (.reference token))
  obtain ⟨object,stored,restore⟩ := reachable_loaned_arithmetic_restore program fuel tree history evaluating shape typed
    context sizes references slots coverage entered evidence checked budget world complete
  let opened : SizedBufferHeap.IndexedState := ⟨SizedBufferHeap.lend before.heap.metadata object,before.heap.cell⟩
  have checkedLend := shape ▸ checked
  have use := LoanTyping.ResourceQuantity.projectRaw_lend_owner_demand checkedLend
  have live := (world.live_once owner object 0 stored use).1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,readTyped,_,_,_,readProjected,_,_,_,_⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract checkedLend
  rw [tree.specialize_term] at readTyped readProjected
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  have beforeNumbers := (initial_run_numbers program fuel).legacy.1
  have openedNumbers : HeapNumbers opened.metadata := ⟨beforeNumbers.payload, beforeNumbers.length⟩
  have openedSizes : OwnerSizes env opened.metadata code meanings := sizes.steps (.cons (.beginLease live) .nil)
  have openedReferences : ReferenceSizes env opened.metadata code meanings :=
    references.lend (initial_run_invariant program fuel).1 object
  have leased : opened.metadata.heap.lease token = some object := by
    simp [opened,SizedBufferHeap.lend,HeapLeases.put,token]
  let readerStack := .lendFinish token object (some (code.context.length-owner)) origin reader.origin
    (code.child (.lam false first (.lam false again body))) :: before.stack
  let atReader : State := ⟨opened,.evaluate reader,readerStack,before.pending⟩
  have start : run 5 before = ⟨atReader,
      [.legacy (.heap (.beginLease token object)),.legacy (.activate false tree.term (.borrow origin))],5⟩ :=
    named_reader_steps before evaluating shape stored live
  have progress := tree.checked_progress (heap := opened) history readTyped context aligned openedNumbers openedSizes openedReferences
    stored leased readProjected evidence ready domain tree.term (.borrow origin) readerStack before.pending
  refine ⟨object,stored,?_⟩
  rcases progress with ⟨observation,observed,executed⟩ | ⟨ticks,events,remaining,ticksBound,executed,onlyReads⟩
  · obtain ⟨finished,retired,older,absent,_,view,nextReferences,rest⟩ := restore observation observed
    exact .inl ⟨observation,observed,finished,retired,older,absent,view,nextReferences,rest⟩
  · have readFault : run ticks atReader =
        ⟨⟨opened,.fault .arithmeticOverflow,remaining,before.pending⟩,events,ticks⟩ := executed
    have faulted := join_runs start readFault
    refine .inr ⟨ticks,events,remaining,ticksBound,onlyReads,faulted,?_,?_⟩
    · rw [faulted]
      exact leased
    · rw [faulted]
      rfl

namespace Examples

private def nestedReaderOverflow : Term :=
  let buffer := Term.buffer (.natural 2)
  let index := UnsignedOperand.add (.literal 0) (.literal 1)
  let bound := Term.ltAdd (.natural 0) (.natural 1) (.natural 1) (.zeroLe (.natural 0))
  let overflowing := LoanedArithmetic.arithmetic .add (.read .bound index bound) (.literal ((2^63 : Int)-1))
  let computation := LoanedArithmetic.arithmetic .add overflowing (.read (.captured 1) index bound)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let inner := Term.lend (.var 0) (.lam false (.ref buffer) computation.term) release
  let body := Term.app (.lam false buffer inner) (.alloc (.natural 2) (.integer 31))
  let outer := Term.lend (.var 0) (.lam false (.ref buffer) body) release
  .app (.lam false buffer outer) (.alloc (.natural 2) (.integer 8))

set_option maxRecDepth 4096 in
/-- The admitted inner reader first reads its own lease, overflows, and
stops before reading the captured outer reference or closing either lease. -/
theorem nested_reader_overflow_retains_both_leases :
    LoanTyping.MixedProgram.checkDeclaration 96 192 .empty ⟨.i64,nestedReaderOverflow⟩ =
      some ⟨.i64,nestedReaderOverflow⟩ ∧
    let result := run 100 (initial nestedReaderOverflow)
    observe result = .fault .arithmeticOverflow ∧
      result.events.filterMap (fun event => match event with
        | .legacy (.heap (.read token offset payload)) => some (token,offset,payload)
        | _ => none) = [(1,1,encodeInteger 31)] ∧
      result.events.filterMap Event.lifecycle? =
        [.alloc 0 2 (encodeInteger 8),.beginLease 0 0,.alloc 1 2 (encodeInteger 31),.beginLease 1 1] ∧
      result.state.heap.metadata.heap.lease 0 = some 0 ∧ result.state.heap.metadata.heap.lease 1 = some 1 ∧
      step result.state = none := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
