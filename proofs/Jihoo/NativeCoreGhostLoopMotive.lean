import Jihoo.NativeCoreGhostBackMotive

/-! Loop uses the same relevant product exposure as Back, but the result
sort selects the proof bit. Data motives must have a single non-return-pair
accumulator representation after normalization. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLoopMotive

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained requireTypes requireTypes_progress
  requireTypes_refines next_progress)
open NativeCoreGhostBackMotive (exposeProduct product_progress product_refines checkRepresentation
  representation_progress representation_refines iteration_representation_policy)
open NativeCoreGhostReferenceTypes (BoxedFamilies)
open EnvironmentDelta (expand expandArgs)

structure CheckedMotive where
  proof : Bool
  compared : List (Nat × Nat)

private def inspectSort (normal : Visit) (isBoxed : Nat → Bool) (state : State) (level motive : Nat) : Outcome Bool :=
  (NativeCoreGhostSort.sort normal state level).next fun after sort =>
    match sort with
    | .prop => ⟨after,.ok true⟩
    | .type 0 => (checkRepresentation normal isBoxed after motive false).next fun checked _ => ⟨checked,.ok false⟩
    | _ => ⟨after,.error (.outsideFragment motive)⟩

/-- The comparison uses the same fresh U64 node later reused for the count. -/
def run (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (limit depth : Nat) (state : State)
    (word motive : Nat) : Outcome CheckedMotive :=
  (infer state motive).next fun inferred answer =>
    (exposeProduct normal inferred answer.typeRoot motive).next fun exposed product =>
      (requireTypes normal limit depth exposed product.1 word motive).next fun compared pair =>
        (inspectSort normal isBoxed compared product.2 motive).next fun after proof =>
          ⟨after,.ok ⟨proof,answer.compared ++ [pair]⟩⟩

private theorem inspectSort_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (inspectSort normal isBoxed state level motive) := by
  unfold inspectSort
  apply (NativeCoreGhostSort.sort_progress normalizes).next
  intro sort
  split
  · exact Progress.atState _ _
  · exact (representation_progress normalizes).next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal isBoxed limit depth state word motive) := by
  unfold run
  apply next_progress (infers _ _ room) room
  intro answer _ inferRoom
  apply next_progress (product_progress normalizes) inferRoom
  intro product _ productRoom
  apply next_progress (requireTypes_progress (fun after root _ => normalizes after root) productRoom) productRoom
  intro pair _ _
  exact (inspectSort_progress normalizes).next (fun _ => Progress.atState _ _)

private theorem inspectSort_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (sortRep : Represents state.arena level sort) (motiveRep : Represents state.arena motive written)
    (success : (inspectSort normal isBoxed state level motive).result = .ok proof) :
    let after := (inspectSort normal isBoxed state level motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env sort) (loopSortTerm proof) ∧
      (∀ mode, BoxedFamilies env isBoxed → LoanTyping.IterationMotiveAllowed env mode proof (expand env written)) := by
  unfold inspectSort at success ⊢
  obtain ⟨selected,sorted,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,converted⟩ := NativeCoreGhostSort.sort_refines normalSound onBase sortRep sorted
  split at success
  · cases success
    exact ⟨kept,backward,converted,fun _ _ => .inr (.inl rfl)⟩
  · obtain ⟨⟨⟩,allowed,accepted⟩ := Outcome.next_success success
    rw [accepted] at success ⊢
    cases success
    obtain ⟨after,afterBack⟩ := representation_refines normalSound (onBase.trans kept) (motiveRep.frame kept) allowed
    exact ⟨kept.trans after,afterBack ∘ backward,converted,
      fun mode metadata => iteration_representation_policy (mode := mode) metadata
        normalSound (onBase.trans kept) (motiveRep.frame kept) allowed⟩
  · cases success

/-- Native sort selection yields the original motive at the relevant U64
product and the exact sort used to check the remaining iteration operands. -/
theorem run_refines_with_policy
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (wordRep : Represents state.arena word .u64) (motiveRep : Represents state.arena motive written)
    (success : (run infer normal isBoxed limit depth state word motive).result = .ok checked)
    (ambient : Prefix (run infer normal isBoxed limit depth state word motive).state.arena final)
    (retained : ∀ pair ∈ checked.compared, PairRetained final pair) :
    let after := (run infer normal isBoxed limit depth state word motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env written) (.pi false .u64 (loopSortTerm checked.proof)) ∧
      (∀ mode, BoxedFamilies env isBoxed → LoanTyping.IterationMotiveAllowed env mode checked.proof (expand env written)) := by
  unfold run at success ambient ⊢
  obtain ⟨inferred,inferOk,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ambient ⊢
  obtain ⟨pair,equalOk,equalNext⟩ := Outcome.next_success success
  rw [equalNext] at success ambient ⊢
  obtain ⟨proof,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst checked
  let inferredType := infer state motive
  let exposed := exposeProduct normal inferredType.state inferred.typeRoot motive
  let equality := requireTypes normal limit depth exposed.state product.1 word motive
  have inferRoom := (infers _ _ room).accepted room inferred inferOk
  have productCost := product_progress (state := inferredType.state) (type := inferred.typeRoot) (motive := motive) normalizes
  have productRoom := productCost.accepted inferRoom product productOk
  have equalCost := requireTypes_progress (state := exposed.state) (depth := depth) (actual := product.1)
    (expected := word) (argument := motive) (fun after root _ => normalizes after root) productRoom
  have resultCost := inspectSort_progress (state := equality.state) (isBoxed := isBoxed)
    (level := product.2) (motive := motive) normalizes
  have afterEqual := resultCost.kept.trans ambient
  obtain ⟨inferKept,inferBack,_,typeRep,typed⟩ := childSound onBase room motiveRep inferOk
    (productCost.kept.trans (equalCost.kept.trans afterEqual))
    (fun entry member => retained entry (List.mem_append_left _ member))
  obtain ⟨productKept,productBack,_,_,domainRep,sortRep,converted⟩ :=
    product_refines normalSound (onBase.trans inferKept) typeRep productOk
  have throughProduct := inferKept.trans productKept
  obtain ⟨equalKept,equalBack,domainConv⟩ := requireTypes_refines normalSound (onBase.trans throughProduct)
    domainRep (wordRep.frame throughProduct) equalOk afterEqual (retained pair (by simp))
  have throughEqual := throughProduct.trans equalKept
  obtain ⟨resultKept,resultBack,levelConv,resultPolicy⟩ := inspectSort_refines normalSound (onBase.trans throughEqual)
    (sortRep.frame equalKept) (motiveRep.frame throughEqual) resultOk
  have wordShape : expand env .u64 = .u64 := by simp only [Term.u64,expand,expandArgs]
  rw [wordShape] at domainConv
  exact ⟨throughEqual.trans resultKept,resultBack ∘ equalBack ∘ productBack ∘ inferBack,
    typed.convert (converted.trans (.node (.pi false) (.cons domainConv (.cons levelConv .nil)))),resultPolicy⟩

theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (wordRep : Represents state.arena word .u64) (motiveRep : Represents state.arena motive written)
    (success : (run infer normal isBoxed limit depth state word motive).result = .ok checked)
    (ambient : Prefix (run infer normal isBoxed limit depth state word motive).state.arena final)
    (retained : ∀ pair ∈ checked.compared, PairRetained final pair) :
    let after := (run infer normal isBoxed limit depth state word motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env written) (.pi false .u64 (loopSortTerm checked.proof)) := by
  obtain ⟨kept,backward,typed,_⟩ :=
    run_refines_with_policy normalSound normalizes childSound infers onBase room wordRep motiveRep success ambient retained
  exact ⟨kept,backward,typed⟩

end Jihoo.NativeKernel.NativeCoreGhostLoopMotive
