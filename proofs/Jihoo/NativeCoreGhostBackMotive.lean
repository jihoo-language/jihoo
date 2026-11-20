import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreGhostReferenceTypes

/-! Native owner-return motives use a relevant owner argument. Their result
sort controls erasure, and data results pass the live representation gate. -/
namespace Jihoo.NativeKernel.NativeCoreGhostBackMotive

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound PairRetained requireTypes requireTypes_progress
  requireTypes_refines next_progress)
open NativeCoreGhostReferenceTypes (BoxedFamilies)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def resultSort (erased : Bool) : SortTag := if erased then .prop else .type 0

private def fixedHead (isBoxed : Nat → Bool) (allowBack : Bool) (node : Option Node) : Bool :=
  match node with
  | some (.node .u64 []) | some (.node .i64 []) | some (.node .refine [_])
  | some (.node .buffer [_]) => true
  | some (.node (.back _) [_,_]) => allowBack
  | some (.node (.ind family _) _) => isBoxed family
  | _ => false

def checkRepresentation (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (motive : Nat) (allowBack : Bool := true) : Outcome Unit :=
  (normal state motive).next fun exposed root =>
    match exposed.arena[root]? with
    | some (.node (.lam _) [_,body]) =>
      if fixedHead isBoxed allowBack exposed.arena[body]? then ⟨exposed,.ok ()⟩ else reject exposed motive
    | _ => reject exposed motive

private def checkResult (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (erased : Bool) (level motive : Nat) : Outcome Unit :=
  (NativeCoreGhostSort.sort normal state level).next fun after kind =>
    if kind = resultSort erased then
      if erased then ⟨after,.ok ()⟩ else checkRepresentation normal isBoxed after motive
    else reject after motive

def exposeProduct (normal : Visit) (state : State) (type motive : Nat) : Outcome (Nat × Nat) :=
  (normal state type).next fun exposed selected =>
    match exposed.arena[selected]? with
    | some (.node (.pi false) [domain,level]) => ⟨exposed,.ok (domain,level)⟩
    | _ => reject exposed motive

/-- Comparison uses the original owner type even if a normalized root was
already inspected to establish that the owner is a buffer or boxed data. -/
def run (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (limit depth : Nat)
    (state : State) (erased : Bool) (ownerType motive : Nat) : Outcome (List (Nat × Nat)) :=
  (infer state motive).next fun inferred answer =>
    (exposeProduct normal inferred answer.typeRoot motive).next fun exposed product =>
      (requireTypes normal limit depth exposed product.1 ownerType motive).next fun compared pair =>
        (checkResult normal isBoxed compared erased product.2 motive).next fun after _ =>
          ⟨after,.ok (answer.compared ++ [pair])⟩

theorem representation_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkRepresentation normal isBoxed state motive allowBack) := by
  unfold checkRepresentation
  exact (normalProgress _ _).next (fun _ => by
    split
    · split <;> exact Progress.atState _ _
    · exact Progress.atState _ _)

private theorem result_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkResult normal isBoxed state erased level motive) := by
  unfold checkResult
  exact (NativeCoreGhostSort.sort_progress normalProgress).next (fun _ => by
    split
    · split
      · exact Progress.atState _ _
      · exact representation_progress normalProgress
    · exact Progress.atState _ _)

theorem product_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (exposeProduct normal state type motive) := by
  unfold exposeProduct
  exact (normalProgress _ _).next (fun _ => by split <;> exact Progress.atState _ _)

theorem run_progress
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal isBoxed limit depth state erased ownerType motive) := by
  unfold run
  apply next_progress (inferProgress _ _ room) room
  intro answer _ inferRoom
  apply next_progress (product_progress normalProgress) inferRoom
  intro product _ productRoom
  apply next_progress (requireTypes_progress (fun after root _ => normalProgress after root) productRoom) productRoom
  intro pair _ _
  exact (result_progress normalProgress).next (fun _ => Progress.atState _ _)

theorem product_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (represented : Represents state.arena type written)
    (success : (exposeProduct normal state type motive).result = .ok product) :
    let after := (exposeProduct normal state type motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ domain level, Represents after product.1 domain ∧ Represents after product.2 level ∧
        LoanTyping.Conversion.Conv env (expand env written) (.pi false (expand env domain) (expand env level)) := by
  unfold exposeProduct at success ⊢
  obtain ⟨selected,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,residual,held,converted⟩ := normalSound onBase represented normalized
  split at success
  · rename_i domain level read
    cases success
    refine ⟨kept,backward,?_⟩
    cases held with
    | var found => rw [read] at found; cases found
    | node found _ children =>
      rw [read] at found
      cases found
      cases children with
      | cons domainRep remaining =>
        cases remaining with
        | cons levelRep tail =>
          cases tail
          exact ⟨_,_,domainRep,levelRep,by simpa only [Term.pi,expand,expandArgs] using converted.converted⟩
  · simp [reject] at success

theorem representation_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (represented : Represents state.arena motive written)
    (success : (checkRepresentation normal isBoxed state motive allowBack).result = .ok ()) :
    let after := (checkRepresentation normal isBoxed state motive allowBack).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) := by
  unfold checkRepresentation at success ⊢
  obtain ⟨selected,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,_,_,_⟩ := normalSound onBase represented normalized
  split at success
  · split at success
    · rename_i accepted
      simpa only [ite_eq_left accepted] using And.intro kept backward
    · simp [reject] at success
  · simp [reject] at success

private theorem result_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (levelRep : Represents state.arena level kind) (motiveRep : Represents state.arena motive written)
    (success : (checkResult normal isBoxed state erased level motive).result = .ok ()) :
    let after := (checkResult normal isBoxed state erased level motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env kind) (loopSortTerm erased) := by
  unfold checkResult at success ⊢
  obtain ⟨sort,selected,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,converted⟩ := NativeCoreGhostSort.sort_refines normalSound onBase levelRep selected
  split at success
  · rename_i kindMatched
    subst sort
    simp only [ite_true]
    have kindConversion : LoanTyping.Conversion.Conv env (expand env kind) (loopSortTerm erased) := by
      cases erased <;> simpa only [resultSort,Bool.false_eq_true,ite_false,ite_true,SortTag.term,loopSortTerm] using converted
    split at success
    · rename_i isErased
      simp only [ite_eq_left isErased]
      exact ⟨kept,backward,kindConversion⟩
    · rename_i isRelevant
      simp only [ite_eq_right isRelevant]
      obtain ⟨checked,checkedBack⟩ := representation_refines normalSound (onBase.trans kept) (motiveRep.frame kept) success
      exact ⟨kept.trans checked,checkedBack ∘ backward,kindConversion⟩
  · simp [reject] at success

/-- Successful motive checking yields the original source function at the
Pi type over the authenticated owner and the sort selected by erasure. -/
theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena ownerType owner) (motiveRep : Represents state.arena motive written)
    (success : (run infer normal isBoxed limit depth state erased ownerType motive).result = .ok compared)
    (ambient : Prefix (run infer normal isBoxed limit depth state erased ownerType motive).state.arena final)
    (retained : ∀ pair ∈ compared, PairRetained final pair) :
    let after := (run infer normal isBoxed limit depth state erased ownerType motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env written) (.pi false (expand env owner) (loopSortTerm erased)) := by
  unfold run at success ambient ⊢
  obtain ⟨inferred,inferOk,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ambient ⊢
  obtain ⟨pair,equalOk,equalNext⟩ := Outcome.next_success success
  rw [equalNext] at success ambient ⊢
  obtain ⟨⟨⟩,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst compared
  let inferredType := infer state motive
  let exposed := exposeProduct normal inferredType.state inferred.typeRoot motive
  let equality := requireTypes normal limit depth exposed.state product.1 ownerType motive
  have inferredRoom := (inferProgress _ _ room).accepted room inferred inferOk
  have productProgress := product_progress (state := inferredType.state) (type := inferred.typeRoot) (motive := motive) normalProgress
  have productRoom := productProgress.accepted inferredRoom product productOk
  have equalityProgress := requireTypes_progress (state := exposed.state) (depth := depth) (actual := product.1)
    (expected := ownerType) (argument := motive) (fun after root _ => normalProgress after root) productRoom
  have resultProgress := result_progress (state := equality.state) (isBoxed := isBoxed) (erased := erased)
    (level := product.2) (motive := motive) normalProgress
  have equalityFinal := resultProgress.kept.trans ambient
  obtain ⟨inferKept,inferBack,_,typeRep,typed⟩ := inferSound onBase room motiveRep inferOk
    (productProgress.kept.trans (equalityProgress.kept.trans equalityFinal))
    (fun entry member => retained entry (List.mem_append_left _ member))
  obtain ⟨productKept,productBack,_,_,domainRep,levelRep,converted⟩ :=
    product_refines normalSound (onBase.trans inferKept) typeRep productOk
  have throughProduct := inferKept.trans productKept
  obtain ⟨equalKept,equalBack,domainConversion⟩ := requireTypes_refines normalSound (onBase.trans throughProduct)
    domainRep (ownerRep.frame throughProduct) equalOk equalityFinal (retained pair (by simp))
  have throughEqual := throughProduct.trans equalKept
  obtain ⟨resultKept,resultBack,levelConversion⟩ := result_refines normalSound (onBase.trans throughEqual)
    (levelRep.frame equalKept) (motiveRep.frame throughEqual) resultOk
  exact ⟨throughEqual.trans resultKept,resultBack ∘ equalBack ∘ productBack ∘ inferBack,
    typed.convert (converted.trans (.node (.pi false) (.cons domainConversion (.cons levelConversion .nil))))⟩

end Jihoo.NativeKernel.NativeCoreGhostBackMotive
