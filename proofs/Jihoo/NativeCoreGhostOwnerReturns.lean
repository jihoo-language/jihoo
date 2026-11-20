import Jihoo.NativeCoreGhostBackMotive

/-! Live arena checks for forming an owner-return type and giving back a
value. The result requirement uses a freshly formed application of the
written motive to the original owner expression. -/
namespace Jihoo.NativeKernel.NativeCoreGhostOwnerReturns

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines PairRetained RetainedComparisons
  requireTypes requireTypes_progress requireTypes_refines next_progress)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreGhostReferenceTypes (BoxedFamilies requireOwned requireOwned_progress requireOwned_refines)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def ownedFormation (normal : Visit) (isBoxed : Nat → Bool) (state : State)
    (owner inferred : Nat) : Outcome Unit :=
  (NativeCoreGhostSort.sort normal state inferred).next fun after sort =>
    if sort = .type 0 then requireOwned normal isBoxed after owner owner else reject after owner

def runBack (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (limit depth : Nat)
    (state : State) (erased : Bool) (owner motive : Nat) : Outcome Inferred :=
  (infer state owner).next fun inferred ownerType =>
    (ownedFormation normal isBoxed inferred owner ownerType.typeRoot).next fun formed _ =>
      (NativeCoreGhostBackMotive.run infer normal isBoxed limit depth formed erased owner motive).next fun checked pairs =>
        (append checked (.universe 0) []).next fun after root =>
          ⟨after,.ok ⟨root,ownerType.compared ++ pairs⟩⟩

private def requireResult (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (motive owner result : Nat) : Outcome (List (Nat × Nat)) :=
  (append state .app [motive,owner]).next fun expected expectedRoot =>
    (infer expected result).next fun inferred answer =>
      (requireTypes normal limit depth inferred answer.typeRoot expectedRoot result).next fun checked pair =>
        ⟨checked,.ok (answer.compared ++ [pair])⟩

def runGive (infer : Infer) (normal : Visit) (isBoxed : Nat → Bool) (limit depth : Nat)
    (state : State) (erased : Bool) (motive owner result : Nat) : Outcome Inferred :=
  (infer state owner).next fun inferred ownerType =>
    (requireOwned normal isBoxed inferred ownerType.typeRoot owner).next fun owned _ =>
      (NativeCoreGhostBackMotive.run infer normal isBoxed limit depth owned erased ownerType.typeRoot motive).next fun formed pairs =>
        (requireResult infer normal limit depth formed motive owner result).next fun checked resultPairs =>
          (append checked (.back erased) [ownerType.typeRoot,motive]).next fun after root =>
            ⟨after,.ok ⟨root,ownerType.compared ++ (pairs ++ resultPairs)⟩⟩

private theorem ownedFormation_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (ownedFormation normal isBoxed state owner inferred) := by
  unfold ownedFormation
  exact (NativeCoreGhostSort.sort_progress normalizes).next (fun _ => by
    split
    · exact requireOwned_progress normalizes
    · exact Progress.atState _ _)

theorem runBack_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runBack infer normal isBoxed limit depth state erased owner motive) := by
  unfold runBack
  apply next_progress (infers _ _ room) room
  intro ownerType _ ownerRoom
  apply next_progress (ownedFormation_progress normalizes) ownerRoom
  intro _ _ formedRoom
  exact (NativeCoreGhostBackMotive.run_progress infers normalizes formedRoom).next
    (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))

private theorem requireResult_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (requireResult infer normal limit depth state motive owner result) := by
  unfold requireResult
  apply next_progress (append_progress _ _ _) room
  intro _ _ formedRoom
  apply next_progress (infers _ _ formedRoom) formedRoom
  intro _ _ inferredRoom
  exact (requireTypes_progress (fun after root _ => normalizes after root) inferredRoom).next
    (fun _ => Progress.atState _ _)

theorem runGive_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runGive infer normal isBoxed limit depth state erased motive owner result) := by
  unfold runGive
  apply next_progress (infers _ _ room) room
  intro _ _ ownerRoom
  apply next_progress (requireOwned_progress normalizes) ownerRoom
  intro _ _ ownedRoom
  apply next_progress (NativeCoreGhostBackMotive.run_progress infers normalizes ownedRoom) ownedRoom
  intro _ _ formedRoom
  exact (requireResult_progress infers normalizes formedRoom).next
    (fun _ => (append_progress _ _ _).next (fun _ => Progress.atState _ _))

private theorem ownedFormation_refines (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (ownerRep : Represents state.arena owner A) (inferredRep : Represents state.arena inferred T)
    (success : (ownedFormation normal isBoxed state owner inferred).result = .ok ()) :
    let after := (ownedFormation normal isBoxed state owner inferred).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env T) (.univ 0) ∧ LoanTyping.Owned env (expand env A) := by
  unfold ownedFormation at success ⊢
  obtain ⟨selected,sorted,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨sortKept,sortBack,converted⟩ := NativeCoreGhostSort.sort_refines normalSound onBase inferredRep sorted
  split at success
  · rename_i same
    subst selected
    simp only [ite_true]
    obtain ⟨kept,backward,owned⟩ := requireOwned_refines metadata normalSound (onBase.trans sortKept)
      (ownerRep.frame sortKept) success
    exact ⟨sortKept.trans kept,backward ∘ sortBack,converted,owned⟩
  · simp [reject] at success

theorem runBack_refines (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena owner A) (motiveRep : Represents state.arena motive M)
    (success : (runBack infer normal isBoxed limit depth state erased owner motive).result = .ok answer)
    (ambient : Prefix (runBack infer normal isBoxed limit depth state erased owner motive).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.back erased A M) (runBack infer normal isBoxed limit depth state erased owner motive) answer := by
  unfold runBack at success ambient ⊢
  obtain ⟨type,typeOk,typeNext⟩ := Outcome.next_success success
  rw [typeNext] at success ambient ⊢
  obtain ⟨⟨⟩,formedOk,formedNext⟩ := Outcome.next_success success
  rw [formedNext] at success ambient ⊢
  obtain ⟨pairs,checkedOk,checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨root,appended,appendNext⟩ := Outcome.next_success success
  rw [appendNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let formed := ownedFormation normal isBoxed (infer state owner).state owner type.typeRoot
  let checked := NativeCoreGhostBackMotive.run infer normal isBoxed limit depth formed.state erased owner motive
  have ownerRoom := (infers _ _ room).accepted room type typeOk
  have formationProgress := ownedFormation_progress (state := (infer state owner).state) (isBoxed := isBoxed)
    (owner := owner) (inferred := type.typeRoot) normalizes
  have formedRoom := formationProgress.accepted ownerRoom () formedOk
  have checkedProgress := NativeCoreGhostBackMotive.run_progress (state := formed.state) (isBoxed := isBoxed)
    (depth := depth) (erased := erased) (ownerType := owner) (motive := motive) infers normalizes formedRoom
  have afterCheck := (append_progress (limit := limit) checked.state (.universe 0) []).kept.trans ambient
  obtain ⟨ownerKept,ownerBack,_,typeRep,ownerTyped⟩ := childSound onBase room ownerRep typeOk
    (formationProgress.kept.trans (checkedProgress.kept.trans afterCheck))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨formedKept,formedBack,sort,owned⟩ := ownedFormation_refines metadata normalSound
    (onBase.trans ownerKept) (ownerRep.frame ownerKept) typeRep formedOk
  have throughFormation := ownerKept.trans formedKept
  obtain ⟨checkedKept,checkedBack,motiveTyped⟩ := NativeCoreGhostBackMotive.run_refines normalSound normalizes childSound infers
    (onBase.trans throughFormation) formedRoom (ownerRep.frame throughFormation) (motiveRep.frame throughFormation)
    checkedOk afterCheck (fun pair member => retained pair (List.mem_append_right _ member))
  obtain ⟨addedKept,addedBack,kindRep⟩ := append_refines .nil rfl appended
  refine ⟨throughFormation.trans (checkedKept.trans addedKept),addedBack ∘ checkedBack ∘ formedBack ∘ ownerBack,_,kindRep,?_⟩
  simpa only [expand,expandArgs] using LoanTyping.HasType.back (ownerTyped.convert sort) owned motiveTyped (.inl rfl)

private theorem requireResult_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (motiveRep : Represents state.arena motive M) (ownerRep : Represents state.arena owner x)
    (resultRep : Represents state.arena result a)
    (success : (requireResult infer normal limit depth state motive owner result).result = .ok pairs)
    (ambient : Prefix (requireResult infer normal limit depth state motive owner result).state.arena final)
    (retained : ∀ pair ∈ pairs, PairRetained final pair) :
    let after := (requireResult infer normal limit depth state motive owner result).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env a) (.app (expand env M) (expand env x)) := by
  unfold requireResult at success ambient ⊢
  obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
  rw [expectedNext] at success ambient ⊢
  obtain ⟨answer,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨pair,requiredOk,requiredNext⟩ := Outcome.next_success success
  rw [requiredNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst pairs
  let formed := append state .app [motive,owner]
  let inferred := infer formed.state result
  have formedRoom := (append_progress _ _ _).accepted room expected expectedOk
  have resultRoom := (infers formed.state result formedRoom).accepted formedRoom answer inferredOk
  have requiredProgress := requireTypes_progress (state := inferred.state) (depth := depth) (actual := answer.typeRoot)
    (expected := expected) (argument := result) (fun after root _ => normalizes after root) resultRoom
  obtain ⟨formedKept,formedBack,expectedRep⟩ := append_refines (.cons motiveRep (.cons ownerRep .nil)) rfl expectedOk
  obtain ⟨inferredKept,inferredBack,_,typeRep,typed⟩ := childSound (onBase.trans formedKept) formedRoom
    (resultRep.frame formedKept) inferredOk (requiredProgress.kept.trans ambient)
    (fun receipt member => retained receipt (List.mem_append_left _ member))
  obtain ⟨requiredKept,requiredBack,converted⟩ := requireTypes_refines normalSound (onBase.trans (formedKept.trans inferredKept))
    typeRep (expectedRep.frame inferredKept) requiredOk ambient (retained pair (by simp))
  refine ⟨formedKept.trans (inferredKept.trans requiredKept),requiredBack ∘ inferredBack ∘ formedBack,?_⟩
  simpa only [Term.app,expand,expandArgs] using typed.convert converted

theorem runGive_refines (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (childSound : InferSound env base ctx limit infer)
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (motiveRep : Represents state.arena motive M) (ownerRep : Represents state.arena owner x)
    (resultRep : Represents state.arena result a)
    (success : (runGive infer normal isBoxed limit depth state erased motive owner result).result = .ok answer)
    (ambient : Prefix (runGive infer normal isBoxed limit depth state erased motive owner result).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.give erased M x a) (runGive infer normal isBoxed limit depth state erased motive owner result) answer := by
  unfold runGive at success ambient ⊢
  obtain ⟨type,typeOk,typeNext⟩ := Outcome.next_success success
  rw [typeNext] at success ambient ⊢
  obtain ⟨⟨⟩,ownedOk,ownedNext⟩ := Outcome.next_success success
  rw [ownedNext] at success ambient ⊢
  obtain ⟨pairs,formedOk,formedNext⟩ := Outcome.next_success success
  rw [formedNext] at success ambient ⊢
  obtain ⟨resultPairs,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  obtain ⟨root,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let accepted := requireOwned normal isBoxed (infer state owner).state type.typeRoot owner
  let formed := NativeCoreGhostBackMotive.run infer normal isBoxed limit depth accepted.state erased type.typeRoot motive
  let checked := requireResult infer normal limit depth formed.state motive owner result
  have ownerRoom := (infers _ _ room).accepted room type typeOk
  have ownershipProgress := requireOwned_progress (state := (infer state owner).state) (isBoxed := isBoxed)
    (root := type.typeRoot) (rejected := owner) normalizes
  have ownedRoom := ownershipProgress.accepted ownerRoom () ownedOk
  have motiveProgress := NativeCoreGhostBackMotive.run_progress (state := accepted.state) (isBoxed := isBoxed)
    (depth := depth) (erased := erased) (ownerType := type.typeRoot) (motive := motive) infers normalizes ownedRoom
  have formedRoom := motiveProgress.accepted ownedRoom pairs formedOk
  have resultProgress := requireResult_progress (state := formed.state) (depth := depth) (motive := motive)
    (owner := owner) (result := result) infers normalizes formedRoom
  have afterResult := (append_progress (limit := limit) checked.state (.back erased) [type.typeRoot,motive]).kept.trans ambient
  have afterMotive := resultProgress.kept.trans afterResult
  obtain ⟨ownerKept,ownerBack,_,typeRep,ownerTyped⟩ := childSound onBase room ownerRep typeOk
    (ownershipProgress.kept.trans (motiveProgress.kept.trans afterMotive))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨ownedKept,ownedBack,owned⟩ := requireOwned_refines metadata normalSound (onBase.trans ownerKept) typeRep ownedOk
  have throughOwner := ownerKept.trans ownedKept
  obtain ⟨formedKept,formedBack,motiveTyped⟩ := NativeCoreGhostBackMotive.run_refines normalSound normalizes childSound infers
    (onBase.trans throughOwner) ownedRoom (typeRep.frame ownedKept) (motiveRep.frame throughOwner)
    formedOk afterMotive (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughMotive := throughOwner.trans formedKept
  obtain ⟨resultKept,resultBack,resultTyped⟩ := requireResult_refines normalSound normalizes childSound infers
    (onBase.trans throughMotive) formedRoom (motiveRep.frame throughMotive) (ownerRep.frame throughMotive)
    (resultRep.frame throughMotive) resultOk afterResult
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
  have later := ownedKept.trans (formedKept.trans resultKept)
  obtain ⟨outputKept,outputBack,outputRep⟩ := append_refines
    (.cons (typeRep.frame later) (.cons (motiveRep.frame (ownerKept.trans later)) .nil)) rfl outputOk
  refine ⟨ownerKept.trans (later.trans outputKept),outputBack ∘ resultBack ∘ formedBack ∘ ownedBack ∘ ownerBack,_,outputRep,?_⟩
  simpa only [expand,expandArgs] using LoanTyping.HasType.give ownerTyped owned motiveTyped (.inl rfl) resultTyped

end Jihoo.NativeKernel.NativeCoreGhostOwnerReturns
