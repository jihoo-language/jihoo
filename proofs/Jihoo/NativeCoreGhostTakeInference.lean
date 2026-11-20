import Jihoo.NativeCoreGhostTypeRequirement

/-! The native Take branch first exposes the value's owner-return type.
It checks the original continuation annotations before inferring its body,
then normalizes and removes the two callback binders from the result. -/
namespace Jihoo.NativeKernel.NativeCoreGhostTakeInference

open NativeArena NativeCoreGraph Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred InferSound Refines PairRetained RetainedComparisons
  requireTypes requireTypes_progress requireTypes_refines next_progress)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def shift (limit depth : Nat) (state : State) (root : Nat) (amount : Int) : Outcome Nat :=
  let changed := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨changed.state,changed.result.mapError .substitution⟩

private def ownerVar (state : State) : Outcome Nat :=
  match addNode state.arena (.var 0) with
  | .error reason => ⟨state,.error (.add reason)⟩
  | .ok (arena,root) => ⟨{state with arena},.ok root⟩

structure GivenType where
  erased : Bool
  owner : Nat
  motive : Nat

private def exposeGiven (normal : Visit) (state : State) (type subject : Nat) : Outcome GivenType :=
  (normal state type).next fun exposed root =>
    match exposed.arena[root]? with
    | some (.node (.back erased) [owner,motive]) => ⟨exposed,.ok ⟨erased,owner,motive⟩⟩
    | _ => reject exposed subject

private def continuationDomains (arena : Arena) (root : Nat) (erased : Bool) : Option (Nat × Nat) :=
  match arena[root]? with
  | some (.node (.lam false) [owner,inner]) =>
    match arena[inner]? with
    | some (.node (.lam flag) [result,_]) => if flag = erased then some (owner,result) else none
    | _ => none
  | _ => none

private def expectedResult (limit depth : Nat) (state : State) (motive : Nat) : Outcome Nat :=
  (shift limit depth state motive 1).next fun lifted motiveUnderOwner =>
    (ownerVar lifted).next fun formed owner =>
      append formed .app [motiveUnderOwner,owner]

private def checkCallback (normal : Visit) (limit depth : Nat) (state : State) (expected : GivenType)
    (continuation : Nat) : Outcome (List (Nat × Nat)) :=
  match continuationDomains state.arena continuation expected.erased with
  | none => reject state continuation
  | some (owner,result) =>
    (expectedResult limit depth state expected.motive).next fun formed application =>
      (requireTypes normal limit depth formed owner expected.owner continuation).next fun owned first =>
        (requireTypes normal limit depth owned result application continuation).next fun checked second =>
          ⟨checked,.ok [first,second]⟩

private def finish (normal : Visit) (limit depth : Nat) (state : State) (type continuation : Nat) : Outcome Nat :=
  (normal state type).next fun exposed root =>
    match exposed.arena[root]? with
    | some (.node (.pi false) [_,inner]) =>
      match exposed.arena[inner]? with
      | some (.node (.pi _) [_,result]) =>
        (normal exposed result).next fun normalized body => shift limit depth normalized body (-2)
      | _ => reject exposed continuation
    | _ => reject exposed continuation

def run (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State) (subject continuation : Nat) : Outcome Inferred :=
  (infer state subject).next fun inferred value =>
    (exposeGiven normal inferred value.typeRoot subject).next fun exposed expected =>
      (checkCallback normal limit depth exposed expected continuation).next fun checked binderPairs =>
        (infer checked continuation).next fun afterCallback callback =>
          (finish normal limit depth afterCallback callback.typeRoot continuation).next fun after result =>
            ⟨after,.ok ⟨result,value.compared ++ (binderPairs ++ callback.compared)⟩⟩

private theorem shift_answer (accepted : (shift limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shift at accepted
  cases observed : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [observed,Except.mapError,reduceCtorEq,Except.ok.injEq] at accepted ⊢
  exact accepted

private theorem shift_progress : Progress limit state (shift limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ checked => progress.accepted room _ (shift_answer checked)⟩

private theorem ownerVar_progress : Progress limit state (ownerVar state) := by
  cases added : addNode state.arena (.var 0) with
  | error reason =>
    simpa only [ownerVar,added] using (Progress.atState (limit := limit) state (.error (.add reason)) : Progress limit state _)
  | ok result =>
    obtain ⟨arena,root⟩ := result
    simp only [ownerVar,added]
    exact ⟨(addNode_commits added).1,Nat.le_refl _,Nat.le_succ_of_le,fun room _ _ => room⟩

private theorem checkCallback_progress
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (checkCallback normal limit depth state expected continuation) := by
  unfold checkCallback
  split
  · exact Progress.atState _ _
  · have prepared : Progress limit state (expectedResult limit depth state expected.motive) :=
      shift_progress.next fun _ => ownerVar_progress.next fun _ => append_progress _ _ _
    apply next_progress prepared room
    intro _ _ preparedRoom
    apply next_progress (requireTypes_progress (fun after root _ => normalizes after root) preparedRoom) preparedRoom
    intro _ _ firstRoom
    exact (requireTypes_progress (fun after root _ => normalizes after root) firstRoom).next (fun _ => Progress.atState _ _)

private theorem finish_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (finish normal limit depth state type continuation) := by
  unfold finish
  apply (normalizes _ _).next
  intro _
  split
  · split
    · exact (normalizes _ _).next (fun _ => shift_progress)
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth state subject continuation) := by
  unfold run
  apply next_progress (infers _ _ room) room
  intro _ _ inferredRoom
  have exposed : ∀ state type, Progress limit state (exposeGiven normal state type subject) := by
    intro state type
    unfold exposeGiven
    exact (normalizes _ _).next (fun _ => by split <;> exact Progress.atState _ _)
  apply next_progress (exposed _ _) inferredRoom
  intro _ _ exposedRoom
  apply next_progress (checkCallback_progress normalizes exposedRoom) exposedRoom
  intro _ _ checkedRoom
  apply next_progress (infers _ _ checkedRoom) checkedRoom
  intro _ _ _
  exact (finish_progress normalizes).next (fun _ => Progress.atState _ _)

private theorem binary_read (represented : Represents arena root term) (read : arena[root]? = some (.node op [a,b])) :
    ∃ first second, term = .node op [first,second] ∧ Represents arena a first ∧ Represents arena b second := by
  cases represented with
  | var found => rw [read] at found; cases found
  | node found _ children =>
    rw [read] at found
    cases found
    cases children with
    | cons first rest =>
      cases rest with
      | cons second tail =>
        cases tail
        exact ⟨_,_,rfl,first,second⟩

private theorem exposeGiven_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (original : Represents state.arena type written)
    (success : (exposeGiven normal state type subject).result = .ok expected) :
    let after := (exposeGiven normal state type subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ owner motive, Represents after expected.owner owner ∧ Represents after expected.motive motive ∧
        LoanTyping.Conversion.Conv env (expand env written) (.back expected.erased (expand env owner) (expand env motive)) := by
  unfold exposeGiven at success ⊢
  obtain ⟨root,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,selected,selectedRep,converted⟩ := normalSound onBase original normalized
  split at success
  · rename_i erased owner motive read
    cases success
    obtain ⟨_,_,shape,ownerRep,motiveRep⟩ := binary_read selectedRep read
    exact ⟨kept,backward,_,_,ownerRep,motiveRep,by simpa only [shape,expand,expandArgs] using converted.converted⟩
  · simp [reject] at success

private theorem continuationDomains_refines
    (source : Represents arena root written)
    (found : continuationDomains arena root erased = some (owner,result)) :
    ∃ T A body, written = .lam false T (.lam erased A body) ∧ Represents arena owner T ∧ Represents arena result A := by
  unfold continuationDomains at found
  split at found
  · rename_i domain inner read
    split at found
    · rename_i flag codomain bodyRef readInner
      split at found
      · rename_i same
        subst flag
        cases found
        obtain ⟨T,innerTerm,writtenShape,held,innerRep⟩ := binary_read source read
        obtain ⟨A,body,innerWritten,results,_⟩ := binary_read innerRep readInner
        exact ⟨T,A,body,by rw [writtenShape,innerWritten],held,results⟩
      · cases found
    · cases found
  · cases found

private theorem expectedResult_refines (wf : UnifiedProgram.EnvWellFormed env)
    (motiveRep : Represents state.arena motive written)
    (success : (expectedResult limit depth state motive).result = .ok appRoot) :
    let after := (expectedResult limit depth state motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ term, Represents after appRoot term ∧ expand env term = takeResultType (expand env written) := by
  unfold expectedResult at success ⊢
  obtain ⟨lifted,liftedOk,liftedNext⟩ := Outcome.next_success success
  rw [liftedNext] at success ⊢
  obtain ⟨owner,ownerOk,ownerNext⟩ := Outcome.next_success success
  rw [ownerNext] at success ⊢
  obtain ⟨shiftKept,shiftBack,raised,changed,liftedRep⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift 1) (binders := 0) (value := written)
      motiveRep trivial (shift_answer liftedOk)).1
  change PartialRenaming.shift 1 0 written = some raised at changed
  rw [PartialRenaming.shift_nonnegative (by decide)] at changed
  have renameOne : PartialRenaming.raiseIndex 0 ((1 : Int).toNat) = Nat.succ := by
    funext index
    change PartialRenaming.raiseIndex 0 1 index = index+1
    simp [PartialRenaming.raiseIndex]
  rw [renameOne] at changed
  cases changed
  let shiftedState := (shift limit depth state motive 1).state
  change (ownerVar shiftedState).result = .ok owner at ownerOk
  have ownerFacts : ∃ kept : Prefix shiftedState.arena (ownerVar shiftedState).state.arena,
      (Backward shiftedState.arena → Backward (ownerVar shiftedState).state.arena) ∧
        Represents (ownerVar shiftedState).state.arena owner (.var 0) := by
    cases added : addNode shiftedState.arena (.var 0) with
    | error reason => simp [ownerVar,added] at ownerOk
    | ok selected =>
      obtain ⟨arena,root⟩ := selected
      simp only [ownerVar,added,Except.ok.injEq] at ownerOk ⊢
      subst root
      obtain ⟨kept,_,_,_,_,held⟩ := addNode_commits added
      exact ⟨kept,fun valid => addNode_preserves_backward valid added (by simp [Node.references]),.var held⟩
  obtain ⟨ownerKept,ownerBack,ownerRep⟩ := ownerFacts
  obtain ⟨appKept,appBack,appRep⟩ := append_refines (.cons (liftedRep.frame ownerKept) (.cons ownerRep .nil)) rfl success
  refine ⟨shiftKept.trans (ownerKept.trans appKept),appBack ∘ ownerBack ∘ shiftBack,_,appRep,?_⟩
  simp only [takeResultType,EnvironmentDelta.expand_node_cons,expandArgs,expand,EnvironmentDelta.expand_renaming wf.admissible]

private theorem finish_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (original : Represents state.arena type written)
    (success : (finish normal limit depth state type continuation).result = .ok selected) :
    let after := (finish normal limit depth state type continuation).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ owner flag result tail normalType outside, Represents after selected outside ∧
        LoanTyping.Conversion.Conv env (expand env written) (.pi false owner (.pi flag result tail)) ∧
        LoanTyping.Conversion.Conv env tail normalType ∧
        PartialRenaming.shift (-2) 0 normalType = some (expand env outside) := by
  unfold finish at success ⊢
  obtain ⟨root,exposedOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨exposedKept,exposedBack,_,exposedRep,converted⟩ := normalSound onBase original exposedOk
  split at success
  · rename_i owner inner read
    split at success
    · rename_i flag result tail readInner
      obtain ⟨outside,normalized,thenShift⟩ := Outcome.next_success success
      rw [thenShift] at success ⊢
      obtain ⟨ownerDomain,inside,shape,ownerRep,innerRep⟩ := binary_read exposedRep read
      obtain ⟨resultDomain,resultBody,innerShape,resultRep,tailRep⟩ := binary_read innerRep readInner
      obtain ⟨normalKept,normalBack,normalType,normalRep,tailConv⟩ :=
        normalSound (onBase.trans exposedKept) tailRep normalized
      obtain ⟨lowerKept,lowerBack,residual,removed,outsideRep⟩ :=
        (NativeCoreTransformExact.run_refines (mode := .shift (-2)) (binders := 0) (value := normalType)
          normalRep trivial (shift_answer success)).1
      change PartialRenaming.shift (-2) 0 normalType = some residual at removed
      have outsideShape := load_result_reweakens removed
      have expandedShift : PartialRenaming.shift (-2) 0 (expand env normalType) = some (expand env residual) := by
        rw [← outsideShape,EnvironmentDelta.expand_renaming wf.admissible]
        exact load_result_shifted (expand env residual)
      refine ⟨exposedKept.trans (normalKept.trans lowerKept),lowerBack ∘ normalBack ∘ exposedBack,
        expand env ownerDomain,flag,expand env resultDomain,expand env resultBody,expand env normalType,
        residual,outsideRep,?_,tailConv.converted,expandedShift⟩
      simpa only [shape,innerShape,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs] using converted.converted
    · simp [reject] at success
  · simp [reject] at success

private theorem checkCallback_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena expected.owner T) (motiveRep : Represents state.arena expected.motive M)
    (source : Represents state.arena continuation callback)
    (success : (checkCallback normal limit depth state expected continuation).result = .ok pairs)
    (ambient : Prefix (checkCallback normal limit depth state expected continuation).state.arena final)
    (retained : ∀ entry ∈ pairs, PairRetained final entry) :
    let after := (checkCallback normal limit depth state expected continuation).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ declaredOwner declaredResult body, callback = .lam false declaredOwner (.lam expected.erased declaredResult body) ∧
        LoanTyping.Conversion.Conv env (expand env declaredOwner) (expand env T) ∧
        LoanTyping.Conversion.Conv env (expand env declaredResult) (takeResultType (expand env M)) := by
  unfold checkCallback at success ambient ⊢
  cases found : continuationDomains state.arena continuation expected.erased with
  | none => simp [found,reject] at success
  | some observed =>
    obtain ⟨owner,result⟩ := observed
    simp only [found] at success ambient ⊢
    obtain ⟨application,appOk,appNext⟩ := Outcome.next_success success
    rw [appNext] at success ambient ⊢
    obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
    rw [firstNext] at success ambient ⊢
    obtain ⟨second,secondOk,secondNext⟩ := Outcome.next_success success
    rw [secondNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst pairs
    let formed := expectedResult limit depth state expected.motive
    let compared := requireTypes normal limit depth formed.state owner expected.owner continuation
    have appProgress : Progress limit state formed :=
      shift_progress.next fun _ => ownerVar_progress.next fun _ => append_progress _ _ _
    have appRoom := appProgress.accepted room application appOk
    have firstProgress := requireTypes_progress (state := formed.state) (depth := depth) (actual := owner)
      (expected := expected.owner) (argument := continuation) (fun after root _ => normalProgress after root) appRoom
    have firstRoom := firstProgress.accepted appRoom first firstOk
    have secondProgress := requireTypes_progress (state := compared.state) (depth := depth) (actual := result)
      (expected := application) (argument := continuation) (fun after root _ => normalProgress after root) firstRoom
    obtain ⟨declaredOwner,declaredResult,body,shape,declaredOwnerRep,declaredResultRep⟩ := continuationDomains_refines source found
    obtain ⟨appKept,appBack,_,appRep,appShape⟩ := expectedResult_refines wf motiveRep appOk
    obtain ⟨firstKept,firstBack,ownerConversion⟩ := requireTypes_refines normalSound (onBase.trans appKept)
      (declaredOwnerRep.frame appKept) (ownerRep.frame appKept) firstOk (secondProgress.kept.trans ambient) (retained first (by simp))
    have throughFirst := appKept.trans firstKept
    obtain ⟨secondKept,secondBack,resultConversion⟩ := requireTypes_refines normalSound (onBase.trans throughFirst)
      (declaredResultRep.frame throughFirst) (appRep.frame firstKept) secondOk ambient (retained second (by simp))
    rw [appShape] at resultConversion
    exact ⟨throughFirst.trans secondKept,secondBack ∘ firstBack ∘ appBack,declaredOwner,declaredResult,body,
      shape,ownerConversion,resultConversion⟩

/-- The checked continuation receives the actual owner and dependent result.
The selected type lives in the original context after both binders are lowered. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (subjectRep : Represents state.arena subject x) (callbackRep : Represents state.arena continuation k)
    (success : (run infer normal limit depth state subject continuation).result = .ok answer)
    (ambient : Prefix (run infer normal limit depth state subject continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.take x k) (run infer normal limit depth state subject continuation) answer := by
  unfold run at success ambient ⊢
  obtain ⟨value,valueOk,valueNext⟩ := Outcome.next_success success
  rw [valueNext] at success ambient ⊢
  obtain ⟨package,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  obtain ⟨pairs,checkedOk,checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨callback,callbackOk,callbackNext⟩ := Outcome.next_success success
  rw [callbackNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let inferred := infer state subject
  let exposed := exposeGiven normal inferred.state value.typeRoot subject
  let checked := checkCallback normal limit depth exposed.state package continuation
  let inferredCallback := infer checked.state continuation
  have valueRoom := (inferProgress _ _ room).accepted room value valueOk
  have exposition : Progress limit inferred.state exposed := by
    change Progress limit inferred.state (exposeGiven normal inferred.state value.typeRoot subject)
    unfold exposeGiven
    exact (normalProgress _ _).next (fun _ => by split <;> exact Progress.atState _ _)
  have exposedRoom := exposition.accepted valueRoom package exposedOk
  have comparisonCost := checkCallback_progress (state := exposed.state) (depth := depth)
    (expected := package) (continuation := continuation) normalProgress exposedRoom
  have callbackRoom := comparisonCost.accepted exposedRoom pairs checkedOk
  have callbackCost := inferProgress checked.state continuation callbackRoom
  have resultCost := finish_progress (state := inferredCallback.state) (depth := depth)
    (type := callback.typeRoot) (continuation := continuation) normalProgress
  have afterCallback := resultCost.kept.trans ambient
  have afterCheck := callbackCost.kept.trans afterCallback
  obtain ⟨valueKept,valueBack,_,valueRep,valueTyped⟩ := inferSound onBase room subjectRep valueOk
    (exposition.kept.trans (comparisonCost.kept.trans afterCheck))
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨exposedKept,exposedBack,_,_,ownerRep,motiveRep,valueConv⟩ :=
    exposeGiven_refines normalSound (onBase.trans valueKept) valueRep exposedOk
  have throughExpose := valueKept.trans exposedKept
  obtain ⟨checkedKept,checkedBack,_,_,_,callbackShape,ownerConv,resultConv⟩ := checkCallback_refines wf
    normalSound normalProgress (onBase.trans throughExpose) exposedRoom ownerRep motiveRep
    (callbackRep.frame throughExpose) checkedOk afterCheck
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
  have throughCheck := throughExpose.trans checkedKept
  obtain ⟨callbackKept,callbackBack,_,callbackType,callbackTyped⟩ := inferSound (onBase.trans throughCheck) callbackRoom
    (callbackRep.frame throughCheck) callbackOk afterCallback
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
  have throughCallback := throughCheck.trans callbackKept
  obtain ⟨finished,finishBack,_,_,_,_,_,_,outsideRep,callbackConv,tailConv,lowered⟩ := finish_refines wf normalSound
    (onBase.trans throughCallback) callbackType resultOk
  rw [callbackShape] at callbackTyped ⊢
  simp only [Term.lam,expand,expandArgs] at callbackTyped
  refine ⟨throughCallback.trans finished,finishBack ∘ callbackBack ∘ checkedBack ∘ exposedBack ∘ valueBack,
    _,outsideRep,?_⟩
  simpa only [Term.take,Term.lam,expand,expandArgs] using
    LoanTyping.HasType.take (valueTyped.convert valueConv) (callbackTyped.convert callbackConv)
      ownerConv resultConv tailConv lowered (.inl rfl)

end Jihoo.NativeKernel.NativeCoreGhostTakeInference
