import Jihoo.NativeCoreIterationTelescope
import Jihoo.NativeCoreGhostReferenceTypes
import Jihoo.NativeCoreEffectAnalysis

/-! Fold checks its count, the original accumulator and a dependent
three-binder body in order. An initial I64 inspection still incurs the
second native normalization used by the owned-data query. -/
namespace Jihoo.NativeKernel.NativeCoreGhostFoldInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostReferenceTypes (BoxedFamilies isBoxedAt)
open NativeCoreGhostSpineInference (Infer Inferred Visit InferSound Refines PairRetained RetainedComparisons
  next_progress requireTypes requireTypes_progress requireTypes_refines)
open NativeCoreCaseStrict (append append_refines append_progress)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def beginsWithLambdas (arena : Arena) : Nat → Nat → Bool
  | 0, _ => true
  | count+1, root =>
    match arena[root]? with
    | some (.node (.lam _) [_,rest]) => beginsWithLambdas arena count rest
    | _ => false

private def checkBodyPolicy (memoryFree : Arena → Nat → Nat → Bool) (arena : Arena) (depth body : Nat) : Bool :=
  beginsWithLambdas arena 3 body || memoryFree arena depth body

private theorem beginsWithLambdas_refines (represented : Represents arena root term) (count : Nat) :
    beginsWithLambdas arena count root = hasLeadingLambdas count term := by
  induction count generalizing root term with
  | zero => rfl
  | succ count ih =>
    cases represented with
    | var read => simp only [beginsWithLambdas,read,hasLeadingLambdas]
    | @node _ op refs terms read arity children =>
      cases op <;> try simp only [beginsWithLambdas,read,hasLeadingLambdas]
      case lam erased =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons first rest =>
          cases rest with
          | cons body tail =>
            cases tail
            exact ih body

/-- The native iteration gate recognizes a full raw callback telescope.
Otherwise its bounded graph scan establishes the original raw body is free
of operations classified as repeated memory effects. -/
theorem body_policy_refines (represented : Represents arena root term)
    (accepted : checkBodyPolicy (CoreEffectAnalysis.graphMemoryFree env) arena depth root = true) :
    hasLeadingLambdas 3 term = true ∨ iterationMemoryFree env term = true := by
  rw [checkBodyPolicy,beginsWithLambdas_refines represented,CoreEffectAnalysis.graphMemoryFree_refines represented] at accepted
  simp only [Bool.or_eq_true] at accepted
  exact accepted.imp id CoreEffectAnalysis.termMemoryFree_sound

private def ownedHead (isBoxed : Nat → Bool) (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node .buffer [_]) => true
  | some (.node (.ind family _) _) => isBoxed family
  | _ => false

private def acceptAccumulator (isBoxed : Nat → Bool) (normal : Visit) (state : State) (type subject : Nat) : Outcome Nat :=
  (normal state type).next fun normalized chosen =>
    (normal normalized chosen).next fun after inspected =>
      if normalized.arena[chosen]? = some (.node .i64 []) ∨ ownedHead isBoxed after.arena inspected = true then
        ⟨after,.ok chosen⟩
      else reject after subject

private def checkAgainst (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (expected argument : Nat) : Outcome (List (Nat × Nat)) :=
  (infer state argument).next fun inferred answer =>
    (requireTypes normal limit depth inferred answer.typeRoot expected argument).next fun checked pair =>
      ⟨checked,.ok (answer.compared ++ [pair])⟩

/-- The output uses the first normalized accumulator root, even when the
separate native owned test visits it again and selects a different row. -/
def runWith (isBoxed : Nat → Bool) (memoryFree : Arena → Nat → Nat → Bool) (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (count initial body : Nat) : Outcome Inferred :=
  (append state .u64 []).next fun withWord word =>
    (checkAgainst infer normal limit depth withWord word count).next fun checkedCount countPairs =>
      (infer checkedCount initial).next fun inferred accumulator =>
        (acceptAccumulator isBoxed normal inferred accumulator.typeRoot initial).next fun exposed chosen =>
          (NativeCoreIterationTelescope.fold limit depth exposed count chosen).next fun withType callbackType =>
            (checkAgainst infer normal limit depth withType callbackType body).next fun after bodyPairs =>
              if checkBodyPolicy memoryFree after.arena depth body then
                ⟨after,.ok ⟨chosen,countPairs ++ (accumulator.compared ++ bodyPairs)⟩⟩
              else reject after body

private theorem acceptAccumulator_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (acceptAccumulator isBoxed normal state type subject) := by
  unfold acceptAccumulator
  exact (normalizes _ _).next (fun _ => (normalizes _ _).next (fun _ => by split <;> exact Progress.atState _ _))

private theorem checkAgainst_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (checkAgainst infer normal limit depth state expected argument) := by
  unfold checkAgainst
  apply next_progress (infers _ _ room) room
  intro _ _ inferredRoom
  exact (requireTypes_progress (fun after root _ => normalizes after root) inferredRoom).next
    (fun _ => Progress.atState _ _)

theorem runWith_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (runWith isBoxed memoryFree infer normal limit depth state count initial body) := by
  unfold runWith
  apply next_progress (append_progress _ _ _) room
  intro _ _ wordRoom
  apply next_progress (checkAgainst_progress infers normalizes wordRoom) wordRoom
  intro _ _ countRoom
  apply next_progress (infers _ _ countRoom) countRoom
  intro _ _ inferRoom
  apply next_progress (acceptAccumulator_progress normalizes) inferRoom
  intro _ _ accRoom
  apply next_progress NativeCoreIterationTelescope.fold_progress accRoom
  intro _ _ bodyRoom
  exact (checkAgainst_progress infers normalizes bodyRoom).next (fun _ => by split <;> exact Progress.atState _ _)

private theorem ownedHead_refines (metadata : BoxedFamilies env isBoxed) (held : Represents arena root term)
    (checked : ownedHead isBoxed arena root = true)
    (converted : LoanTyping.Conversion.Conv env original (expand env term)) : LoanTyping.Owned env original := by
  unfold ownedHead at checked
  split at checked
  · rename_i length read
    cases held with
    | var found => rw [read] at found; cases found
    | node found _ args =>
      rw [read] at found
      cases found
      cases args with
      | cons head tail =>
        cases tail
        exact .buffer (by simpa only [Term.buffer,expand,expandArgs] using converted)
  · rename_i family count refs read
    obtain ⟨entry,found,boxed⟩ := metadata family checked
    cases held with
    | var seen => rw [read] at seen; cases seen
    | node seen _ args =>
      rw [read] at seen
      cases seen
      exact .family found boxed (by simpa only [expand] using converted)
  · cases checked

private theorem acceptAccumulator_refines (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (written : Represents state.arena type declared)
    (success : (acceptAccumulator isBoxed normal state type subject).result = .ok chosen) :
    let after := (acceptAccumulator isBoxed normal state type subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ accumulator, Represents after chosen accumulator ∧
        LoanTyping.Conversion.Conv env (expand env declared) (expand env accumulator) ∧
        (expand env accumulator = .i64 ∨ LoanTyping.Owned env (expand env accumulator)) := by
  unfold acceptAccumulator at success ⊢
  obtain ⟨root,normalized,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ⊢
  obtain ⟨inspected,exposed,secondNext⟩ := Outcome.next_success success
  rw [secondNext] at success ⊢
  obtain ⟨firstKept,firstBack,accumulator,accRep,converted⟩ := normalSound onBase written normalized
  obtain ⟨secondKept,secondBack,_,inspectedRep,related⟩ := normalSound (onBase.trans firstKept) accRep exposed
  split at success
  · rename_i accepted
    simp only [ite_eq_left accepted]
    cases success
    refine ⟨firstKept.trans secondKept,secondBack ∘ firstBack,accumulator,accRep.frame secondKept,converted.converted,?_⟩
    rcases accepted with signed | owned
    · have shape := accRep.unique (Represents.node signed rfl .nil)
      exact .inl (by simp only [shape,Term.i64,expand,expandArgs])
    · exact .inr (ownedHead_refines metadata inspectedRep owned related.converted)
  · simp [reject] at success

private theorem checkAgainst_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (argumentRep : Represents state.arena argument term) (expectedRep : Represents state.arena expected type)
    (success : (checkAgainst infer normal limit depth state expected argument).result = .ok pairs)
    (ambient : Prefix (checkAgainst infer normal limit depth state expected argument).state.arena final)
    (retained : ∀ pair ∈ pairs, PairRetained final pair) :
    let after := (checkAgainst infer normal limit depth state expected argument).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env [] ctx true (expand env term) (expand env type) := by
  unfold checkAgainst at success ambient ⊢
  obtain ⟨answer,inferred,inferNext⟩ := Outcome.next_success success
  rw [inferNext] at success ambient ⊢
  obtain ⟨pair,checked,checkNext⟩ := Outcome.next_success success
  rw [checkNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst pairs
  have inferredRoom := (inferProgress state argument room).accepted room answer inferred
  have checking := requireTypes_progress (state := (infer state argument).state) (depth := depth)
    (actual := answer.typeRoot) (expected := expected) (argument := argument)
    (fun after root _ => normalProgress after root) inferredRoom
  obtain ⟨inferKept,inferBack,_,typeRep,typed⟩ := inferSound onBase room argumentRep inferred
    (checking.kept.trans ambient) (fun entry member => retained entry (List.mem_append_left _ member))
  obtain ⟨kept,backward,converted⟩ := requireTypes_refines normalSound (onBase.trans inferKept)
    typeRep (expectedRep.frame inferKept) checked ambient (retained pair (by simp))
  exact ⟨inferKept.trans kept,backward ∘ inferBack,typed.convert converted⟩

private theorem expand_fold_type (wf : UnifiedProgram.EnvWellFormed env) (count accumulator : Term) :
    expand env (foldAccumulatorBodyType count accumulator) = foldAccumulatorBodyType (expand env count) (expand env accumulator) := by
  simp only [foldAccumulatorBodyType,Term.pi,Term.lt,Term.u64,EnvironmentDelta.expand_node_cons,expandArgs,expand,
    EnvironmentDelta.expand_renaming wf.admissible]

/-- Exact metered Fold inference gives either the signed or the owned
source rule. The original count and accumulator types determine the body
telescope used by the comparison, and the result is the same accumulator. -/
theorem runWith_refines (wf : UnifiedProgram.EnvWellFormed env) (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (countRep : Represents state.arena count n) (initRep : Represents state.arena initial init)
    (bodyRep : Represents state.arena body loopBody)
    (success : (runWith isBoxed memoryFree infer normal limit depth state count initial body).result = .ok answer)
    (ambient : Prefix (runWith isBoxed memoryFree infer normal limit depth state count initial body).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.fold n init loopBody) (runWith isBoxed memoryFree infer normal limit depth state count initial body) answer := by
  unfold runWith at success ambient ⊢
  obtain ⟨word,wordOk,wordNext⟩ := Outcome.next_success success
  rw [wordNext] at success ambient ⊢
  obtain ⟨countPairs,countOk,countNext⟩ := Outcome.next_success success
  rw [countNext] at success ambient ⊢
  obtain ⟨accumulator,accOk,accNext⟩ := Outcome.next_success success
  rw [accNext] at success ambient ⊢
  obtain ⟨chosen,chosenOk,chosenNext⟩ := Outcome.next_success success
  rw [chosenNext] at success ambient ⊢
  obtain ⟨callbackType,callbackOk,callbackNext⟩ := Outcome.next_success success
  rw [callbackNext] at success ambient ⊢
  obtain ⟨bodyPairs,bodyOk,bodyNext⟩ := Outcome.next_success success
  rw [bodyNext] at success ambient ⊢
  split at success
  · rename_i allowed
    simp only [ite_eq_left allowed] at ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let wordGraph := append state .u64 []
    let countChecked := checkAgainst infer normal limit depth wordGraph.state word count
    let inferred := infer countChecked.state initial
    let exposed := acceptAccumulator isBoxed normal inferred.state accumulator.typeRoot initial
    let callbackGraph := NativeCoreIterationTelescope.fold limit depth exposed.state count chosen
    have wordRoom := (append_progress _ _ _).accepted room word wordOk
    have countCost := checkAgainst_progress (state := wordGraph.state) (depth := depth) (expected := word) (argument := count)
      inferProgress normalProgress wordRoom
    have countRoom := countCost.accepted wordRoom countPairs countOk
    have inferCost := inferProgress countChecked.state initial countRoom
    have inferRoom := inferCost.accepted countRoom accumulator accOk
    have exposeCost := acceptAccumulator_progress (state := inferred.state) (isBoxed := isBoxed)
      (type := accumulator.typeRoot) (subject := initial) normalProgress
    have exposeRoom := exposeCost.accepted inferRoom chosen chosenOk
    have callbackCost := NativeCoreIterationTelescope.fold_progress (limit := limit) (depth := depth) (state := exposed.state)
      (count := count) (accumulator := chosen)
    have callbackRoom := callbackCost.accepted exposeRoom callbackType callbackOk
    have bodyCost := checkAgainst_progress (state := callbackGraph.state) (depth := depth) (expected := callbackType)
      (argument := body) inferProgress normalProgress callbackRoom
    have afterCallback := bodyCost.kept.trans ambient
    have afterExpose := callbackCost.kept.trans afterCallback
    have afterInfer := exposeCost.kept.trans afterExpose
    obtain ⟨wordKept,wordBack,wordRep⟩ := append_refines .nil rfl wordOk
    obtain ⟨countKept,countBack,checkedCount⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
      (onBase.trans wordKept) wordRoom (countRep.frame wordKept) wordRep countOk (inferCost.kept.trans afterInfer)
      (fun pair member => retained pair (List.mem_append_left _ member))
    have throughCount := wordKept.trans countKept
    obtain ⟨inferredKept,inferredBack,_,initialType,checkedInit⟩ := inferSound (onBase.trans throughCount) countRoom
      (initRep.frame throughCount) accOk afterInfer (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
    have throughInit := throughCount.trans inferredKept
    obtain ⟨exposedKept,exposedBack,_,accRep,accConv,classification⟩ :=
      acceptAccumulator_refines metadata normalSound (onBase.trans throughInit) initialType chosenOk
    have throughExpose := throughInit.trans exposedKept
    obtain ⟨callbackKept,callbackBack,callbackRep⟩ := NativeCoreIterationTelescope.fold_refines
      (countRep.frame throughExpose) accRep callbackOk
    have throughCallback := throughExpose.trans callbackKept
    obtain ⟨bodyKept,bodyBack,checkedBody⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
      (onBase.trans throughCallback) callbackRoom (bodyRep.frame throughCallback) callbackRep bodyOk ambient
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
    rw [expand_fold_type wf] at checkedBody
    have wordType : expand env (.node .u64 []) = .u64 := by simp only [expand,expandArgs,Term.u64]
    rw [wordType] at checkedCount
    have initTyped := checkedInit.convert accConv
    refine ⟨throughCallback.trans bodyKept, bodyBack ∘ callbackBack ∘ exposedBack ∘ inferredBack ∘ countBack ∘ wordBack,
      _,accRep.frame (callbackKept.trans bodyKept),?_⟩
    rcases classification with signed | owned
    · rw [signed] at initTyped checkedBody ⊢
      rw [foldAccumulatorBodyType_i64] at checkedBody
      simpa only [Term.fold,expand,expandArgs] using LoanTyping.HasType.foldI64 checkedCount initTyped checkedBody (.inl rfl)
    · simpa only [Term.fold,expand,expandArgs] using LoanTyping.HasType.foldOwned checkedCount initTyped owned checkedBody (.inl rfl)
  · simp [reject] at success

def run (env : Environment) (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (count initial body : Nat) : Outcome Inferred :=
  runWith (isBoxedAt env) (CoreEffectAnalysis.graphMemoryFree env) infer normal limit depth state count initial body

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run env infer normal limit depth state count initial body) :=
  runWith_progress infers normalizes room

theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (countRep : Represents state.arena count n) (initRep : Represents state.arena initial init)
    (bodyRep : Represents state.arena body loopBody)
    (success : (run env infer normal limit depth state count initial body).result = .ok answer)
    (ambient : Prefix (run env infer normal limit depth state count initial body).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.fold n init loopBody) (run env infer normal limit depth state count initial body) answer :=
  runWith_refines wf (NativeCoreGhostReferenceTypes.isBoxedAt_sound env) normalSound normalProgress inferSound
    inferProgress onBase room countRep initRep bodyRep success ambient retained

end Jihoo.NativeKernel.NativeCoreGhostFoldInference
