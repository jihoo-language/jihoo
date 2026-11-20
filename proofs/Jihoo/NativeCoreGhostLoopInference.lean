import Jihoo.NativeCoreGhostLoopMotive
import Jihoo.NativeCoreGhostFoldInference

/-! Dependent Loop keeps the motive's actual proof flag in the callback
while checking its count, initial fiber and successor fiber in native order. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLoopInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines PairRetained RetainedComparisons next_progress)
open NativeCoreGhostFoldInference (checkAgainst checkAgainst_progress checkAgainst_refines checkBodyPolicy)
open NativeCoreCaseStrict (append append_refines append_progress)
open EnvironmentDelta (expand expandArgs)

private def initialType (state : State) (motive : Nat) : Outcome Nat :=
  (append state (.natural 0) []).next fun after initialIndex => append after .app [motive,initialIndex]

def run (isBoxed : Nat → Bool) (memoryFree : Arena → Nat → Nat → Bool)
    (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State) (count motive initial body : Nat) : Outcome Inferred :=
  (append state .u64 []).next fun withWord word =>
    (NativeCoreGhostLoopMotive.run infer normal isBoxed limit depth withWord word motive).next fun checkedMotive choice =>
      (checkAgainst infer normal limit depth checkedMotive word count).next fun checkedCount countPairs =>
        (initialType checkedCount motive).next fun formed initialRoot =>
          (checkAgainst infer normal limit depth formed initialRoot initial).next fun checkedInitial initialPairs =>
            (NativeCoreIterationTelescope.loop limit depth checkedInitial choice.proof count motive).next
              fun withTelescope callbackType =>
                (checkAgainst infer normal limit depth withTelescope callbackType body).next fun checkedBody bodyPairs =>
                  if checkBodyPolicy memoryFree checkedBody.arena depth body then
                    (append checkedBody .app [motive,count]).next fun after output =>
                      ⟨after,.ok ⟨output,choice.compared ++ (countPairs ++ (initialPairs ++ bodyPairs))⟩⟩
                  else ⟨checkedBody,.error (.outsideFragment body)⟩

private theorem initialType_progress : Progress limit state (initialType state motive) :=
  (append_progress _ _ _).next (fun _ => append_progress _ _ _)

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run isBoxed memoryFree infer normal limit depth state count motive initial body) := by
  unfold run
  apply next_progress (append_progress _ _ _) room
  intro _ _ wordRoom
  apply next_progress (NativeCoreGhostLoopMotive.run_progress infers normalizes wordRoom) wordRoom
  intro _ _ motiveRoom
  apply next_progress (checkAgainst_progress infers normalizes motiveRoom) motiveRoom
  intro _ _ countRoom
  apply next_progress initialType_progress countRoom
  intro _ _ initialRoom
  apply next_progress (checkAgainst_progress infers normalizes initialRoom) initialRoom
  intro _ _ checkedRoom
  apply next_progress NativeCoreIterationTelescope.loop_progress checkedRoom
  intro _ _ bodyRoom
  exact (checkAgainst_progress infers normalizes bodyRoom).next (fun _ => by
    split
    · exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)
    · exact Progress.atState _ _)

private theorem initialType_refines (motiveRep : Represents state.arena motive M)
    (success : (initialType state motive).result = .ok selected) :
    let after := (initialType state motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected (.app M (.natural 0)) := by
  unfold initialType at success ⊢
  obtain ⟨withZero,zeroOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨zeroKept,zeroBack,zeroRep⟩ := append_refines .nil rfl zeroOk
  obtain ⟨appKept,appBack,appRep⟩ := append_refines (.cons (motiveRep.frame zeroKept) (.cons zeroRep .nil)) rfl success
  exact ⟨zeroKept.trans appKept,appBack ∘ zeroBack,appRep⟩

private theorem expand_loop_type (wf : UnifiedProgram.EnvWellFormed env) (count motive : Term) (proof : Bool) :
    expand env (loopBodyType count motive proof) = loopBodyType (expand env count) (expand env motive) proof := by
  simp only [loopBodyType,Term.pi,Term.lt,Term.u64,Term.uadd,Term.app,Term.natural,EnvironmentDelta.expand_node_cons,expandArgs,
    expand,EnvironmentDelta.expand_renaming wf.admissible]

/-- The executable branch checks each original operand at its dependent
code, and the final output represents the original motive at the count. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (countRep : Represents state.arena count n) (motiveRep : Represents state.arena motive M)
    (initialRep : Represents state.arena initial init) (bodyRep : Represents state.arena body next)
    (success : (run isBoxed memoryFree infer normal limit depth state count motive initial body).result = .ok answer)
    (ambient : Prefix (run isBoxed memoryFree infer normal limit depth state count motive initial body).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.loop n M init next)
      (run isBoxed memoryFree infer normal limit depth state count motive initial body) answer := by
  unfold run at success ambient ⊢
  obtain ⟨word,wordOk,wordNext⟩ := Outcome.next_success success
  rw [wordNext] at success ambient ⊢
  obtain ⟨choice,motiveOk,motiveNext⟩ := Outcome.next_success success
  rw [motiveNext] at success ambient ⊢
  obtain ⟨countPairs,countOk,countNext⟩ := Outcome.next_success success
  rw [countNext] at success ambient ⊢
  obtain ⟨initType,initTypeOk,initTypeNext⟩ := Outcome.next_success success
  rw [initTypeNext] at success ambient ⊢
  obtain ⟨initPairs,initOk,initNext⟩ := Outcome.next_success success
  rw [initNext] at success ambient ⊢
  obtain ⟨callbackType,callbackOk,callbackNext⟩ := Outcome.next_success success
  rw [callbackNext] at success ambient ⊢
  obtain ⟨bodyPairs,bodyOk,bodyNext⟩ := Outcome.next_success success
  rw [bodyNext] at success ambient ⊢
  split at success
  · rename_i allowed
    simp only [ite_eq_left allowed] at ambient ⊢
    obtain ⟨output,outputOk,outputNext⟩ := Outcome.next_success success
    rw [outputNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let wordGraph := append state .u64 []
    let motiveChecked := NativeCoreGhostLoopMotive.run infer normal isBoxed limit depth wordGraph.state word motive
    let countChecked := checkAgainst infer normal limit depth motiveChecked.state word count
    let expected := initialType countChecked.state motive
    let initialChecked := checkAgainst infer normal limit depth expected.state initType initial
    let telescope := NativeCoreIterationTelescope.loop limit depth initialChecked.state choice.proof count motive
    let bodyChecked := checkAgainst infer normal limit depth telescope.state callbackType body
    have wordRoom := (append_progress _ _ _).accepted room word wordOk
    have motiveCost := NativeCoreGhostLoopMotive.run_progress (state := wordGraph.state) (isBoxed := isBoxed)
      (depth := depth) (word := word) (motive := motive) inferProgress normalProgress wordRoom
    have motiveRoom := motiveCost.accepted wordRoom choice motiveOk
    have countCost := checkAgainst_progress (state := motiveChecked.state) (depth := depth) (expected := word) (argument := count)
      inferProgress normalProgress motiveRoom
    have countRoom := countCost.accepted motiveRoom countPairs countOk
    have expectedCost := initialType_progress (limit := limit) (state := countChecked.state) (motive := motive)
    have expectedRoom := expectedCost.accepted countRoom initType initTypeOk
    have initCost := checkAgainst_progress (state := expected.state) (depth := depth) (expected := initType) (argument := initial)
      inferProgress normalProgress expectedRoom
    have initialRoom := initCost.accepted expectedRoom initPairs initOk
    have telescopeCost := NativeCoreIterationTelescope.loop_progress (limit := limit) (state := initialChecked.state)
      (depth := depth) (proof := choice.proof) (count := count) (motive := motive)
    have bodyRoom := telescopeCost.accepted initialRoom callbackType callbackOk
    have bodyCost := checkAgainst_progress (state := telescope.state) (depth := depth) (expected := callbackType)
      (argument := body) inferProgress normalProgress bodyRoom
    have afterBody := (append_progress (limit := limit) bodyChecked.state .app [motive,count]).kept.trans ambient
    have afterTelescope := bodyCost.kept.trans afterBody
    have afterInit := telescopeCost.kept.trans afterTelescope
    have afterExpected := initCost.kept.trans afterInit
    have afterCount := expectedCost.kept.trans afterExpected
    have afterMotive := countCost.kept.trans afterCount
    obtain ⟨wordKept,wordBack,wordRep⟩ := append_refines .nil rfl wordOk
    obtain ⟨motiveKept,motiveBack,typedMotive⟩ := NativeCoreGhostLoopMotive.run_refines normalSound normalProgress
      inferSound inferProgress (onBase.trans wordKept) wordRoom wordRep (motiveRep.frame wordKept) motiveOk afterMotive
      (fun pair member => retained pair (List.mem_append_left _ member))
    have throughMotive := wordKept.trans motiveKept
    obtain ⟨countKept,countBack,typedCount⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
      (onBase.trans throughMotive) motiveRoom (countRep.frame throughMotive) (wordRep.frame motiveKept) countOk afterCount
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
    have throughCount := throughMotive.trans countKept
    obtain ⟨expectedKept,expectedBack,expectedRep⟩ := initialType_refines (motiveRep.frame throughCount) initTypeOk
    have throughExpected := throughCount.trans expectedKept
    obtain ⟨initKept,initBack,typedInit⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
      (onBase.trans throughExpected) expectedRoom (initialRep.frame throughExpected) expectedRep initOk afterInit
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))))
    have throughInit := throughExpected.trans initKept
    obtain ⟨telescopeKept,telescopeBack,telescopeRep⟩ := NativeCoreIterationTelescope.loop_refines
      (countRep.frame throughInit) (motiveRep.frame throughInit) callbackOk
    have throughTelescope := throughInit.trans telescopeKept
    obtain ⟨bodyKept,bodyBack,typedBody⟩ := checkAgainst_refines normalSound normalProgress inferSound inferProgress
      (onBase.trans throughTelescope) bodyRoom (bodyRep.frame throughTelescope) telescopeRep bodyOk afterBody
      (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member))))
    have throughBody := throughTelescope.trans bodyKept
    obtain ⟨outputKept,outputBack,outputRep⟩ := append_refines
      (.cons (motiveRep.frame throughBody) (.cons (countRep.frame throughBody) .nil)) rfl outputOk
    have typedWord : LoanTyping.HasType env [] ctx true (expand env n) .u64 := by
      simpa only [Term.u64,expand,expandArgs] using typedCount
    have typedFirst : LoanTyping.HasType env [] ctx true (expand env init) (.app (expand env M) (.natural 0)) := by
      simpa only [Term.app,Term.natural,expand,expandArgs] using typedInit
    rw [expand_loop_type wf] at typedBody
    refine ⟨throughBody.trans outputKept, outputBack ∘ bodyBack ∘ telescopeBack ∘ initBack ∘ expectedBack ∘
      countBack ∘ motiveBack ∘ wordBack,_,outputRep,?_⟩
    simpa only [Term.loop,Term.app,expand,expandArgs] using
      LoanTyping.HasType.loop typedMotive (.inl rfl) typedWord typedFirst typedBody (.inl rfl)
  · cases success

end Jihoo.NativeKernel.NativeCoreGhostLoopInference
