import Jihoo.NativeCoreBufferRelease
import Jihoo.NativeCoreCodeHeadInference

/-! Runtime scalar inference recurses in code mode on both arithmetic
operands, on both sides of Strict, and through buffer release. Leaf inference is the same code-mode
checker that refuses an erased local before shifting its domain. -/
namespace Jihoo.NativeKernel.NativeCoreCodeScalarInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreGhostSpineInference (GraphBinding ContextRep Infer Visit Inferred PairRetained RetainedComparisons
  requireTypes requireTypes_progress requireTypes_refines next_progress)
open NativeCoreCodeHeadInference (Refines Sound)
open NativeCoreBufferRelease (ModeSound inferFree inferFree_progress)
open EnvironmentDelta (expand expandArgs)

abbrev NormalAt := Nat → Visit

def enter (limit depth : Nat) (state : State) (root : Nat) (next : State → Outcome Inferred) : Outcome Inferred :=
  let (paid,steps) := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let entered := {state with steps}
  match paid with
  | .error reason => ⟨entered,.error (.tick reason)⟩
  | .ok () => next entered

private def checkOperand (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (expected operand : Nat) : Outcome (List (Nat × Nat)) :=
  (infer state operand).next fun inferred answer =>
    (requireTypes normal limit depth inferred answer.typeRoot expected operand).next fun checked pair =>
      ⟨checked,.ok (answer.compared ++ [pair])⟩

def arithmetic (infer : Infer) (normal : Visit) (limit depth : Nat) (state : State)
    (type : Op) (left right : Nat) : Outcome Inferred :=
  (append state type []).next fun expected typeRoot =>
    (checkOperand infer normal limit depth expected typeRoot left).next fun checked first =>
      (checkOperand infer normal limit depth checked typeRoot right).next fun inferred second =>
        (append inferred type []).next fun after output => ⟨after,.ok ⟨output,first ++ second⟩⟩

def strict (infer : Infer) (state : State) (effect value : Nat) : Outcome Inferred :=
  (infer state effect).next fun checked first =>
    (infer checked value).next fun after second => ⟨after,.ok ⟨second.typeRoot,first.compared ++ second.compared⟩⟩

def run (normal : NormalAt) (limit : Nat) (rows : List GraphBinding) : Nat → State → Nat → Outcome Inferred
  | 0, state, root => NativeCoreCodeHeadInference.run limit 0 rows state root
  | depth+1, state, root =>
    match state.arena[root]? with
    | some (.node (.arith _) [a,b]) => enter limit (depth+1) state root fun checked =>
        arithmetic (run normal limit rows depth) (normal depth) limit depth checked .i64 a b
    | some (.node .uadd [a,b]) => enter limit (depth+1) state root fun checked =>
        arithmetic (run normal limit rows depth) (normal depth) limit depth checked .u64 a b
    | some (.node .strict [a,b]) => enter limit (depth+1) state root fun checked =>
        strict (run normal limit rows depth) checked a b
    | some (.node .free [buffer,tail]) => enter limit (depth+1) state root fun checked =>
        inferFree (run normal limit rows depth) (normal depth) checked buffer tail
    | _ => NativeCoreCodeHeadInference.run limit (depth+1) rows state root

theorem enter_progress
    (continued : ∀ entered, entered.steps ≤ limit → Progress limit entered (next entered)) :
    Progress limit state (enter limit depth state root next) := by
  have rejected (reason : NativeCoreIdentical.Error) :
      Progress limit state (⟨{state with steps := state.steps+1},.error (.tick reason)⟩ : Outcome Inferred) :=
    ⟨.refl _,Nat.le_succ _,Nat.succ_le_succ,fun _ _ bad => by cases bad⟩
  by_cases clock : limit < state.steps+1
  · simpa only [enter,NativeCoreUnsignedCancellation.tick,ite_eq_left clock] using rejected (.stepLimit root)
  by_cases tooDeep : depth = 0
  · simpa only [enter,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_left tooDeep] using rejected (.depthLimit root)
  by_cases missing : state.arena.size ≤ root
  · simpa only [enter,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_right tooDeep,ite_eq_left missing] using
      rejected (.invalidReference root)
  have room : state.steps + 1 ≤ limit := by omega
  have progress := continued {state with steps := state.steps+1} room
  simp only [enter,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_right tooDeep,ite_eq_right missing]
  exact ⟨progress.kept,Nat.le_trans (Nat.le_succ _) progress.monotone,
    fun _ => progress.bounded room,fun _ => progress.accepted room⟩

theorem enter_success (success : (enter limit depth state root next).result = .ok answer) :
    enter limit depth state root next = next {state with steps := state.steps+1} ∧ state.steps+1 ≤ limit := by
  by_cases clock : limit < state.steps+1
  · simp [enter,NativeCoreUnsignedCancellation.tick,clock] at success
  by_cases tooDeep : depth = 0
  · simp [enter,NativeCoreUnsignedCancellation.tick,clock,tooDeep] at success
  by_cases missing : state.arena.size ≤ root
  · simp [enter,NativeCoreUnsignedCancellation.tick,clock,tooDeep,missing] at success
  exact ⟨by simp [enter,NativeCoreUnsignedCancellation.tick,clock,tooDeep,missing],by omega⟩

private theorem checkOperand_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (checkOperand infer normal limit depth state expected operand) := by
  unfold checkOperand
  apply next_progress (infers _ _ room) room
  intro _ _ inferredRoom
  exact (requireTypes_progress (fun after root _ => normalizes after root) inferredRoom).next
    (fun _ => Progress.atState _ _)

theorem arithmetic_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (arithmetic infer normal limit depth state type left right) := by
  unfold arithmetic
  apply next_progress (append_progress _ _ _) room
  intro _ _ expectedRoom
  apply next_progress (checkOperand_progress infers normalizes expectedRoom) expectedRoom
  intro _ _ leftRoom
  exact (checkOperand_progress infers normalizes leftRoom).next (fun _ =>
    (append_progress _ _ _).next (fun _ => Progress.atState _ _))

theorem strict_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root)) (room : state.steps ≤ limit) :
    Progress limit state (strict infer state effect value) := by
  unfold strict
  apply next_progress (infers _ _ room) room
  intro _ _ firstRoom
  exact (infers _ _ firstRoom).next (fun _ => Progress.atState _ _)

theorem run_progress
    (normalizes : ∀ depth state root, Progress limit state (normal depth state root)) (room : state.steps ≤ limit) :
    Progress limit state (run normal limit rows depth state root) := by
  induction depth generalizing state root with
  | zero => exact NativeCoreCodeHeadInference.run_progress
  | succ depth ih =>
    unfold run
    split
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalizes depth) inside)
    · exact enter_progress (fun _ inside => arithmetic_progress (fun _ _ => ih) (normalizes depth) inside)
    · exact enter_progress (fun _ inside => strict_progress (fun _ _ => ih) inside)
    · exact enter_progress (fun _ inside => inferFree_progress (fun _ _ => ih) (normalizes depth) inside)
    · exact NativeCoreCodeHeadInference.run_progress

private theorem checkOperand_refinesMode
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : ModeSound env loans base ctx limit false infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena operand term) (wanted : Represents state.arena expected type)
    (success : (checkOperand infer normal limit depth state expected operand).result = .ok pairs)
    (ambient : Prefix (checkOperand infer normal limit depth state expected operand).state.arena final)
    (retained : ∀ entry ∈ pairs, PairRetained final entry) :
    let after := (checkOperand infer normal limit depth state expected operand).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.HasType env loans ctx false (expand env term) (expand env type) := by
  unfold checkOperand at success ambient ⊢
  obtain ⟨answer,inferred,next⟩ := Outcome.next_success success
  rw [next] at success ambient ⊢
  obtain ⟨pair,checked,checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst pairs
  have bodyRoom := (childProgress state operand room).accepted room answer inferred
  have cost := requireTypes_progress (state := (infer state operand).state) (depth := depth)
    (actual := answer.typeRoot) (expected := expected) (argument := operand)
    (fun after root _ => normalProgress after root) bodyRoom
  obtain ⟨kept,backward,_,typeRep,typed⟩ := childSound onBase room source inferred (cost.kept.trans ambient)
    (fun entry member => retained entry (List.mem_append_left _ member))
  obtain ⟨checkedKept,checkedBack,converted⟩ := requireTypes_refines normalSound (onBase.trans kept)
    typeRep (wanted.frame kept) checked ambient (retained pair (by simp))
  exact ⟨kept.trans checkedKept,checkedBack ∘ backward,typed.convert converted⟩

theorem arithmetic_refinesMode
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : ModeSound env loans base ctx limit false infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (arity : type.arity = 0)
    (typing : LoanTyping.HasType env loans ctx false (expand env a) (expand env (.node type [])) →
      LoanTyping.HasType env loans ctx false (expand env b) (expand env (.node type [])) →
      LoanTyping.HasType env loans ctx false (expand env term) (expand env (.node type [])))
    (success : (arithmetic infer normal limit depth state type left right).result = .ok answer)
    (ambient : Prefix (arithmetic infer normal limit depth state type left right).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (arithmetic infer normal limit depth state type left right).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env loans ctx false (expand env term) (expand env type) := by
  unfold arithmetic at success ambient ⊢
  obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
  rw [expectedNext] at success ambient ⊢
  obtain ⟨leftPairs,leftOk,leftNext⟩ := Outcome.next_success success
  rw [leftNext] at success ambient ⊢
  obtain ⟨rightPairs,rightOk,rightNext⟩ := Outcome.next_success success
  rw [rightNext] at success ambient ⊢
  obtain ⟨output,outputOk,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let added := append state type []
  let leftChecked := checkOperand infer normal limit depth added.state expected left
  let rightChecked := checkOperand infer normal limit depth leftChecked.state expected right
  have addedRoom := (append_progress _ _ _).accepted room expected expectedOk
  have leftCost := checkOperand_progress (state := added.state) (depth := depth) (expected := expected) (operand := left)
    childProgress normalProgress addedRoom
  have leftRoom := leftCost.accepted addedRoom leftPairs leftOk
  have rightCost := checkOperand_progress (state := leftChecked.state) (depth := depth) (expected := expected) (operand := right)
    childProgress normalProgress leftRoom
  have afterRight := (append_progress (limit := limit) rightChecked.state type []).kept.trans ambient
  obtain ⟨addedKept,addedBack,expectedRep⟩ := append_refines .nil arity.symm expectedOk
  obtain ⟨leftKept,leftBack,typedLeft⟩ := checkOperand_refinesMode normalSound normalProgress childSound childProgress
    (onBase.trans addedKept) addedRoom (leftRep.frame addedKept) expectedRep leftOk (rightCost.kept.trans afterRight)
    (fun pair member => retained pair (List.mem_append_left _ member))
  have throughLeft := addedKept.trans leftKept
  obtain ⟨rightKept,rightBack,typedRight⟩ := checkOperand_refinesMode normalSound normalProgress childSound childProgress
    (onBase.trans throughLeft) leftRoom (rightRep.frame throughLeft) (expectedRep.frame leftKept) rightOk afterRight
    (fun pair member => retained pair (List.mem_append_right _ member))
  obtain ⟨outputKept,outputBack,resultRep⟩ := append_refines .nil arity.symm outputOk
  exact ⟨throughLeft.trans (rightKept.trans outputKept),outputBack ∘ rightBack ∘ leftBack ∘ addedBack,
    _,resultRep,typing typedLeft typedRight⟩

theorem strict_refinesMode (childSound : ModeSound env loans base ctx limit false infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (firstRep : Represents state.arena effect first) (tailRep : Represents state.arena value tail)
    (success : (strict infer state effect value).result = .ok answer)
    (ambient : Prefix (strict infer state effect value).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (strict infer state effect value).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env loans ctx false (expand env (.strict first tail)) (expand env type) := by
  unfold strict at success ambient ⊢
  obtain ⟨a,firstOk,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ambient ⊢
  obtain ⟨b,tailOk,tailNext⟩ := Outcome.next_success success
  rw [tailNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  have firstRoom := (childProgress state effect room).accepted room a firstOk
  have later := childProgress (infer state effect).state value firstRoom
  obtain ⟨firstKept,firstBack,_,_,typedFirst⟩ := childSound onBase room firstRep firstOk (later.kept.trans ambient)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨tailKept,tailBack,_,typedRep,typedTail⟩ := childSound (onBase.trans firstKept) firstRoom (tailRep.frame firstKept)
    tailOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
  refine ⟨firstKept.trans tailKept,tailBack ∘ firstBack,_,typedRep,?_⟩
  simpa only [Term.strict,expand,expandArgs] using LoanTyping.HasType.strict typedFirst typedTail

private theorem asModeSound (sound : Sound env base ctx limit infer) :
    ModeSound env [] base ctx limit false infer := by
  intro _ _ _ _ _ onBase room represented accepted final retained
  obtain ⟨kept,backward,typed⟩ := sound onBase room represented accepted final retained
  exact ⟨kept,backward,typed⟩

theorem arithmetic_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : Sound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (leftRep : Represents state.arena left a) (rightRep : Represents state.arena right b)
    (arity : type.arity = 0)
    (typing : LoanTyping.HasType env [] ctx false (expand env a) (expand env (.node type [])) →
      LoanTyping.HasType env [] ctx false (expand env b) (expand env (.node type [])) →
      LoanTyping.HasType env [] ctx false (expand env term) (expand env (.node type [])))
    (success : (arithmetic infer normal limit depth state type left right).result = .ok answer)
    (ambient : Prefix (arithmetic infer normal limit depth state type left right).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx term (arithmetic infer normal limit depth state type left right) answer := by
  obtain ⟨kept,backward,typed⟩ := arithmetic_refinesMode normalSound normalProgress (asModeSound childSound)
    childProgress onBase room leftRep rightRep arity typing success ambient retained
  exact ⟨kept,backward,typed⟩

theorem strict_refines (childSound : Sound env base ctx limit infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (firstRep : Represents state.arena effect first) (tailRep : Represents state.arena value tail)
    (success : (strict infer state effect value).result = .ok answer)
    (ambient : Prefix (strict infer state effect value).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.strict first tail) (strict infer state effect value) answer := by
  obtain ⟨kept,backward,typed⟩ := strict_refinesMode (asModeSound childSound) childProgress
    onBase room firstRep tailRep success ambient retained
  exact ⟨kept,backward,typed⟩

theorem run_sound (wf : UnifiedProgram.EnvWellFormed env) (context : ContextRep env base rows ctx)
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth)) :
    Sound env base ctx limit (run normal limit rows depth) := by
  induction depth with
  | zero => exact NativeCoreCodeHeadInference.run_sound wf context
  | succ depth childSound =>
    intro state root term answer final onBase room source success ambient retained
    unfold run at success ambient ⊢
    have modeSound : NativeCoreBufferRelease.ModeSound env [] base ctx limit false (run normal limit rows depth) := by
      intro _ _ _ _ _ onBase inside source accepted ambient retained
      obtain ⟨kept,backward,typed⟩ := childSound onBase inside source accepted ambient retained
      exact ⟨kept,backward,typed⟩
    have childCost : ∀ state root, state.steps ≤ limit → Progress limit state (run normal limit rows depth state root) :=
      fun _ _ inside => run_progress normalProgress inside
    cases source with
    | var read =>
      simp only [read] at success ambient ⊢
      exact NativeCoreCodeHeadInference.run_sound wf context onBase room (.var read) success ambient retained
    | @node _ op refs terms read arity children =>
      simp only [read] at success ambient ⊢
      cases op
      case arith | uadd | strict | free =>
        have length : refs.length = 2 := arity
        rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons first rest =>
          cases rest with
          | cons second tail =>
            cases tail
            dsimp only at success ambient ⊢
            obtain ⟨entered,inside⟩ := enter_success success
            rw [entered] at success ambient ⊢
            first
            | exact strict_refines (state := {state with steps := state.steps+1})
                childSound childCost onBase inside first second success ambient retained
            | obtain ⟨kept,backward,typed⟩ := NativeCoreBufferRelease.inferFree_refines
                (state := {state with steps := state.steps+1}) (normalSound depth) (normalProgress depth)
                modeSound childCost onBase inside first second success ambient retained
              exact ⟨kept,backward,typed⟩
            | apply arithmetic_refines (state := {state with steps := state.steps+1}) (depth := depth)
                (normalSound depth) (normalProgress depth) childSound childCost
                onBase inside first second rfl _ success ambient retained
              intro left right
              simp only [expand,expandArgs] at left right ⊢
              first | exact .arith left right | exact .uadd left right
      all_goals
        exact NativeCoreCodeHeadInference.run_sound wf context onBase room (.node read arity children)
          success ambient retained

private def scalarArena : Arena := #[.node (.integer (-2)) [],.node (.integer 3) [],.node (.arith .add) [0,1],
  .node (.natural 2) [],.node (.natural 3) [],.node .uadd [3,4],.node .strict [2,5]]

/-- Runtime arithmetic retains both operands and their order, while Strict
returns the original unsigned tail type. Erased access rejects an arithmetic
operand before it shifts or visits the next operand. -/
theorem code_scalar_checks_both_children :
    (let normal := NativeCoreGhostLiteralAddition.run [] 0 19
     let checked := run normal 19 [] 16 ⟨scalarArena,0⟩ 6
     checked.state.steps = 19 ∧ checked.result.map Inferred.typeRoot = .ok 14 ∧
       checked.state.arena = scalarArena ++ #[.node .i64 [],.node .i64 [],.node .i64 [],.node .i64 [],
         .node .u64 [],.node .u64 [],.node .u64 [],.node .u64 []]) ∧
    (let arena := scalarArena ++ #[.var 0,.node (.arith .add) [7,0],.node .i64 []]
     let normal := NativeCoreGhostLiteralAddition.run [] 0 2
     run normal 2 [⟨9,true⟩] 16 ⟨arena,0⟩ 8 =
       ⟨⟨arena.push (.node .i64 []),2⟩,.error (.outsideFragment 7)⟩) := by cbv

end Jihoo.NativeKernel.NativeCoreCodeScalarInference
