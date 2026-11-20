import Jihoo.NativeCoreGhostTypeRequirement

/-! The runtime plain-type gate normalizes the original argument once.
Its traversal ticks every visited row, skips lambda annotations, and
stops at the first disallowed representation. -/
namespace Jihoo.NativeKernel.NativeCoreCodePlain

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand)

private def children (visit : State → Nat → Outcome Bool) : List Nat → State → Outcome Bool
  | [],state => ⟨state,.ok true⟩
  | root :: rest,state =>
    (visit state root).next fun after allowed =>
      if allowed then children visit rest after else ⟨after,.ok false⟩

private def afterTick (env : Environment) (visit : State → Nat → Outcome Bool)
    (state : State) (root : Nat) : Outcome Bool :=
  match state.arena[root]? with
  | some (.var _) => ⟨state,.ok true⟩
  | some (.node op refs) =>
    match op with
    | .buffer | .ref | .pi _ | .back _ => ⟨state,.ok false⟩
    | .ind family _ =>
      if (env.families[family]?).any (fun entry => !entry.boxed) then children visit refs state
      else ⟨state,.ok false⟩
    | .lam _ =>
      match refs with
      | [_,body] => visit state body
      | _ => ⟨state,.ok false⟩
    | _ => children visit refs state
  | none => ⟨state,.error (.outsideFragment root)⟩

def scan (env : Environment) (limit : Nat) : Nat → State → Nat → Outcome Bool
  | 0,state,root =>
    let (paid,steps) := NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root
    ⟨{state with steps},.error (.tick (match paid with | .error reason => reason | .ok () => .depthLimit root))⟩
  | depth+1,state,root =>
    let (paid,steps) := NativeCoreUnsignedCancellation.tick state.arena limit (depth+1) state.steps root
    let entered := {state with steps}
    match paid with
    | .error reason => ⟨entered,.error (.tick reason)⟩
    | .ok () => afterTick env (scan env limit depth) entered root

def run (normal : State → Nat → Outcome Nat) (env : Environment) (limit depth : Nat) (state : State)
    (argument : Nat) : Outcome Bool :=
  (normal state argument).next fun after normalized => scan env limit depth after normalized

private theorem children_progress (progress : ∀ state root, Progress limit state (visit state root))
    (state : State) (refs : List Nat) : Progress limit state (children visit refs state) := by
  induction refs generalizing state with
  | nil => exact Progress.atState _ _
  | cons root rest ih =>
    unfold children
    exact (progress _ _).next fun allowed => by
      cases allowed
      · exact Progress.atState _ _
      · exact ih _

private theorem afterTick_progress (progress : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (afterTick env visit state root) := by
  unfold afterTick
  split
  · exact Progress.atState _ _
  · split
    · exact Progress.atState _ _
    · exact Progress.atState _ _
    · exact Progress.atState _ _
    · exact Progress.atState _ _
    · split
      · exact children_progress progress _ _
      · exact Progress.atState _ _
    · split
      · exact progress _ _
      · exact Progress.atState _ _
    · exact children_progress progress _ _
  · exact Progress.atState _ _

theorem scan_progress : Progress limit state (scan env limit depth state root) := by
  have failed (state : State) (reason : NativeCoreIdentical.Error) :
      Progress limit state (⟨{state with steps := state.steps+1},.error (.tick reason)⟩ : Outcome Bool) :=
    ⟨.refl _,Nat.le_succ _,Nat.succ_le_succ,fun _ _ impossible => by cases impossible⟩
  induction depth generalizing root state with
  | zero =>
    unfold scan NativeCoreUnsignedCancellation.tick
    by_cases tooMuch : limit < state.steps+1
    · simpa only [ite_eq_left tooMuch] using failed state (.stepLimit root)
    · simpa only [ite_eq_right tooMuch,ite_true] using failed state (.depthLimit root)
  | succ depth ih =>
    unfold scan NativeCoreUnsignedCancellation.tick
    by_cases tooMuch : limit < state.steps+1
    · simpa only [ite_eq_left tooMuch] using failed state (.stepLimit root)
    by_cases missing : state.arena.size ≤ root
    · simpa only [ite_eq_right tooMuch,Nat.succ_ne_zero,ite_false,ite_eq_left missing] using failed state (.invalidReference root)
    simp only [ite_eq_right tooMuch,Nat.succ_ne_zero,ite_false,ite_eq_right missing]
    have inside : state.steps+1 ≤ limit := by omega
    have later := afterTick_progress (visit := scan env limit depth) (env := env) (state := {state with steps := state.steps+1}) (root := root)
      (fun _ _ => ih)
    exact ⟨later.kept,Nat.le_trans (Nat.le_succ _) later.monotone,fun _ => later.bounded inside,
      fun _ => later.accepted inside⟩

theorem run_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (run normal env limit depth state argument) :=
  (normalProgress _ _).next fun _ => scan_progress

private theorem children_arena (kept : ∀ state root, (visit state root).state.arena = state.arena)
    (state : State) (refs : List Nat) : (children visit refs state).state.arena = state.arena := by
  induction refs generalizing state with
  | nil => rfl
  | cons root refs ih =>
    unfold children Outcome.next
    split
    · exact kept _ _
    · dsimp only
      split
      · exact (ih _).trans (kept _ _)
      · exact kept _ _

private theorem afterTick_arena (kept : ∀ state root, (visit state root).state.arena = state.arena) :
    (afterTick env visit state root).state.arena = state.arena := by
  unfold afterTick
  split
  · rfl
  · split
    · rfl
    · rfl
    · rfl
    · rfl
    · split
      · exact children_arena kept _ _
      · rfl
    · split
      · exact kept _ _
      · rfl
    · exact children_arena kept _ _
  · rfl

theorem scan_arena (depth : Nat) (state : State) (root : Nat) :
    (scan env limit depth state root).state.arena = state.arena := by
  induction depth generalizing state root with
  | zero => rfl
  | succ depth ih =>
    unfold scan
    rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth+1) state.steps root with ⟨status,steps⟩
    cases status
    · rfl
    · exact afterTick_arena ih

private theorem children_refines
    (kept : ∀ state root, (visit state root).state.arena = state.arena)
    (typed : ∀ {state root term}, Represents state.arena root term → (visit state root).result = .ok true →
      familyPlain env term = true)
    (represented : RepresentsList state.arena refs terms)
    (accepted : (children visit refs state).result = .ok true) :
    familyPlainArgs env terms = true := by
  induction refs generalizing state terms with
  | nil => cases represented; simp only [familyPlainArgs]
  | cons root refs ih =>
    cases represented with
    | cons first rest =>
      unfold children at accepted
      obtain ⟨allowed,allowedOk,next⟩ := Outcome.next_success accepted
      rw [next] at accepted
      cases allowed
      · simp only [Bool.false_eq_true,ite_false,Except.ok.injEq] at accepted
      · simp only [ite_true] at accepted
        have restRep := (kept state root).symm ▸ rest
        simp only [familyPlainArgs,Bool.and_eq_true]
        exact ⟨typed first allowedOk,ih restRep accepted⟩

private theorem afterTick_refines
    (kept : ∀ state root, (visit state root).state.arena = state.arena)
    (typed : ∀ {state root term}, Represents state.arena root term → (visit state root).result = .ok true →
      familyPlain env term = true)
    (represented : Represents state.arena root term)
    (accepted : (afterTick env visit state root).result = .ok true) : familyPlain env term = true := by
  unfold afterTick at accepted
  cases represented with
  | var read => simp only [familyPlain]
  | @node _ op refs terms read arity reps =>
    simp only [read] at accepted
    cases op <;> dsimp only at accepted
    case buffer | ref | pi | back =>
      cases accepted
    case ind family count =>
      split at accepted
      · rename_i flat
        simp only [familyPlain,Bool.and_eq_true]
        exact ⟨flat,children_refines kept typed reps accepted⟩
      · cases accepted
    case lam erased =>
      have length : refs.length = 2 := arity
      rcases refs with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
      cases reps with
      | cons _ rest =>
        cases rest with
        | cons body tail =>
          cases tail
          simpa only [familyPlain] using typed body accepted
    all_goals simpa only [familyPlain] using children_refines kept typed reps accepted

/-- A successful scan proves that every relevant visited part of the
normalized tree has its native first-order representation. -/
theorem scan_refines (represented : Represents state.arena root term)
    (accepted : (scan env limit depth state root).result = .ok true) : familyPlain env term = true := by
  induction depth generalizing state root term with
  | zero => cases accepted
  | succ depth ih =>
    unfold scan at accepted
    rcases paid : NativeCoreUnsignedCancellation.tick state.arena limit (depth+1) state.steps root with ⟨status,steps⟩
    rw [paid] at accepted
    cases status
    · cases accepted
    · exact afterTick_refines (state := {state with steps}) (scan_arena depth) (fun p ok => ih p ok) represented accepted

/-- The native scan operates on a graph root. When that selected tree is
closed under global expansion, its shape proves the semantic plain policy. -/
theorem run_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (represented : Represents state.arena argument term)
    (free : ∀ ref residual, (normal state argument).result = .ok ref →
      Represents (normal state argument).state.arena ref residual → globalFree residual = true)
    (success : (run normal env limit depth state argument).result = .ok true) :
    ∃ residual, RawLend.Conv env (expand env term) residual ∧ Environment.plain env residual = true := by
  unfold run at success
  obtain ⟨root,normalOk,next⟩ := Outcome.next_success success
  rw [next] at success
  obtain ⟨_,_,residual,held,related⟩ := normalSound onBase represented normalOk
  have global := free root residual normalOk held
  have plainShape := scan_refines held success
  have converted := related.converted
  rw [EnvironmentDelta.expand_globalFree ((globalFree_correct _).mp global)] at converted
  exact ⟨residual,converted,by simp [Environment.plain,global,plainShape]⟩

/-- The scan visits a lambda body without touching its annotation. A
forbidden first operand prevents a visit to the next operand. -/
theorem scan_skips_annotations_and_stops_at_first_failure :
    let input : Arena := #[.node .u64 [],.node (.natural 1) [],.node .buffer [1],
      .node (.lam false) [2,0],.node .strict [2,3]]
    scan empty 2 8 ⟨input,0⟩ 3 = ⟨⟨input,2⟩,.ok true⟩ ∧
      scan empty 2 8 ⟨input,0⟩ 4 = ⟨⟨input,2⟩,.ok false⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodePlain
