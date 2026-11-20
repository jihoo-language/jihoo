import Jihoo.NativeCoreExpandedTraversal
import Jihoo.NativeCoreCaseStrict
import Jihoo.NativeScopeCheck

/-! Pure Case and data Elim move a retained Strict scrutinee outside the
eliminator. A motive that ignores the scrutinee gives the same original
checked type on either side of this graph rewrite. -/
namespace Jihoo.NativeKernel.NativeCoreFamilyStrict

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress RefinesFor ExpandedNormalization expandedRules
  visitOperands visitOperands_progress visitOperands_relatesFrom)
open NativeCoreExpandedTraversal (ExpandedChange)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs expandArgs_map expand_node_cons)
open NativeKernel.Conversion (ListRel)

def familyOp (analysis : Bool) (family count : Nat) : Op :=
  if analysis then .caseOf family count else .elim family count

def familyTerm (analysis : Bool) (family : Nat) (motive : Term) (arms : List Term) (subject : Term) : Term :=
  .node (familyOp analysis family arms.length) (motive :: (arms ++ [subject]))

structure Stable (env : Environment) (family : Nat) (motive : Term) : Prop where
  data : ∃ entry, env.families[family]? = some entry ∧
    entry.declaration.data = true ∧ entry.declaration.params = entry.declaration.arity
  result : ∀ a b, LoanTyping.Conversion.Conv env (.app (expand env motive) a) (.app (expand env motive) b)

private theorem Stable.metadata (stable : Stable env family motive) (found : env.families[family]? = some entry) :
    entry.declaration.data = true ∧ entry.declaration.params = entry.declaration.arity := by
  obtain ⟨other, listed, data, fixed⟩ := stable.data
  have same := Option.some.inj (listed.symm.trans found)
  subst other
  exact ⟨data, fixed⟩

theorem Stable.transport (stable : Stable env family motive)
    (converted : LoanTyping.Conversion.Conv env (expand env motive) (expand env normalized)) :
    Stable env family normalized := by
  refine ⟨stable.data, fun a b => ?_⟩
  have app (x : Term) : LoanTyping.Conversion.Conv env
      (.app (expand env motive) x) (.app (expand env normalized) x) :=
    .node .app (.cons converted (.cons (.refl _) .nil))
  exact (app a).symm.trans ((stable.result a b).trans (app b))

def constantMotive (env : Environment) (depth : Nat) (arena : Arena) (family motive : Nat) : Bool :=
  match env.families[family]?, arena[motive]? with
  | some entry, some (.node (.lam _) [_, body]) =>
      entry.declaration.data && (entry.declaration.params == entry.declaration.arity) &&
        ((decode depth arena body).map (fun term => scopeCheck 0 (expand env term))).getD false
  | _, _ => false

private theorem binary_read (represented : Represents arena root term)
    (read : arena[root]? = some (.node op [a, b])) :
    ∃ first second, term = .node op [first, second] ∧ Represents arena a first ∧ Represents arena b second := by
  cases represented with
  | var variableRead => rw [read] at variableRead; cases variableRead
  | node original _ children =>
      rw [read] at original
      cases original
      cases children with
      | cons first tail =>
        cases tail with
        | cons second tail =>
          cases tail
          exact ⟨_, _, rfl, first, second⟩

theorem constantMotive_sound (represented : Represents arena root motive)
    (accepted : constantMotive env depth arena family root = true) :
    Stable env family motive := by
  unfold constantMotive at accepted
  split at accepted
  case h_2 => cases accepted
  case h_1 entry erased domain body found read =>
    obtain ⟨data, complete⟩ := Bool.and_eq_true_iff.mp accepted
    obtain ⟨data, fixed⟩ := Bool.and_eq_true_iff.mp data
    refine ⟨⟨entry, found, data, beq_iff_eq.mp fixed⟩, ?_⟩
    obtain ⟨A, B, rfl, _, bodyRep⟩ := binary_read represented read
    cases decoded : decode depth arena body with
    | none => simp [decoded] at complete
    | some closed =>
      have same := bodyRep.unique (decode_sound decoded)
      subst closed
      have closedBody : (expand env B).Scoped 0 := scopeCheck_sound (by simpa [decoded] using complete)
      intro a b
      simp only [expand_node_cons, expandArgs]
      have beta (arg : Term) : LoanTyping.Conversion.Conv env
          (.app (.lam erased (expand env A) (expand env B)) arg) (expand env B) := by
        have reduced := RawLend.Forward.acu (env := env)
          (.compute (.beta erased (expand env A) (expand env B) arg))
        simpa only [Environment.closed_subst closedBody] using reduced.toConv
      exact (beta a).trans (beta b).symm

private theorem data_elim_scrutinee_context
    (typed : LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms scrutinee) type)
    (metadata : ∀ {entry}, env.families[family]? = some entry →
      entry.declaration.data = true ∧ entry.declaration.params = entry.declaration.arity)
    (stable : ∀ a b, LoanTyping.Conversion.Conv env (.app motive a) (.app motive b)) :
    ∃ scrutineeType, LoanTyping.HasType env [] ctx true scrutinee scrutineeType ∧
      ∀ {replacement}, LoanTyping.HasType env [] ctx true replacement scrutineeType →
        LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms replacement) type := by
  obtain ⟨entry, motive', arms', scrutinee', indices, _, layout, found, kind⟩ :=
    LoanTyping.FamilyIota.elim_inputs typed
  obtain ⟨rfl, tails⟩ := List.cons.inj layout
  obtain ⟨rfl, single⟩ := List.append_inj' tails (by simp)
  obtain rfl := (List.cons.inj single).1
  rcases kind with ⟨data, _⟩ | ⟨data, proof, types, size, motiveTyped, scrutineeTyped, generated, branches, result⟩
  · rw [(metadata found).1] at data
    cases data
  have suffix : indices.drop entry.declaration.params = [] :=
    List.drop_eq_nil_of_le (by simp only [size, (metadata found).2, Nat.le_refl])
  refine ⟨_, scrutineeTyped, fun replacementTyped => ?_⟩
  have replaced := LoanTyping.HasType.dataElim (analysis := false) (ghost := true) found data
    (by intro impossible; cases impossible) size motiveTyped (by simpa only [Bool.true_or] using replacementTyped)
    (by simpa only [Bool.not_false, Bool.and_true] using generated)
    (by simpa only [Bool.true_or] using branches) (Or.inl rfl)
  simp only [suffix, applications, List.foldl_nil] at result replaced
  exact replaced.convert ((stable _ _).trans result)

private theorem expanded_familyTerm (env : Environment) :
    expand env (familyTerm analysis family motive arms subject) =
      familyTerm analysis family (expand env motive) (arms.map (expand env)) (expand env subject) := by
  simp only [familyTerm, expand_node_cons, expandArgs_map, List.map_append, List.map_cons, List.map_nil, List.length_map]

private theorem scrutinee_context (stable : Stable env family motive)
    (typed : LoanTyping.HasType env [] ctx true (expand env (familyTerm analysis family motive arms scrutinee)) type) :
    ∃ scrutineeType, LoanTyping.HasType env [] ctx true (expand env scrutinee) scrutineeType ∧
      ∀ {replacement}, LoanTyping.HasType env [] ctx true (expand env replacement) scrutineeType →
        LoanTyping.HasType env [] ctx true (expand env (familyTerm analysis family motive arms replacement)) type := by
  simp only [expanded_familyTerm] at typed ⊢
  cases analysis
  · obtain ⟨T, scrutineeTyped, rebuild⟩ := data_elim_scrutinee_context typed stable.metadata stable.result
    exact ⟨T, scrutineeTyped, fun replacementTyped => rebuild replacementTyped⟩
  · obtain ⟨T, scrutineeTyped, rebuild⟩ :=
      LoanTyping.FamilyIota.case_scrutinee_context typed (fun found => (stable.metadata found).2) stable.result
    exact ⟨T, scrutineeTyped, fun replacementTyped => rebuild replacementTyped⟩

theorem changeScrutinee (stable : Stable env family motive) (change : ExpandedChange env scrutinee replacement) :
    ExpandedChange env (familyTerm analysis family motive arms scrutinee)
      (familyTerm analysis family motive arms replacement) := by
  intro ctx type typed
  obtain ⟨_, scrutineeTyped, rebuild⟩ := scrutinee_context stable typed
  exact rebuild (change scrutineeTyped)

/-- The strict root uses the exact codomain recovered by the original
case or elimination. Its effect is checked independently and retained. -/
theorem commute_preserves (stable : Stable env family motive)
    (change : ExpandedChange env (familyTerm analysis family motive arms value) result) :
    ExpandedChange env (familyTerm analysis family motive arms (.strict effect value)) (.strict effect result) := by
  intro ctx type typed
  obtain ⟨_, strictTyped, rebuild⟩ := scrutinee_context stable typed
  simp only [Term.strict, expand_node_cons, expandArgs] at strictTyped ⊢
  obtain ⟨_, prefixTyped⟩ := NativeCoreValueContexts.strict_effect_typing strictTyped
  obtain ⟨_, valueTyped, converted⟩ := strictTyped.principalView
  exact .strict prefixTyped (change (rebuild (valueTyped.convert converted)))

def run (visit : State → Nat → Outcome Nat) (state : State) (analysis : Bool) (family : Nat)
    (motive : Nat) (arms : List Nat) (effect value : Nat) : Outcome Nat :=
  (append state (familyOp analysis family arms.length) (motive :: (arms ++ [value]))).next
    fun afterInner inner => (visit afterInner inner).next
      fun afterVisit residual => append afterVisit .strict [effect, residual]

theorem run_progress (metered : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (run visit state analysis family motive arms effect value) :=
  (append_progress _ _ _).next (fun _ => (metered _ _).next (fun _ => append_progress _ _ _))

theorem represented_snoc (children : RepresentsList arena refs terms) (last : Represents arena ref term) :
    RepresentsList arena (refs ++ [ref]) (terms ++ [term]) := by
  induction children using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact .cons last .nil
  | cons head _ _ rest => exact .cons head rest

theorem run_refines (stable : Stable env family motive) (onBase : Prefix base state.arena)
    (visitor : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armRefs arms)
    (effectRep : Represents state.arena effectRef effect) (valueRep : Represents state.arena valueRef value)
    (success : (run visit state analysis family motiveRef armRefs effectRef valueRef).result = .ok selected) :
    RefinesFor (ExpandedChange env) state (familyTerm analysis family motive arms (.strict effect value))
      (run visit state analysis family motiveRef armRefs effectRef valueRef) selected := by
  unfold run at success ⊢
  obtain ⟨inner, added, next⟩ := Outcome.next_success success
  obtain ⟨kept, backward, held⟩ := append_refines
    (.cons motiveRep (represented_snoc armsRep valueRep))
    (by cases analysis <;> simp [familyOp, Op.arity]) added
  rw [next] at success ⊢
  obtain ⟨residual, visited, next⟩ := Outcome.next_success success
  have count := NativeCoreIdentical.represented_length armsRep
  have innerRep : Represents
      (append state (familyOp analysis family armRefs.length) (motiveRef :: (armRefs ++ [valueRef]))).state.arena
      inner (familyTerm analysis family motive arms value) := by
    simpa only [familyTerm, ← count] using held
  obtain ⟨following, followingBack, output, outputRep, changed⟩ :=
    visitor (onBase.trans kept) innerRep visited
  rw [next] at success ⊢
  have throughVisit := kept.trans following
  obtain ⟨last, lastBack, result⟩ :=
    append_refines (.cons (effectRep.frame throughVisit) (.cons outputRep .nil)) rfl success
  exact ⟨throughVisit.trans last, lastBack ∘ followingBack ∘ backward, .strict effect output, result,
    commute_preserves stable changed⟩

structure Plan where
  analysis : Bool
  family : Nat
  motive : Nat
  arms : List Nat
  scrutinee : Nat

private def getPlan (env : Environment) (depth : Nat) (arena : Arena) (analysis : Bool) (family count : Nat) :
    List Nat → Option Plan
  | motive :: operands =>
      match operands.drop count with
      | [scrutinee] =>
          if constantMotive env depth arena family motive then
            some ⟨analysis, family, motive, operands.take count, scrutinee⟩
          else none
      | _ => none
  | [] => none

def plan (env : Environment) (depth : Nat) (arena : Arena) (op : Op) (refs : List Nat) : Option Plan :=
  match op with
  | .caseOf family count => getPlan env depth arena true family count refs
  | .elim family count => getPlan env depth arena false family count refs
  | _ => none

private theorem getPlan_sound (found : getPlan env depth arena analysis family count refs = some chosen) :
    familyOp analysis family count = familyOp chosen.analysis chosen.family chosen.arms.length ∧
      refs = chosen.motive :: (chosen.arms ++ [chosen.scrutinee]) ∧
      constantMotive env depth arena chosen.family chosen.motive = true := by
  cases refs with
  | nil => simp [getPlan] at found
  | cons motive operands =>
    simp only [getPlan] at found
    split at found
    case h_2 => cases found
    case h_1 scrutinee last =>
      by_cases constant : constantMotive env depth arena family motive = true
      · simp only [ite_eq_left constant, Option.some.injEq] at found
        subst chosen
        have length := congrArg List.length last
        simp only [List.length_drop, List.length_singleton] at length
        have armsCount : (operands.take count).length = count := by
          rw [List.length_take, Nat.min_eq_left (by omega)]
        have splitOperands := List.take_append_drop count operands
        rw [last] at splitOperands
        exact ⟨by simp [armsCount], congrArg (List.cons motive) splitOperands.symm, constant⟩
      · simp [constant] at found

theorem plan_sound (found : plan env depth arena op refs = some chosen) :
    op = familyOp chosen.analysis chosen.family chosen.arms.length ∧
      refs = chosen.motive :: (chosen.arms ++ [chosen.scrutinee]) ∧
      constantMotive env depth arena chosen.family chosen.motive = true := by
  cases op <;> try contradiction
  case caseOf family count =>
    exact getPlan_sound (analysis := true) (family := family) (count := count) found
  case elim family count =>
    exact getPlan_sound (analysis := false) (family := family) (count := count) found

def finish (visit : State → Nat → Outcome Nat) (otherwise : State → List Nat → Outcome Nat)
    (state : State) (analysis : Bool) (family motive : Nat) (arms : List Nat) (scrutinee : Nat) : Outcome Nat :=
  match state.arena[scrutinee]? with
  | some (.node .strict [effect, value]) => run visit state analysis family motive arms effect value
  | _ => otherwise state (motive :: (arms ++ [scrutinee]))

theorem finish_progress (metered : ∀ state root, Progress limit state (visit state root))
    (fallbackMetered : ∀ state refs, Progress limit state (otherwise state refs)) :
    Progress limit state (finish visit otherwise state analysis family motive arms scrutinee) := by
  unfold finish
  split
  · exact run_progress metered
  · exact fallbackMetered _ _

theorem finish_refines (stable : Stable env family motive) (onBase : Prefix base state.arena)
    (visitor : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armRefs arms)
    (scrutineeRep : Represents state.arena scrutineeRef scrutinee)
    (fallback : (otherwise state (motiveRef :: (armRefs ++ [scrutineeRef]))).result = .ok selected →
      RefinesFor (ExpandedChange env) state (familyTerm analysis family motive arms scrutinee)
        (otherwise state (motiveRef :: (armRefs ++ [scrutineeRef]))) selected)
    (success : (finish visit otherwise state analysis family motiveRef armRefs scrutineeRef).result = .ok selected) :
    RefinesFor (ExpandedChange env) state (familyTerm analysis family motive arms scrutinee)
      (finish visit otherwise state analysis family motiveRef armRefs scrutineeRef) selected := by
  unfold finish at success ⊢
  split at success
  case h_2 => exact fallback success
  case h_1 effect value read =>
    obtain ⟨t, y, rfl, effectRep, valueRep⟩ := binary_read scrutineeRep read
    exact run_refines stable onBase visitor motiveRep armsRep effectRep valueRep success

def walk (raw visit : State → Nat → Outcome Nat) (otherwise : State → List Nat → Outcome Nat)
    (state : State) (chosen : Plan) : Outcome Nat :=
  (visitOperands raw state (chosen.motive :: chosen.arms)).next fun afterHead heads =>
    match heads with
    | motive :: arms =>
        (visit afterHead chosen.scrutinee).next fun afterScrutinee scrutinee =>
          finish visit otherwise afterScrutinee chosen.analysis chosen.family motive arms scrutinee
    | [] => ⟨afterHead, .error (.outsideFragment chosen.motive)⟩

theorem walk_progress (rawMetered : ∀ state root, Progress limit state (raw state root))
    (visitMetered : ∀ state root, Progress limit state (visit state root))
    (fallbackMetered : ∀ state refs, Progress limit state (otherwise state refs)) :
    Progress limit state (walk raw visit otherwise state chosen) := by
  apply (visitOperands_progress rawMetered state (chosen.motive :: chosen.arms)).next
  intro heads
  cases heads with
  | nil => exact Progress.atState _ _
  | cons _ _ =>
      exact (visitMetered _ _).next (fun _ => finish_progress visitMetered fallbackMetered)

private theorem changes_snoc (children : ListRel R firsts seconds) (last : R left right) :
    ListRel R (firsts ++ [left]) (seconds ++ [right]) := by
  induction children with
  | nil => exact .cons last .nil
  | cons head _ rest => exact .cons head rest

theorem walk_refines (wf : UnifiedProgram.EnvWellFormed env) (onBase : Prefix base state.arena)
    (stable : Stable env chosen.family motive)
    (motiveRep : Represents state.arena chosen.motive motive) (armsRep : RepresentsList state.arena chosen.arms arms)
    (subjectRep : Represents state.arena chosen.scrutinee subject)
    (rawSound : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (raw state root).result = .ok selected → RefinesFor (ExpandedNormalization env) state term (raw state root) selected)
    (visitSound : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (fallbackSound : ∀ {next newMotive newArms newScrutinee p cases x selected}, Prefix state.arena next.arena →
      newArms.length = chosen.arms.length →
      Represents next.arena newMotive p → RepresentsList next.arena newArms cases → Represents next.arena newScrutinee x →
      (otherwise next (newMotive :: (newArms ++ [newScrutinee]))).result = .ok selected →
      RefinesFor (ExpandedChange env) next (familyTerm chosen.analysis chosen.family p cases x)
        (otherwise next (newMotive :: (newArms ++ [newScrutinee]))) selected)
    (success : (walk raw visit otherwise state chosen).result = .ok selected) :
    RefinesFor (ExpandedChange env) state (familyTerm chosen.analysis chosen.family motive arms subject)
      (walk raw visit otherwise state chosen) selected := by
  unfold walk at success ⊢
  obtain ⟨heads, normalized, next⟩ := Outcome.next_success success
  obtain ⟨kept, backward, width, terms, headsRep, changes⟩ :=
    visitOperands_relatesFrom (relation := ExpandedNormalization env) onBase (.cons motiveRep armsRep)
      (fun prior source found => by
        obtain ⟨kept, backward, result⟩ := rawSound prior source found
        exact ⟨kept, backward, result⟩) normalized
  rw [next] at success ⊢
  cases headsRep with
  | nil => cases width
  | @cons newMotive p newArms cases newMotiveRep newArmsRep =>
    have widthArms := Nat.succ.inj width
    cases changes with
    | cons motiveChange armsChange =>
      have stableNew := stable.transport motiveChange.converted
      dsimp only at success ⊢
      obtain ⟨scrutinee, visited, entered⟩ := Outcome.next_success success
      obtain ⟨following, followingBack, x, scrutineeRep, changed⟩ :=
        visitSound (onBase.trans kept) (subjectRep.frame kept) visited
      rw [entered] at success ⊢
      have throughSubject := kept.trans following
      obtain ⟨last, lastBack, result, held, converted⟩ :=
        finish_refines stableNew (onBase.trans throughSubject) visitSound
          (newMotiveRep.frame following) (newArmsRep.frame following) scrutineeRep
          (fallbackSound throughSubject widthArms (newMotiveRep.frame following)
            (newArmsRep.frame following) scrutineeRep) success
      have widthTerms := (NativeCoreIdentical.represented_length armsRep).symm.trans
        (widthArms.symm.trans (NativeCoreIdentical.represented_length newArmsRep))
      have reconsidered := (expandedRules wf).node (op := familyOp chosen.analysis chosen.family arms.length)
        (by cases chosen.analysis <;> intro impossible <;> cases impossible)
        (by cases chosen.analysis <;> rfl)
        (.cons motiveChange (changes_snoc armsChange (LoanTyping.GhostTransform.refl (expand env subject))))
      have rawChanged : ExpandedChange env (familyTerm chosen.analysis chosen.family motive arms subject)
          (familyTerm chosen.analysis chosen.family p cases subject) := by
        intro ctx type typed
        unfold familyTerm
        rw [← widthTerms]
        exact reconsidered.preserves typed
      exact ⟨throughSubject.trans last, lastBack ∘ followingBack ∘ backward, result, held, fun typed =>
        converted (changeScrutinee stableNew changed (rawChanged typed))⟩

end Jihoo.NativeKernel.NativeCoreFamilyStrict
