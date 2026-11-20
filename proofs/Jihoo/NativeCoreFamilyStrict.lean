import Jihoo.NativeCoreExpandedTraversal
import Jihoo.NativeCoreCaseStrict
import Jihoo.NativeLoanCheckerPolicySoundness

/-! Pure Case and data Elim move a retained Strict scrutinee outside the
eliminator. A motive that ignores the scrutinee gives the same original
checked type on either side of this graph rewrite. Its result may depend on
the family's indices and on variables from the enclosing context. -/
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
  data : ∃ entry, env.families[family]? = some entry ∧ entry.declaration.data = true
  result : ∀ {entry} {indices : List Term}, env.families[family]? = some entry →
    indices.length = entry.declaration.arity - entry.declaration.params →
    ∀ a b, LoanTyping.Conversion.Conv env
      (.app (applications (expand env motive) indices) a)
      (.app (applications (expand env motive) indices) b)

private theorem Stable.metadata (stable : Stable env family motive) (found : env.families[family]? = some entry) :
    entry.declaration.data = true := by
  obtain ⟨other, listed, data⟩ := stable.data
  have same := Option.some.inj (listed.symm.trans found)
  subst other
  exact data

private theorem arguments_refl (env : Environment) (indices : List Term) :
    ListRel (LoanTyping.Conversion.Conv env) indices indices := by
  induction indices with
  | nil => exact .nil
  | cons value _ rest => exact .cons (.refl value) rest

theorem Stable.transport (stable : Stable env family motive)
    (converted : LoanTyping.Conversion.Conv env (expand env motive) (expand env normalized)) :
    Stable env family normalized := by
  refine ⟨stable.data, fun {entry} {indices} found size a b => ?_⟩
  have app (x : Term) : LoanTyping.Conversion.Conv env
      (.app (applications (expand env motive) indices) x)
      (.app (applications (expand env normalized) indices) x) :=
    .node .app (.cons (LoanTyping.applications_congr converted (arguments_refl env indices)) (.cons (.refl _) .nil))
  exact (app a).symm.trans ((stable.result found size a b).trans (app b))

private def ignoresScrutinee (env : Environment) (depth : Nat) (arena : Arena) : Nat → Nat → Bool
  | 0, motive =>
      match arena[motive]? with
      | some (.node (.lam _) [_, body]) =>
          ((decode depth arena body).map (fun term =>
            (PartialRenaming.shift (-1) 0 (expand env term)).isSome)).getD false
      | _ => false
  | n + 1, motive =>
      match arena[motive]? with
      | some (.node (.lam _) [_, body]) => ignoresScrutinee env depth arena n body
      | _ => false

def constantMotive (env : Environment) (depth : Nat) (arena : Arena) (family motive : Nat) : Bool :=
  match env.families[family]? with
  | some entry =>
      entry.declaration.data &&
        ignoresScrutinee env depth arena (entry.declaration.arity - entry.declaration.params) motive
  | none => false

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

private inductive IgnoresLast : Nat → Term → Prop where
  | last {erased : Bool} {domain body : Term} : IgnoresLast 0 (.lam erased domain (body.rename Nat.succ))
  | index {n : Nat} {body : Term} {erased : Bool} {domain : Term} :
      IgnoresLast n body → IgnoresLast (n + 1) (.lam erased domain body)

private theorem ignoresScrutinee_sound (represented : Represents arena root motive)
    (accepted : ignoresScrutinee env depth arena n root = true) :
    IgnoresLast n (expand env motive) := by
  induction n generalizing motive root with
  | zero =>
    simp only [ignoresScrutinee] at accepted
    split at accepted
    case h_2 => cases accepted
    case h_1 erased domain body read =>
      obtain ⟨A, B, rfl, _, bodyRep⟩ := binary_read represented read
      cases decoded : decode depth arena body with
      | none => simp [decoded] at accepted
      | some term =>
        have same := bodyRep.unique (decode_sound decoded)
        subst term
        have canLower : (PartialRenaming.shift (-1) 0 (expand env B)).isSome = true := by
          simpa [decoded] using accepted
        cases lowered : PartialRenaming.shift (-1) 0 (expand env B) with
        | none => simp [lowered] at canLower
        | some outer =>
          have weakened := LoanTyping.Checker.branch_type_reweakens lowered
          simp only [expand_node_cons, expandArgs]
          rw [← weakened]
          exact .last
  | succ n ih =>
    simp only [ignoresScrutinee] at accepted
    split at accepted
    case h_2 => cases accepted
    case h_1 erased domain body read =>
      obtain ⟨A, B, rfl, _, bodyRep⟩ := binary_read represented read
      simp only [expand_node_cons, expandArgs]
      exact .index (ih bodyRep accepted)

private theorem substitute_lambda (erased : Bool) (domain body : Term) (values : Nat → Term) :
    (Term.lam erased domain body).subst values =
      .lam erased (domain.subst values) (body.subst (liftSubOne values)) := by
  simp only [Term.lam, Term.subst, substArgs, Op.binders, liftSub]

private theorem IgnoresLast.substitution (shape : IgnoresLast n motive) (values : Nat → Term) :
    IgnoresLast n (motive.subst values) := by
  induction shape generalizing values with
  | @last erased domain body =>
    have shifted : (body.rename Nat.succ).subst (liftSubOne values) =
        (body.subst values).rename Nat.succ := by
      simp only [Term.subst_rename, Term.rename_subst, liftSubOne]
    rw [substitute_lambda, shifted]
    exact .last
  | @index n body erased domain _ ih =>
    rw [substitute_lambda]
    exact .index (ih (liftSubOne values))

private theorem beta (env : Environment) (erased : Bool) (domain body value : Term) :
    LoanTyping.Conversion.Conv env (.app (.lam erased domain body) value) (body.subst (single value)) :=
  (RawLend.Forward.acu (.compute (.beta erased domain body value))).toConv

private theorem IgnoresLast.stable (shape : IgnoresLast indices.length motive) :
    LoanTyping.Conversion.Conv env (.app (applications motive indices) a) (.app (applications motive indices) b) := by
  induction indices generalizing motive with
  | nil =>
    cases shape with
    | @last erased domain body =>
      have reduce (value : Term) :
          LoanTyping.Conversion.Conv env (.app (.lam erased domain (body.rename Nat.succ)) value) body := by
        simpa only [Term.shift_subst_single] using beta env erased domain (body.rename Nat.succ) value
      exact (reduce a).trans (reduce b).symm
  | cons first rest ih =>
    cases shape with
    | @index n body erased domain shape =>
      have applied := LoanTyping.applications_congr (beta env erased domain body first) (arguments_refl env rest)
      have reduce (value : Term) := RawLend.Conv.node .app (.cons applied (.cons (.refl value) .nil))
      exact (reduce a).trans ((ih (shape.substitution (single first))).trans (reduce b).symm)

theorem constantMotive_sound (represented : Represents arena root motive)
    (accepted : constantMotive env depth arena family root = true) :
    Stable env family motive := by
  unfold constantMotive at accepted
  cases metadata : env.families[family]? with
  | none => simp [metadata] at accepted
  | some entry =>
    simp only [metadata, Bool.and_eq_true] at accepted
    obtain ⟨data, skipped⟩ := accepted
    refine ⟨⟨entry, metadata, data⟩, fun {other} {indices} found size a b => ?_⟩
    have same := Option.some.inj (metadata.symm.trans found)
    subst other
    have shape := ignoresScrutinee_sound represented skipped
    rw [← size] at shape
    exact shape.stable

private theorem data_elim_replacement
    (typed : LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms scrutinee) type)
    (metadata : ∀ {entry}, env.families[family]? = some entry → entry.declaration.data = true) :
    ∃ (entry : CheckedFamily) (indices : List Term), env.families[family]? = some entry ∧
      indices.length = entry.declaration.arity ∧
      LoanTyping.HasType env [] ctx true scrutinee (.node (.ind family entry.declaration.arity) indices) ∧
      (∀ {replacement}, LoanTyping.HasType env [] ctx true replacement (.node (.ind family entry.declaration.arity) indices) →
        LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms replacement)
          (.app (applications motive (indices.drop entry.declaration.params)) replacement)) ∧
      LoanTyping.Conversion.Conv env (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) type := by
  obtain ⟨entry, motive', arms', scrutinee', indices, _, layout, found, kind⟩ :=
    LoanTyping.FamilyIota.elim_inputs typed
  obtain ⟨rfl, tails⟩ := List.cons.inj layout
  obtain ⟨rfl, single⟩ := List.append_inj' tails (by simp)
  obtain rfl := (List.cons.inj single).1
  rcases kind with ⟨data, _⟩ | ⟨data, proof, types, size, motiveTyped, scrutineeTyped, generated, branches, result⟩
  · rw [metadata found] at data
    cases data
  refine ⟨entry, indices, found, size, scrutineeTyped, fun replacementTyped => ?_, result⟩
  exact LoanTyping.HasType.dataElim (analysis := false) (ghost := true) found data
    (by intro impossible; cases impossible) size motiveTyped (by simpa only [Bool.true_or] using replacementTyped)
    (by simpa only [Bool.not_false, Bool.and_true] using generated)
    (by simpa only [Bool.true_or] using branches) (Or.inl rfl)

private theorem data_elim_scrutinee_context
    (typed : LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms scrutinee) type)
    (metadata : ∀ {entry}, env.families[family]? = some entry → entry.declaration.data = true)
    (stable : ∀ {entry} {indices : List Term}, env.families[family]? = some entry →
      indices.length = entry.declaration.arity - entry.declaration.params →
      ∀ a b, LoanTyping.Conversion.Conv env (.app (applications motive indices) a) (.app (applications motive indices) b)) :
    ∃ scrutineeType, LoanTyping.HasType env [] ctx true scrutinee scrutineeType ∧
      ∀ {replacement}, LoanTyping.HasType env [] ctx true replacement scrutineeType →
        LoanTyping.HasType env [] ctx true (FamilyIota.elimTerm family motive arms replacement) type := by
  obtain ⟨entry, indices, found, size, scrutineeTyped, replace, result⟩ := data_elim_replacement typed metadata
  have indexCount : (indices.drop entry.declaration.params).length = entry.declaration.arity - entry.declaration.params := by
    rw [List.length_drop, size]
  exact ⟨_, scrutineeTyped, fun replacementTyped => (replace replacementTyped).convert ((stable found indexCount _ _).trans result)⟩

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
      LoanTyping.FamilyIota.case_scrutinee_context typed stable.result
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

/-- Pure ghost typing keeps the exact formed annotation for a motive that
depends on its scrutinee. The retained effect changes the written motive
application by the shaped Strict equation in RawValue conversion. -/
theorem commute_pure_preserves {sort : SortTag}
    (dataFamily : ∀ {entry}, env.families[family]? = some entry → entry.declaration.data = true)
    (change : ∀ {type}, LoanTyping.HasType env [] ctx true (familyTerm analysis family motive arms value) type →
      LoanTyping.HasType env [] ctx true result type)
    (typed : LoanTyping.HasType env [] ctx true (familyTerm analysis family motive arms (.strict effect value)) requested)
    (formed : LoanTyping.HasType env [] ctx true requested sort.term) :
    LoanTyping.PureTyping.HasType env ctx (.strict effect result) requested := by
  cases analysis
  · obtain ⟨entry, indices, _, _, strictTyped, replace, resultType⟩ := data_elim_replacement typed dataFamily
    obtain ⟨_, prefixTyped⟩ := NativeCoreValueContexts.strict_effect_typing strictTyped
    obtain ⟨_, valueTyped, aligned⟩ := strictTyped.principalView
    have reduced := replace (valueTyped.convert aligned)
    let applied := applications motive (indices.drop entry.declaration.params)
    have shifted : RawValue.Conv env (.app applied value) (.app applied (.strict effect value)) :=
      .node .app (.cons (.refl _) (.cons (.symm (.strict effect value)) .nil))
    exact LoanTyping.PureTyping.convert_native (.strict prefixTyped (change reduced)) formed (shifted.trans (.old resultType))
  · obtain ⟨_, _, prefixTyped, inner, converted⟩ := LoanTyping.FamilyIota.strict_case_inputs typed
    exact LoanTyping.PureTyping.convert_native (.strict prefixTyped (change inner)) formed converted

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

private theorem run_strict_result (onBase : Prefix base state.arena)
    (visitor : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armRefs arms)
    (effectRep : Represents state.arena effectRef effect) (valueRep : Represents state.arena valueRef value)
    (success : (run visit state analysis family motiveRef armRefs effectRef valueRef).result = .ok selected) :
    let after := (run visit state analysis family motiveRef armRefs effectRef valueRef).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ output, Represents after selected (.strict effect output) ∧
        ExpandedChange env (familyTerm analysis family motive arms value) output := by
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
  exact ⟨throughVisit.trans last, lastBack ∘ followingBack ∘ backward, output, result, changed⟩

theorem run_refines (stable : Stable env family motive) (onBase : Prefix base state.arena)
    (visitor : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armRefs arms)
    (effectRep : Represents state.arena effectRef effect) (valueRep : Represents state.arena valueRef value)
    (success : (run visit state analysis family motiveRef armRefs effectRef valueRef).result = .ok selected) :
    RefinesFor (ExpandedChange env) state (familyTerm analysis family motive arms (.strict effect value))
      (run visit state analysis family motiveRef armRefs effectRef valueRef) selected := by
  obtain ⟨kept, backward, output, represented, changed⟩ :=
    run_strict_result onBase visitor motiveRep armsRep effectRep valueRep success
  exact ⟨kept, backward, .strict effect output, represented, commute_preserves stable changed⟩

/-- The same arena execution preserves independently formed annotations in
pure typing for arbitrary scrutinee-dependent Case and data Elim motives. -/
theorem run_pure_refines {sort : SortTag}
    (dataFamily : ∀ {entry}, env.families[family]? = some entry → entry.declaration.data = true)
    (onBase : Prefix base state.arena)
    (visitor : ∀ {state root term selected}, Prefix base state.arena → Represents state.arena root term →
      (visit state root).result = .ok selected → RefinesFor (ExpandedChange env) state term (visit state root) selected)
    (motiveRep : Represents state.arena motiveRef motive) (armsRep : RepresentsList state.arena armRefs arms)
    (effectRep : Represents state.arena effectRef effect) (valueRep : Represents state.arena valueRef value)
    (typed : LoanTyping.HasType env [] ctx true
      (expand env (familyTerm analysis family motive arms (.strict effect value))) requested)
    (formed : LoanTyping.HasType env [] ctx true requested sort.term)
    (success : (run visit state analysis family motiveRef armRefs effectRef valueRef).result = .ok selected) :
    let after := (run visit state analysis family motiveRef armRefs effectRef valueRef).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ output, Represents after selected output ∧ LoanTyping.PureTyping.HasType env ctx (expand env output) requested := by
  obtain ⟨kept, backward, output, represented, changed⟩ :=
    run_strict_result onBase visitor motiveRep armsRep effectRep valueRep success
  have innerChange {type : Term} : LoanTyping.HasType env [] ctx true
      (familyTerm analysis family (expand env motive) (arms.map (expand env)) (expand env value)) type →
        LoanTyping.HasType env [] ctx true (expand env output) type := by
    intro original
    exact changed (by simpa only [expanded_familyTerm] using original)
  have expanded := commute_pure_preserves dataFamily innerChange
    (by simpa only [expanded_familyTerm, Term.strict, expand, expandArgs] using typed) formed
  exact ⟨kept, backward, .strict effect output, represented,
    by simpa only [Term.strict, expand, expandArgs] using expanded⟩

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

namespace Examples

private def box : Term := .node (.ind 0 0) []
private def buffer : Term := .buffer (.natural 2)
private def family : FamilyDeclaration := ⟨true, 0, 0, [.pi false buffer box], 0⟩
private def env : Environment := ⟨#[], #[⟨family, [⟨[⟨false, buffer, none⟩], []⟩], true⟩]⟩
private def arena : Arena := #[.node (.ind 0 0) [], .var 0, .var 1, .node .buffer [2], .node .u64 [],
  .node .strict [1, 4], .node (.lam false) [0, 3], .node (.lam false) [0, 5]]

/-- Buffer uses the older length binder. The other motive refers to the
scrutinee itself and the same check rejects it. -/
theorem open_motive_keeps_outer_index :
    constantMotive env 8 arena 0 6 = true ∧ constantMotive env 8 arena 0 7 = false ∧
      Stable env 0 (.lam false box (.buffer (.var 1))) := by
  have accepted : constantMotive env 8 arena 0 6 = true := by cbv
  have represented : Represents arena 6 (.lam false box (.buffer (.var 1))) := decode_sound (fuel := 4) rfl
  exact ⟨accepted, by cbv, constantMotive_sound represented accepted⟩

private def sizedFamily : FamilyDeclaration :=
  ⟨true, 0, 0, [.pi false .u64 (.pi false (.buffer (.var 0)) box)], 0⟩
private def sizedEntry : CheckedFamily := ⟨sizedFamily,
  [⟨[⟨false, .u64, none⟩, ⟨false, .buffer (.var 0), none⟩], []⟩], true⟩
private def sizedEnv : Environment := ⟨#[], #[sizedEntry]⟩
private def storedLength (subject : Term) : Term :=
  familyTerm false 0 (.lam false box .u64)
    [.lam false .u64 (.lam false (.buffer (.var 0)) (.var 1))] subject
private def dependentMotive : Term := .lam false box (.buffer (storedLength (.var 0)))
private def returnBuffer : Term := .lam false .u64 (.lam false (.buffer (.var 0)) (.var 0))
private def boxedValue : Term := .node (.con 0 0 2) [.natural 2, .alloc (.natural 2) (.integer 7)]
private def overflowingPrefix : Term := .arith .add (.integer 9223372036854775807) (.integer 1)
private def strictSubject : Term := .strict overflowingPrefix boxedValue
private def writtenType : Term := .app dependentMotive strictSubject

set_option maxRecDepth 4096 in
/-- The result length is a field of the scrutinized value. The pure
conversion keeps the exact annotation that mentions the original Strict
scrutinee after moving the effect outside the eliminator. -/
theorem dependent_motive_keeps_written_annotation :
    LoanTyping.PureTyping.HasType sizedEnv []
      (.strict overflowingPrefix (familyTerm false 0 dependentMotive [returnBuffer] boxedValue)) writtenType := by
  have typed : LoanTyping.HasType sizedEnv [] [] true
      (familyTerm false 0 dependentMotive [returnBuffer] strictSubject) writtenType :=
    LoanTyping.Checker.check_sound (fuel := 64) (by cbv)
  have formed : LoanTyping.HasType sizedEnv [] [] true writtenType (.univ 0) :=
    LoanTyping.Checker.infer_sound (fuel := 64) (by cbv)
  apply commute_pure_preserves (sort := .type 0) _ (fun original => original) typed formed
  intro entry found
  have known : sizedEnv.families[0]? = some sizedEntry := rfl
  have same := Option.some.inj (known.symm.trans found)
  subst entry
  rfl

end Examples

end Jihoo.NativeKernel.NativeCoreFamilyStrict
