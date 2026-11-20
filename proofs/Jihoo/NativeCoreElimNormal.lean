import Jihoo.NativeCoreCaseNormal
import Jihoo.NativeFamilyIotaDelta

/-! The pure known-constructor Elim path after the original operands have
normalized. All ordinary fields are applied before the recursive hypotheses.
Every hypothesis appends its own Elim followed immediately by its application. -/
namespace Jihoo.NativeKernel.NativeCoreElimNormal

open NativeArena Environment NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress Refines GhostNormalization runWithConditionals)
open NativeCoreCaseNormal (appendApplications appendApplications_refines appendApplications_progress)
open FamilyIota (elimTerm elimBody elimHypotheses)

def parameterSkip (entry : CheckedFamily) : Nat :=
  if entry.declaration.data then entry.declaration.params else 0

def recursiveFields (signatureFields : List Field) (fields : List α) : List α :=
  (signatureFields.zip fields).filterMap fun (signature, value) =>
    if signature.recursive.isSome then some value else none

private def eliminationRow (family motive : Nat) (cases : List Nat) (field : Nat) : Node :=
  .node (.elim family cases.length) (motive :: (cases ++ [field]))

def appendHypotheses (family motive : Nat) (cases : List Nat) (state : State) (callee : Nat) :
    List Nat → Outcome Nat
  | [] => ⟨state, .ok callee⟩
  | field :: rest =>
      match addNode state.arena (eliminationRow family motive cases field) with
      | .error reason => ⟨state, .error (.add reason)⟩
      | .ok (arena, hypothesis) =>
          let applied := appendApplications {state with arena} callee [hypothesis]
          match applied.result with
          | .error reason => ⟨applied.state, .error reason⟩
          | .ok root => appendHypotheses family motive cases applied.state root rest

def buildSpine (state : State) (entry : CheckedFamily) (signature : Signature) (family motive : Nat)
    (cases : List Nat) (branch : Nat) (fields : List Nat) : Outcome Nat :=
  let applied := appendApplications state branch (fields.drop (parameterSkip entry))
  match applied.result with
  | .error reason => ⟨applied.state, .error reason⟩
  | .ok root => appendHypotheses family motive cases applied.state root (recursiveFields signature.fields fields)

inductive Selection where
  | neutral (ref : Nat)
  | spine (ref : Nat)
  deriving Repr, DecidableEq

private def rebuild (state : State) (family motive : Nat) (cases : List Nat)
    (scrutinee : Nat) : Outcome Selection :=
  match addNode state.arena (eliminationRow family motive cases scrutinee) with
  | .error reason => ⟨state, .error (.add reason)⟩
  | .ok (arena, root) => ⟨{state with arena}, .ok (.neutral root)⟩

def selectSignature (env : Environment) (family actual constructor : Nat)
    (cases : List Nat) (fieldCount : Nat) : Option (CheckedFamily × Signature × Nat) := do
  if actual ≠ family then none else do
    let entry ← env.families[family]?
    let branch ← cases[constructor]?
    let signature ← entry.signatures[constructor]?
    if cases.length = entry.signatures.length ∧ fieldCount = signature.fields.length then
      some (entry, signature, branch)
    else none

/-- The native constructor guard compares the family, selected case, total
case count and field count. A neutral scrutinee always appends its row. -/
def prepare (env : Environment) (state : State) (family motive : Nat) (cases : List Nat)
    (scrutinee : Nat) : Outcome Selection :=
  match state.arena[scrutinee]? with
  | some (.node (.con actual constructor _) fields) =>
      match selectSignature env family actual constructor cases fields.length with
      | some (entry, signature, branch) =>
          let built := buildSpine state entry signature family motive cases branch fields
          ⟨built.state, built.result.map Selection.spine⟩
      | none => rebuild state family motive cases scrutinee
  | some (.node .strict _) => ⟨state, .error (.outsideFragment scrutinee)⟩
  | some _ => rebuild state family motive cases scrutinee
  | _ => ⟨state, .error (.outsideFragment scrutinee)⟩

def reenter (visit : State → Nat → Outcome Nat) (prepared : Outcome Selection) : Outcome Nat :=
  match prepared.result with
  | .error reason => ⟨prepared.state, .error reason⟩
  | .ok (.neutral root) => ⟨prepared.state, .ok root⟩
  | .ok (.spine root) => visit prepared.state root

def run (env : Environment) (limit childDepth : Nat) (state : State)
    (family motive : Nat) (cases : List Nat) (scrutinee : Nat) : Outcome Nat :=
  reenter (runWithConditionals limit childDepth) (prepare env state family motive cases scrutinee)

/-- All appends precede the single reentry at the already decremented depth.
Failed appends report their final partial arena, without calling the visitor. -/
theorem prepare_known {cases : List Nat} {fields : List Nat}
    (read : state.arena[scrutinee]? = some (.node (.con family constructor arity) fields))
    (found : env.families[family]? = some entry) (selected : cases[constructor]? = some branch)
    (sig : entry.signatures[constructor]? = some signature)
    (caseCount : cases.length = entry.signatures.length) (fieldCount : fields.length = signature.fields.length) :
    prepare env state family motive cases scrutinee =
      let built := buildSpine state entry signature family motive cases branch fields
      ⟨built.state, built.result.map Selection.spine⟩ := by
  simp [prepare, read, selectSignature, found, selected, sig, caseCount, fieldCount]

theorem selectSignature_sound
    (chosen : selectSignature env family actual constructor cases fieldCount = some (entry, signature, branch)) :
    actual = family ∧ env.families[family]? = some entry ∧ cases[constructor]? = some branch ∧
      entry.signatures[constructor]? = some signature ∧ cases.length = entry.signatures.length ∧
      fieldCount = signature.fields.length := by
  by_cases same : actual = family
  · simp only [selectSignature, same, ne_eq, not_true_eq_false, ite_false] at chosen
    obtain ⟨entry', found, chosen⟩ := Option.bind_eq_some_iff.mp chosen
    obtain ⟨branch', selected, chosen⟩ := Option.bind_eq_some_iff.mp chosen
    obtain ⟨signature', signatureRead, chosen⟩ := Option.bind_eq_some_iff.mp chosen
    split at chosen
    · rename_i sizes
      cases chosen
      exact ⟨same, found, selected, signatureRead, sizes.1, sizes.2⟩
    · contradiction
  · simp [selectSignature, same] at chosen

private theorem represented_append (left : RepresentsList arena xs first)
    (right : RepresentsList arena ys second) : RepresentsList arena (xs ++ ys) (first ++ second) := by
  induction left using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact right
  | cons head _ _ tail => exact .cons head tail

private theorem represented_get {index : Nat} (held : RepresentsList arena refs terms)
    (selected : terms[index]? = some term) :
    ∃ ref, refs[index]? = some ref ∧ Represents arena ref term := by
  induction index generalizing refs terms with
  | zero =>
      cases held with
      | nil => simp at selected
      | cons first tail =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          cases selected
          exact ⟨_, rfl, first⟩
  | succ index ih =>
      cases held with
      | nil => simp at selected
      | cons first tail =>
          simp only [List.getElem?_cons_succ] at selected ⊢
          exact ih tail selected

theorem represented_ref {index : Nat} (held : RepresentsList arena refs terms)
    (selected : refs[index]? = some ref) :
    ∃ term, terms[index]? = some term ∧ Represents arena ref term := by
  induction index generalizing refs terms with
  | zero =>
      cases held with
      | nil => simp at selected
      | cons first _ =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst ref
          exact ⟨_, rfl, first⟩
  | succ index ih =>
      cases held with
      | nil => simp at selected
      | cons _ rest =>
          exact ih rest selected

private theorem represented_drop (held : RepresentsList arena refs terms) (count : Nat) :
    RepresentsList arena (refs.drop count) (terms.drop count) := by
  induction count generalizing refs terms with
  | zero => exact held
  | succ count ih =>
      cases held with
      | nil => exact .nil
      | cons head tail => exact ih tail

private theorem represented_length (held : RepresentsList arena refs terms) : refs.length = terms.length := by
  induction held using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => rfl
  | cons head _ _ tail => exact congrArg Nat.succ tail

private theorem represented_recursive (held : RepresentsList arena refs terms) (fields : List Field) :
    RepresentsList arena (recursiveFields fields refs) (recursiveFields fields terms) := by
  induction fields generalizing refs terms with
  | nil => exact .nil
  | cons someField rest ih =>
      cases held with
      | nil => exact .nil
      | cons ref tail =>
          cases recursive : someField.recursive.isSome
          · simpa [recursiveFields, recursive] using ih tail
          · simpa [recursiveFields, recursive] using RepresentsList.cons ref (ih tail)

private theorem hypotheses_eq (fields : List Field) (values : List Term) (family : Nat)
    (motive : Term) (cases : List Term) :
    elimHypotheses family motive cases fields values =
      (recursiveFields fields values).map (elimTerm family motive cases) := by
  induction fields generalizing values with
  | nil => rfl
  | cons field rest ih =>
      cases values with
      | nil => rfl
      | cons value vs =>
          cases recursive : field.recursive.isSome
          · simpa [elimHypotheses, recursiveFields, recursive] using ih vs
          · simpa [elimHypotheses, recursiveFields, recursive] using
              congrArg ((elimTerm family motive cases value) :: ·) (ih vs)

private theorem reference_bound (held : Represents arena ref term) : ref < arena.size := by
  cases held with
  | var found | node found => exact (Array.getElem?_eq_some_iff.mp found).1

private theorem represented_members (held : RepresentsList arena refs terms) :
    ∀ ref ∈ refs, ref < arena.size := by
  induction held using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => simp
  | cons head _ _ tail =>
      intro ref member
      rcases List.mem_cons.mp member with rfl | found
      · exact reference_bound head
      · exact tail _ found

private theorem addHypothesis_refines
    (motiveRep : Represents arena motiveRef motive) (caseRep : RepresentsList arena caseRefs cases)
    (fieldRep : Represents arena field value)
    (added : addNode arena (eliminationRow family motiveRef caseRefs field) = .ok (after, hypothesis)) :
    Prefix arena after ∧ Represents after hypothesis (elimTerm family motive cases value) ∧
      (Backward arena → Backward after) := by
  obtain ⟨frame, fresh, _, _, _, row⟩ := addNode_commits added
  have refs : RepresentsList arena (motiveRef :: (caseRefs ++ [field])) (motive :: (cases ++ [value])) :=
    .cons motiveRep (represented_append caseRep (.cons fieldRep .nil))
  have rowAligned : after[hypothesis]? = some
      (.node (.elim family cases.length) (motiveRef :: (caseRefs ++ [field]))) := by
    simpa only [eliminationRow, represented_length caseRep] using row
  refine ⟨frame, .node rowAligned (by simp [Op.arity, represented_length caseRep] <;> omega)
    (refs.frame frame), ?_⟩
  intro backward
  apply addNode_preserves_backward backward added
  rw [fresh]
  exact represented_members refs

/-- Recursive fields are represented in signature order. The actual Elim
rows and alternating App rows recover exactly the family hypothesis list. -/
theorem appendHypotheses_refines
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (calleeRep : Represents state.arena callee alreadyApplied)
    (fieldsRep : RepresentsList state.arena fieldRefs fields)
    (success : (appendHypotheses family motiveRef caseRefs state callee fieldRefs).result = .ok root) :
    let built := appendHypotheses family motiveRef caseRefs state callee fieldRefs
    Prefix state.arena built.state.arena ∧ (Backward state.arena → Backward built.state.arena) ∧
      built.state.steps = state.steps ∧
      Represents built.state.arena root (applications alreadyApplied (fields.map (elimTerm family motive cases))) := by
  induction fieldRefs generalizing state callee alreadyApplied fields with
  | nil =>
      cases fieldsRep
      cases success
      exact ⟨.refl _, fun checked => checked, rfl, calleeRep⟩
  | cons field rest ih =>
      cases fieldsRep with
      | cons fieldRep restRep =>
          simp only [appendHypotheses] at success ⊢
          cases added : addNode state.arena (eliminationRow family motiveRef caseRefs field) with
          | error reason => simp [added] at success
          | ok hypothesisResult =>
              obtain ⟨arena, hyp⟩ := hypothesisResult
              simp only [added] at success ⊢
              obtain ⟨frame, hypothesis, backward⟩ := addHypothesis_refines motiveRep caseRep fieldRep added
              generalize applied : appendApplications {state with arena} callee [hyp] = next at success ⊢
              cases emitted : next.result with
              | error reason => simp [emitted] at success
              | ok app =>
                  simp only [emitted] at success ⊢
                  have computed : (appendApplications {state with arena} callee [hyp]).result = .ok app :=
                    congrArg Outcome.result applied |>.trans emitted
                  have result := appendApplications_refines (calleeRep.frame frame) (.cons hypothesis .nil) computed
                  rw [applied] at result
                  obtain ⟨later, laterBackward, exactSteps, represented⟩ := result
                  have combined := frame.trans later
                  obtain ⟨last, lastBackward, steps, output⟩ := ih (motiveRep.frame combined)
                    (caseRep.frame combined) represented (restRep.frame combined) success
                  exact ⟨combined.trans last, fun old => lastBackward (laterBackward (backward old)),
                    steps.trans exactSteps, output⟩

/-- The actual post-operand spine represents the independent full family
reduct, including the data parameter skip and all recursive hypotheses. -/
theorem buildSpine_refines
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (branchRep : Represents state.arena branchRef branch)
    (fieldsRep : RepresentsList state.arena fieldRefs values)
    (success : (buildSpine state entry signature family motiveRef caseRefs branchRef fieldRefs).result =
      .ok root) :
    let built := buildSpine state entry signature family motiveRef caseRefs branchRef fieldRefs
    Prefix state.arena built.state.arena ∧ (Backward state.arena → Backward built.state.arena) ∧
      built.state.steps = state.steps ∧ Represents built.state.arena root
        (elimBody entry signature family motive branch cases values) := by
  unfold buildSpine at success ⊢
  generalize applied : appendApplications state branchRef (fieldRefs.drop (parameterSkip entry)) =
    arguments at success ⊢
  cases selected : arguments.result with
  | error reason => simp [selected] at success
  | ok callee =>
      simp only [selected] at success ⊢
      have computed : (appendApplications state branchRef (fieldRefs.drop (parameterSkip entry))).result =
        .ok callee := congrArg Outcome.result applied |>.trans selected
      have result := appendApplications_refines branchRep (represented_drop fieldsRep _) computed
      rw [applied] at result
      obtain ⟨frame, backward, clock, represented⟩ := result
      have hyps := represented_recursive (fieldsRep.frame frame) signature.fields
      obtain ⟨later, afterBackward, finalClock, output⟩ := appendHypotheses_refines
        (motiveRep.frame frame) (caseRep.frame frame) represented hyps success
      refine ⟨frame.trans later, fun checked => afterBackward (backward checked), finalClock.trans clock, ?_⟩
      simpa only [elimBody, parameterSkip, hypotheses_eq] using output

/-- Capacity can be exhausted after committing an Elim but before its
App. Exactly the available prefix survives and no append charges a tick. -/
theorem appendHypotheses_progress (family motive : Nat) (cases : List Nat) (state : State)
    (callee : Nat) (fields : List Nat) :
    let built := appendHypotheses family motive cases state callee fields
    Prefix state.arena built.state.arena ∧ built.state.steps = state.steps ∧
      built.state.arena.size = state.arena.size + min (2 * fields.length) (entryLimit - state.arena.size) ∧
      (built.result = .error (.add .termLimit) ↔ entryLimit - state.arena.size < 2 * fields.length) := by
  induction fields generalizing state callee with
  | nil =>
      refine ⟨.refl _, rfl, ?_, ?_⟩
      · simp [appendHypotheses]
      · simp [appendHypotheses]
  | cons field rest ih =>
      by_cases room : state.arena.size < entryLimit
      · let row := eliminationRow family motive cases field
        let middle := state.arena.push row
        let hypothesis := state.arena.size
        have first : addNode state.arena (eliminationRow family motive cases field) = .ok (middle, hypothesis) := by
          simp only [addNode, room, ite_true, allocate, middle, row, hypothesis]
        have pushed : middle.size = state.arena.size + 1 := by simp [middle]
        by_cases secondRoom : middle.size < entryLimit
        · let app := Node.node .app [callee, hypothesis]
          let after := middle.push app
          have applied : appendApplications {state with arena := middle} callee [hypothesis] =
              ⟨{state with arena := after}, .ok middle.size⟩ := by
            simp only [appendApplications, addNode, secondRoom, ite_true, allocate, after, app]
          have doubled : after.size = state.arena.size + 2 := by simp [after, pushed]
          simp only [appendHypotheses, first, applied]
          obtain ⟨kept, ticks, length, failure⟩ := ih {state with arena := after} middle.size
          refine ⟨((Prefix.push _ _).trans (Prefix.push _ _)).trans kept, ticks, ?_, ?_⟩
          · rw [length, doubled]
            simp only [List.length_cons]
            omega
          · rw [failure, doubled]
            simp only [List.length_cons]
            omega
        · have applied : appendApplications {state with arena := middle} callee [hypothesis] =
              ⟨{state with arena := middle}, .error (.add .termLimit)⟩ := by
            simp only [appendApplications, addNode, secondRoom, ite_false]
          have one : entryLimit - state.arena.size = 1 := by omega
          simp only [appendHypotheses, first, applied, one]
          refine ⟨Prefix.push _ _, True.intro, ?_, ?_⟩
          · rw [pushed]
            simp only [List.length_cons]
            omega
          · simp [List.length_cons] <;> omega
      · have full : entryLimit - state.arena.size = 0 := by omega
        simp [appendHypotheses, addNode, room, full, Prefix.refl]

private theorem field_append_error (failed : (appendApplications state callee fields).result = .error reason) :
    reason = .add .termLimit := by
  induction fields generalizing state callee with
  | nil => cases failed
  | cons field rest ih =>
      by_cases room : state.arena.size < entryLimit
      · simp only [appendApplications, addNode, room, ite_true, allocate] at failed
        exact ih failed
      · simp only [appendApplications, addNode, room, ite_false, Except.error.injEq] at failed
        exact failed.symm

/-- The complete two-phase construction commits exactly the allocated
prefix, preserves the original tick count, and fails at the node limit
precisely when its field and hypothesis applications do not fit. -/
theorem buildSpine_progress (state : State) (entry : CheckedFamily) (signature : Signature) (family motive : Nat)
    (cases : List Nat) (branch : Nat) (fields : List Nat) :
    let built := buildSpine state entry signature family motive cases branch fields
    let required := (fields.drop (parameterSkip entry)).length + 2 * (recursiveFields signature.fields fields).length
    Prefix state.arena built.state.arena ∧ built.state.steps = state.steps ∧
      built.state.arena.size = state.arena.size + min required (entryLimit - state.arena.size) ∧
      (built.result = .error (.add .termLimit) ↔ entryLimit - state.arena.size < required) := by
  let ordinary := fields.drop (parameterSkip entry)
  let recursive := recursiveFields signature.fields fields
  have progress := appendApplications_progress state branch ordinary
  unfold buildSpine
  simp only
  generalize selected : appendApplications state branch ordinary = arguments at progress ⊢
  cases applied : arguments.result with
  | error reason =>
      have actual := congrArg Outcome.result selected |>.trans applied
      have reasonEq := field_append_error actual
      subst reason
      have tooMany := progress.2.2.2.mp (by rw [applied])
      have allocated := progress.2.2.1
      refine ⟨progress.1, progress.2.1, ?_, ?_⟩
      · simp only [Nat.min_eq_right (Nat.le_of_lt tooMany)] at allocated
        rw [allocated]
        have full : entryLimit - state.arena.size ≤ ordinary.length + 2 * recursive.length := by omega
        rw [Nat.min_eq_right full]
      · have rejected : entryLimit - state.arena.size < ordinary.length + 2 * recursive.length := by omega
        exact ⟨fun _ => rejected, fun _ => rfl⟩
  | ok callee =>
      have fits : ordinary.length ≤ entryLimit - state.arena.size := by
        apply Nat.le_of_not_gt
        intro tooMany
        have error := progress.2.2.2.mpr tooMany
        rw [applied] at error
        cases error
      have allocated : arguments.state.arena.size = state.arena.size + ordinary.length := by
        simpa only [Nat.min_eq_left fits] using progress.2.2.1
      have roomAfter : entryLimit - arguments.state.arena.size = entryLimit - state.arena.size - ordinary.length := by
        rw [allocated]
        omega
      have following := appendHypotheses_progress family motive cases arguments.state callee recursive
      refine ⟨progress.1.trans following.1, following.2.1.trans progress.2.1, ?_, ?_⟩
      · change (appendHypotheses family motive cases arguments.state callee recursive).state.arena.size =
          state.arena.size + min (ordinary.length + 2 * recursive.length) (entryLimit - state.arena.size)
        rw [following.2.2.1, roomAfter, allocated]
        omega
      · change (appendHypotheses family motive cases arguments.state callee recursive).result =
          .error (.add .termLimit) ↔ entryLimit - state.arena.size < ordinary.length + 2 * recursive.length
        rw [following.2.2.2, roomAfter]
        omega

private def Selection.root : Selection → Nat
  | .neutral ref | .spine ref => ref

structure PreparedRefines (env : Environment) (before after : Arena)
    (input : Term) (selection : Selection) : Prop where
  kept : Prefix before after
  backward : Backward before → Backward after
  term : ∃ residual, Represents after selection.root residual ∧
    match selection with
    | .neutral _ => residual = input
    | .spine _ => FamilyIota.Root env input residual

private theorem rebuild_refines (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases) (valueRep : Represents state.arena scrutinee value)
    (success : (rebuild state family motiveRef caseRefs scrutinee).result = .ok selected) :
    PreparedRefines env state.arena (rebuild state family motiveRef caseRefs scrutinee).state.arena
      (elimTerm family motive cases value) selected := by
  cases committed : addNode state.arena (eliminationRow family motiveRef caseRefs scrutinee) with
  | error reason => simp [rebuild, committed] at success
  | ok result =>
      obtain ⟨arena, fresh⟩ := result
      simp [rebuild, committed] at success
      subst selected
      simp only [rebuild, committed]
      obtain ⟨kept, index, _, _, _, read⟩ := addNode_commits committed
      have children := RepresentsList.cons motiveRep (represented_append caseRep (.cons valueRep .nil))
      have backward (prior : Backward state.arena) : Backward arena := by
        apply addNode_preserves_backward prior committed
        rw [index]
        exact represented_members children
      have count := represented_length caseRep
      refine ⟨kept, backward, _, ?_, rfl⟩
      unfold elimTerm
      rw [← count]
      exact .node read (by simp [Op.arity]) (children.frame kept)

/-- A successful spine represents an exact family contraction. A neutral
result represents the original eliminator with its normalized operands. -/
theorem prepare_refines (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases) (valueRep : Represents state.arena scrutinee value)
    (success : (prepare env state family motiveRef caseRefs scrutinee).result = .ok selected) :
    PreparedRefines env state.arena (prepare env state family motiveRef caseRefs scrutinee).state.arena
      (elimTerm family motive cases value) selected := by
  cases valueRep with
  | var read =>
      simpa only [prepare, read] using
        rebuild_refines (env := env) (family := family) motiveRep caseRep (.var read)
          (by simpa only [prepare, read] using success)
  | @node _ op fieldRefs values read arity fields =>
      cases op
      all_goals try solve
        | simpa only [prepare, read] using
            rebuild_refines (env := env) (family := family) motiveRep caseRep (.node read arity fields)
              (by simpa only [prepare, read] using success)
        | simp [prepare, read] at success
      case con actual constructor width =>
        cases picked : selectSignature env family actual constructor caseRefs fieldRefs.length with
        | none =>
            simpa only [prepare, read, picked] using
              rebuild_refines (env := env) (family := family) motiveRep caseRep (.node read arity fields)
                (by simpa only [prepare, read, picked] using success)
        | some triple =>
            obtain ⟨entry, signature, branchRef⟩ := triple
            obtain ⟨same, found, branchRead, sig, count, fieldCount⟩ := selectSignature_sound picked
            subst actual
            obtain ⟨branch, branchFound, branchRep⟩ := represented_ref caseRep branchRead
            have keptCount := represented_length caseRep
            have keptFields := represented_length fields
            have shape : width = values.length := arity.symm.trans keptFields
            subst width
            simp only [prepare, read, picked] at success ⊢
            cases emitted : (buildSpine state entry signature family motiveRef caseRefs branchRef fieldRefs).result with
            | error reason => simp [emitted, Except.map] at success
            | ok root =>
                simp only [emitted, Except.map, Except.ok.injEq] at success
                subst selected
                obtain ⟨kept, backward, _, represented⟩ :=
                  buildSpine_refines motiveRep caseRep branchRep fields emitted
                exact ⟨kept, backward, _, represented,
                  .elim found sig branchFound (keptCount.symm.trans count) (keptFields.symm.trans fieldCount)⟩

theorem iota_normalization (history : ScopedProgram.History definitions declarations env)
    (step : FamilyIota.Root env input output) : GhostNormalization env input output :=
  ⟨LoanTyping.FamilyEvaluation.Steps.ghost_transform history (.iota step),
    LoanTyping.FamilyEvaluation.Steps.ghost_transform history (.iota (FamilyIota.Extended.root_expansion step))⟩

/-- Compose constructor selection with recursion on the emitted application
spine and preserve its representation through transparent expansion. -/
theorem reenter_graph_refines (history : ScopedProgram.History definitions declarations env)
    (visitRefines : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases) (valueRep : Represents state.arena scrutinee value)
    (success : (reenter visit (prepare env state family motiveRef caseRefs scrutinee)).result = .ok selected) :
    Refines env state (elimTerm family motive cases value)
      (reenter visit (prepare env state family motiveRef caseRefs scrutinee)) selected := by
  cases chosen : (prepare env state family motiveRef caseRefs scrutinee).result with
  | error reason => simp [reenter, chosen] at success
  | ok selection =>
      obtain ⟨kept, backward, residual, represented, change⟩ :=
        prepare_refines motiveRep caseRep valueRep chosen
      cases selection with
      | neutral root =>
          simp only [reenter, chosen, Except.ok.injEq] at success ⊢
          subst selected
          change residual = _ at change
          subst residual
          exact ⟨kept, backward, _, represented, GhostNormalization.refl _⟩
      | spine root =>
          simp only [reenter, chosen] at success ⊢
          obtain ⟨later, preserves, term, output, reduced⟩ := visitRefines represented success
          exact ⟨kept.trans later, fun old => preserves (backward old), term, output,
            (iota_normalization history change).trans reduced⟩

private theorem rebuild_uncharged (state : State) (family motive : Nat) (cases : List Nat) (scrutinee : Nat) :
    let staged := rebuild state family motive cases scrutinee
    Prefix state.arena staged.state.arena ∧ staged.state.steps = state.steps := by
  cases added : addNode state.arena (eliminationRow family motive cases scrutinee) with
  | error reason =>
      exact ⟨(by simp only [rebuild, added]; exact .refl _), by simp [rebuild, added]⟩
  | ok result =>
      obtain ⟨arena, root⟩ := result
      exact ⟨by simpa only [rebuild, added] using (addNode_commits added).1, by simp [rebuild, added]⟩

private theorem prepare_uncharged (env : Environment) (state : State)
    (family motive : Nat) (cases : List Nat) (scrutinee : Nat) :
    let staged := prepare env state family motive cases scrutinee
    Prefix state.arena staged.state.arena ∧ staged.state.steps = state.steps := by
  cases read : state.arena[scrutinee]? with
  | none =>
      exact ⟨(by simp only [prepare, read]; exact .refl _), by simp [prepare, read]⟩
  | some row =>
      cases row with
      | var index => simpa only [prepare, read] using rebuild_uncharged state family motive cases scrutinee
      | node op fields =>
          cases op
          all_goals try solve
            | simpa only [prepare, read] using rebuild_uncharged state family motive cases scrutinee
            | exact ⟨(by simp only [prepare, read]; exact .refl _), by simp [prepare, read]⟩
          case con actual constructor width =>
            cases picked : selectSignature env family actual constructor cases fields.length with
            | none => simpa only [prepare, read, picked] using rebuild_uncharged state family motive cases scrutinee
            | some triple =>
                obtain ⟨entry, signature, branch⟩ := triple
                simp only [prepare, read, picked]
                have progress := buildSpine_progress state entry signature family motive cases branch fields
                exact ⟨progress.1, progress.2.1⟩

/-- Spine construction charges no ticks, including on capacity failure.
The recursive visitor uses the original clock and can charge a rejecting tick. -/
theorem reenter_progress (visitProgress : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (reenter visit (prepare env state family motive cases scrutinee)) := by
  let staged := prepare env state family motive cases scrutinee
  obtain ⟨kept, clock⟩ := prepare_uncharged env state family motive cases scrutinee
  change Progress limit state (reenter visit staged)
  cases chosen : staged.result with
  | error reason =>
      simp only [reenter, chosen]
      exact ⟨kept, Nat.le_of_eq clock.symm, fun room => Nat.le.step (clock ▸ room), fun _ _ found => by cases found⟩
  | ok selection =>
      cases selection with
      | neutral ref =>
          simp only [reenter, chosen]
          exact ⟨kept, Nat.le_of_eq clock.symm, fun room => Nat.le.step (clock ▸ room), fun room _ _ => clock ▸ room⟩
      | spine ref =>
          simp only [reenter, chosen]
          have progress := visitProgress staged.state ref
          exact ⟨kept.trans progress.kept, Nat.le_trans (Nat.le_of_eq clock.symm) progress.monotone,
            fun room => progress.bounded (clock ▸ room), fun room => progress.accepted (clock ▸ room)⟩

private theorem splitCases_exact (cases : List Term) (scrutinee : Term) :
    Checker.splitCases cases.length (cases ++ [scrutinee]) = some (cases, scrutinee) := by
  induction cases with
  | nil => rfl
  | cons branch rest ih =>
      simp only [List.length_cons, List.cons_append, Checker.splitCases, ih, Bind.bind, Option.bind, pure]

private theorem aligned_constructor
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env [] ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ entry signature branch, env.families[family]? = some entry ∧
      entry.signatures[constructor]? = some signature ∧ cases.length = entry.signatures.length ∧
      values.length = signature.fields.length ∧ cases[constructor]? = some branch ∧
      RawLend.Forward env (elimTerm family motive cases (.node (.con family constructor values.length) values))
        (elimBody entry signature family motive branch cases values) ∧
      LoanTyping.HasType env [] ctx true (elimBody entry signature family motive branch cases values) type := by
  obtain ⟨_, computed, resultTyped⟩ :=
    LoanTyping.FamilyIota.contract_elim_from_typing (ScopedProgram.History.ofLoanMixed history) typed
  simp only [elimTerm, FamilyIota.contract, FamilyIota.eliminate] at computed
  cases found : env.families[family]? with
  | none => simp [found] at computed
  | some entry =>
      simp only [found, Bind.bind, Option.bind, splitCases_exact] at computed
      cases sig : entry.signatures[constructor]? with
      | none => simp [sig] at computed
      | some signature =>
          simp only [sig] at computed
          cases selected : cases[constructor]? with
          | none => simp [selected] at computed
          | some branch =>
              simp only [selected, true_and] at computed
              split at computed
              · rename_i counts
                cases computed
                exact ⟨entry, signature, branch, rfl, sig, counts.1, counts.2, rfl,
                  .old (.iota (.elim found sig selected counts.1 counts.2)), resultTyped⟩
              · cases computed

private theorem prepared_checked
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ built : Outcome Nat, prepare env state family motiveRef caseRefs scrutinee =
      ⟨built.state, built.result.map Selection.spine⟩ ∧
      ∀ root, built.result = .ok root →
        built.state.steps = state.steps ∧
        NativeCoreCaseNormal.Refines env state.arena built.state.arena root ctx
          (elimTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  obtain ⟨entry, signature, branch, found, sig, caseCount, fieldCount, branchFound, reduced, spineTyped⟩ :=
    aligned_constructor history (typed.ghost [])
  obtain ⟨branchRef, branchRead, branchRep⟩ := represented_get caseRep branchFound
  cases valueRep with
  | node read arity fieldsRep =>
      rename_i fieldRefs
      refine ⟨buildSpine state entry signature family motiveRef caseRefs branchRef fieldRefs,
        prepare_known read found branchRead sig
          ((represented_length caseRep).trans caseCount) ((represented_length fieldsRep).trans fieldCount), ?_⟩
      intro root finished
      obtain ⟨frame, backward, steps, represented⟩ :=
        buildSpine_refines motiveRep caseRep branchRep fieldsRep finished
      exact ⟨steps, ⟨frame, backward, _, represented, reduced, spineTyped⟩⟩

/-- Typed input and an authentic mixed history determine the actual
contraction and the append-only spine. No successful reentry is needed. -/
theorem prepare_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type)
    (success : (prepare env state family motiveRef caseRefs scrutinee).result = .ok (.spine root)) :
    let built := prepare env state family motiveRef caseRefs scrutinee
    built.state.steps = state.steps ∧ NativeCoreCaseNormal.Refines env state.arena built.state.arena root ctx
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  obtain ⟨built, shape, preserved⟩ := prepared_checked history motiveRep caseRep valueRep typed
  rw [shape] at success ⊢
  cases emitted : built.result with
  | error reason => simp [emitted, Except.map] at success
  | ok spine =>
      simp only [emitted, Except.map, Except.ok.injEq, Selection.spine.injEq] at success
      subst spine
      exact preserved _ emitted

/-- A type-preserving reentry visitor composes with the checked Elim
contract, retaining the original type and arena prefix. -/
theorem reenter_preserves
    (visit : State → Nat → Outcome Nat)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type)
    (visitSound : ∀ {next root term output}, Represents next.arena root term →
      LoanTyping.HasType env [] ctx true term type → (visit next root).result = .ok output →
      NativeCoreCaseNormal.Refines env next.arena (visit next root).state.arena output ctx term type)
    (success : (reenter visit (prepare env state family motiveRef caseRefs scrutinee)).result = .ok selected) :
    NativeCoreCaseNormal.Refines env state.arena
      (reenter visit (prepare env state family motiveRef caseRefs scrutinee)).state.arena selected ctx
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  obtain ⟨built, shape, preserved⟩ := prepared_checked history motiveRep caseRep valueRep typed
  simp only [shape, reenter] at success ⊢
  cases emitted : built.result with
  | error reason => simp [emitted, Except.map] at success
  | ok root =>
      simp only [emitted, Except.map] at success ⊢
      obtain ⟨_, frame, backward, term, represented, contracted, termTyped⟩ := preserved _ emitted
      obtain ⟨later, laterBackward, residual, output, normalized, originalType⟩ :=
        visitSound represented termTyped success
      exact ⟨frame.trans later, fun old => laterBackward (backward old), residual, output,
        contracted.trans normalized, originalType⟩

/-- The existing pure driver supplies the visitor proof for its supported
reentry fragment. The parameter and recursive spine proofs are shared. -/
theorem run_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type)
    (success : (run env limit childDepth state family motiveRef caseRefs scrutinee).result = .ok selected) :
    NativeCoreCaseNormal.Refines env state.arena
      (run env limit childDepth state family motiveRef caseRefs scrutinee).state.arena selected ctx
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  apply reenter_preserves (runWithConditionals limit childDepth) history motiveRep caseRep valueRep typed ?_ success
  intro _ _ _ _ represented termTyped reduced
  obtain ⟨frame, backward, residual, output, normalized, originalType⟩ :=
    NativeCorePureComputationNormal.runWithConditionals_preserves history.wellFormed represented termTyped reduced
  exact ⟨frame, backward, residual, output, normalized, originalType⟩

namespace Examples

private def evidenceFamily : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration :=
  ⟨false, 0, 0, [evidenceFamily, .pi true evidenceFamily (.pi true evidenceFamily evidenceFamily)], 0⟩
private def evidenceField : Field := ⟨true, evidenceFamily, some []⟩
private def entry : CheckedFamily := ⟨declaration, [⟨[], []⟩, ⟨[evidenceField, evidenceField], []⟩], false⟩
private def env : Environment := ⟨#[], #[entry]⟩

private def motive : Term := .eq (.natural 0) (.natural 0)
private def base : Term := .refl (.natural 0)
private def branch : Term := .lam true evidenceFamily (.lam true evidenceFamily (.lam true motive (.lam true motive (.var 0))))
private def branches : List Term := [base, branch]
private def leaf : Term := .node (.con 0 0 0) []
private def fork (first second : Term) : Term := .node (.con 0 1 2) [first, second]
private def source : Term := elimTerm 0 motive branches (fork leaf (fork leaf leaf))
private def leafSource : Term := elimTerm 0 motive branches leaf

private def arena : Arena := #[.node (.natural 0) [], .node .eq [0, 0], .node .refl [0],
  .node (.ind 0 0) [], .var 0, .node (.lam true) [1, 4], .node (.lam true) [1, 5],
  .node (.lam true) [3, 6], .node (.lam true) [3, 7], .node (.con 0 0 0) [],
  .node (.con 0 1 2) [9, 9], .node (.con 0 1 2) [9, 10]]
private def state : State := ⟨arena, 3⟩

private theorem history : LoanTyping.MixedProgram.History [] [declaration] env :=
  LoanTyping.MixedProgram.checkProgram_sound
    (by cbv : LoanTyping.MixedProgram.checkProgram 48 96 [] [declaration] = some env)

private theorem zero_rep : Represents arena 0 (.natural 0) := .node rfl rfl .nil
private theorem motive_rep : Represents arena 1 motive := .node rfl rfl (.cons zero_rep (.cons zero_rep .nil))
private theorem family_rep : Represents arena 3 evidenceFamily := .node rfl rfl .nil
private theorem leaf_rep : Represents arena 9 leaf := .node rfl rfl .nil
private theorem fork_rep : Represents arena 10 (fork leaf leaf) :=
  .node rfl rfl (.cons leaf_rep (.cons leaf_rep .nil))

private theorem branches_rep : RepresentsList arena [2, 8] branches := by
  apply RepresentsList.cons (.node rfl rfl (.cons zero_rep .nil))
  apply RepresentsList.cons
  · refine .node rfl rfl (.cons family_rep (.cons (?_ : Represents arena 7 _) .nil))
    refine .node rfl rfl (.cons family_rep (.cons (?_ : Represents arena 6 _) .nil))
    refine .node rfl rfl (.cons motive_rep (.cons (?_ : Represents arena 5 _) .nil))
    exact .node rfl rfl (.cons motive_rep (.cons (.var rfl) .nil))
  · exact .nil

/-- Both recursive fields are genuine. The retained application spine must
finish the two field applications before adding the left then right Elim
hypotheses. Its exact source type comes from the mixed checker. -/
theorem checked_recursive_spine_has_signature_order :
    let built := prepare env state 0 1 [2, 8] 11
    built =
      ⟨⟨arena ++ #[.node .app [8, 9], .node .app [12, 10], .node (.elim 0 2) [1, 2, 8, 9],
        .node .app [13, 14], .node (.elim 0 2) [1, 2, 8, 10], .node .app [15, 16]], 3⟩,
        .ok (.spine 17)⟩ ∧
      NativeCoreCaseNormal.Refines env arena built.state.arena 17 [] source motive := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true source motive = true := by cbv
  have held : Represents arena 11 (fork leaf (fork leaf leaf)) :=
    .node rfl rfl (.cons leaf_rep (.cons fork_rep .nil))
  have computed : (prepare env state 0 1 [2, 8] 11).result = .ok (.spine 17) := by cbv
  refine ⟨by cbv, ?_⟩
  have typed : LoanTyping.HasType env [] [] true source motive := LoanTyping.Checker.check_sound accepted
  exact (prepare_preserves (constructor := 1) (values := [leaf, fork leaf leaf]) history motive_rep branches_rep
    held typed computed).2

/-- A constructor with no retained fields still uses the original child
depth and counter when reentering, and returns checked base evidence. -/
theorem checked_leaf_reenters_normalizer :
    let result := run env 64 16 state 0 1 [2, 8] 9
    result = ⟨⟨arena, 5⟩, .ok 2⟩ ∧
      NativeCoreCaseNormal.Refines env arena result.state.arena 2 [] leafSource motive := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true leafSource motive = true := by cbv
  have computed : (run env 64 16 state 0 1 [2, 8] 9).result = .ok 2 := by cbv
  have typed : LoanTyping.HasType env [] [] true leafSource motive := LoanTyping.Checker.check_sound accepted
  exact ⟨by cbv, run_preserves (constructor := 0) (values := []) history motive_rep branches_rep leaf_rep typed computed⟩

end Examples

end Jihoo.NativeKernel.NativeCoreElimNormal
