import Jihoo.NativeCoreCaseNormal

/-! The pure known-owner View path at the result of `view_shape`. Its
two loops build ordinary field applications first, then recursive applications.
Each recursive hypothesis allocates a fresh borrow of the underlying field. -/
namespace Jihoo.NativeKernel.NativeCoreViewNormal

open NativeArena Environment NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress runWithConditionals)
open NativeCoreCaseNormal (Refines appendApplications appendApplications_refines appendApplications_progress)
open FamilyIota (viewTerm viewBody viewArguments viewHypotheses)

abbrev Shape := List (Bool × Bool)

def checkedShape (plans : List ViewFieldPlan) : Shape :=
  plans.map fun plan => (plan.borrowed, plan.self)

inductive ArgumentKind where
  | direct
  | borrow
  | recursive

private def ordinary (shape : Shape) (fields : List α) : List (ArgumentKind × α) :=
  (shape.zip fields).map fun (flags, field) =>
    (if flags.1 then .borrow else .direct, field)

private def hypotheses (recursion : Bool) (shape : Shape) (fields : List α) : List (ArgumentKind × α) :=
  if recursion then (shape.zip fields).filterMap fun (flags, field) =>
    if flags.2 then some (.recursive, field) else none
  else []

private def borrowRow (field : Nat) : Node := .node .borrow [field]

private def viewRow (family motive : Nat) (cases : List Nat) (borrow : Nat) : Node :=
  .node (.view true family cases.length) (motive :: (cases ++ [borrow]))

private def emit (state : State) (row : Node) : Outcome Nat :=
  match addNode state.arena row with
  | .error reason => ⟨state, .error (.add reason)⟩
  | .ok (arena, ref) => ⟨{state with arena}, .ok ref⟩

private def thenVisit (visit : State → Nat → Outcome Nat) (before : Outcome Nat) : Outcome Nat :=
  match before.result with
  | .error reason => ⟨before.state, .error reason⟩
  | .ok ref => visit before.state ref

private theorem thenVisit_progress (prior : Progress limit state output)
    (following : ∀ ref, Progress limit output.state (visit output.state ref)) :
    Progress limit state (thenVisit visit output) := by
  have sequence : thenVisit visit output = output.next visit := by
    cases found : output.result <;> simp only [thenVisit, Outcome.next, found]
  rw [sequence]
  exact prior.next following

private def emitArgument (family motive : Nat) (cases : List Nat) (state : State) (field : Nat) :
    ArgumentKind → Outcome Nat
  | .direct => ⟨state, .ok field⟩
  | .borrow => emit state (borrowRow field)
  | .recursive => thenVisit (fun next borrow => emit next (viewRow family motive cases borrow))
      (emit state (borrowRow field))

private def appendArguments (family motive : Nat) (cases : List Nat) (state : State) (branch : Nat) :
    List (ArgumentKind × Nat) → Outcome Nat
  | [] => ⟨state, .ok branch⟩
  | (kind, field) :: rest =>
      thenVisit (fun next callee => appendArguments family motive cases next callee rest)
        (thenVisit (fun next ref => appendApplications next branch [ref])
          (emitArgument family motive cases state field kind))

def buildSpine (state : State) (recursion : Bool) (family motive params : Nat)
    (cases : List Nat) (branch : Nat) (fields : List Nat) (shape : Shape) : Outcome Nat :=
  let retained := fields.drop params
  appendArguments family motive cases state branch
    (ordinary shape retained ++ hypotheses recursion shape retained)

private theorem emit_progress (state : State) (node : Node) : Progress limit state (emit state node) := by
  cases added : addNode state.arena node with
  | error reason =>
      simp only [emit, added]
      exact Progress.atState _ _
  | ok result =>
      obtain ⟨arena, ref⟩ := result
      simp only [emit, added]
      exact Progress.fromAppend (addNode_commits added).1 (Progress.atState _ _)

private theorem emitArgument_progress (family motive : Nat) (cases : List Nat) (state : State)
    (field : Nat) (kind : ArgumentKind) : Progress limit state (emitArgument family motive cases state field kind) := by
  cases kind with
  | direct => exact Progress.atState _ _
  | borrow => exact emit_progress _ _
  | recursive =>
      rw [emitArgument]
      exact thenVisit_progress (emit_progress _ _) (fun _ => emit_progress _ _)

private theorem appendArguments_progress (family motive : Nat) (cases : List Nat) (state : State) (branch : Nat)
    (arguments : List (ArgumentKind × Nat)) :
    Progress limit state (appendArguments family motive cases state branch arguments) := by
  induction arguments generalizing state branch with
  | nil => exact Progress.atState _ _
  | cons argument tail ih =>
      obtain ⟨kind, field⟩ := argument
      let first := emitArgument family motive cases state field kind
      have applied (ref : Nat) : Progress limit first.state (appendApplications first.state branch [ref]) := by
        obtain ⟨kept, clock, _, _⟩ := appendApplications_progress first.state branch [ref]
        exact Progress.uncharged kept clock
      rw [appendArguments]
      apply thenVisit_progress
      · exact thenVisit_progress (emitArgument_progress family motive cases state field kind) applied
      · intro callee
        exact ih _ callee

/-- Each borrow, recursive View and application append commits immediately
without charging a tick, including the prefix of a capacity failure. -/
theorem buildSpine_progress (state : State) (recursion : Bool) (family motive params : Nat)
    (cases : List Nat) (branch : Nat) (fields : List Nat) (shape : Shape) :
    Progress limit state (buildSpine state recursion family motive params cases branch fields shape) :=
  appendArguments_progress family motive cases state branch _

inductive Selection where
  | decline
  | spine (ref : Nat)
  deriving DecidableEq, Repr

/-- The known-owner layout is checked against the completed shape. Decline
returns to the caller's unreduced View, retaining the state of the shape run. -/
def prepare (env : Environment) (state : State) (recursion : Bool) (family motive : Nat)
    (cases : List Nat) (scrutinee : Nat) (shape : Shape) : Outcome Selection :=
  match state.arena[scrutinee]? with
  | some (.node .borrow [owner]) =>
    match state.arena[owner]? with
    | some (.node (.con actual constructor _) fields) =>
      if actual = family then
        match env.families[family]?, cases[constructor]? with
        | some entry, some branch =>
          if entry.boxed = true ∧ cases.length = entry.signatures.length ∧
              fields.length = entry.declaration.params + shape.length then
            let built := buildSpine state recursion family motive entry.declaration.params cases branch fields shape
            ⟨built.state, built.result.map Selection.spine⟩
          else ⟨state, .ok .decline⟩
        | _, _ => ⟨state, .ok .decline⟩
      else ⟨state, .ok .decline⟩
    | _ => ⟨state, .error (.outsideFragment owner)⟩
  | _ => ⟨state, .error (.outsideFragment scrutinee)⟩

def reenter (visit : State → Nat → Outcome Nat) (prepared : Outcome Selection) : Outcome (Option Nat) :=
  match prepared.result with
  | .error reason => ⟨prepared.state, .error reason⟩
  | .ok .decline => ⟨prepared.state, .ok none⟩
  | .ok (.spine root) =>
      let evaluated := visit prepared.state root
      ⟨evaluated.state, evaluated.result.map some⟩

def run (env : Environment) (limit childDepth : Nat) (state : State) (recursion : Bool)
    (family motive : Nat) (cases : List Nat) (scrutinee : Nat) (shape : Shape) : Outcome (Option Nat) :=
  reenter (runWithConditionals limit childDepth) (prepare env state recursion family motive cases scrutinee shape)

theorem prepare_known
    (borrowed : state.arena[scrutinee]? = some (borrowRow owner))
    (read : state.arena[owner]? = some (.node (.con family constructor arity) fields))
    (found : env.families[family]? = some entry) (selected : cases[constructor]? = some branch)
    (boxed : entry.boxed = true) (caseCount : cases.length = entry.signatures.length)
    (fieldCount : fields.length = entry.declaration.params + shape.length) :
    prepare env state recursion family motive cases scrutinee shape =
      let built := buildSpine state recursion family motive entry.declaration.params cases branch fields shape
      ⟨built.state, built.result.map Selection.spine⟩ := by
  simp only [prepare, borrowRow] at *
  simp only [borrowed, read, found, selected, boxed, caseCount, fieldCount, true_and, ite_true]

private theorem represented_append (left : RepresentsList arena xs first)
    (right : RepresentsList arena ys second) : RepresentsList arena (xs ++ ys) (first ++ second) := by
  induction left using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact right
  | cons head _ _ tail => exact .cons head tail

private theorem represented_length (held : RepresentsList arena refs terms) : refs.length = terms.length := by
  induction held using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => rfl
  | cons head _ _ tail => exact congrArg Nat.succ tail

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

private theorem represented_drop (held : RepresentsList arena refs terms) (count : Nat) :
    RepresentsList arena (refs.drop count) (terms.drop count) := by
  induction count generalizing refs terms with
  | zero => exact held
  | succ count ih =>
      cases held with
      | nil => exact .nil
      | cons head tail => exact ih tail

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

private def Preserves (before : State) (after : Outcome Nat) (ref : Nat) (term : Term) : Prop :=
  Prefix before.arena after.state.arena ∧ (Backward before.arena → Backward after.state.arena) ∧
    after.state.steps = before.steps ∧ Represents after.state.arena ref term

private theorem Preserves.trans (first : Preserves before intermediate ref term)
    (second : Preserves intermediate.state after root result) : Preserves before after root result :=
  ⟨first.1.trans second.1, fun checked => second.2.1 (first.2.1 checked), second.2.2.1.trans first.2.2.1,
    second.2.2.2⟩

private theorem emit_refines (held : RepresentsList state.arena refs terms) (arity : terms.length = op.arity)
    (success : (emit state (.node op refs)).result = .ok ref) :
    Preserves state (emit state (.node op refs)) ref (.node op terms) := by
  cases added : addNode state.arena (.node op refs) with
  | error reason => simp [emit, added] at success
  | ok pair =>
      obtain ⟨arena, root⟩ := pair
      simp only [emit, added, Except.ok.injEq] at success
      subst root
      obtain ⟨frame, fresh, _, _, _, row⟩ := addNode_commits added
      simp only [emit, added]
      refine ⟨frame, ?_, rfl, .node row ((represented_length held).trans arity) (held.frame frame)⟩
      intro checked
      apply addNode_preserves_backward checked added
      rw [fresh]
      exact represented_members held

private def argumentTerm (family : Nat) (motive : Term) (cases : List Term) (value : Term) :
    ArgumentKind → Term
  | .direct => value
  | .borrow => .borrow value
  | .recursive => viewTerm true family motive cases (.borrow value)

private theorem emitArgument_refines
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (fieldRep : Represents state.arena field value)
    (success : (emitArgument family motiveRef caseRefs state field kind).result = .ok ref) :
    Preserves state (emitArgument family motiveRef caseRefs state field kind) ref
      (argumentTerm family motive cases value kind) := by
  cases kind with
  | direct =>
      cases success
      exact ⟨.refl _, id, rfl, fieldRep⟩
  | borrow =>
      exact emit_refines (.cons fieldRep .nil) rfl success
  | recursive =>
      generalize result : emit state (borrowRow field) = borrowed
      have shape : emitArgument family motiveRef caseRefs state field .recursive =
          thenVisit (fun next borrow => emit next (viewRow family motiveRef caseRefs borrow)) borrowed := by
        simp only [emitArgument, result]
      rw [shape] at success ⊢
      cases emitted : borrowed.result with
      | error reason => simp [thenVisit, emitted] at success
      | ok borrow =>
          simp only [thenVisit, emitted] at success ⊢
          have first : Preserves state borrowed borrow (.borrow value) := by
            rw [← result]
            exact emit_refines (.cons fieldRep .nil) rfl (congrArg Outcome.result result |>.trans emitted)
          have children : RepresentsList borrowed.state.arena (motiveRef :: (caseRefs ++ [borrow]))
              (motive :: (cases ++ [.borrow value])) :=
            .cons (motiveRep.frame first.1)
              (represented_append (caseRep.frame first.1) (.cons first.2.2.2 .nil))
          have scanLength := represented_length caseRep
          have next := emit_refines children (op := .view true family cases.length)
            (by simp [Op.arity] <;> omega)
            (by simpa only [viewRow, scanLength] using success)
          simpa only [argumentTerm, viewTerm, viewRow, scanLength] using first.trans next

private inductive Arguments (arena : Arena) : List (ArgumentKind × Nat) → List (ArgumentKind × Term) → Prop
  | nil : Arguments arena [] []
  | cons : Represents arena ref term → Arguments arena refs terms →
      Arguments arena ((kind, ref) :: refs) ((kind, term) :: terms)

private theorem Arguments.frame (held : Arguments arena refs terms) (kept : Prefix arena after) :
    Arguments after refs terms := by
  induction held with
  | nil => exact .nil
  | cons first _ tail => exact .cons (first.frame kept) tail

private theorem Arguments.append (left : Arguments arena refs terms) (right : Arguments arena more values) :
    Arguments arena (refs ++ more) (terms ++ values) := by
  induction left with
  | nil => exact right
  | cons head _ tail => exact .cons head tail

private theorem represented_ordinary (held : RepresentsList arena refs terms) (shape : Shape) :
    Arguments arena (ordinary shape refs) (ordinary shape terms) := by
  induction shape generalizing refs terms with
  | nil => exact .nil
  | cons flags rest ih =>
      cases held with
      | nil => exact .nil
      | cons head tail => exact .cons head (ih tail)

private theorem represented_hypotheses (held : RepresentsList arena refs terms) (shape : Shape) (recursion : Bool) :
    Arguments arena (hypotheses recursion shape refs) (hypotheses recursion shape terms) := by
  cases recursion with
  | false => exact .nil
  | true =>
      induction shape generalizing refs terms with
      | nil => exact .nil
      | cons flags rest ih =>
          cases held with
          | nil => exact .nil
          | cons head tail =>
              cases owned : flags.2
              · simpa [hypotheses, owned] using ih tail
              · simpa [hypotheses, owned] using Arguments.cons (kind := .recursive) head (ih tail)

private theorem ordinary_terms (plans : List ViewFieldPlan) (values : List Term) :
    (ordinary (checkedShape plans) values).map (fun (kind, value) => argumentTerm family motive cases value kind) =
      viewArguments plans values := by
  induction plans generalizing values with
  | nil => rfl
  | cons plan plans ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases borrowed : plan.borrowed
          · simpa only [ordinary, checkedShape, viewArguments, List.map_cons, List.zip_cons_cons,
              borrowed, Bool.false_eq_true, ite_false, argumentTerm] using congrArg (value :: ·) (ih values)
          · simpa only [ordinary, checkedShape, viewArguments, List.map_cons, List.zip_cons_cons,
              borrowed, ite_true, argumentTerm] using congrArg (.borrow value :: ·) (ih values)

private theorem hypotheses_terms (plans : List ViewFieldPlan) (values : List Term) (recursion : Bool) :
    (hypotheses recursion (checkedShape plans) values).map (fun (kind, value) =>
      argumentTerm family motive cases value kind) = viewHypotheses recursion family motive cases plans values := by
  cases recursion with
  | false => rfl
  | true =>
      induction plans generalizing values with
      | nil => rfl
      | cons plan plans ih =>
          cases values with
          | nil => rfl
          | cons value values =>
              cases owned : plan.self
              · simpa only [hypotheses, checkedShape, viewHypotheses, List.map_cons, List.zip_cons_cons,
                  List.filterMap_cons, owned, Bool.false_eq_true, ite_false, ite_true] using ih values
              · simpa only [hypotheses, checkedShape, viewHypotheses, List.map_cons, List.zip_cons_cons,
                  List.filterMap_cons, owned, ite_true, argumentTerm] using
                  congrArg (viewTerm true family motive cases (.borrow value) :: ·) (ih values)

private theorem appendArguments_refines
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (branchRep : Represents state.arena branch branchTerm) (held : Arguments state.arena refs values)
    (success : (appendArguments family motiveRef caseRefs state branch refs).result = .ok ref) :
    Preserves state (appendArguments family motiveRef caseRefs state branch refs) ref
      (applications branchTerm (values.map fun (kind, value) => argumentTerm family motive cases value kind)) := by
  induction refs generalizing state branch branchTerm values with
  | nil =>
      cases held
      cases success
      exact ⟨.refl _, id, rfl, branchRep⟩
  | cons head rest ih =>
      obtain ⟨kind, field⟩ := head
      cases held with
      | cons fieldRep restRep =>
          simp only [appendArguments] at success ⊢
          generalize argument : emitArgument family motiveRef caseRefs state field kind = arg at success ⊢
          cases argResult : arg.result with
          | error reason => simp [thenVisit, argResult] at success
          | ok argRef =>
              simp only [thenVisit, argResult] at success ⊢
              have emitted : (emitArgument family motiveRef caseRefs state field kind).result = .ok argRef :=
                congrArg Outcome.result argument |>.trans argResult
              have first := emitArgument_refines motiveRep caseRep fieldRep emitted
              rw [argument] at first
              generalize applied : appendApplications arg.state branch [argRef] = app at success ⊢
              cases appResult : app.result with
              | error reason => simp [appResult] at success
              | ok callee =>
                  simp only [appResult] at success ⊢
                  have result : (appendApplications arg.state branch [argRef]).result = .ok callee :=
                    congrArg Outcome.result applied |>.trans appResult
                  have second := appendApplications_refines (branchRep.frame first.1)
                    (.cons first.2.2.2 .nil) result
                  rw [applied] at second
                  have combined := first.1.trans second.1
                  have last := ih (motiveRep.frame combined) (caseRep.frame combined) second.2.2.2
                    (restRep.frame combined) success
                  exact first.trans ((show Preserves arg.state app callee _ from second).trans last)

/-- The two ordered native loops build exactly the independent View reduct,
keep old graph rows, and charge no ticks beyond the earlier shape computation. -/
theorem buildSpine_refines
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (branchRep : Represents state.arena branchRef branch)
    (fieldsRep : RepresentsList state.arena fieldRefs values)
    (success : (buildSpine state recursion family motiveRef params caseRefs branchRef fieldRefs
      (checkedShape plans)).result = .ok root) :
    let built := buildSpine state recursion family motiveRef params caseRefs branchRef fieldRefs (checkedShape plans)
    Prefix state.arena built.state.arena ∧ (Backward state.arena → Backward built.state.arena) ∧
      built.state.steps = state.steps ∧ Represents built.state.arena root
        (viewBody recursion family params motive branch cases values plans) := by
  have retained := represented_drop fieldsRep params
  have held := (represented_ordinary retained (checkedShape plans)).append
    (represented_hypotheses retained (checkedShape plans) recursion)
  have result := appendArguments_refines motiveRep caseRep branchRep held success
  simpa only [Preserves, buildSpine, List.map_append, applications, List.foldl_append,
    ordinary_terms, hypotheses_terms, viewBody]
    using result

private theorem planned_length (planned : viewPlan env family fields = some plans) :
    plans.length = fields.length := by
  induction fields generalizing plans with
  | nil => cases planned; rfl
  | cons field rest ih =>
      simp only [viewPlan, List.mapM_cons] at planned
      obtain ⟨_, _, mappedTail⟩ := Option.bind_eq_some_iff.mp planned
      obtain ⟨_, tail, equals⟩ := Option.bind_eq_some_iff.mp mappedTail
      cases equals
      exact congrArg Nat.succ (ih tail)

/-- The flags returned by the earlier shape run match the independently
checked signature for this family and constructor. -/
def ShapeAgrees (env : Environment) (family constructor : Nat) (shape : Shape) : Prop :=
  ∀ {entry signature plans}, env.families[family]? = some entry →
    entry.signatures[constructor]? = some signature →
    viewPlan env family (signature.fields.drop entry.declaration.params) = some plans →
    shape = checkedShape plans

theorem checkedShape_agrees (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans) :
    ShapeAgrees env family constructor (checkedShape plans) := by
  intro _ _ _ actual actualSig actualPlan
  cases Option.some.inj (found.symm.trans actual)
  cases Option.some.inj (sig.symm.trans actualSig)
  exact congrArg checkedShape (Option.some.inj (planned.symm.trans actualPlan))

private theorem checked_layout
    (history : ScopedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env [] ctx true
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    ∃ entry signature branch plans, env.families[family]? = some entry ∧
      entry.boxed = true ∧ entry.signatures[constructor]? = some signature ∧
      cases.length = entry.signatures.length ∧ values.length = signature.fields.length ∧
      cases[constructor]? = some branch ∧ entry.declaration.params ≤ signature.fields.length ∧
      viewPlan env family (signature.fields.drop entry.declaration.params) = some plans := by
  open LoanTyping.FamilyIota in
  obtain ⟨entry, _, _, _, _, _, _, _, layout, found, _, boxed, _, _, scrutinee, _, generated, branches, _⟩ :=
    view_inputs typed
  obtain ⟨rfl, last⟩ := List.append_inj' (List.cons.inj layout).2 (by simp)
  obtain rfl := (List.cons.inj last).1
  have count := LoanTyping.FamilyIota.checked_generated_branch_count generated branches
  obtain ⟨_, owner, _⟩ := scrutinee.principalView
  obtain ⟨signature, branch, sig, fields, selected⟩ :=
    LoanTyping.FamilyIota.checked_constructor_selection history found owner count
  have parameters := (LoanTyping.FamilyIota.signature_metadata history found sig).2.2.1
  obtain ⟨_, _, generatedBranch⟩ := LoanTyping.FamilyIota.viewCaseTypes_get generated sig
  obtain ⟨plans, planned⟩ : ∃ plans,
      viewPlan env family (signature.fields.drop entry.declaration.params) = some plans := by
    unfold viewCaseType at generatedBranch
    split at generatedBranch
    · contradiction
    · exact ⟨_, (Option.bind_eq_some_iff.mp generatedBranch).choose_spec.1⟩
  exact ⟨entry, signature, branch, plans, found, boxed, sig, count, fields, selected, parameters, planned⟩

private theorem prepared_checked
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (sourceRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (aligned : ShapeAgrees env family constructor shape) :
    ∃ built : Outcome Nat, prepare env state recursion family motiveRef caseRefs scrutinee shape =
      ⟨built.state, built.result.map Selection.spine⟩ ∧
      ∀ root, built.result = .ok root →
        built.state.steps = state.steps ∧ Refines env state.arena built.state.arena root ctx
          (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type := by
  have admitted := ScopedProgram.History.ofLoanMixed history
  obtain ⟨entry, signature, branch, plans, found, boxed, sig, count, fields, selected, parameters, planned⟩ :=
    checked_layout admitted (typed.ghost [])
  have exactShape := aligned found sig planned
  subst shape
  have shapeLength : (checkedShape plans).length = signature.fields.length - entry.declaration.params := by
    simpa only [checkedShape, List.length_map, List.length_drop] using planned_length planned
  obtain ⟨branchRef, branchRead, branchRep⟩ := represented_get caseRep selected
  cases sourceRep with
  | node borrowRead _ operands =>
      cases operands with
      | cons ownerRep tail =>
          cases tail
          cases ownerRep with
          | @node _ _ refs _ ownerRead _ fieldsRep =>
              have fieldCount : refs.length = entry.declaration.params + (checkedShape plans).length := by
                rw [represented_length fieldsRep, fields, shapeLength]
                omega
              refine ⟨buildSpine state recursion family motiveRef entry.declaration.params caseRefs branchRef refs
                (checkedShape plans), prepare_known borrowRead ownerRead found branchRead boxed
                  ((represented_length caseRep).trans count) fieldCount, ?_⟩
              intro root success
              obtain ⟨kept, backward, clock, represented⟩ :=
                buildSpine_refines motiveRep caseRep branchRep fieldsRep success
              have step : FamilyIota.Root env (viewTerm recursion family motive cases
                  (.borrow (.node (.con family constructor values.length) values)))
                  (viewBody recursion family entry.declaration.params motive branch cases values plans) :=
                .view found boxed sig selected count fields parameters planned
              exact ⟨clock, kept, backward, _, represented, .old (.iota step),
                LoanTyping.FamilyIota.Root.preserves admitted step (typed.ghost [])⟩

/-- Given the agreed shape, checked inputs determine a genuine View
contraction at the exact source type. Spine construction consumes no ticks. -/
theorem prepare_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (sourceRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (aligned : ShapeAgrees env family constructor shape)
    (success : (prepare env state recursion family motiveRef caseRefs scrutinee shape).result = .ok (.spine root)) :
    let built := prepare env state recursion family motiveRef caseRefs scrutinee shape
    built.state.steps = state.steps ∧ Refines env state.arena built.state.arena root ctx
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type := by
  obtain ⟨built, computed, preserved⟩ := prepared_checked history motiveRep caseRep sourceRep typed aligned
  rw [computed] at success ⊢
  cases emitted : built.result with
  | error reason => simp [emitted, Except.map] at success
  | ok spine =>
      simp only [emitted, Except.map, Except.ok.injEq, Selection.spine.injEq] at success
      subst spine
      exact preserved _ emitted

/-- Compose the exact View spine with a visitor that preserves the supplied
result type, at the counter and arena left by spine construction. -/
theorem reenter_preserves
    (visit : State → Nat → Outcome Nat)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (sourceRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (aligned : ShapeAgrees env family constructor shape)
    (visitSound : ∀ {next root term output}, Represents next.arena root term →
      LoanTyping.HasType env [] ctx true term type → (visit next root).result = .ok output →
      Refines env next.arena (visit next root).state.arena output ctx term type)
    (success : (reenter visit (prepare env state recursion family motiveRef caseRefs scrutinee shape)).result =
      .ok (some selected)) :
    Refines env state.arena
      (reenter visit (prepare env state recursion family motiveRef caseRefs scrutinee shape)).state.arena selected ctx
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type := by
  obtain ⟨built, computed, preserved⟩ := prepared_checked history motiveRep caseRep sourceRep typed aligned
  simp only [computed, reenter] at success ⊢
  cases emitted : built.result with
  | error reason => simp [emitted, Except.map] at success
  | ok root =>
      simp only [emitted, Except.map] at success ⊢
      cases visited : (visit built.state root).result with
      | error reason => simp [visited] at success
      | ok result =>
          simp only [visited, Except.ok.injEq, Option.some.injEq] at success
          subst result
          obtain ⟨_, kept, backward, term, represented, contracted, termTyped⟩ := preserved _ emitted
          obtain ⟨later, laterBackward, residual, output, normalized, originalType⟩ :=
            visitSound represented termTyped visited
          exact ⟨kept.trans later, fun old => laterBackward (backward old), residual, output,
            contracted.trans normalized, originalType⟩

/-- The existing graph driver supplies the visitor proof for supported
reentry results. The exact original dependent View type is retained. -/
theorem run_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (motiveRep : Represents state.arena motiveRef motive)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (sourceRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (aligned : ShapeAgrees env family constructor shape)
    (success : (run env limit childDepth state recursion family motiveRef caseRefs scrutinee shape).result =
      .ok (some selected)) :
    Refines env state.arena
      (run env limit childDepth state recursion family motiveRef caseRefs scrutinee shape).state.arena selected ctx
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type := by
  apply reenter_preserves (runWithConditionals limit childDepth) history motiveRep caseRep sourceRep typed aligned ?_
    success
  intro _ _ _ _ represented termTyped reduced
  obtain ⟨kept, backward, residual, output, normalized, originalType⟩ :=
    NativeCorePureComputationNormal.runWithConditionals_preserves history.wellFormed represented termTyped reduced
  exact ⟨kept, backward, residual, output, normalized, originalType⟩

namespace Examples

private def box (n : Term) : Term := .node (.ind 0 1) [n]
private def declaration : FamilyDeclaration :=
  ⟨true, 1, 1, [.pi true .u64 (box (.var 0)),
    .pi true .u64 (.pi false (box (.var 0)) (.pi false (box (.var 1)) (box (.var 2))))], 0⟩
private def leafSignature : Signature := ⟨[⟨true, .u64, none⟩], [.var 0]⟩
private def forkSignature : Signature :=
  ⟨[⟨true, .u64, none⟩, ⟨false, box (.var 0), some [.var 0]⟩,
    ⟨false, box (.var 1), some [.var 1]⟩], [.var 2]⟩
private def entry : CheckedFamily := ⟨declaration, [leafSignature, forkSignature], true⟩
private def env : Environment := ⟨#[], #[entry]⟩
private def parameter : Term := .natural 3
private def ownerType : Term := .ref (box parameter)
private def motive : Term := .lam false ownerType .u64
private def branch : Term := .lam false ownerType (.lam false ownerType
  (.lam false .u64 (.lam false .u64 (.var 0))))
private def cases : List Term := [.natural 0, branch]
private def leaf : Term := .node (.con 0 0 1) [parameter]
private def fork : Term := .node (.con 0 1 3) [parameter, leaf, leaf]
private def source : Term := viewTerm true 0 motive cases (.borrow fork)
private def leafSource : Term := viewTerm true 0 motive cases (.borrow leaf)
private def shape : Shape := [(true, true), (true, true)]
private def forkPlan : List ViewFieldPlan :=
  [⟨⟨false, box (.var 0), some [.var 0]⟩, true, true⟩,
    ⟨⟨false, box (.var 1), some [.var 1]⟩, true, true⟩]

private def arena : Arena := #[.node (.natural 3) [], .node .u64 [], .node (.ind 0 1) [0],
  .node .ref [2], .node (.lam false) [3, 1], .node (.natural 0) [], .var 0, .node (.lam false) [1, 6],
  .node (.lam false) [1, 7], .node (.lam false) [3, 8], .node (.lam false) [3, 9],
  .node (.con 0 0 1) [0], .node (.con 0 0 1) [0], .node (.con 0 1 3) [0, 11, 12],
  .node .borrow [13], .node .borrow [11]]
private def state : State := ⟨arena, 3⟩
private theorem history : LoanTyping.MixedProgram.History [] [declaration] env :=
  LoanTyping.MixedProgram.checkProgram_sound
    (by cbv : LoanTyping.MixedProgram.checkProgram 64 128 [] [declaration] = some env)

private theorem motiveRep : Represents arena 4 motive := decode_sound (fuel := 16) (by cbv)
private theorem casesRep : RepresentsList arena [5, 10] cases :=
  .cons (decode_sound (fuel := 16) (by cbv)) (.cons (decode_sound (fuel := 16) (by cbv)) .nil)

/-- The first field borrows are distinct from the borrows supplied to the
recursive calls. Both own fields are visited in their checked signature order. -/
theorem checked_recursive_spine_uses_fresh_borrows :
    let built := prepare env state true 0 4 [5, 10] 14 shape
    built = ⟨⟨arena ++ #[.node .borrow [11], .node .app [10, 16], .node .borrow [12],
      .node .app [17, 18], .node .borrow [11], .node (.view true 0 2) [4, 5, 10, 20], .node .app [19, 21],
      .node .borrow [12], .node (.view true 0 2) [4, 5, 10, 23], .node .app [22, 24]], 3⟩,
      .ok (.spine 25)⟩ ∧
    Refines env arena built.state.arena 25 [] source (.app motive (.borrow fork)) := by
  have checked : LoanTyping.Checker.check 64 env [] [] true source (.app motive (.borrow fork)) = true := by cbv
  have typed := LoanTyping.Checker.check_sound checked
  have held : Represents arena 14 (.borrow fork) := decode_sound (fuel := 16) (by cbv)
  have aligned : ShapeAgrees env 0 1 shape :=
    checkedShape_agrees (env := env) (family := 0) (constructor := 1) (entry := entry)
      (signature := forkSignature) (plans := forkPlan) (by rfl) (by rfl) (by rfl)
  have computed : (prepare env state true 0 4 [5, 10] 14 shape).result = .ok (.spine 25) := by cbv
  exact ⟨by cbv, (prepare_preserves (constructor := 1) (values := [parameter, leaf, leaf])
    history motiveRep casesRep held typed aligned computed).2⟩

/-- A parameter-only constructor reenters the existing graph driver
with its original clock and retains the exact dependent motive application. -/
theorem checked_parameter_only_view_reenters :
    let evaluated := run env 64 16 state true 0 4 [5, 10] 15 []
    evaluated = ⟨⟨arena, 4⟩, .ok (some 5)⟩ ∧
      Refines env arena evaluated.state.arena 5 [] leafSource (.app motive (.borrow leaf)) := by
  have checked : LoanTyping.Checker.check 64 env [] [] true leafSource (.app motive (.borrow leaf)) = true := by cbv
  have typed := LoanTyping.Checker.check_sound checked
  have held : Represents arena 15 (.borrow leaf) := decode_sound (fuel := 16) (by cbv)
  have aligned : ShapeAgrees env 0 0 [] :=
    checkedShape_agrees (entry := entry) (signature := leafSignature) (plans := []) (by rfl) (by rfl) (by rfl)
  have computed : (run env 64 16 state true 0 4 [5, 10] 15 []).result = .ok (some 5) := by cbv
  exact ⟨by cbv, run_preserves (constructor := 0) (values := [parameter])
    history motiveRep casesRep held typed aligned computed⟩

end Examples

end Jihoo.NativeKernel.NativeCoreViewNormal
