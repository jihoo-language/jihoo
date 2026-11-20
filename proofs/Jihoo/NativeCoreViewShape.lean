import Jihoo.NativeCoreViewNormal

/-! The known-owner View reads the stored constructor telescope anew. It
skips parameter Pis without normalizing their domains, visits each retained
domain at the common child depth, and reads heap flags from the resulting row. -/
namespace Jihoo.NativeKernel.NativeCoreViewShape

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress runWithConditionals)
open NativeCoreViewNormal (Shape checkedShape ShapeAgrees checkedShape_agrees prepare reenter)
open NativeCoreCaseNormal (Refines)
open FamilyIota (viewTerm)

def piAt (arena : Arena) (cursor : Nat) : Option (Bool × Nat × Nat) :=
  match arena[cursor]? with
  | some (.node (.pi erased) [domain, rest]) => some (erased, domain, rest)
  | _ => none

def skipParameters (arena : Arena) : Nat → Nat → Nat
  | 0, cursor => cursor
  | n + 1, cursor =>
      match piAt arena cursor with
      | none => cursor
      | some (_, _, rest) => skipParameters arena n rest

/-- Native classification on the normalized domain's head. In particular,
an erased field never receives a borrow, even if its domain is a heap type. -/
def classify (env : Environment) (family : Nat) (erased : Bool) (domain : Node) : Bool × Bool :=
  if erased then (false, false) else
    match domain with
    | .node .buffer _ => (true, false)
    | .node (.ind observed _) _ =>
        if observed = family then (true, true)
        else (((env.families[observed]?).map CheckedFamily.boxed).getD false, false)
    | _ => (false, false)

/-- One live normalization call per retained Pi. Its final arena and
counter are passed to the next call, or reported at the first error.
The cursor check bounds recursion on malformed, non-backward graphs. -/
def readFields (env : Environment) (family : Nat) (visit : State → Nat → Outcome Nat)
    (state : State) (cursor : Nat) : Outcome Shape :=
  match piAt state.arena cursor with
  | none => ⟨state, .ok []⟩
  | some (erased, domain, rest) =>
      if rest < cursor then
        (visit state domain).next fun next ref =>
            match next.arena[ref]? with
            | none => ⟨next, .error (.outsideFragment ref)⟩
            | some row =>
                let scanned := readFields env family visit next rest
                ⟨scanned.state, scanned.result.map (classify env family erased row :: ·)⟩
      else ⟨state, .error (.outsideFragment cursor)⟩
termination_by cursor

def run (env : Environment) (family : Nat) (visit : State → Nat → Outcome Nat)
    (state : State) (params typeRoot : Nat) : Outcome Shape :=
  readFields env family visit state (skipParameters state.arena params typeRoot)

private theorem readFields_progress (metered : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (cursor : Nat) :
    Progress limit state (readFields env family visit state cursor) := by
  induction cursor using Nat.strongRecOn generalizing state with
  | ind cursor ih =>
      rw [readFields]
      cases found : piAt state.arena cursor with
      | none => exact Progress.atState _ _
      | some triple =>
          obtain ⟨erased, domain, rest⟩ := triple
          simp only
          by_cases earlier : rest < cursor
          · rw [ite_eq_left earlier]
            apply (metered state domain).next
            intro ref
            split
            · exact Progress.atState _ _
            · exact (ih rest earlier _).map _
          · rw [ite_eq_right earlier]
            exact Progress.atState _ _

theorem run_progress (metered : ∀ state ref, Progress limit state (visit state ref))
    (state : State) (params typeRoot : Nat) :
    Progress limit state (run env family visit state params typeRoot) :=
  readFields_progress metered state _

private theorem pi_children (represented : Represents arena root term)
    (found : piAt arena root = some (erased, domain, rest)) :
    ∃ A B, Represents arena domain A ∧ Represents arena rest B := by
  cases represented with
  | var read => simp [piAt, read] at found
  | @node _ op refs terms read arity children =>
      cases op <;> try solve | simp [piAt, read] at found
      case pi flag =>
        cases children with
        | nil => cases arity
        | cons first remaining =>
            cases remaining with
            | nil => cases arity
            | cons second tail =>
                cases tail with
                | cons => cases arity
                | nil =>
                    have exactRefs := Option.some.inj (show some (_, _, _) = some (erased, domain, rest) from
                      by simpa only [piAt, read] using found)
                    cases exactRefs
                    exact ⟨_, _, first, second⟩

private theorem skip_represented (represented : Represents arena root term) (params : Nat) :
    ∃ residual, Represents arena (skipParameters arena params root) residual := by
  induction params generalizing root term with
  | zero => exact ⟨_, represented⟩
  | succ params ih =>
      cases found : piAt arena root with
      | none => exact ⟨term, by simpa only [skipParameters, found] using represented⟩
      | some triple =>
          obtain ⟨erased, domain, rest⟩ := triple
          obtain ⟨_, _, _, body⟩ := pi_children represented found
          simpa only [skipParameters, found] using ih body

private theorem readFields_frames
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      NativeCorePureComputationNormal.Refines env state term (visit state ref) selected)
    (source : Represents state.arena cursor term)
    (success : (readFields env family visit state cursor).result = .ok shape) :
    let after := (readFields env family visit state cursor).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) := by
  induction cursor using Nat.strongRecOn generalizing state term shape with
  | ind cursor ih =>
      cases found : piAt state.arena cursor with
      | none =>
          rw [readFields, found]
          exact ⟨.refl _, id⟩
      | some triple =>
          obtain ⟨erased, domain, rest⟩ := triple
          by_cases earlier : rest < cursor
          · rw [readFields, found] at success ⊢
            simp only [ite_eq_left earlier] at success ⊢
            obtain ⟨_, _, domainRep, restRep⟩ := pi_children source found
            obtain ⟨ref, returned, done⟩ := Outcome.next_success success
            rw [done] at success ⊢
            cases lookup : (visit state domain).state.arena[ref]? with
            | none => simp [lookup] at success
            | some row =>
                simp only [lookup] at success ⊢
                have first := visitor domainRep returned
                cases scanned : (readFields env family visit (visit state domain).state rest).result with
                | error reason => simp [scanned, Except.map] at success
                | ok flags =>
                    obtain ⟨later, backward⟩ := ih rest earlier (restRep.frame first.kept) scanned
                    exact ⟨first.kept.trans later, fun old => backward (first.backward old)⟩
          · rw [readFields, found] at success
            simp only [ite_eq_right earlier] at success
            cases success

/-- A represented constructor telescope supplies each live visitor with its
actual domain representation. No computed flag can invalidate old edges. -/
theorem run_frames
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      NativeCorePureComputationNormal.Refines env state term (visit state ref) selected)
    (source : Represents state.arena typeRoot type)
    (success : (run env family visit state params typeRoot).result = .ok shape) :
    let after := (run env family visit state params typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) := by
  obtain ⟨_, remaining⟩ := skip_represented source params
  exact readFields_frames visitor remaining success

/-- A raw Pi whose edge lies in a well-formed backward graph always passes
the traversal's decreasing-cursor guard. -/
theorem pi_tail_backward {cursor domain rest : Nat} (backward : Backward arena)
    (found : arena[cursor]? = some (.node (.pi erased) [domain, rest])) : rest < cursor :=
  backward cursor _ found rest (by simp [Node.references])

private theorem classify_plan
    (represented : Represents arena root field.domain)
    (planned : viewFieldPlan env family field = some plan) :
    ∃ row, arena[root]? = some row ∧ classify env family field.erased row = (plan.borrowed, plan.self) := by
  cases field with
  | mk erased domain recursive =>
      cases erased with
      | true =>
          change (some ⟨⟨true, domain, recursive⟩, false, false⟩ : Option ViewFieldPlan) = some plan at planned
          cases planned
          cases represented with
          | var found | node found => exact ⟨_, found, rfl⟩
      | false =>
          cases represented with
          | var found => simp [viewFieldPlan] at planned
          | @node _ op refs terms found arity children =>
              cases op <;> simp [viewFieldPlan] at planned
              case ind =>
                rename_i observed count
                by_cases own : observed = family
                · simp only [own, ite_true, Option.some.injEq] at planned
                  cases planned
                  exact ⟨_, found, by simp [classify, own]⟩
                · simp only [own, ite_false] at planned
                  cases lookup : env.families[observed]? with
                  | none => simp [lookup] at planned
                  | some entry =>
                      simp only [lookup, Option.map_some, Option.some.injEq] at planned
                      cases planned
                      exact ⟨_, found, by simp [classify, own, lookup]⟩
              all_goals
                cases terms with
                | nil => simp at planned <;> cases planned <;> exact ⟨_, found, rfl⟩
                | cons head tail =>
                    cases tail <;> simp at planned
                    all_goals cases planned <;> exact ⟨_, found, rfl⟩

/-- Evidence relating successful *live domain visits* to the canonical
checked signature. The raw domain reference and the normalized field term
are distinct, and every step carries the visitor's actual resulting state. -/
inductive CheckedVisits (visit : State → Nat → Outcome Nat) : State → Nat → List Field → State → Prop
  | done : piAt state.arena cursor = none → CheckedVisits visit state cursor [] state
  | step : piAt state.arena cursor = some (field.erased, domain, rest) → rest < cursor →
      (visit state domain).result = .ok normalized →
      Represents (visit state domain).state.arena normalized field.domain →
      CheckedVisits visit (visit state domain).state rest fields after →
      CheckedVisits visit state cursor (field :: fields) after

private theorem readFields_checked
    (visited : CheckedVisits visit state cursor fields after)
    (planned : viewPlan env family fields = some plans) :
    readFields env family visit state cursor = ⟨after, .ok (checkedShape plans)⟩ := by
  induction visited generalizing plans with
  | done found =>
      cases planned
      rw [readFields, found]
      rfl
  | step found older returned represented tail ih =>
      simp only [viewPlan, List.mapM_cons] at planned
      obtain ⟨_, plannedField, remainder⟩ := Option.bind_eq_some_iff.mp planned
      obtain ⟨_, plannedFields, equals⟩ := Option.bind_eq_some_iff.mp remainder
      cases equals
      obtain ⟨_, normalRow, flags⟩ := classify_plan represented plannedField
      rw [readFields, found]
      simp only [older, ↓reduceIte, Outcome.next, returned, normalRow, ih plannedFields, flags]
      rfl

/-- When the graph's live visits compute the authenticated canonical
domains, the shape read from their rows is exactly the independent plan.
The conclusion retains the same arena and clock produced by the visits. -/
theorem run_checked
    (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (visited : CheckedVisits visit state (skipParameters state.arena entry.declaration.params typeRoot)
      (signature.fields.drop entry.declaration.params) after)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans) :
    run env family visit state entry.declaration.params typeRoot = ⟨after, .ok (checkedShape plans)⟩ ∧
      ShapeAgrees env family constructor (checkedShape plans) :=
  ⟨readFields_checked visited planned, checkedShape_agrees found sig planned⟩

theorem CheckedVisits.frame
    (visited : CheckedVisits visit state cursor fields after)
    (visitFrame : ∀ before root, Prefix before.arena (visit before root).state.arena ∧
      (Backward before.arena → Backward (visit before root).state.arena)) :
    Prefix state.arena after.arena ∧ (Backward state.arena → Backward after.arena) := by
  induction visited with
  | done => exact ⟨.refl _, id⟩
  | step _ _ _ _ _ ih =>
      exact ⟨(visitFrame _ _).1.trans ih.1, fun checked => ih.2 ((visitFrame _ _).2 checked)⟩

/-- After the boxed known-owner guard has supplied the raw type root,
the shape traversal runs before the field-count guard and spine emission.
The same child visitor handles normalization of both domains and the spine. -/
def runWithShape (env : Environment) (visit : State → Nat → Outcome Nat) (state : State)
    (recursion : Bool) (family motive params typeRoot : Nat)
    (cases : List Nat) (scrutinee : Nat) : Outcome (Option Nat) :=
  let scanned := run env family visit state params typeRoot
  match scanned.result with
  | .error reason => ⟨scanned.state, .error reason⟩
  | .ok shape => reenter visit (prepare env scanned.state recursion family motive cases scrutinee shape)

/-- Even a failing visit may already have committed graph rows and paid
ticks; the caller receives that exact outcome without allocating a spine. -/
theorem runWithShape_stops_on_error
    (failed : (run env family visit state params typeRoot).result = .error reason) :
    runWithShape env visit state recursion family motive params typeRoot cases scrutinee =
      ⟨(run env family visit state params typeRoot).state, .error reason⟩ := by
  simp only [runWithShape, failed]

/-- Authentic checked metadata and the live canonical-domain visits compose
with the known-owner View contraction and reentry at the original type. -/
theorem runWithShape_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (visited : CheckedVisits visit state (skipParameters state.arena entry.declaration.params typeRoot)
      (signature.fields.drop entry.declaration.params) after)
    (motiveRep : Represents state.arena motiveRef motive)
    (casesRep : RepresentsList state.arena caseRefs cases)
    (scrutineeRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (shapeFrame : Prefix state.arena after.arena)
    (shapeBackward : Backward state.arena → Backward after.arena)
    (visitSound : ∀ {next root term output}, Represents next.arena root term →
      LoanTyping.HasType env [] ctx true term type → (visit next root).result = .ok output →
      Refines env next.arena (visit next root).state.arena output ctx term type)
    (success : (runWithShape env visit state recursion family motiveRef entry.declaration.params
      typeRoot caseRefs scrutinee).result = .ok (some selected)) :
    Refines env state.arena
      (runWithShape env visit state recursion family motiveRef entry.declaration.params
        typeRoot caseRefs scrutinee).state.arena selected ctx
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type := by
  obtain ⟨scanned, aligned⟩ := run_checked found sig visited planned
  simp only [runWithShape, scanned] at success ⊢
  obtain ⟨later, laterBackward, residual, represented, reduced, resultTyped⟩ :=
    NativeCoreViewNormal.reenter_preserves visit history (motiveRep.frame shapeFrame) (casesRep.frame shapeFrame)
      (scrutineeRep.frame shapeFrame) typed aligned visitSound success
  exact ⟨shapeFrame.trans later, fun old => laterBackward (shapeBackward old), residual, represented, reduced, resultTyped⟩

namespace Examples

private def arena : Arena := #[.node .u64 [], .var 0, .node .buffer [1], .node (.ind 0 1) [1],
  .node (.pi false) [3, 3], .node (.pi false) [2, 4], .node (.pi true) [2, 5], .node (.pi true) [0, 6]]

private def erasedField : Field := ⟨true, .buffer (.var 0), none⟩
private def bufferField : Field := ⟨false, .buffer (.var 0), none⟩
private def ownedField : Field := ⟨false, .node (.ind 0 1) [.var 0], some [.var 0]⟩

/-- Skipping the leading Pi does not visit its domain. The remaining
domains are visited even for the erased Buffer. The shape distinguishes
an erased heap field, a borrowed Buffer, and an owned recursive field. -/
theorem exact_visits_share_clock :
    run Environment.empty 0 (runWithConditionals 32 8) ⟨arena, 2⟩ 1 7 =
      ⟨⟨arena, 8⟩, .ok [(false, false), (true, false), (true, true)]⟩ := by
  have fields : CheckedVisits (runWithConditionals 32 8) ⟨arena, 2⟩ 6 [erasedField, bufferField, ownedField]
      ⟨arena, 8⟩ := by
    apply CheckedVisits.step (domain := 2) (rest := 5) (normalized := 2) rfl (by decide) (by cbv)
      (decode_sound (fuel := 8) (by cbv))
    apply CheckedVisits.step (domain := 2) (rest := 4) (normalized := 2) rfl (by decide) (by cbv)
      (decode_sound (fuel := 8) (by cbv))
    apply CheckedVisits.step (domain := 3) (rest := 3) (normalized := 3) rfl (by decide) (by cbv)
      (decode_sound (fuel := 8) (by cbv))
    exact .done rfl
  exact readFields_checked (env := Environment.empty) (family := 0)
    (plans := [⟨erasedField, false, false⟩, ⟨bufferField, true, false⟩, ⟨ownedField, true, true⟩]) fields rfl

end Examples

namespace CheckedExamples

private def box : Term := .node (.ind 0 0) []
private def scalarConstructor : Term := .pi false .u64 box
private def declaration : FamilyDeclaration := ⟨true, 0, 0, [scalarConstructor, .pi false box box], 0⟩
private def scalar : Field := ⟨false, .u64, none⟩
private def signature : Signature := ⟨[scalar], []⟩
private def entry : CheckedFamily :=
  ⟨declaration, [signature, ⟨[⟨false, box, some []⟩], []⟩], true⟩
private def env : Environment := ⟨#[], #[entry]⟩
private def owner : Term := .node (.con 0 0 1) [.natural 7]
private def cases : List Term := [.lam false .u64 (.var 0), .lam false (.ref box) (.natural 0)]
private def source : Term := viewTerm false 0 .u64 cases (.borrow owner)
private def arena : Arena := #[.node .u64 [], .node (.ind 0 0) [], .node (.pi false) [0, 1],
  .node (.natural 7) [], .node (.con 0 0 1) [3], .node .borrow [4], .var 0, .node (.lam false) [0, 6],
  .node .ref [1], .node (.natural 0) [], .node (.lam false) [8, 9]]
private def state : State := ⟨arena, 2⟩
private def visit := runWithConditionals 64 16

/-- A mixed-checker-admitted boxed family drives both the raw telescope
walk and the resulting scalar application. The single domain visit and
the subsequent beta contraction use the same counter. -/
theorem checked_scalar_shape_and_view_reenter :
    let output := runWithShape env visit state false 0 0 entry.declaration.params 2 [7, 10] 5
    declaration.constructors[0]? = some scalarConstructor ∧ Represents arena 2 scalarConstructor ∧
      output = ⟨⟨arena.push (.node .app [7, 3]), 11⟩, .ok (some 3)⟩ ∧
      Refines env arena output.state.arena 3 [] source .u64 := by
  have history : LoanTyping.MixedProgram.History [] [declaration] env :=
    LoanTyping.MixedProgram.checkProgram_sound
      (by cbv : LoanTyping.MixedProgram.checkProgram 48 96 [] [declaration] = some env)
  have accepted : LoanTyping.Checker.check 48 env [] [] true source .u64 = true := by cbv
  have stored : Represents arena 2 scalarConstructor := decode_sound (fuel := 8) (by cbv)
  have motiveRep : Represents arena 0 .u64 := decode_sound (fuel := 8) (by cbv)
  have casesRep : RepresentsList arena [7, 10] cases :=
    .cons (decode_sound (fuel := 8) (by cbv)) (.cons (decode_sound (fuel := 8) (by cbv)) .nil)
  have sourceRep : Represents arena 5 (.borrow owner) := decode_sound (fuel := 8) (by cbv)
  have found : env.families[0]? = some entry := rfl
  have sig : entry.signatures[0]? = some signature := rfl
  have planned : viewPlan env 0 signature.fields = some [⟨scalar, false, false⟩] := rfl
  have reads : CheckedVisits visit state (skipParameters arena 0 2) signature.fields ⟨arena, 3⟩ := by
    exact .step (domain := 0) (rest := 1) (normalized := 0) rfl (by decide) (by cbv)
      (decode_sound (fuel := 8) (by cbv)) (.done rfl)
  have scanned := (run_checked (typeRoot := 2) found sig reads planned).1
  have evaluated : runWithShape env visit state false 0 0 entry.declaration.params 2 [7, 10] 5 =
      ⟨⟨arena.push (.node .app [7, 3]), 11⟩, .ok (some 3)⟩ := by
    simp only [runWithShape, scanned]
    cbv
  refine ⟨rfl, stored, evaluated, ?_⟩
  apply runWithShape_preserves (constructor := 0) (values := [.natural 7])
    history found sig planned reads motiveRep casesRep sourceRep (LoanTyping.Checker.check_sound accepted)
    (.refl _) id ?_ (by rw [evaluated])
  intro _ _ _ _ input typed success
  obtain ⟨kept, backward, residual, represented, reduced, resultTyped⟩ :=
    NativeCorePureComputationNormal.runWithConditionals_preserves history.wellFormed input typed success
  exact ⟨kept, backward, residual, represented, reduced, resultTyped⟩

end CheckedExamples
end Jihoo.NativeKernel.NativeCoreViewShape
