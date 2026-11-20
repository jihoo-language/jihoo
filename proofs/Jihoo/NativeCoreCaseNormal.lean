import Jihoo.NativeCorePureComputationNormal
import Jihoo.NativeLoanMixedPreservation

/-! The pure known-constructor Case path after the motive, cases, and
scrutinee have normalized. Append each retained application before reentering
the recursive normalizer at the original child depth and shared counter. -/
namespace Jihoo.NativeKernel.NativeCoreCaseNormal

open NativeArena Environment NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome runWithConditionals)
open FamilyIota (caseTerm)

def appendApplications (state : State) (branch : Nat) : List Nat → Outcome Nat
  | [] => ⟨state, .ok branch⟩
  | field :: fields =>
      match addNode state.arena (.node .app [branch, field]) with
      | .error reason => ⟨state, .error (.add reason)⟩
      | .ok (arena, root) => appendApplications {state with arena} root fields

/-- The native fast path reads a known constructor and its selected case,
skips the leading parameters, and builds the spine. Other Case branches
lie outside this entry point. Checked graph/table lookup is explicit. -/
def run (env : Environment) (limit childDepth : Nat) (state : State)
    (family : Nat) (branches : List Nat) (scrutinee : Nat) : Outcome Nat :=
  match state.arena[scrutinee]? with
  | some (.node (.con actual constructor _) fields) =>
      if actual = family then
        match branches[constructor]?, env.families[family]? with
        | some branch, some entry =>
            let built := appendApplications state branch (fields.drop entry.declaration.params)
            match built.result with
            | .error reason => ⟨built.state, .error reason⟩
            | .ok root => runWithConditionals limit childDepth built.state root
        | _, _ => ⟨state, .error (.outsideFragment scrutinee)⟩
      else ⟨state, .error (.outsideFragment scrutinee)⟩
  | _ => ⟨state, .error (.outsideFragment scrutinee)⟩

/-- Even a fieldless branch reenters normal at the child depth. A failed
append returns its partial arena, without entering normal or charging ticks. -/
theorem run_known (read : state.arena[scrutinee]? = some (.node (.con family constructor arity) fields))
    (selected : branches[constructor]? = some branch) (found : env.families[family]? = some entry) :
    run env limit childDepth state family branches scrutinee =
      let built := appendApplications state branch (fields.drop entry.declaration.params)
      match built.result with
      | .error reason => ⟨built.state, .error reason⟩
      | .ok root => runWithConditionals limit childDepth built.state root := by
  simp only [run, read, selected, found, ite_true]

private theorem reference_bound (held : Represents arena ref term) : ref < arena.size := by
  cases held with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1

private theorem addApplication_refines
    (callee : Represents arena branch function) (arg : Represents arena field argument)
    (added : addNode arena (.node .app [branch, field]) = .ok (after, root)) :
    Prefix arena after ∧ Represents after root (.app function argument) ∧
      (Backward arena → Backward after) := by
  obtain ⟨kept, index, _, _, _, row⟩ := addNode_commits added
  refine ⟨kept, .node row rfl (.cons (callee.frame kept) (.cons (arg.frame kept) .nil)), ?_⟩
  intro backward
  apply addNode_preserves_backward backward added
  rw [index]
  intro child member
  simp only [Node.references, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · exact reference_bound callee
  · exact reference_bound arg

/-- The left-associated spine represents the exact family contraction,
keeps existing nodes and charges no normalization ticks. -/
theorem appendApplications_refines
    (chosen : Represents state.arena branch function)
    (fields : RepresentsList state.arena fieldRefs values)
    (success : (appendApplications state branch fieldRefs).result = .ok root) :
    let built := appendApplications state branch fieldRefs
    Prefix state.arena built.state.arena ∧ (Backward state.arena → Backward built.state.arena) ∧
      built.state.steps = state.steps ∧ Represents built.state.arena root (applications function values) := by
  induction fieldRefs generalizing state branch function values with
  | nil =>
      cases fields
      cases success
      exact ⟨.refl _, fun checked => checked, rfl, chosen⟩
  | cons field rest ih =>
      cases fields with
      | cons represented tail =>
          cases added : addNode state.arena (.node .app [branch, field]) with
          | error reason => simp [appendApplications, added] at success
          | ok result =>
              obtain ⟨arena, fresh⟩ := result
              simp only [appendApplications, added] at success ⊢
              obtain ⟨first, applied, checked⟩ := addApplication_refines chosen represented added
              obtain ⟨later, laterChecked, clock, output⟩ :=
                ih (state := {state with arena}) applied (tail.frame first) success
              exact ⟨first.trans later, fun old => laterChecked (checked old), clock, output⟩

/-- Each successful append commits immediately. Exhaustion leaves exactly
the prefix that fit in the arena and leaves the input counter unchanged. -/
theorem appendApplications_progress (state : State) (branch : Nat) (fields : List Nat) :
    let built := appendApplications state branch fields
    Prefix state.arena built.state.arena ∧ built.state.steps = state.steps ∧
      built.state.arena.size = state.arena.size + min fields.length (entryLimit - state.arena.size) ∧
      (built.result = .error (.add .termLimit) ↔ entryLimit - state.arena.size < fields.length) := by
  induction fields generalizing state branch with
  | nil =>
      refine ⟨.refl _, rfl, ?_, ?_⟩
      · simp [appendApplications]
      · simp [appendApplications]
  | cons field rest ih =>
      by_cases room : state.arena.size < entryLimit
      · let row := Node.node .app [branch, field]
        let arena := state.arena.push row
        have added : addNode state.arena (.node .app [branch, field]) = .ok (arena, state.arena.size) := by
          simp only [addNode, room, ite_true, allocate, arena, row]
        simp only [appendApplications, added]
        obtain ⟨kept, ticks, size, failed⟩ := ih {state with arena} state.arena.size
        have pushed : arena.size = state.arena.size + 1 := by simp [arena]
        refine ⟨(Prefix.push _ _).trans kept, ticks, ?_, ?_⟩
        · rw [size, pushed]
          simp only [List.length_cons]
          omega
        · rw [failed, pushed]
          simp only [List.length_cons]
          omega
      · have full : entryLimit - state.arena.size = 0 := by omega
        simp [appendApplications, addNode, room, full, Prefix.refl]

theorem represented_get {index : Nat} (held : RepresentsList arena refs terms)
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

theorem represented_drop (held : RepresentsList arena refs terms) (count : Nat) :
    RepresentsList arena (refs.drop count) (terms.drop count) := by
  induction count generalizing refs terms with
  | zero => exact held
  | succ count ih =>
      cases held with
      | nil => exact .nil
      | cons head tail => exact ih tail

structure Refines (env : Environment) (before after : Arena) (root : Nat) (ctx : Context)
    (input type : Term) : Prop where
  frame : Prefix before after
  backward : Backward before → Backward after
  result : ∃ residual, Represents after root residual ∧ RawLend.Forward env input residual ∧
    LoanTyping.HasType env [] ctx true residual type

/-- Aligned checked metadata identifies exactly the source Case contraction
that the graph realizes. The existing recursive driver then preserves the
original type through reentry, sharing its depth and counter. -/
theorem run_aligned_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (isData : entry.declaration.data = true)
    (sigFound : entry.signatures[constructor]? = some signature)
    (caseCount : cases.length = entry.signatures.length)
    (fieldCount : values.length = signature.fields.length) (branchFound : cases[constructor]? = some branch)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type)
    (success : (run env limit childDepth state family caseRefs scrutinee).result = .ok selected) :
    Refines env state.arena (run env limit childDepth state family caseRefs scrutinee).state.arena selected ctx
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  have root : FamilyIota.Root env (caseTerm family motive cases (.node (.con family constructor values.length) values))
      (applications branch (values.drop entry.declaration.params)) :=
    .caseOf found isData sigFound branchFound caseCount fieldCount
  have iota : RawLend.Forward env (caseTerm family motive cases (.node (.con family constructor values.length) values))
      (applications branch (values.drop entry.declaration.params)) :=
    .old (.iota root)
  have typedSpine := history.family_contract_preserves root.complete (typed.ghost [])
  obtain ⟨branchRef, branchRead, branchRep⟩ := represented_get caseRep branchFound
  cases valueRep with
  | node read arity fieldsRep =>
      rename_i fieldRefs
      rw [run_known read branchRead found] at success ⊢
      generalize construction : appendApplications state branchRef
        (fieldRefs.drop entry.declaration.params) = built at success ⊢
      cases emitted : built.result with
      | error reason => simp [emitted] at success
      | ok spine =>
          simp only [emitted] at success ⊢
          have made : (appendApplications state branchRef (fieldRefs.drop entry.declaration.params)).result = .ok spine := by
            rw [construction, emitted]
          have actual := appendApplications_refines branchRep (represented_drop fieldsRep _) made
          rw [construction] at actual
          obtain ⟨kept, checked, _, represented⟩ := actual
          obtain ⟨later, laterChecked, residual, output, normalization, originalType⟩ :=
            NativeCorePureComputationNormal.runWithConditionals_preserves history.wellFormed represented typedSpine success
          exact ⟨kept.trans later, fun before => laterChecked (checked before), residual, output,
            iota.trans normalization, originalType⟩

/-- Loan64 typing and the authentic mixed history determine the family,
signature and both vector lengths used by the independent contraction. -/
theorem run_preserves
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (caseRep : RepresentsList state.arena caseRefs cases)
    (valueRep : Represents state.arena scrutinee (.node (.con family constructor values.length) values))
    (typed : LoanTyping.HasType env loans ctx mode
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type)
    (success : (run env limit childDepth state family caseRefs scrutinee).result = .ok selected) :
    Refines env state.arena (run env limit childDepth state family caseRefs scrutinee).state.arena selected ctx
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type := by
  obtain ⟨_, _, _, found, isData, sigFound, caseCount, fieldCount, branchFound⟩ :=
    LoanTyping.FamilyIota.checked_case_alignment (ScopedProgram.History.ofLoanMixed history) (typed.ghost [])
  exact run_aligned_preserves history found isData sigFound caseCount fieldCount branchFound caseRep valueRep typed success

namespace Examples

private def box (n : Term) : Term := .node (.ind 0 1) [n]
private def declaration : FamilyDeclaration :=
  ⟨true, 1, 1, [.pi true .u64 (.pi false (.buffer (.var 0)) (box (.var 1)))], 0⟩
private def signature : Signature := ⟨[⟨true, .u64, none⟩, ⟨false, .buffer (.var 0), none⟩], [.var 1]⟩
private def entry : CheckedFamily := ⟨declaration, [signature], true⟩
private def env : Environment := ⟨#[], #[entry]⟩

private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def motive : Term := .lam false (box (.natural 2)) (.buffer (.natural 2))
private def branch : Term := .lam false (.buffer (.natural 2)) (.var 0)
private def constructor : Term := .node (.con 0 0 2) [.natural 2, allocation]
private def source : Term := caseTerm 0 motive [branch] constructor
private def resultType : Term := .buffer (.uadd (.natural 1) (.natural 1))

private def arena : Arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
  .node (.ind 0 1) [0], .node .buffer [0], .node (.lam false) [3, 4], .var 0,
  .node (.lam false) [4, 6], .node (.con 0 0 2) [0, 2]]
private def state : State := ⟨arena, 0⟩
private def result : Outcome Nat := run env 64 16 state 0 [7] 8

private theorem history : LoanTyping.MixedProgram.History [] [declaration] env :=
  LoanTyping.MixedProgram.checkProgram_sound
    (by cbv : LoanTyping.MixedProgram.checkProgram 48 96 [] [declaration] = some env)

private theorem value_rep : Represents arena 8 constructor :=
  .node rfl rfl (.cons (.node rfl rfl .nil)
    (.cons (.node rfl rfl (.cons (.node rfl rfl .nil) (.cons (.node rfl rfl .nil) .nil))) .nil))

private theorem branch_rep : RepresentsList arena [7] [branch] :=
  .cons (.node rfl rfl (.cons (.node rfl rfl (.cons (.node rfl rfl .nil) .nil)) (.cons (.var rfl) .nil))) .nil

/-- The authentic installed family has one erased parameter and one runtime
field whose buffer size depends on it. The graph appends only the application
to the dependent field, reenters beta, and returns the original Buffer at
its converted requested index. -/
theorem checked_parameter_case_returns_buffer :
    result.result = .ok 2 ∧ result.state.arena = arena.push (.node .app [7, 2]) ∧
      Refines env arena result.state.arena 2 [] source resultType := by
  have accepted : LoanTyping.Checker.check 48 env [] [] true source resultType = true := by cbv
  have succeeded : result.result = .ok 2 := by cbv
  refine ⟨succeeded, by cbv, ?_⟩
  have admitted : LoanTyping.HasType env [] [] true source resultType := LoanTyping.Checker.check_sound accepted
  exact run_preserves (constructor := 0) (values := [.natural 2, allocation]) (motive := motive)
    history branch_rep value_rep admitted succeeded

/-- Appending the application commits before the first reentry tick.
The exhausted counter rejects on the new reference and retains the append. -/
theorem reentry_step_limit_keeps_spine :
    run env 64 16 ⟨arena, 64⟩ 0 [7] 8 =
      ⟨⟨arena.push (.node .app [7, 2]), 65⟩, .error (.tick (.stepLimit 9))⟩ := by
  cbv

end Examples

end Jihoo.NativeKernel.NativeCoreCaseNormal
