import Jihoo.NativeCoreGhostSpineInference

/-! Code-mode inference for local variables, scalar values and sort heads.
An erased variable is rejected immediately after the entry tick. A relevant
variable retains the live graph shift of its written pre-binder annotation. -/
namespace Jihoo.NativeKernel.NativeCoreCodeHeadInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreGhostSpineInference (GraphBinding ContextRep Infer Inferred RetainedComparisons)
open EnvironmentDelta (expand expandArgs)

structure Refines (env : Environment) (arena : Arena) (ctx : Context) (source : Term)
    (outcome : Outcome Inferred) (answer : Inferred) : Prop where
  kept : Prefix arena outcome.state.arena
  backward : Backward arena → Backward outcome.state.arena
  inferred : ∃ type, Represents outcome.state.arena answer.typeRoot type ∧
    LoanTyping.HasType env [] ctx false (expand env source) (expand env type)

def Sound (env : Environment) (base : Arena) (ctx : Context) (limit : Nat) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final →
    RetainedComparisons final answer → Refines env state.arena ctx term (visit state root) answer

private def plain (root : Nat) : Inferred := ⟨root,[]⟩

private def reject (state : State) (root : Nat) : Outcome Inferred := ⟨state,.error (.outsideFragment root)⟩

private def shifted (limit depth : Nat) (state : State) (root amount : Nat) : Outcome Nat :=
  let result := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨result.state,result.result.mapError .substitution⟩

private def inferred (root : Outcome Nat) : Outcome Inferred := ⟨root.state,root.result.map plain⟩

private def afterEntry (limit remaining : Nat) (rows : List GraphBinding) (state : State) (root : Nat) : Outcome Inferred :=
  let emit := fun op => inferred (append state op [])
  match state.arena[root]? with
  | some (.var index) =>
    match rows[index]? with
    | some row => if row.erased then reject state root else inferred (shifted limit remaining state row.typeRoot (index+1))
    | none => reject state root
  | some (.node (.universe level) []) => if level < 32 then emit (.universe (level+1)) else reject state root
  | some (.node .prop []) | some (.node .u64 []) | some (.node .i64 []) => emit (.universe 0)
  | some (.node (.natural word) []) => if word < 2^64 then emit .u64 else reject state root
  | some (.node (.integer word) []) => if -(2^63 : Int) ≤ word ∧ word < 2^63 then emit .i64 else reject state root
  | _ => reject state root

def run (limit depth : Nat) (rows : List GraphBinding) (state : State) (root : Nat) : Outcome Inferred :=
  let (paid,steps) := NativeCoreUnsignedCancellation.tick state.arena limit depth state.steps root
  let paidState := {state with steps}
  match paid with
  | .error reason => ⟨paidState,.error (.tick reason)⟩
  | .ok () => afterEntry limit (depth-1) rows paidState root

private theorem inferred_answer (checked : (inferred outcome).result = .ok answer) :
    ∃ root, outcome.result = .ok root ∧ answer = plain root := by
  cases found : outcome.result <;> simp [inferred,found,Except.map] at checked
  exact ⟨_,rfl,checked.symm⟩

private theorem shift_answer (checked : (shifted limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shifted at checked
  cases read : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [read,Except.mapError,reduceCtorEq,Except.ok.injEq] at checked ⊢
  exact checked

private theorem shifted_progress : Progress limit state (shifted limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ checked =>
    progress.accepted room _ (shift_answer checked)⟩

private theorem afterEntry_progress : Progress limit state (afterEntry limit depth rows state root) := by
  unfold afterEntry
  split
  · split
    · split
      · exact Progress.atState _ _
      · exact shifted_progress.map plain
    · exact Progress.atState _ _
  · split
    · exact (append_progress _ _ _).map plain
    · exact Progress.atState _ _
  · exact (append_progress _ _ _).map plain
  · exact (append_progress _ _ _).map plain
  · exact (append_progress _ _ _).map plain
  · split
    · exact (append_progress _ _ _).map plain
    · exact Progress.atState _ _
  · split
    · exact (append_progress _ _ _).map plain
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem run_progress : Progress limit state (run limit depth rows state root) := by
  have rejected (reason : NativeCoreIdentical.Error) :
      Progress limit state (⟨{state with steps := state.steps+1},.error (.tick reason)⟩ : Outcome Inferred) :=
    ⟨.refl _,Nat.le_succ _,Nat.succ_le_succ,fun _ _ impossible => by cases impossible⟩
  by_cases clock : limit < state.steps+1
  · simpa only [run,NativeCoreUnsignedCancellation.tick,ite_eq_left clock] using rejected (.stepLimit root)
  by_cases tooDeep : depth = 0
  · simpa only [run,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_left tooDeep] using rejected (.depthLimit root)
  by_cases missing : state.arena.size ≤ root
  · simpa only [run,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_right tooDeep,ite_eq_left missing] using
      rejected (.invalidReference root)
  have room : state.steps + 1 ≤ limit := by omega
  have progress := afterEntry_progress (limit := limit) (depth := depth-1) (rows := rows)
    (state := {state with steps := state.steps+1}) (root := root)
  simp only [run,NativeCoreUnsignedCancellation.tick,ite_eq_right clock,ite_eq_right tooDeep,ite_eq_right missing]
  exact ⟨progress.kept,Nat.le_trans (Nat.le_succ _) progress.monotone,
    fun _ => progress.bounded room,fun _ => progress.accepted room⟩

private theorem emit_refines (arity : op.arity = 0)
    (typed : LoanTyping.HasType env [] ctx false (expand env source) (expand env (.node op [])))
    (checked : (inferred (append state op [])).result = .ok answer) :
    Refines env state.arena ctx source (inferred (append state op [])) answer := by
  obtain ⟨root,added,rfl⟩ := inferred_answer checked
  obtain ⟨kept,backward,represented⟩ := append_refines .nil arity.symm added
  exact ⟨kept,backward,_,represented,typed⟩

private theorem variable_refines (wf : UnifiedProgram.EnvWellFormed env)
    (represented : ContextRep env state.arena rows ctx) (found : rows[index]? = some row)
    (relevant : row.erased = false)
    (checked : (inferred (shifted limit depth state row.typeRoot (index+1))).result = .ok answer) :
    Refines env state.arena ctx (.var index)
      (inferred (shifted limit depth state row.typeRoot (index+1))) answer := by
  obtain ⟨root,inferredRoot,rfl⟩ := inferred_answer checked
  obtain ⟨written,domain,lookupType⟩ := represented.lookup_type found
  let amount := index+1
  obtain ⟨kept,backward,result,expected,resultRep⟩ :=
    (NativeCoreTransformExact.run_refines (mode := .shift (Int.ofNat amount)) (binders := 0) (value := written)
      domain trivial (shift_answer inferredRoot)).1
  change PartialRenaming.shift amount 0 written = some result at expected
  rw [PartialRenaming.shift_nonnegative (by omega)] at expected
  have raising : PartialRenaming.raiseIndex 0 ((amount : Int).toNat) = fun x => x+amount := by
    funext position
    simp [PartialRenaming.raiseIndex]
  rw [raising] at expected
  cases expected
  refine ⟨kept,backward,_,resultRep,?_⟩
  rw [EnvironmentDelta.expand_renaming wf.admissible,expand]
  exact .var lookupType (.inr relevant)

theorem run_sound (wf : UnifiedProgram.EnvWellFormed env) (context : ContextRep env base rows ctx) :
    Sound env base ctx limit (run limit depth rows) := by
  intro state root source answer final onBase room represented success _ _
  unfold run NativeCoreUnsignedCancellation.tick at success ⊢
  by_cases clock : limit < state.steps+1
  · simp [clock] at success
  by_cases exhausted : depth = 0
  · simp [clock,exhausted] at success
  by_cases invalid : state.arena.size ≤ root
  · simp [clock,exhausted,invalid] at success
  simp only [ite_eq_right clock,ite_eq_right exhausted,ite_eq_right invalid] at success ⊢
  unfold afterEntry at success ⊢
  cases represented with
  | var read =>
    simp only [read] at success ⊢
    split at success
    · rename_i row found
      split at success
      · simp [reject] at success
      · rename_i relevant
        simp only [ite_eq_right relevant]
        exact variable_refines (state := {state with steps := state.steps+1}) wf (context.frame onBase) found (Bool.eq_false_iff.mpr relevant) success
    · simp [reject] at success
  | @node _ op refs terms read arity children =>
    simp only [read] at success ⊢
    cases op
    case «universe» | prop | u64 | i64 | natural | integer =>
      simp only [Op.arity,List.length_eq_zero_iff] at arity
      subst refs
      cases children
      dsimp only at success ⊢
      first
      | exact emit_refines rfl (by simp only [expand,expandArgs]; exact .prop) success
      | exact emit_refines rfl (by simp only [expand,expandArgs]; exact .u64) success
      | exact emit_refines rfl (by simp only [expand,expandArgs]; exact .i64) success
      | split at success
        · rename_i allowed
          simp only [ite_eq_left allowed]
          apply emit_refines rfl _ success
          simp only [expand,expandArgs]
          first | exact .univ allowed | exact .natural allowed | exact .integer allowed.1 allowed.2
        · simp [reject] at success
    all_goals simp [reject] at success

private def openArena : Arena := #[.var 0,.node .array [0],.node (.natural 5) []]

/-- Code mode uses the written local type only for a relevant binder. The
rejecting erased access does not shift the domain or append a new row. -/
theorem relevant_variable_shift_and_erased_rejection :
    (let accepted := run 3 16 [⟨1,false⟩] ⟨openArena,0⟩ 0
     accepted.state.steps = 3 ∧ accepted.result.map Inferred.typeRoot = .ok 4 ∧
       accepted.state.arena = openArena ++ #[.var 1,.node .array [3]]) ∧
    run 1 16 [⟨1,true⟩] ⟨openArena,0⟩ 0 = ⟨⟨openArena,1⟩,.error (.outsideFragment 0)⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeHeadInference
