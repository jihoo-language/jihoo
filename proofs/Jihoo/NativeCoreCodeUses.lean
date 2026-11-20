import Jihoo.NativeCoreMeteredVisit
import Jihoo.NativeOwnership

/-! Metered native runtime demand on variables, neutral leaves and the
two-operand scalar and memory branches. Leading lambdas share a single
function body and shift the counted variable before visiting that body. -/
namespace Jihoo.NativeKernel.NativeCoreCodeUses

open NativeArena
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreMeteredVisit (charge charge_progress)
open Jihoo.Quantity

def pair (op : Op) : Bool :=
  match op with
  | .arith _ | .strict | .uadd | .usub | .alloc | .free | .drop _ | .index => true
  | _ => false

def neutral (op : Op) : Bool :=
  match op with
  | .global _ | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refl |
    .transport | .ind _ _ | .ltAdd | .ltCancel | .ltLe | .zeroLe | .refine | .proof |
    .buffer | .ref | .back _ | .borrow | .deref | .absurd | .pi _ |
    .natural _ | .integer _ | .decide => true
  | _ => false

private def reject (state : State) (root : Nat) : Outcome Nat := ⟨state,.error (.outsideFragment root)⟩

def run (limit slot : Nat) : Nat → State → Nat → Outcome Nat
  | 0,state,root => (charge limit 0 state root).next fun paid _ => reject paid root
  | depth+1,state,root =>
    (charge limit (depth+1) state root).next fun paid _ =>
      match paid.arena[root]? with
      | some (.var index) => ⟨paid,.ok (if index = slot then 1 else 0)⟩
      | some (.node op refs) =>
        if neutral op then ⟨paid,.ok 0⟩
        else if pair op then
          match refs with
          | left :: right :: _ =>
            (run limit slot depth paid left).next fun after count =>
              (run limit slot depth after right).next fun final next =>
                ⟨final,.ok (count+next)⟩
          | _ => reject paid root
        else reject paid root
      | none => reject paid root

theorem run_progress (limit slot depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run limit slot depth state root) := by
  induction depth generalizing state root with
  | zero => exact (charge_progress _ _ _ _).next fun _ => Progress.atState _ _
  | succ depth ih =>
    unfold run
    apply (charge_progress _ _ _ _).next
    intro _
    split
    · exact Progress.atState _ _
    · split
      · exact Progress.atState _ _
      · split
        · split
          · exact (ih _ _).next fun _ => (ih _ _).next fun _ => Progress.atState _ _
          · exact Progress.atState _ _
        · exact Progress.atState _ _
    · exact Progress.atState _ _

inductive Projects : Term → Control → Prop
  | var (index : Nat) : Projects (.var index) (.use index)
  | neutral : neutral op = true → Projects (.node op refs) .pure
  | pair : pair op = true → Projects left a → Projects right b →
      Projects (.node op (left :: right :: rest)) (.seq a b)

theorem run_refines (source : Represents state.arena root term)
    (success : (run limit slot depth state root).result = .ok result) :
    (run limit slot depth state root).state.arena = state.arena ∧
      ∃ control, Projects term control ∧ control.demand slot = some result := by
  induction depth generalizing state root term result with
  | zero =>
    rw [run] at success
    obtain ⟨⟨⟩,_,next⟩ := Outcome.next_success success
    rw [next] at success
    cases success
  | succ depth ih =>
    rw [run] at success ⊢
    obtain ⟨⟨⟩,_,entered⟩ := Outcome.next_success success
    rw [entered] at success ⊢
    cases source with
    | var read =>
      simp only [charge,read] at success ⊢
      cases success
      exact ⟨True.intro,_,.var _,rfl⟩
    | node read width held =>
      simp only [charge,read] at success ⊢
      split at success
      · rename_i pure
        simp only [ite_eq_left pure]
        cases success
        exact ⟨True.intro,_,.neutral pure,rfl⟩
      · rename_i active
        simp only [ite_eq_right active]
        split at success
        · rename_i usesPair
          simp only [ite_eq_left usesPair]
          cases held with
          | nil => cases success
          | cons left remaining =>
            cases remaining with
            | nil => cases success
            | cons right rest =>
              dsimp only at success ⊢
              obtain ⟨count,counted,leftNext⟩ := Outcome.next_success success
              rw [leftNext] at success ⊢
              let paid := (charge limit (depth+1) state root).state
              obtain ⟨kept,leftControl,projected,leftDemand⟩ := ih (state := paid) left counted
              obtain ⟨more,moreCounted,rightNext⟩ := Outcome.next_success success
              rw [rightNext] at success ⊢
              obtain ⟨same,rightControl,readRight,rightDemand⟩ := ih (kept.symm ▸ right) moreCounted
              cases success
              exact ⟨same.trans kept,_,.pair usesPair projected readRight,
                by simp [Control.demand,leftDemand,rightDemand]⟩
        · cases success

def leadingLambdas (arena : Arena) : Nat → Nat → Nat × Nat
  | 0,root => (0,root)
  | fuel+1,root =>
    match arena[root]? with
    | some (.node (.lam _) [_,body]) =>
      let (count,inner) := leadingLambdas arena fuel body
      (count+1,inner)
    | _ => (0,root)

def function (limit depth : Nat) (state : State) (body slot : Nat) : Outcome Nat :=
  let (count,inner) := leadingLambdas state.arena (state.arena.size+1) body
  run limit (slot+count) (if count = 0 then depth else depth-1) state inner

theorem function_progress : Progress limit state (function limit depth state body slot) :=
  run_progress _ _ _ _ _

inductive BodyOf : Term → Nat → Term → Prop
  | var (index : Nat) : BodyOf (.var index) 0 (.var index)
  | node (notLambda : ∀ erased, op ≠ .lam erased) : BodyOf (.node op refs) 0 (.node op refs)
  | lambda : BodyOf rest binders body → BodyOf (Term.lam erased domain rest) (binders+1) body

theorem leadingLambdas_refines (back : Backward arena) (source : Represents arena root term)
    (room : root < fuel) :
    let (count,inner) := leadingLambdas arena fuel root
    ∃ body, Represents arena inner body ∧ BodyOf term count body := by
  induction fuel generalizing root term with
  | zero => omega
  | succ fuel ih =>
    cases source with
    | var read =>
      simp only [leadingLambdas,read]
      exact ⟨_,.var read,.var _⟩
    | @node root op refs children read width held =>
      cases op
      case lam erased =>
        cases held with
        | nil => cases width
        | cons domain tail =>
          cases tail with
          | nil => cases width
          | @cons bodyRoot bodyTerm tailRefs tailTerms body tail =>
            cases tail with
            | nil =>
              have below : bodyRoot < root := back root _ read bodyRoot (by simp [Node.references])
              have later := ih body (by omega : bodyRoot < fuel)
              obtain ⟨count,inner⟩ := leadingLambdas arena fuel bodyRoot
              obtain ⟨representedTerm,represented,opened⟩ := later
              simp only [leadingLambdas,read]
              exact ⟨representedTerm,represented,.lambda opened⟩
            | cons _ _ => simp [Op.arity] at width
      all_goals
        simp only [leadingLambdas,read]
        exact ⟨_,.node read width held,.node (by intro erased impossible; cases impossible)⟩

/-- The native meter counts the same resource demand in the body reached
after all the leading function binders are entered. -/
theorem function_refines (back : Backward state.arena) (source : Represents state.arena body term)
    (success : (function limit depth state body slot).result = .ok count) :
    (function limit depth state body slot).state.arena = state.arena ∧
      ∃ binders inner control, BodyOf term binders inner ∧ Projects inner control ∧
        control.demand (slot+binders) = some count := by
  have inside : body < state.arena.size := by
    cases source with
    | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1
  obtain ⟨inner,represented,opened⟩ := leadingLambdas_refines back source (Nat.lt_succ_of_lt inside)
  obtain ⟨kept,control,projected,demand⟩ := run_refines represented success
  exact ⟨kept,_,inner,control,opened,projected,demand⟩

theorem function_tracks_shifted_slot :
    let arena : Arena := #[.node .i64 [],.var 1,.node (.integer 0) [],.node .free [1,2],.node (.lam false) [0,3]]
    function 3 8 ⟨arena,0⟩ 4 0 = ⟨⟨arena,3⟩,.ok 1⟩ ∧
      function 3 8 ⟨arena,0⟩ 4 1 = ⟨⟨arena,3⟩,.ok 0⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreCodeUses
