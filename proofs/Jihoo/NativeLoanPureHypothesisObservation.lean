import Jihoo.NativeBindingMachineLoanTyping
import Jihoo.NativeLoanPureProofObservation
import Jihoo.NativeScopeAlgebra

/-! A valuation of a mixed ghost telescope constructs an actual Loan64
closing. Numeric slots become bounded literals, and true affine hypotheses
become Decide or Refl evidence at their original instantiated annotations. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureHypothesisObservation

open CodeKinds (consValues)
open AffineSum (Expr)
open Semantics.PureArithmetic (Formula Recognized UniversalTruth)

inductive Entry where
  | scalar (erased : Bool)
  | less (left right : Expr)
  | equal (left right : Expr)

def Entry.binding : Entry → Binding
  | .scalar erased => ⟨.u64, erased⟩
  | .less left right => ⟨.lt left.toTerm right.toTerm, true⟩
  | .equal left right => ⟨.eq left.toTerm right.toTerm, true⟩

def context (entries : List Entry) : Context := entries.map Entry.binding

inductive ScalarSlot : List Entry → Nat → Prop where
  | here : ScalarSlot (.scalar erased :: entries) 0
  | there : ScalarSlot entries index → ScalarSlot (entry :: entries) (index + 1)

private theorem ScalarSlot.lookup (slot : ScalarSlot entries index) :
    ∃ erased, NativeKernel.lookup (context entries) index = some ⟨.u64, erased⟩ := by
  induction slot with
  | @here erased _ =>
      exact ⟨erased, by simp [context, Entry.binding, NativeKernel.lookup, Term.u64, Term.rename, renameArgs]⟩
  | there _ ih =>
      obtain ⟨erased, selected⟩ := ih
      refine ⟨erased, ?_⟩
      change (NativeKernel.lookup (context _) _).map _ = _
      simp [selected, Term.u64, Term.rename, renameArgs]

private theorem ScalarSlot.bound (slot : ScalarSlot entries index) : index < (context entries).length := by
  induction slot with
  | here => simp [context]
  | there _ inside =>
      simp only [context, List.map_cons, List.length_cons]
      exact Nat.succ_lt_succ inside

inductive ScalarExpr (entries : List Entry) : Expr → Prop where
  | var : ScalarSlot entries index → ScalarExpr entries (.var index)
  | literal : value < 2^64 → ScalarExpr entries (.literal value)
  | add : ScalarExpr entries left → ScalarExpr entries right → ScalarExpr entries (.add left right)

theorem ScalarExpr.typed (valid : ScalarExpr entries expression) :
    HasType env [] (context entries) true expression.toTerm .u64 := by
  induction valid with
  | var slot =>
      obtain ⟨_, selected⟩ := slot.lookup
      exact .var selected (Or.inl rfl)
  | literal bound => exact .natural bound
  | add _ _ first second => exact .uadd first second

private theorem scoped_pair {op : Op} (nonbinding : ∀ index, op.binders index = 0)
    (left : a.Scoped depth) (right : b.Scoped depth) : (Term.node op [a,b]).Scoped depth := by
  apply Term.Scoped.nonbinding nonbinding
  intro term member
  rcases List.mem_cons.mp member with rfl | member
  · exact left
  · exact (List.mem_singleton.mp member).symm ▸ right

theorem ScalarExpr.scoped (valid : ScalarExpr entries expression) :
    expression.toTerm.Scoped (context entries).length := by
  induction valid with
  | var slot => exact .var slot.bound
  | literal => exact Term.Scoped.leaf _ _
  | add _ _ first second => exact scoped_pair (by intro index; rfl) first second

private def push (value : Nat) (older : Nat → Nat) : Nat → Nat
  | 0 => value
  | index + 1 => older index

/-- Each erased assumption is interpreted in the earlier scalar valuation.
No evidence term is part of the valuation. -/
inductive Valuation : List Entry → (Nat → Nat) → Type where
  | empty : Valuation [] (fun _ => 0)
  | scalar (prior : Valuation entries words) (value : Fin (2^64)) :
      Valuation (.scalar erased :: entries) (push value.val words)
  | less (left right : Expr) (prior : Valuation entries words) :
      ScalarExpr entries left → ScalarExpr entries right →
      left.eval words < 2^64 → right.eval words < 2^64 → left.eval words < right.eval words →
      Valuation (.less left right :: entries) (push 0 words)
  | equal (left right : Expr) (prior : Valuation entries words) :
      ScalarExpr entries left → ScalarExpr entries right →
      left.eval words < 2^64 → right.eval words < 2^64 → left.eval words = right.eval words →
      Valuation (.equal left right :: entries) (push 0 words)

def Valuation.terms : Valuation entries words → Nat → Term
  | .empty => fun _ => .natural 0
  | .scalar prior value => consValues (.natural value.val) prior.terms
  | .less (words := words) left right prior _ _ _ _ _ =>
      consValues (.decide (.natural (left.eval words)) (.natural (right.eval words))) prior.terms
  | .equal (words := words) left _ prior _ _ _ _ _ => consValues (.refl (.natural (left.eval words))) prior.terms

private theorem Valuation.scalar_term (valuation : Valuation entries words) (slot : ScalarSlot entries index) :
    valuation.terms index = .natural (words index) := by
  induction slot generalizing words with
  | here => cases valuation; rfl
  | there _ ih =>
      cases valuation with
      | scalar prior value => exact ih prior
      | less _ _ prior => exact ih prior
      | equal _ _ prior => exact ih prior

/-- Grounded affine indices agree with the valuation's mathematical result
when that result fits in U64. The derivation gives the actual raw conversion. -/
theorem Valuation.affine_conversion (valuation : Valuation entries words)
    (valid : ScalarExpr entries expression) (bound : expression.eval words < 2^64) :
    RawLend.Conv env (expression.toTerm.subst valuation.terms) (.natural (expression.eval words)) := by
  induction valid with
  | var slot =>
      simp only [Expr.toTerm, Expr.eval, Term.subst]
      rw [valuation.scalar_term slot]
      exact .refl _
  | literal =>
      simp only [Expr.toTerm, Expr.eval, Term.subst, substArgs]
      exact .refl _
  | add left right leftIH rightIH =>
      simp only [Expr.toTerm, Expr.eval, Term.subst, substArgs] at bound ⊢
      refine (RawLend.Conv.node .uadd (.cons (leftIH (by omega)) (.cons (rightIH (by omega)) .nil))).trans ?_
      exact .old (.legacy (.add _ _ bound))

theorem Valuation.context_formed (valuation : Valuation entries words) :
    ResourceModes.ContextFormed env [] (context entries) := by
  induction valuation with
  | empty => exact .nil
  | scalar prior literal ih =>
      refine .cons ih (.intro (s := .type 0) .u64 (.inl ?_)) (Term.Scoped.leaf _ _)
      rename_i erased
      cases erased
      · intro impossible
        cases impossible
      · exact Or.inr (.refl _)
  | less left right previous leftValid rightValid _ _ _ ih =>
      exact .cons ih (.intro (s := .prop) (.lt leftValid.typed rightValid.typed) (.inl (.inl rfl)))
        (scoped_pair (by intro index; rfl) leftValid.scoped rightValid.scoped)
  | equal left right previous leftValid rightValid _ _ _ ih =>
      exact .cons ih (.intro (s := .prop) (.eq leftValid.typed rightValid.typed) (.inl (.inl rfl)))
        (scoped_pair (by intro index; rfl) leftValid.scoped rightValid.scoped)

/-- The mixed valuation constructs native-typed replacements for all actual
lookups, including older scalar slots under an arbitrary number of proofs. -/
theorem Valuation.realizes (valuation : Valuation entries words) :
    Ghost.Substitution env (context entries) [] valuation.terms := by
  induction valuation with
  | empty => intro index binding absent; cases absent
  | scalar prior value ih =>
      exact ih.consValues (by simpa only [Term.u64, Term.subst, substArgs] using
        (HasType.natural (env := env) (loans := []) (ctx := []) (ghost := true) value.isLt))
  | less left right previous leftValid rightValid leftBound rightBound ordered ih =>
      apply ih.consValues
      simp only [Term.lt, Term.subst, substArgs]
      exact LoanTyping.HasType.convert (.decide leftBound rightBound ordered)
        (.node .lt (.cons (previous.affine_conversion leftValid leftBound).symm
          (.cons (previous.affine_conversion rightValid rightBound).symm .nil)))
  | equal left right previous leftValid rightValid leftBound rightBound same ih =>
      have rightGround := previous.affine_conversion (env := env) rightValid rightBound
      rw [← same] at rightGround
      apply ih.consValues
      simp only [Term.eq, Term.subst, substArgs]
      exact LoanTyping.HasType.convert (.refl (.natural leftBound))
        (.node .eq (.cons (previous.affine_conversion leftValid leftBound).symm (.cons rightGround.symm .nil)))

def checkClosing? (env : Environment) (limits : PureProofObservation.Limits) (fuel : Nat)
    (ctx : Context) (values : Nat → Term) (term requested : Term) : Option Term := do
  let _ ← PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget
    ctx term requested
  PureProofObservation.observe? env limits [] fuel (term.subst values)

theorem checkClosing?_sound (wf : UnifiedProgram.EnvWellFormed env) (closing : Ghost.Substitution env ctx [] values)
    (checked : checkClosing? env limits fuel ctx values term requested = some residual) :
    ∃ sort : SortTag, HasType env [] [] true (requested.subst values) sort.term ∧
      PureTyping.HasType env [] residual (requested.subst values) ∧ Recognized env residual := by
  obtain ⟨sort, admitted, observed⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨formed, typed⟩ := PureTyping.Checker.check?_sound admitted
  have closedFormed := formed.ghostSubstitution wf closing
  rw [SortTag.subst_term] at closedFormed
  exact ⟨sort, closedFormed, PureProofObservation.observe?_sound wf (typed.ghostSubstitution wf closing) observed⟩

def checkObserve? (env : Environment) (limits : PureProofObservation.Limits) (fuel : Nat)
    (valuation : Valuation entries words) (term requested : Term) : Option Term :=
  checkClosing? env limits fuel (context entries) valuation.terms term requested

theorem checkObserve?_sound (wf : UnifiedProgram.EnvWellFormed env)
    (checked : checkObserve? env limits fuel valuation term requested = some residual) :
    ∃ sort : SortTag, HasType env [] [] true (requested.subst valuation.terms) sort.term ∧
      PureTyping.HasType env [] residual (requested.subst valuation.terms) ∧ Recognized env residual :=
  checkClosing?_sound wf valuation.realizes checked

theorem checked_arithmetic_truth (wf : UnifiedProgram.EnvWellFormed env)
    (checked : checkObserve? env limits fuel valuation term requested = some residual) :
    UniversalTruth env (requested.subst valuation.terms) := by
  obtain ⟨_, _, typed, recognized⟩ := checkObserve?_sound wf checked
  exact Semantics.PureArithmetic.recognized_fundamental wf typed recognized

/-- A false affine conclusion at any realizable input valuation cannot pass
checked observation. The condition is on the original arithmetic indices. -/
theorem rejects_false_inequality (wf : UnifiedProgram.EnvWellFormed env) (valuation : Valuation entries words)
    (leftValid : ScalarExpr entries left) (rightValid : ScalarExpr entries right)
    (leftBound : left.eval words < 2^64) (rightBound : right.eval words < 2^64)
    (unordered : ¬ left.eval words < right.eval words) :
    checkObserve? env limits fuel valuation term (.lt left.toTerm right.toTerm) = none := by
  cases observed : checkObserve? env limits fuel valuation term (.lt left.toTerm right.toTerm) with
  | none => rfl
  | some residual =>
      have normalized : RawLend.Conv env ((Term.lt left.toTerm right.toTerm).subst valuation.terms)
          (.lt (.natural (left.eval words)) (.natural (right.eval words))) := by
        simp only [Term.lt, Term.subst, substArgs]
        exact .node .lt (.cons (valuation.affine_conversion leftValid leftBound)
          (.cons (valuation.affine_conversion rightValid rightBound) .nil))
      have truth := (checked_arithmetic_truth wf observed).convert (.old normalized)
      have ordered := (UniversalTruth.formula_iff wf (.less (.literal (left.eval words)) (.literal (right.eval words)))).mp
        truth (fun _ => 0)
      exact False.elim (unordered ordered)

private def scalarValuation : Valuation [.scalar false] (push 2 (fun _ => 0)) :=
  .scalar .empty ⟨2, by decide⟩

private def lessValuation : Valuation [.less (.var 0) (.literal 3), .scalar false] (push 0 (push 2 (fun _ => 0))) :=
  .less (.var 0) (.literal 3) scalarValuation (.var .here) (.literal (by decide)) (by decide) (by decide) (by decide)

private def mixedValuation : Valuation
    [.equal (.var 1) (.add (.literal 1) (.literal 1)), .less (.var 0) (.literal 3), .scalar false]
    (push 0 (push 0 (push 2 (fun _ => 0)))) :=
  .equal (.var 1) (.add (.literal 1) (.literal 1)) lessValuation (.var (.there .here))
    (.add (.literal (by decide)) (.literal (by decide))) (by decide) (by decide) (by decide)

private def openProof : Term :=
  .transport (.lam false .u64 (.lt (.uadd (.var 0) (.natural 1)) (.natural 4))) (.var 0)
    (.ltAdd (.var 2) (.natural 3) (.natural 1) (.var 1))
private def requested : Term := .lt (.free PureFreeBoundary.owner (.natural 3)) (.natural 4)
private def residual : Term :=
  .ltAdd (.natural 2) (.natural 3) (.natural 1) (.decide (.natural 2) (.natural 3))
private def limits : PureProofObservation.Limits := ⟨32, 32, 8192⟩

/-- The checked source uses both erased assumptions and the scalar under
them. The valuation constructs the comparison evidence used by LtAdd and
the equality witness used by Transport. -/
theorem checked_mixed_hypotheses :
    checkObserve? .empty limits 12 mixedValuation openProof requested = some residual ∧ UniversalTruth .empty requested := by
  have checked : checkObserve? .empty limits 12 mixedValuation openProof requested = some residual := by cbv
  have truth := checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked
  exact ⟨checked, by simpa only [show requested.subst mixedValuation.terms = requested by cbv] using truth⟩

end Jihoo.NativeKernel.Environment.LoanTyping.PureHypothesisObservation
