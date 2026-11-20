import Jihoo.NativeCoreUnsignedSubtract
import Jihoo.NativeEffectfulDependentRelation
import Jihoo.NativeDependentNumericCoherence

set_option maxUniverseOffset 40

/-! Successful ghost cancellation of two checked literal sum trees emits
their mathematical difference in the concrete dependent numeric model.
Only the individual source leaves need to fit a physical word. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

open NativeArena NativeConstantAccumulator
open NativeCoreUnsignedCollect (Collects View termView view)
open NativeCoreUnsignedSubtract (Parts numerical)
open NativeCorePureUnsignedSum (wrapPrefixes)
open EnvironmentDelta.NumeralForward renaming Represents → NumeralTree

private theorem collected_numeral (numeric : NumeralTree source number)
    (typed : LoanTyping.HasType env [] ctx true source .u64)
    (collected : Collects source atoms prefixes updates visits) (initial : Nat) :
    atoms = [] ∧ runNatural updates initial = some (initial+number) := by
  induction numeric generalizing atoms prefixes updates visits initial with
  | natural value =>
    have fits := typed.natural_bound
    cases collected with
    | literal observed =>
      have same : UInt64.ofNat value = _ := View.literal.inj observed
      cases same
      exact ⟨rfl,by simp only [runNatural,UInt64.toNat_ofNat_of_lt' fits]⟩
    | sum observed => simp only [termView,view,reduceCtorEq] at observed
    | strict observed => simp only [termView,view,reduceCtorEq] at observed
    | atom observed => simp only [termView,view,reduceCtorEq] at observed
  | add left right ihLeft ihRight =>
    cases collected with
    | sum observed first second =>
      obtain ⟨rfl,rfl⟩ := View.sum.inj observed
      obtain ⟨leftTyped,rightTyped,_⟩ := typed.uadd_inputs
      obtain ⟨rfl,leftValue⟩ := ihLeft leftTyped first initial
      obtain ⟨rfl,rightValue⟩ := ihRight rightTyped second (initial + _)
      refine ⟨rfl,?_⟩
      have append (first second : List Update) (base : Nat) :
          runNatural (first++second) base = (runNatural first base).bind (runNatural second) := by
        induction first generalizing base with
        | nil => rfl
        | cons piece rest ih =>
          cases piece with
          | literal => exact ih _
          | cancel => simp only [List.cons_append,runNatural]; split <;> first | exact ih _ | rfl
      rw [append,leftValue]
      simpa only [Option.bind_some,Nat.add_assoc] using rightValue
    | literal observed => simp only [termView,view,reduceCtorEq] at observed
    | strict observed => simp only [termView,view,reduceCtorEq] at observed
    | atom observed => simp only [termView,view,reduceCtorEq] at observed

private theorem numeral_parts (numeric : NumeralTree source number)
    (typed : LoanTyping.HasType env [] ctx true source .u64) (parts : Parts source atoms constant) :
    atoms = [] ∧ constant = number := by
  obtain ⟨_,_,_,collected,sum⟩ := parts
  obtain ⟨empty,constantSum⟩ := collected_numeral numeric typed collected 0
  exact ⟨empty,Option.some.inj (sum.symm.trans (by simpa only [Nat.zero_add] using constantSum))⟩

private theorem projected_numeral_tree (admissible : EnvironmentDelta.Admissible env) (point : Γ)
    (numeric : NumeralTree source value) (typed : LoanTyping.HasType env [] ctx true source .u64) :
    ((natural env Γ).projected admissible).realizes point source ⟨value⟩ := by
  induction numeric with
  | natural value => exact projected_natural_literal admissible value typed.natural_bound
  | add left right ihLeft ihRight =>
    obtain ⟨leftTyped,rightTyped,_⟩ := typed.uadd_inputs
    exact projected_natural_add admissible (ihLeft leftTyped) (ihRight rightTyped)

private theorem projected_prefixes (result : Term) (prefixes : List Term) :
    ValueErasure.Loan.project env (wrapPrefixes result prefixes) = ValueErasure.Loan.project env result := by
  induction prefixes generalizing result with
  | nil => rfl
  | cons first rest ih =>
    change ValueErasure.Loan.project env (wrapPrefixes (.strict first result) rest) = _
    rw [ih,ValueErasure.Loan.project_strict]

/-- Native ghost subtraction of checked arithmetic trees produces a typed
result representing the mathematical difference in every valuation. The
native constant computation may exceed U64, and any Strict prefixes are
retained in the represented syntax and erased only by the ghost relation. -/
theorem native_literal_subtraction_realizes (wf : UnifiedProgram.EnvWellFormed env)
    (first : Represents arena left a) (second : Represents arena right b)
    (leftNumeric : NumeralTree a m) (rightNumeric : NumeralTree b n)
    (typed : LoanTyping.HasType env loans ctx mode (.usub a b evidence) originalType)
    (limitBound : limit ≤ 1000000)
    (computed : (NativeCoreUnsignedSubtract.run env false arena limit depth initial left right).result =
      .ok (some output)) :
    let after := (NativeCoreUnsignedSubtract.run env false arena limit depth initial left right).arena
    Prefix arena after ∧ (Backward arena → Backward after) ∧
      ∃ result, Represents after output result ∧ LoanTyping.HasType env [] ctx true result originalType ∧
        ∀ (Γ : Contextual.Context) (point : Γ),
          ((natural env Γ).projected wf.admissible).realizes point result ⟨m-n⟩ := by
  obtain ⟨kept,back,remainder,atoms,prefixes,agreement,represented,_,outputRep,outputTyped⟩ :=
    NativeCoreUnsignedSubtract.run_refines wf first second typed limitBound computed
  obtain ⟨leftTyped,rightTyped,_⟩ := typed.usub_inputs
  obtain ⟨leftAtoms,rightAtoms,remaining,leftConstant,rightConstant,leftParts,rightParts,remainingRep,subset,balanced⟩ :=
    agreement.values
  obtain ⟨noLeft,leftCount⟩ := numeral_parts leftNumeric (leftTyped.ghost []) leftParts
  obtain ⟨noRight,rightCount⟩ := numeral_parts rightNumeric (rightTyped.ghost []) rightParts
  subst leftAtoms
  subst rightAtoms
  have emptyRemaining := List.sublist_nil.mp subset
  subst remaining
  have length := (NativeCoreIdentical.represented_length represented).symm.trans
    (NativeCoreIdentical.represented_length remainingRep)
  have empty : atoms = [] := List.length_eq_zero_iff.mp length
  subst atoms
  have balance := balanced (fun _ => 0)
  simp only [numerical,List.map_nil,List.sum_nil,Nat.zero_add,leftCount,rightCount] at balance
  have difference : remainder.constant.toNat = m-n := by omega
  change Represents _ output (wrapPrefixes (naturalSum remainder.constant.toNat) prefixes) at outputRep
  change LoanTyping.HasType env [] ctx true (wrapPrefixes (naturalSum remainder.constant.toNat) prefixes) originalType at outputTyped
  rw [difference] at outputRep outputTyped
  refine ⟨kept,back,_,outputRep,outputTyped,?_⟩
  intro Γ point
  change (natural env Γ).realizes point (ValueErasure.Loan.project env
    (wrapPrefixes (naturalSum (m-n)) prefixes)) ⟨m-n⟩
  rw [projected_prefixes]
  obtain ⟨numeric,formed⟩ := naturalSum_correct (env := env) (loans := []) (ctx := []) (mode := true) (m-n)
  exact projected_numeral_tree wf.admissible point numeric formed

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
