import Jihoo.NativeLoanNumericalEvidence
import Jihoo.NativeBindingMachineMutableUnsignedSubtraction

/-! A checked unsigned subtraction of observed words computes independently
of the original erased evidence. Conversion uses actual source typing
and a forward literal contraction. -/
namespace Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic

theorem Numeric.to_literal (numeric : Numeric env term value) (bounded : value < 2^64) :
    RawLend.Conv env term (.natural value) := by
  obtain ⟨tree,converted,represented⟩ := numeric
  exact converted.trans (RawLend.Forward.old (.old (represented.contract bounded))).toConv

/-- The original erased proof provides the bound of the actual checked
subtraction. The operands can be any expressions with observed word values. -/
theorem checked_subtraction_to_literal
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode (.usub left right proof) type)
    (observed : ObservedEvidence env values proof)
    (first : Numeric env (left.subst values) m) (second : Numeric env (right.subst values) n)
    (bounded : m < 2^64) :
    RawLend.Conv env ((Term.usub left right proof).subst values) (.natural (m-n)) := by
  have evidence := typed.usub_inputs.2.2
  have read : Order env (.lt (right.subst values) (.uadd (left.subst values) (.natural 1))) := by
    simpa only [Term.lt,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,liftSub] using
      observed_evidence_order wf evidence observed
  have valid := read.reflect wf.admissible second (first.add (Numeric.natural env 1))
  have ordered : n ≤ m := by omega
  have rightBound := Nat.lt_of_le_of_lt ordered bounded
  have exposes : RawLend.Conv env ((Term.usub left right proof).subst values)
      (.usub (.natural m) (.natural n) (proof.subst values)) := by
    simp only [Term.usub,Term.subst,substArgs,Op.binders,liftSub]
    exact .node .usub (.cons (first.to_literal bounded) (.cons (second.to_literal rightBound) (.cons (.refl _) .nil)))
  have computes : ACU.Computes (.usub (.natural m) (.natural n) (proof.subst values)) (.natural (m-n)) :=
    .sub m n _ ordered bounded
  exact exposes.trans (RawLend.Forward.old (.old (.acu (.compute computes)))).toConv

/-- Two source-checked subtraction occurrences with the same observed
operands convert to the same word, including under an open term substitution. -/
theorem checked_subtractions_ignore_observed_evidence
    (wf : UnifiedProgram.EnvWellFormed env)
    (first : LoanTyping.HasType env firstLoans firstCtx firstMode (.usub a b p) firstType)
    (second : LoanTyping.HasType env secondLoans secondCtx secondMode (.usub c d q) secondType)
    (firstProof : ObservedEvidence env values p) (secondProof : ObservedEvidence env replacements q)
    (leftFirst : Numeric env (a.subst values) m) (rightFirst : Numeric env (b.subst values) n)
    (leftSecond : Numeric env (c.subst replacements) m) (rightSecond : Numeric env (d.subst replacements) n)
    (bounded : m < 2^64) :
    RawLend.Conv env ((Term.usub a b p).subst values) ((Term.usub c d q).subst replacements) :=
  (checked_subtraction_to_literal wf first firstProof leftFirst rightFirst bounded).trans
    (checked_subtraction_to_literal wf second secondProof leftSecond rightSecond bounded).symm

end Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
