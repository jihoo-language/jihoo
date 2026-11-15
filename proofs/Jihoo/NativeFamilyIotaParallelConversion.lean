import Jihoo.NativeFamilyIotaParallelBinding

/-! The enlarged quotient parallel calculus derives only genuine raw equations.
Global closedness is the existing substitution invariant; family metadata may
remain completely forged/untyped in this equation soundness theorem. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU
variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env
local notation "Conv" => Extended.Conv env

private theorem old_legacy (h : NativeKernel.Conversion.Conv a b) : Conv a b := .old (.legacy h)
private theorem arithmetic_toConv (h : Arithmetic a b) : Conv a b := .old (.acu h.toConv)

private theorem list_length (related : ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem list_append (first : ListRel R xs ys) (second : ListRel R rest rest') :
    ListRel R (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem listConv_sumTerms (h : ListRel Conv xs ys) : Conv (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact .node .uadd (.cons h (.cons ih .nil))

private theorem conv_instantiate (closed : EnvironmentDelta.Basis.Closed env) (hb : Conv body body') (ha : Conv a a') :
    Conv (body.subst (single a)) (body'.subst (single a')) := by
  apply (hb.substitution (single a) closed).trans
  apply Extended.Conv.subst_congr closed
  intro x
  cases x with
  | zero => exact ha
  | succ x => exact .refl _

/-- Every quotient parallel derivation translates to the actual ACU.Conv
relation containing the legacy rules. No model reflection premise is used. -/
theorem Parallel.toConv (h : QPar a b) (closed : EnvironmentDelta.Basis.Closed env) : Conv a b := by
  induction h using Parallel.rec
    (motive_2 := fun a b _ => Conv a b)
    (motive_3 := fun xs ys _ => ListRel Conv xs ys)
    (motive_4 := fun xs ys _ => ListRel Conv xs ys) with
  | intro p hs out ih =>
      exact (arithmetic_toConv ((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p))).trans
        ((listConv_sumTerms ih).trans (arithmetic_toConv out).symm)
  | var x => exact .refl _
  | node op hs ih => exact .node op ih
  | beta e A body view hb ha ib ia =>
      exact (Extended.Conv.node .app (.cons (arithmetic_toConv view) (.cons (.refl _) .nil))).trans
        ((old_legacy (.beta e A body _)).trans (conv_instantiate closed ib ia))
  | sub m n p left right bound valid =>
      exact (Extended.Conv.node .usub (.cons (arithmetic_toConv left) (.cons (arithmetic_toConv right) (.cons (.refl _) .nil)))).trans
        (old_legacy (.sub m n p bound valid))
  | read count k p arr index hs selected ih =>
      exact (Extended.Conv.node .index (.cons ((arithmetic_toConv arr).trans (.node (.elements count) ih))
        (.cons (arithmetic_toConv index) (.cons (.refl _) .nil)))).trans (old_legacy (.read count _ k p _ selected))
  | witnessPack p a q view ha ih =>
      exact (Extended.Conv.node .witness (.cons (arithmetic_toConv view) .nil)).trans ((old_legacy (.witnessPack p a q)).trans ih)
  | proofPack p a q view ha ih =>
      exact (Extended.Conv.node .proof (.cons (arithmetic_toConv view) .nil)).trans ((old_legacy (.proofPack p a q)).trans ih)
  | derefBorrow a view ha ih =>
      exact (Extended.Conv.node .deref (.cons (arithmetic_toConv view) .nil)).trans ((old_legacy (.derefBorrow a)).trans ih)
  | borrowDeref a view ha ih =>
      exact (Extended.Conv.node .borrow (.cons (arithmetic_toConv view) .nil)).trans ((old_legacy (.borrowDeref a)).trans ih)
  | transportRefl a view hp ih =>
      exact (Extended.Conv.node .transport (.cons (.refl _) (.cons (arithmetic_toConv view) (.cons (.refl _) .nil)))).trans
        ((old_legacy (.transportRefl _ a _)).trans ih)
  | ifLtTrue m n no left right bound hy ih =>
      exact (Extended.Conv.node .ifLt (.cons (arithmetic_toConv left) (.cons (arithmetic_toConv right) (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((old_legacy (.ifLtTrue m n _ no bound)).trans (conv_instantiate closed ih (.refl _)))
  | ifLtFalse m n yes left right bound hn ih =>
      exact (Extended.Conv.node .ifLt (.cons (arithmetic_toConv left) (.cons (arithmetic_toConv right) (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((old_legacy (.ifLtFalse m n yes _ bound)).trans ih)
  | ifEqTrue n no left right hy ih =>
      exact (Extended.Conv.node .ifEq (.cons (arithmetic_toConv left) (.cons (arithmetic_toConv right) (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((old_legacy (.ifEqTrue n _ no)).trans (conv_instantiate closed ih (.refl _)))
  | ifEqFalse m n yes left right bound hn ih =>
      exact (Extended.Conv.node .ifEq (.cons (arithmetic_toConv left) (.cons (arithmetic_toConv right) (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((old_legacy (.ifEqFalse m n yes _ bound)).trans ih)
  | elim family constructor entry signature motive cases scrutinee found sigFound count fields view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i values motiveOut casesOut valuesOut branchOut
      have constructorChange : Conv (.node (.con family constructor values.length) values)
          (.node (.con family constructor valuesOut.length) valuesOut) := by
        rw [← list_length valueSteps]
        exact .node _ ihValues
      have inputChange : Conv (elimTerm family motive cases scrutinee)
          (elimTerm family motiveOut casesOut (.node (.con family constructor valuesOut.length) valuesOut)) := by
        unfold elimTerm
        rw [← list_length caseSteps]
        exact .node _ (.cons ihMotive (list_append ihCases (.cons ((arithmetic_toConv view).trans constructorChange) .nil)))
      exact inputChange.trans (.iota (.elim found sigFound selected ((list_length caseSteps).symm.trans count)
        ((list_length valueSteps).symm.trans fields)))
  | caseOf family constructor entry signature motive cases scrutinee found data sigFound count fields view caseSteps valueSteps selected ihCases ihValues =>
      rename_i values casesOut valuesOut branchOut
      have constructorChange : Conv (.node (.con family constructor values.length) values)
          (.node (.con family constructor valuesOut.length) valuesOut) := by
        rw [← list_length valueSteps]
        exact .node _ ihValues
      have inputChange : Conv (caseTerm family motive cases scrutinee)
          (caseTerm family motive casesOut (.node (.con family constructor valuesOut.length) valuesOut)) := by
        unfold caseTerm
        rw [← list_length caseSteps]
        exact .node _ (.cons (.refl _) (list_append ihCases (.cons ((arithmetic_toConv view).trans constructorChange) .nil)))
      exact inputChange.trans (.iota (.caseOf found data sigFound selected ((list_length caseSteps).symm.trans count)
        ((list_length valueSteps).symm.trans fields)))
  | view recursion family constructor entry signature motive cases scrutinee found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i plans values motiveOut casesOut valuesOut branchOut
      have constructorChange : Conv (.node (.con family constructor values.length) values)
          (.node (.con family constructor valuesOut.length) valuesOut) := by
        rw [← list_length valueSteps]
        exact .node _ ihValues
      have inputChange : Conv (viewTerm recursion family motive cases scrutinee)
          (viewTerm recursion family motiveOut casesOut (.borrow (.node (.con family constructor valuesOut.length) valuesOut))) := by
        unfold viewTerm
        rw [← list_length caseSteps]
        exact .node _ (.cons ihMotive (list_append ihCases (.cons ((arithmetic_toConv view).trans
          (.node .borrow (.cons constructorChange .nil))) .nil)))
      exact inputChange.trans (.iota (.view found boxed sigFound selected ((list_length caseSteps).symm.trans count)
        ((list_length valueSteps).symm.trans fields) bound planned))
  | drop family owner rest restStep ih => exact (Extended.Conv.iota (.drop family owner rest)).trans ih
  | nil => exact .nil
  | cons h hs ih is => exact .cons ih is
  | _ => first | exact .nil | apply ListRel.cons <;> assumption

end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
