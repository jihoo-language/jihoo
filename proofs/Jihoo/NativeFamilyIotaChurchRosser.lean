import Jihoo.NativeFamilyIotaParallelForward

/-! Actual finite forward Church-Rosser for genuine enlarged delta/ACU/family
conversion. Family tables are arbitrary raw data; only the established global
closed/transparent invariant is needed for delta projection. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU EnvironmentDelta
variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QStar" => Star env

private theorem list_parallel_refl (terms : List Term) : ListRel QPar terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (Parallel.refl term) ih

private theorem list_stars (related : ListRel QStar xs ys) : NativeKernel.Conversion.Closure (ListRel QPar) xs ys := by
  induction related with
  | nil => exact .refl
  | @cons a b xs ys head tail ih =>
    exact (head.map (fun x => x::xs) (fun h => ListRel.cons h (list_parallel_refl xs))).trans
      (ih.map (fun rest => b::rest) (fun h => ListRel.cons (Parallel.refl b) h))

theorem Star.node (op : Op) (children : ListRel QStar xs ys) : QStar (.node op xs) (.node op ys) :=
  (list_stars children).map (Term.node op) (Parallel.node op)

theorem Parallel.ofOldCompute (step : Computes term result) : QPar term result := by
  apply Parallel.ofAtom (atomic := by cases step <;> simp only [arithmeticFlatten])
  cases step with
  | beta erased domain body argument => exact .beta erased domain body (.refl _) (Parallel.refl body) (Parallel.refl argument)
  | sub a b proof lower bound => exact .sub a b proof (.refl _) (.refl _) lower bound
  | read count values index proof value selected => exact .read count index proof (.refl _) (.refl _) (list_parallel_refl values) selected
  | witnessPack predicate value proof => exact .witnessPack predicate _ proof (.refl _) (Parallel.refl _)
  | proofPack predicate value proof => exact .proofPack predicate value _ (.refl _) (Parallel.refl _)
  | derefBorrow value => exact .derefBorrow _ (.refl _) (Parallel.refl _)
  | borrowDeref value => exact .borrowDeref _ (.refl _) (Parallel.refl _)
  | transportRefl motive value proof => exact .transportRefl value (.refl _) (Parallel.refl _)
  | ifLtTrue a b yes no holds => exact .ifLtTrue a b no (.refl _) (.refl _) holds (Parallel.refl yes)
  | ifLtFalse a b yes no holds => exact .ifLtFalse a b yes (.refl _) (.refl _) holds (Parallel.refl _)
  | ifEqTrue value yes no => exact .ifEqTrue value no (.refl _) (.refl _) (Parallel.refl yes)
  | ifEqFalse a b yes no holds => exact .ifEqFalse a b yes (.refl _) (.refl _) holds (Parallel.refl _)

theorem Star.ofOldMixed (step : ACU.MixedRed term result) : QStar term result := by
  induction step using ACU.MixedRed.rec (motive_2 := fun xs ys _ => ListRel QStar xs ys) with
  | refl => exact .refl
  | trans _ _ first second => exact first.trans second
  | node op _ ih => exact Star.node op ih
  | arithmetic original => exact .single (Parallel.arithmetic original.toArithmetic)
  | compute original => exact .single (Parallel.ofOldCompute original)
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

def Join (env : Environment) (first second : Term) : Prop :=
  ∃ common,Star env first common ∧ Star env second common
local notation "QJoin" => Join env

private theorem Join.refl (term : Term) : QJoin term term := ⟨term,.refl,.refl⟩
private theorem Join.symm (joined : QJoin a b) : QJoin b a := by
  obtain ⟨common,first,second⟩ := joined
  exact ⟨common,second,first⟩
private theorem Join.trans (first : QJoin a b) (second : QJoin b c) : QJoin a c := by
  obtain ⟨left,al,bl⟩ := first
  obtain ⟨right,br,cr⟩ := second
  obtain ⟨common,lc,rc⟩ := bl.confluence br
  exact ⟨common,al.trans lc,cr.trans rc⟩

private theorem list_join (related : ListRel QJoin xs ys) :
    ∃ common,ListRel QStar xs common ∧ ListRel QStar ys common := by
  induction related with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons head tail ih =>
    obtain ⟨first,left,right⟩ := head
    obtain ⟨rest,lefts,rights⟩ := ih
    exact ⟨first::rest,.cons left lefts,.cons right rights⟩

private theorem Join.node (op : Op) (related : ListRel QJoin xs ys) : QJoin (.node op xs) (.node op ys) := by
  obtain ⟨common,left,right⟩ := list_join related
  exact ⟨.node op common,Star.node op left,Star.node op right⟩

/-- Every actual enlarged raw equation has a genuine quotient common reduct
following global expansion, including every family iota equation. -/
theorem projected_join (converted : Extended.Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    QJoin (expand env a) (expand env b) := by
  induction converted using Extended.Conv.rec
    (motive_2 := fun xs ys _ => ListRel QJoin (expandArgs env xs) (expandArgs env ys)) with
  | old original =>
    obtain ⟨common,left,right⟩ := ACU.Conv.church_rosser (original.toProjected admissible)
    exact ⟨common,Star.ofOldMixed left,Star.ofOldMixed right⟩
  | iota original => exact ⟨_,.single (Parallel.ofRoot (root_expansion original)),.refl⟩
  | refl term => exact Join.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | node op related ih =>
    cases related with
    | nil => exact Join.refl _
    | cons head tail =>
      simpa only [expand_node_cons,expandArgs] using Join.node op ih
  | nil => simp only [expandArgs];exact .nil
  | cons _ _ first rest => simp only [expandArgs];exact .cons first rest

end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient

namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

/-- Genuine enlarged Church-Rosser yields actual finite forward paths, with
no residual arithmetic quotient endpoint, typing premise or CR oracle. -/
theorem Conv.church_rosser (converted : Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    ∃ common,Forward env a common ∧ Forward env b common := by
  obtain ⟨quotient,left,right⟩ := Quotient.projected_join converted admissible
  obtain ⟨leftResult,leftPath,leftArithmetic⟩ := left.realize (.refl _)
  obtain ⟨rightResult,rightPath,rightArithmetic⟩ := right.realize (.refl _)
  obtain ⟨common,leftFinal,rightFinal⟩ := (leftArithmetic.symm.trans rightArithmetic).church_rosser
  exact ⟨common,
    (Forward.old (EnvironmentDelta.expand_forward env a)).trans
      (leftPath.toForward.trans (.old (.acu (.arithmetic leftFinal)))),
    (Forward.old (EnvironmentDelta.expand_forward env b)).trans
      (rightPath.toForward.trans (.old (.acu (.arithmetic rightFinal))))⟩

theorem Forward.confluence (left : Forward env a b) (right : Forward env a c)
    (admissible : EnvironmentDelta.Admissible env) :
    ∃ common,Forward env b common ∧ Forward env c common :=
  (left.toConv.symm.trans right.toConv).church_rosser admissible

theorem conv_iff_forward_join (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b ↔ ∃ common,Forward env a common ∧ Forward env b common :=
  ⟨fun converted => converted.church_rosser admissible,fun ⟨_,left,right⟩ => Conv.ofForwardJoin left right⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
