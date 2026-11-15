import Jihoo.NativeLoanFamilyIotaParameterInstantiation

/-! Borrowed-field instantiation is related to the original constructor
instantiation by real Deref/Borrow conversion. The relation is pointwise and
preserves all outer variables; no normalization/substitution oracle is used. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

def extendField (σ : Nat → Term) (value : Term) : Nat → Term
  | 0 => value
  | x+1 => σ x

theorem lift_single_extend (σ : Nat → Term) (value : Term) :
    (fun x => (liftSubOne σ x).subst (single value)) = extendField σ value := by
  funext x
  cases x with
  | zero => simp only [liftSubOne,Term.subst,single,extendField]
  | succ x =>
    change ((σ x).rename Nat.succ).subst (single value) = σ x
    exact Term.shift_subst_single _ _

theorem viewReadAt_last (previous : List Bool) (borrowed : Bool) :
    viewReadAt (previous ++ [borrowed]) 0 =
      if borrowed then .deref (.var 0) else .var 0 := by
  have positive : 0 < (previous ++ [borrowed]).length := by simp
  have index : (previous ++ [borrowed]).length - 1 - 0 = previous.length := by simp
  simp only [viewReadAt,positive,index,true_and,List.getElem?_append,
    Nat.lt_irrefl,↓reduceIte,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

theorem viewReadAt_previous (previous : List Bool) (borrowed : Bool) (x : Nat) :
    viewReadAt (previous ++ [borrowed]) (x+1) = (viewReadAt previous x).rename Nat.succ := by
  by_cases inside : x < previous.length
  · have nextInside : x+1 < (previous ++ [borrowed]).length := by simp;omega
    have index : (previous ++ [borrowed]).length - 1 - (x+1) = previous.length-1-x := by simp;omega
    have oldInside : previous.length-1-x < previous.length := by omega
    simp only [viewReadAt,inside,nextInside,true_and,index,List.getElem?_append,
      oldInside,↓reduceIte]
    cases selected : (previous[previous.length-1-x]?).getD false <;>
      simp only [selected,Bool.false_eq_true,ite_false,ite_true,Term.rename,renameArgs,Op.binders,liftRenaming]
  · have nextOutside : ¬ x+1 < (previous ++ [borrowed]).length := by simp;omega
    simp only [viewReadAt,inside,nextOutside,false_and,ite_false,Term.rename]

def ReadsAs (env : Environment) (previous : List Bool) (original borrowed : Nat → Term) : Prop :=
  ∀ x,Conversion.Conv env ((viewReadAt previous x).subst borrowed) (original x)

theorem ReadsAs.empty : ReadsAs env [] Term.var Term.var := by
  intro x
  simp only [viewReadAt,List.length_nil,Nat.not_lt_zero,false_and,ite_false,Term.subst]
  exact .refl _

theorem ReadsAs.extend (reading : ReadsAs env previous original borrowed)
    (flag : Bool) (value : Term) :
    ReadsAs env (previous ++ [flag]) (extendField original value)
      (extendField borrowed (if flag then .borrow value else value)) := by
  intro x
  cases x with
  | zero =>
    rw [viewReadAt_last]
    cases flag with
    | false => simp only [Bool.false_eq_true,ite_false,Term.subst,extendField];exact .refl _
    | true => simp only [ite_true,subst_deref,Term.subst,extendField];exact .legacy (.derefBorrow value)
  | succ x =>
    rw [viewReadAt_previous,Term.subst_rename]
    exact reading x

theorem ReadsAs.term (reading : ReadsAs env previous original borrowed)
    (closed : Conversion.Closed env) (term : Term) :
    Conversion.Conv env ((viewRead previous term).subst borrowed) (term.subst original) := by
  unfold viewRead
  rw [Term.subst_comp]
  exact RawLend.Conv.subst_congr closed reading term

/-- Every computed borrowed field really has an owned source type after
arbitrary parameter and previous-field substitutions. -/
theorem view_plan_borrowed_owned (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
    (planned : viewFieldPlan env family field = some plan) (borrowed : plan.borrowed = true)
    (σ : Nat → Term) : Owned env (field.domain.subst σ) := by
  unfold viewFieldPlan at planned
  simp only [Option.map] at planned
  repeat' first | split at planned | contradiction
  all_goals cases planned
  all_goals simp_all only [Bool.false_eq_true]
  all_goals simp_all only [Term.subst,substArgs,Op.binders,liftSub]
  all_goals first
    | exact Owned.buffer (.refl _)
    | exact Owned.family found boxed (.refl _)
    | exact Owned.family (by assumption) (by assumption) (.refl _)

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
