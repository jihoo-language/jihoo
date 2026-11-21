import Jihoo.NativeLoanGhostPromotion

/-! A runtime case followed immediately by erased applications is checked as
one spine. The intermediate case retains the CODE derivations of its owner
and branches. A completed spine has a nonfunction result. Ghost replay can
use the ordinary Case and application rules at the exact same annotation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ErasedCaseSpines

open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion (Conv)

inductive ErasedProducts : Term → Prop where
  | var (index : Nat) : ErasedProducts (.var index)
  | other : (∀ erased, op ≠ .pi erased) → ErasedProducts (.node op arguments)
  | binder : ErasedProducts range → ErasedProducts (.pi true domain range)

/-- Strip applications in the original expression, retaining the actual
case head used by the native saturation check. -/
def CaseHead : Term → Prop
  | .node .app [function,_] => CaseHead function
  | .node (.caseOf _ _) _ => True
  | _ => False

inductive Spine (env : Environment) (loans : Loans.Stack) (ctx : Context) : Term → Term → Prop where
  | case : env.families[family]? = some entry → entry.declaration.data = true → entry.boxed = true →
      indices.length = entry.declaration.arity →
      HasType env loans ctx true motive (dataMotiveType family entry.declaration.params
        entry.declaration.arity (indices.take entry.declaration.params) false) →
      HasType env loans ctx false scrutinee (.node (.ind family entry.declaration.arity) indices) →
      dataCaseTypes family entry.declaration.params ctx.length entry.signatures
        (indices.take entry.declaration.params) motive false false = some types →
      BranchTypes env loans ctx false types cases →
      Conv env (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) observed →
      ErasedProducts observed →
      Spine env loans ctx (.node (.caseOf family cases.length) (motive :: (cases ++ [scrutinee])))
        (.app (applications motive (indices.drop entry.declaration.params)) scrutinee)
  | apply : Spine env loans ctx function type → Conv env type (.pi true domain body) →
      HasType env loans ctx true argument domain → applicationAllowed env false domain argument →
      Spine env loans ctx (.app function argument) (body.subst (single argument))
  | convert : Spine env loans ctx term type → Conv env type result → Spine env loans ctx term result

private theorem branches_in_ghost (typed : BranchTypes env loans ctx false types terms) :
    BranchTypes env target ctx true types terms := by
  induction types generalizing terms with
  | nil => cases typed; exact .nil
  | cons type types ih =>
    cases typed with
    | cons head tail => exact .cons (head.ghost target) (ih tail)

/-- Promotion preserves the actual data family premises and each dependent
application's original argument and substituted result. -/
theorem Spine.ghost (typed : Spine env loans ctx term type) : HasType env target ctx true term type := by
  induction typed with
  | case found data boxed arity motive subject generated branches _ _ =>
    exact .dataElim (analysis := true) (proof := false) found data (fun _ => boxed) arity
      (motive.ghost target) (subject.ghost target)
      (by simpa only [Bool.not_true,Bool.and_false] using generated)
      (branches_in_ghost branches) (Or.inl rfl)
  | apply head converted argument _ ih =>
    exact .app (ih.convert converted) (argument.ghost target) (Or.inl rfl)
  | convert _ converted ih => exact ih.convert converted

theorem Spine.case_head (typed : Spine env loans ctx term type) : CaseHead term := by
  induction typed with
  | case => trivial
  | apply _ _ _ _ ih => exact ih
  | convert _ _ ih => exact ih

/-- The exposed spine is consumed in the application itself. A function
result is excluded before it could leave the original case expression. -/
inductive Complete (env : Environment) (loans : Loans.Stack) (ctx : Context) : Term → Term → Prop where
  | close : Spine env loans ctx function type → Conv env type (.pi true domain body) →
      HasType env loans ctx true argument domain → applicationAllowed env false domain argument →
      nonFunction env (body.subst (single argument)) →
      Complete env loans ctx (.app function argument) (body.subst (single argument))
  | convert : Complete env loans ctx term type → Conv env type result → Complete env loans ctx term result

theorem Complete.ghost (typed : Complete env loans ctx term type) : HasType env target ctx true term type := by
  induction typed with
  | close head converted argument allowed result => exact (Spine.apply head converted argument allowed).ghost
  | convert _ converted ih => exact ih.convert converted

theorem Complete.has_result_head (typed : Complete env loans ctx term type) : nonFunction env type := by
  induction typed with
  | close head converted argument allowed result => exact result
  | convert _ converted ih => exact ih.of_conversion converted.symm

/-- A completed case application cannot be converted to any product. -/
theorem Complete.not_product (typed : Complete env loans ctx term type)
    (admissible : EnvironmentDelta.Admissible env) : ¬ Conv env type (.pi erased domain body) :=
  fun converted => typed.has_result_head.not_pi converted admissible

end Jihoo.NativeKernel.Environment.LoanTyping.ErasedCaseSpines
