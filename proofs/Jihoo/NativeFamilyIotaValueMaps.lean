import Jihoo.NativeFamilyIotaSyntax

/-! Minimal raw syntax maps for the genuine iota builders. Unlike congruence
on all ordinary nodes, this contract permits Strict/Free erasure and Lend
macro expansion. Its concrete clients prove these seven constructor equations. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

structure BuilderMap (transform : Term → Term) : Prop where
  app : ∀ function argument, transform (.app function argument) = .app (transform function) (transform argument)
  borrow : ∀ value, transform (.borrow value) = .borrow (transform value)
  elim : ∀ family motive cases scrutinee,
    transform (elimTerm family motive cases scrutinee) = elimTerm family (transform motive) (cases.map transform) (transform scrutinee)
  caseOf : ∀ family motive cases scrutinee,
    transform (caseTerm family motive cases scrutinee) = caseTerm family (transform motive) (cases.map transform) (transform scrutinee)
  view : ∀ recursion family motive cases scrutinee,
    transform (viewTerm recursion family motive cases scrutinee) =
      viewTerm recursion family (transform motive) (cases.map transform) (transform scrutinee)
  con : ∀ family constructor values,
    transform (.node (.con family constructor values.length) values) =
      .node (.con family constructor (values.map transform).length) (values.map transform)
  drop : ∀ family owner rest, transform (.node (.drop family) [owner,rest]) =
    .node (.drop family) [transform owner,transform rest]

theorem BuilderMap.applications (compatible : BuilderMap transform) (function : Term) (arguments : List Term) :
    transform (applications function arguments) = applications (transform function) (arguments.map transform) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument rest ih =>
    simpa only [Environment.applications,List.foldl_cons,List.map_cons,compatible.app] using ih (.app function argument)

theorem BuilderMap.elimHypotheses (compatible : BuilderMap transform) (family : Nat) (motive : Term)
    (cases : List Term) (fields : List Field) (values : List Term) :
    (elimHypotheses family motive cases fields values).map transform =
      elimHypotheses family (transform motive) (cases.map transform) fields (values.map transform) := by
  induction fields generalizing values with
  | nil => simp [FamilyIota.elimHypotheses]
  | cons field fields ih =>
    cases values with
    | nil => simp [FamilyIota.elimHypotheses]
    | cons value values =>
      simp only [FamilyIota.elimHypotheses,List.zip_cons_cons,List.filterMap_cons,List.map_cons]
      by_cases recursive : field.recursive.isSome = true
      · simp only [recursive,ite_true,List.map_cons,compatible.elim]
        exact congrArg (fun tail => elimTerm family (transform motive) (cases.map transform) (transform value) :: tail) (ih values)
      · simp only [recursive]
        exact ih values

theorem BuilderMap.elimBody (compatible : BuilderMap transform) (entry : CheckedFamily) (signature : Signature)
    (family : Nat) (motive branch : Term) (cases values : List Term) :
    transform (elimBody entry signature family motive branch cases values) =
      elimBody entry signature family (transform motive) (transform branch) (cases.map transform) (values.map transform) := by
  simp only [FamilyIota.elimBody,compatible.applications,compatible.elimHypotheses,List.map_drop]

theorem BuilderMap.viewArguments (compatible : BuilderMap transform) (plans : List ViewFieldPlan) (values : List Term) :
    (viewArguments plans values).map transform = viewArguments plans (values.map transform) := by
  induction plans generalizing values with
  | nil => simp [FamilyIota.viewArguments]
  | cons plan plans ih =>
    cases values with
    | nil => simp [FamilyIota.viewArguments]
    | cons value values =>
      simp only [FamilyIota.viewArguments,List.zip_cons_cons,List.map_cons]
      by_cases borrowed : plan.borrowed = true
      · simp only [borrowed,ite_true,compatible.borrow]
        exact congrArg (fun tail => Term.borrow (transform value) :: tail) (ih values)
      · simp only [borrowed]
        exact congrArg (fun tail => transform value :: tail) (ih values)

theorem BuilderMap.viewHypotheses (compatible : BuilderMap transform) (recursion : Bool) (family : Nat)
    (motive : Term) (cases : List Term) (plans : List ViewFieldPlan) (values : List Term) :
    (viewHypotheses recursion family motive cases plans values).map transform =
      viewHypotheses recursion family (transform motive) (cases.map transform) plans (values.map transform) := by
  cases recursion with
  | false => simp [FamilyIota.viewHypotheses]
  | true =>
    induction plans generalizing values with
    | nil => simp [FamilyIota.viewHypotheses]
    | cons plan plans ih =>
      cases values with
      | nil => simp [FamilyIota.viewHypotheses]
      | cons value values =>
        simp only [FamilyIota.viewHypotheses,List.zip_cons_cons,List.filterMap_cons,List.map_cons]
        by_cases self : plan.self = true
        · simp only [self,ite_true,List.map_cons,compatible.view,compatible.borrow]
          exact congrArg (fun tail => viewTerm true family (transform motive) (cases.map transform) (.borrow (transform value)) :: tail) (ih values)
        · simp only [self]
          exact ih values

theorem BuilderMap.viewBody (compatible : BuilderMap transform) (recursion : Bool) (family params : Nat)
    (motive branch : Term) (cases values : List Term) (plans : List ViewFieldPlan) :
    transform (viewBody recursion family params motive branch cases values plans) =
      viewBody recursion family params (transform motive) (transform branch) (cases.map transform) (values.map transform) plans := by
  simp only [FamilyIota.viewBody,compatible.applications,compatible.viewArguments,compatible.viewHypotheses,List.map_drop]

/-- The generic mapper retains all lookup guards, recursion plans and field
positions. It requires no typing, honest metadata or equality oracle. -/
theorem BuilderMap.root (compatible : BuilderMap transform) (step : Root env term result) :
    Root env (transform term) (transform result) := by
  cases step with
  | @elim family entry constructor signature cases branch motive values found sigFound selected count fields =>
    rw [compatible.elim,compatible.con,compatible.elimBody]
    exact .elim found sigFound (by simp only [List.getElem?_map,selected,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
  | @caseOf family entry constructor signature cases branch motive values found data sigFound selected count fields =>
    rw [compatible.caseOf,compatible.con,compatible.applications,List.map_drop]
    exact .caseOf found data sigFound (by simp only [List.getElem?_map,selected,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
  | @view family entry constructor signature cases branch plans recursion motive values found boxed sigFound selected count fields bound planned =>
    rw [compatible.view,compatible.borrow,compatible.con,compatible.viewBody]
    exact .view found boxed sigFound (by simp only [List.getElem?_map,selected,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields) bound planned
  | drop => rw [compatible.drop]; exact .drop _ _ _

end Jihoo.NativeKernel.Environment.FamilyIota
