import Jihoo.NativeFamilyIotaCriticalPairs

/-! Genuine root/child residuals for every family equation. The generic
premise is only raw syntax congruence and is instantiated by concrete forward
reduction; it contains no typing, normalization or confluence oracle. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)
set_option linter.unusedSimpArgs false

structure Congruence (R : Term → Term → Prop) : Prop where
  node : ∀ op,GlobalEnvironment.ordinary op = true → ∀ {xs ys},ListRel R xs ys → R (.node op xs) (.node op ys)

private theorem related_length (related : ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem related_append (left : ListRel R xs ys) (right : ListRel R xs' ys') :
    ListRel R (xs ++ xs') (ys ++ ys') := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

private theorem related_drop (related : ListRel R xs ys) (n : Nat) : ListRel R (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih => cases related with
    | nil => exact .nil
    | cons _ tail => exact ih tail

private theorem related_lookup {j : Nat} (related : ListRel R xs ys) (selected : xs[j]? = some value) :
    ∃ value',ys[j]? = some value' ∧ R value value' := by
  induction related generalizing j with
  | nil => simp at selected
  | cons head tail ih => cases j with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected;subst value;exact ⟨_,rfl,head⟩
    | succ j => exact ih selected

private theorem applications_related (compat : Congruence R) (head : R function function') (arguments : ListRel R xs ys) :
    R (applications function xs) (applications function' ys) := by
  induction arguments generalizing function function' with
  | nil => exact head
  | cons argument rest ih => exact ih (compat.node .app (by rfl) (.cons head (.cons argument .nil)))

private theorem elimTerm_related (compat : Congruence R) (motiveRelated : R motive motive')
    (casesRelated : ListRel R cases cases') (valueRelated : R value value') :
    R (elimTerm family motive cases value) (elimTerm family motive' cases' value') := by
  unfold elimTerm
  rw [← related_length casesRelated]
  exact compat.node _ (by rfl) (.cons motiveRelated (related_append casesRelated (.cons valueRelated .nil)))

private theorem viewTerm_related (compat : Congruence R) (motiveRelated : R motive motive')
    (casesRelated : ListRel R cases cases') (valueRelated : R value value') :
    R (viewTerm recursion family motive cases value) (viewTerm recursion family motive' cases' value') := by
  unfold viewTerm
  rw [← related_length casesRelated]
  exact compat.node _ (by rfl) (.cons motiveRelated (related_append casesRelated (.cons valueRelated .nil)))

private theorem elimHypotheses_related (compat : Congruence R) (motiveRelated : R motive motive')
    (casesRelated : ListRel R cases cases') (fields : List Field) (valuesRelated : ListRel R values values') :
    ListRel R (elimHypotheses family motive cases fields values) (elimHypotheses family motive' cases' fields values') := by
  induction fields generalizing values values' with
  | nil => exact .nil
  | cons field fields ih => cases valuesRelated with
    | nil => exact .nil
    | cons value rest =>
      simp only [elimHypotheses,List.zip_cons_cons,List.filterMap_cons]
      by_cases recursive : field.recursive.isSome = true
      · simp only [recursive,ite_true]
        exact .cons (elimTerm_related compat motiveRelated casesRelated value) (ih rest)
      · simp only [recursive,ite_false]
        exact ih rest

private theorem elimBody_related (compat : Congruence R) (motiveRelated : R motive motive') (branchRelated : R branch branch')
    (casesRelated : ListRel R cases cases') (valuesRelated : ListRel R values values') :
    R (elimBody entry signature family motive branch cases values) (elimBody entry signature family motive' branch' cases' values') :=
  applications_related compat (applications_related compat branchRelated (related_drop valuesRelated _))
    (elimHypotheses_related compat motiveRelated casesRelated _ valuesRelated)

private theorem viewArguments_related (compat : Congruence R) (plans : List ViewFieldPlan) (valuesRelated : ListRel R values values') :
    ListRel R (viewArguments plans values) (viewArguments plans values') := by
  induction plans generalizing values values' with
  | nil => exact .nil
  | cons plan plans ih => cases valuesRelated with
    | nil => exact .nil
    | cons value rest =>
      simp only [viewArguments,List.zip_cons_cons,List.map_cons]
      refine .cons ?_ (ih rest)
      split
      · exact compat.node .borrow (by rfl) (.cons value .nil)
      · exact value

private theorem viewHypotheses_related (compat : Congruence R) (motiveRelated : R motive motive')
    (casesRelated : ListRel R cases cases') (plans : List ViewFieldPlan) (valuesRelated : ListRel R values values') :
    ListRel R (viewHypotheses recursion family motive cases plans values) (viewHypotheses recursion family motive' cases' plans values') := by
  cases recursion with
  | false => exact .nil
  | true =>
    induction plans generalizing values values' with
    | nil => exact .nil
    | cons plan plans ih => cases valuesRelated with
      | nil => exact .nil
      | cons value rest =>
        simp only [viewHypotheses,ite_true,List.zip_cons_cons,List.filterMap_cons]
        by_cases self : plan.self = true
        · simp only [self,ite_true]
          exact .cons (viewTerm_related compat motiveRelated casesRelated (compat.node .borrow (by rfl) (.cons value .nil))) (ih rest)
        · simp only [self,ite_false]
          exact ih rest

private theorem viewBody_related (compat : Congruence R) (motiveRelated : R motive motive') (branchRelated : R branch branch')
    (casesRelated : ListRel R cases cases') (valuesRelated : ListRel R values values') :
    R (viewBody recursion family params motive branch cases values plans)
      (viewBody recursion family params motive' branch' cases' values' plans) :=
  applications_related compat (applications_related compat branchRelated (viewArguments_related compat _ (related_drop valuesRelated _)))
    (viewHypotheses_related compat motiveRelated casesRelated _ (related_drop valuesRelated _))

/-- The Elim root residual is a genuine root and the original output follows
all actual changed motives, branches and fields by the same syntax relation. -/
theorem elim_residual (compat : Congruence R)
    (found : env.families[family]? = some entry) (signature : entry.signatures[constructor]? = some sig)
    (selected : cases[constructor]? = some branch) (count : cases.length = entry.signatures.length)
    (fields : values.length = sig.fields.length)
    (motiveRelated : R motive motive') (casesRelated : ListRel R cases cases') (valuesRelated : ListRel R values values') :
    ∃ branch',cases'[constructor]? = some branch' ∧
      Root env (elimTerm family motive' cases' (.node (.con family constructor values'.length) values'))
        (elimBody entry sig family motive' branch' cases' values') ∧
      R (elimBody entry sig family motive branch cases values) (elimBody entry sig family motive' branch' cases' values') := by
  obtain ⟨branch',selected',branchRelated⟩ := related_lookup casesRelated selected
  exact ⟨branch',selected',.elim found signature selected' ((related_length casesRelated).symm.trans count)
    ((related_length valuesRelated).symm.trans fields),elimBody_related compat motiveRelated branchRelated casesRelated valuesRelated⟩

theorem case_residual (compat : Congruence R)
    (found : env.families[family]? = some entry) (data : entry.declaration.data = true)
    (signature : entry.signatures[constructor]? = some sig)
    (selected : cases[constructor]? = some branch) (count : cases.length = entry.signatures.length)
    (fields : values.length = sig.fields.length)
    (casesRelated : ListRel R cases cases') (valuesRelated : ListRel R values values') :
    ∃ branch',cases'[constructor]? = some branch' ∧
      Root env (caseTerm family motive' cases' (.node (.con family constructor values'.length) values'))
        (applications branch' (values'.drop entry.declaration.params)) ∧
      R (applications branch (values.drop entry.declaration.params)) (applications branch' (values'.drop entry.declaration.params)) := by
  obtain ⟨branch',selected',branchRelated⟩ := related_lookup casesRelated selected
  exact ⟨branch',selected',.caseOf found data signature selected' ((related_length casesRelated).symm.trans count)
    ((related_length valuesRelated).symm.trans fields),applications_related compat branchRelated (related_drop valuesRelated _)⟩

theorem view_residual (compat : Congruence R)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
    (signature : entry.signatures[constructor]? = some sig)
    (selected : cases[constructor]? = some branch) (count : cases.length = entry.signatures.length)
    (fields : values.length = sig.fields.length) (bound : entry.declaration.params ≤ sig.fields.length)
    (planned : viewPlan env family (sig.fields.drop entry.declaration.params) = some plans)
    (motiveRelated : R motive motive') (casesRelated : ListRel R cases cases') (valuesRelated : ListRel R values values') :
    ∃ branch',cases'[constructor]? = some branch' ∧
      Root env (viewTerm recursion family motive' cases' (.borrow (.node (.con family constructor values'.length) values')))
        (viewBody recursion family entry.declaration.params motive' branch' cases' values' plans) ∧
      R (viewBody recursion family entry.declaration.params motive branch cases values plans)
        (viewBody recursion family entry.declaration.params motive' branch' cases' values' plans) := by
  obtain ⟨branch',selected',branchRelated⟩ := related_lookup casesRelated selected
  exact ⟨branch',selected',.view found boxed signature selected' ((related_length casesRelated).symm.trans count)
    ((related_length valuesRelated).symm.trans fields) bound planned,viewBody_related compat motiveRelated branchRelated casesRelated valuesRelated⟩

theorem drop_residual {R : Term → Term → Prop} {rest rest' owner' : Term} (restRelated : R rest rest') :
    Root env (.node (.drop family) [owner',rest']) rest' ∧ R rest rest' := ⟨.drop _ _ _,restRelated⟩

theorem Forward.congruence : Congruence (Forward env) :=
  ⟨by intro op ordinary xs ys related;exact .node op related⟩
theorem Iota.congruence : Congruence (Iota env) :=
  ⟨by intro op ordinary xs ys related;exact .node op related⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
