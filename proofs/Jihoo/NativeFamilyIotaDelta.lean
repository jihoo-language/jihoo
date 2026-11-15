import Jihoo.NativeFamilyIotaArithmeticResiduals

/-! Global expansion transports genuine family equations on arbitrary raw
metadata. Together with old checked delta projection this separates the global
critical pairs from the remaining family/ACU parallel diamond. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open EnvironmentDelta (expand expandArgs expandArgs_map expand_ordinary)
open NativeKernel.Conversion (ListRel)

private def Expanded (env : Environment) (term result : Term) : Prop := result = expand env term

private theorem expanded_list (terms : List Term) : ListRel (Expanded env) terms (terms.map (expand env)) := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons rfl ih

private theorem expansion_congruence : Congruence (Expanded env) := by
  constructor
  intro op ordinary xs ys related
  change .node op ys = expand env (.node op xs)
  rw [expand_ordinary ordinary,expandArgs_map]
  apply congrArg (Term.node op)
  induction related with
  | nil => rfl
  | cons head tail ih =>
    change _ = expand env _ at head
    simp only [List.map_cons]
    rw [head,ih]

private theorem constructor_expansion (family constructor : Nat) (values : List Term) :
    expand env (.node (.con family constructor values.length) values) =
      .node (.con family constructor (values.map (expand env)).length) (values.map (expand env)) := by
  rw [expand_ordinary (by rfl),expandArgs_map,List.length_map]

private theorem elimTerm_expansion (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    expand env (elimTerm family motive cases scrutinee) =
      elimTerm family (expand env motive) (cases.map (expand env)) (expand env scrutinee) := by
  unfold elimTerm
  rw [expand_ordinary (by rfl),expandArgs_map]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

private theorem caseTerm_expansion (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    expand env (caseTerm family motive cases scrutinee) =
      caseTerm family (expand env motive) (cases.map (expand env)) (expand env scrutinee) := by
  unfold caseTerm
  rw [expand_ordinary (by rfl),expandArgs_map]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

private theorem viewTerm_expansion (recursion : Bool) (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    expand env (viewTerm recursion family motive cases scrutinee) =
      viewTerm recursion family (expand env motive) (cases.map (expand env)) (expand env scrutinee) := by
  unfold viewTerm
  rw [expand_ordinary (by rfl),expandArgs_map]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

/-- Family equations commute with one-pass transparent expansion without
assuming typing, honest family metadata, closed globals or normalization laws. -/
theorem root_expansion (step : Root env term result) : Root env (expand env term) (expand env result) := by
  cases step with
  | @elim family entry constructor signature cases branch motive values found sigFound selected count fields =>
    obtain ⟨branch',selected',root,output⟩ := elim_residual expansion_congruence found sigFound selected count fields
      (motive' := expand env motive) rfl (expanded_list cases) (expanded_list values)
    change _ = expand env _ at output
    rw [output] at root
    simpa only [elimTerm_expansion,constructor_expansion] using root
  | @caseOf family entry constructor signature cases branch motive values found data sigFound selected count fields =>
    obtain ⟨branch',selected',root,output⟩ := case_residual (motive' := expand env motive) expansion_congruence
      found data sigFound selected count fields (expanded_list cases) (expanded_list values)
    change _ = expand env _ at output
    rw [output] at root
    simpa only [caseTerm_expansion,constructor_expansion] using root
  | @view family entry constructor signature cases branch plans recursion motive values found boxed sigFound selected count fields bound planned =>
    obtain ⟨branch',selected',root,output⟩ := view_residual (recursion := recursion) expansion_congruence
      found boxed sigFound selected count fields bound planned
      (motive' := expand env motive) rfl (expanded_list cases) (expanded_list values)
    change _ = expand env _ at output
    rw [output] at root
    simpa only [viewTerm_expansion,expand,expandArgs,constructor_expansion] using root
  | drop => simp only [expand,expandArgs];exact .drop _ _ _

/-- The actual family-only contextual path also survives global projection. -/
theorem Iota.expansion (step : Iota env term result) : Iota env (expand env term) (expand env result) := by
  induction step using Iota.rec
    (motive_2 := fun xs ys _ => ListRel (Iota env) (expandArgs env xs) (expandArgs env ys)) with
  | root original => exact .root (root_expansion original)
  | refl => exact .refl
  | trans _ _ first second => exact first.trans second
  | node op related ih =>
    cases related with
    | nil => exact .refl
    | cons head tail => simpa only [EnvironmentDelta.expand_node_cons,expandArgs] using Iota.node op ih
  | nil => simp only [expandArgs];exact .nil
  | cons _ _ first rest => simp only [expandArgs];exact .cons first rest

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
