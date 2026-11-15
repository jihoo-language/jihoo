import Jihoo.NativeGhostValueErasure
import Jihoo.NativeFamilyIotaDelta
import Jihoo.NativeFamilyIotaConversion
import Jihoo.NativeFamilyIotaValueMaps

/-! Value erasure of every genuine raw family-iota root. The unchanged family
metadata controls recursion and borrowing; no erased environment, typing,
normalization or runtime destruction premise is manufactured. -/
namespace Jihoo.NativeKernel.Environment.Semantics.ValueErasure
open FamilyIota
open NativeKernel.Conversion (ListRel)

private theorem erase_application (function argument : Term) :
    erase (.app function argument) = .app (erase function) (erase argument) := by
  simp only [Term.app,erase,eraseArgs,emit]

private theorem erase_borrow (value : Term) : erase (.borrow value) = .borrow (erase value) := by
  simp only [Term.borrow,erase,eraseArgs,emit]

private theorem erase_constructor (family constructor : Nat) (values : List Term) :
    erase (.node (.con family constructor values.length) values) =
      .node (.con family constructor (values.map erase).length) (values.map erase) := by
  simp only [erase,emit,eraseArgs_map,List.length_map]

private theorem erase_elimTerm (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    erase (elimTerm family motive cases scrutinee) = elimTerm family (erase motive) (cases.map erase) (erase scrutinee) := by
  simp only [elimTerm,erase,emit,eraseArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]

private theorem erase_caseTerm (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    erase (caseTerm family motive cases scrutinee) = caseTerm family (erase motive) (cases.map erase) (erase scrutinee) := by
  simp only [caseTerm,erase,emit,eraseArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]

private theorem erase_viewTerm (recursion : Bool) (family : Nat) (motive scrutinee : Term) (cases : List Term) :
    erase (viewTerm recursion family motive cases scrutinee) =
      viewTerm recursion family (erase motive) (cases.map erase) (erase scrutinee) := by
  simp only [viewTerm,erase,emit,eraseArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]

private theorem erasureBuilderMap : FamilyIota.BuilderMap erase := {
  app := erase_application
  borrow := erase_borrow
  elim := fun family motive cases scrutinee => erase_elimTerm family motive scrutinee cases
  caseOf := fun family motive cases scrutinee => erase_caseTerm family motive scrutinee cases
  view := fun recursion family motive cases scrutinee => erase_viewTerm recursion family motive scrutinee cases
  con := erase_constructor
  drop := fun family owner rest => by simp only [erase,eraseArgs,emit]
}

/-- Every raw Elim/Case/View/Drop equation survives erasure with the SAME raw
metadata table. This holds even for forged metadata and untyped source terms. -/
theorem root_erasure (step : FamilyIota.Root env term result) : FamilyIota.Root env (erase term) (erase result) :=
  erasureBuilderMap.root step

theorem root_projection (step : FamilyIota.Root env term result) :
    FamilyIota.Root env (project env term) (project env result) :=
  root_erasure (FamilyIota.Extended.root_expansion step)

private theorem project_node_cons (env : Environment) (op : Op) (first : Term) (rest : List Term) :
    project env (.node op (first :: rest)) = emit op ((first :: rest).map (project env)) := by
  rw [project,EnvironmentDelta.expand_node_cons,erase,eraseArgs_map,List.map_cons,
    EnvironmentDelta.expandArgs_map,List.map_map]
  rfl

private theorem extended_emit_congruence (op : Op)
    (related : ListRel (FamilyIota.Extended.Conv env) first second) :
    FamilyIota.Extended.Conv env (emit op first) (emit op second) := by
  cases op <;> try exact .node _ related
  all_goals
    cases related with
    | nil => exact .refl _
    | cons first rest =>
      cases rest with
      | nil => exact .node _ (.cons first .nil)
      | cons second rest =>
        cases rest with
        | nil => exact second
        | cons third rest => exact .node _ (.cons first (.cons second (.cons third rest)))

/-- The projected target includes genuine iota. In particular Drop(owner,T)
may project to a Drop node that only this enlarged target relates to T. -/
theorem family_conversion (admissible : EnvironmentDelta.Admissible env)
    (converted : FamilyIota.Extended.Conv env first second) :
    FamilyIota.Extended.Conv env (project env first) (project env second) := by
  induction converted using FamilyIota.Extended.Conv.rec
    (motive_2 := fun first second _ => ListRel (FamilyIota.Extended.Conv env)
      (first.map (project env)) (second.map (project env))) with
  | old original => exact .old (.acu (basis_conversion admissible original))
  | iota step => exact .iota (root_projection step)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op related ih =>
    cases related with
    | nil => exact .refl _
    | cons first rest => simpa only [project_node_cons,List.map_cons] using extended_emit_congruence op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

/-- Every genuine enlarged finite forward witness has a coherent value
projection; no runtime/heap step is identified with deleting an operand. -/
theorem family_forward (admissible : EnvironmentDelta.Admissible env)
    (forward : FamilyIota.Extended.Forward env first second) :
    FamilyIota.Extended.Conv env (project env first) (project env second) :=
  family_conversion admissible forward.toConv

end Jihoo.NativeKernel.Environment.Semantics.ValueErasure
