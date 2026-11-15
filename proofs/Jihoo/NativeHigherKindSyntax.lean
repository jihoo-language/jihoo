import Jihoo.NativeEnvironmentTypeUniqueness
import Jihoo.NativeAdministrativeUniverseValues
import Jihoo.NativeSemanticUniverseBoundary
set_option maxUniverseOffset 40

/-! Arbitrary higher kinds over all native universe inputs. Contexts may
interleave code variables and functions of any finite kind order. These kinds
retain native noncumulative Pi sorts, including administrative sort32. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds
open Jihoo.NativeKernel.Environment.Conversion

inductive Kind where
  | base (level : Fin 33)
  | arrow (domain codomain : Kind)
  deriving DecidableEq

def Kind.syntax : Kind → Term
  | .base level => .univ level.val
  | .arrow domain codomain => .pi false domain.syntax codomain.syntax

def Kind.nativeLevel : Kind → Nat
  | .base level => level.val+1
  | .arrow domain codomain => max domain.nativeLevel codomain.nativeLevel

def Kind.sort : Kind → Finite.LevelSort
  | .base level => .type ⟨level.val+1,by omega⟩
  | .arrow domain codomain => domain.sort.pi codomain.sort

def Kind.code : (kind : Kind) → Finite.Universe kind.sort
  | .base level => Finite.AdministrativeValues.codeUniverse level
  | .arrow domain codomain => Finite.pi domain.code codomain.sort (fun _ => codomain.code)

theorem Kind.sort_native (kind : Kind) : kind.sort.native = .type kind.nativeLevel := by
  induction kind with
  | base => rfl
  | arrow domain codomain hd hc => simp only [Kind.sort,Kind.nativeLevel,Finite.LevelSort.pi_native,hd,hc,SortTag.pi]

theorem Kind.nativeLevel_bound (kind : Kind) : kind.nativeLevel ≤ 33 := by
  induction kind with
  | base level => exact Nat.succ_le_of_lt level.isLt
  | arrow domain codomain hd hc => exact Nat.max_le.mpr ⟨hd,hc⟩

theorem Kind.syntax_rename (kind : Kind) (indices : Nat → Nat) : kind.syntax.rename indices = kind.syntax := by
  induction kind generalizing indices with
  | base => simp only [Kind.syntax,Term.univ,Term.rename,renameArgs]
  | arrow domain codomain hd hc =>
    simp only [Kind.syntax,Term.pi,Term.rename,renameArgs,Op.binders,hd,hc]

theorem Kind.syntax_subst (kind : Kind) (values : Nat → Term) : kind.syntax.subst values = kind.syntax := by
  induction kind generalizing values with
  | base => simp only [Kind.syntax,Term.univ,Term.subst,substArgs]
  | arrow domain codomain hd hc =>
    simp only [Kind.syntax,Term.pi,Term.subst,substArgs,Op.binders,hd,hc]

def Kind.Valid : Kind → Prop
  | .base level => level.val < 32
  | .arrow domain codomain => domain.Valid ∧ codomain.Valid

theorem Kind.valid_of_typed (kind : Kind) (typed : HasType env ctx mode kind.syntax type) : kind.Valid := by
  induction kind generalizing ctx mode type with
  | base level => exact universe_input_bound typed
  | arrow domain codomain hd hc =>
    obtain ⟨domainSort,bodySort,binder,bodyTyped,converted⟩ := typed.piView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    exact ⟨hd domainTyped,hc bodyTyped⟩

theorem Kind.valid_nativeLevel_bound (kind : Kind) (valid : kind.Valid) : kind.nativeLevel ≤ 32 := by
  induction kind with
  | base level => exact Nat.succ_le_of_lt valid
  | arrow domain codomain hd hc => exact Nat.max_le.mpr ⟨hd valid.1,hc valid.2⟩

theorem Kind.formed (kind : Kind) (valid : kind.Valid) : HasType env ctx mode kind.syntax (.univ kind.nativeLevel) := by
  induction kind generalizing ctx mode with
  | base level => exact .univ valid
  | arrow domain codomain hd hc =>
    exact .pi (s := .type domain.nativeLevel) (r := .type codomain.nativeLevel)
      (.intro (hd valid.1 (mode := true)) (Or.inl (by intro h; cases h))) (hc valid.2 (mode := true))

theorem Kind.syntax_injective (wf : UnifiedProgram.EnvWellFormed env) {first second : Kind}
    (converted : Conv env first.syntax second.syntax) : first = second := by
  induction first generalizing second with
  | base level =>
    cases second with
    | base other =>
      have same := converted.full_universe_injective wf.admissible
      exact congrArg Kind.base (Fin.ext same)
    | arrow domain codomain =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .universe level.val) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | arrow domain codomain hd hc =>
    cases second with
    | base level =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .universe level.val) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow other result =>
      obtain ⟨erased,first,second⟩ := converted.pi_injective wf.admissible
      cases hd first
      cases hc second
      rfl

def context (kinds : List Kind) : Context := kinds.map fun kind => ⟨kind.syntax,false⟩

inductive Member : Kind → List Kind → Nat → Type where
  | here : Member kind (kind :: rest) 0
  | there : Member kind rest index → Member kind (other :: rest) (index+1)

theorem Member.lookup (member : Member kind kinds index) :
    NativeKernel.lookup (context kinds) index = some ⟨kind.syntax,false⟩ := by
  induction member with
  | here => simp only [context,List.map,NativeKernel.lookup,Kind.syntax_rename]
  | there previous ih =>
    change (NativeKernel.lookup (context _) _).map _ = _
    rw [ih]
    simp only [Option.map,Kind.syntax_rename]

theorem lookup_context (kinds : List Kind) (index : Nat) :
    NativeKernel.lookup (context kinds) index = (kinds[index]?).map (fun kind => ⟨kind.syntax,false⟩) := by
  induction kinds generalizing index with
  | nil => rfl
  | cons kind rest ih =>
    cases index with
    | zero => simp only [context,List.map,NativeKernel.lookup,Kind.syntax_rename,List.getElem?_cons_zero,Option.map]
    | succ index =>
      change (NativeKernel.lookup (context rest) index).map _ = (rest[index]?).map _
      rw [ih]
      cases rest[index]? <;> simp only [Option.map,Kind.syntax_rename]

def Member.ofLookup {kinds : List Kind} {index : Nat} {kind : Kind} (found : kinds[index]? = some kind) : Member kind kinds index :=
  match kinds,index with
  | [],_ => by simp at found
  | first :: _,0 => by simp only [List.getElem?_cons_zero,Option.some.injEq] at found; cases found; exact .here
  | _ :: rest,index+1 => .there (Member.ofLookup (kinds := rest) (by simpa only [List.getElem?_cons_succ] using found))

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds
