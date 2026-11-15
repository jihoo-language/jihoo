import Jihoo.NativeHigherKindSyntax

/-! Exact kind-variable lookup under arbitrary native prefix binders. These
frames support type-code Pi bodies without assuming that their ordinary domain
has a closed inhabitant or supplying an invalid strengthening theorem. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds
open Jihoo.NativeKernel.Environment.Conversion

def Frame (kinds : List Kind) (ctx : Context) (positions : Nat → Nat) : Prop :=
  ∀ index,NativeKernel.lookup ctx (positions index) = (kinds[index]?).map (fun kind => ⟨kind.syntax,false⟩)

theorem Frame.identity (kinds : List Kind) : Frame kinds (context kinds) id := lookup_context kinds

theorem Frame.weaken (frame : Frame kinds ctx positions) (binding : Binding) :
    Frame kinds (binding :: ctx) (fun index => positions index + 1) := by
  intro index
  change (NativeKernel.lookup ctx (positions index)).map _ = _
  rw [frame index]
  cases kinds[index]? <;> simp only [Option.map,Kind.syntax_rename]

theorem Frame.extend (frame : Frame kinds ctx positions) (kind : Kind) :
    Frame (kind :: kinds) (⟨kind.syntax,false⟩ :: ctx) (liftRenaming 1 positions) := by
  intro index
  cases index with
  | zero => simp only [liftRenaming,Indexed.liftRenaming,NativeKernel.lookup,Kind.syntax_rename,List.getElem?_cons_zero,Option.map]
  | succ index =>
    change (NativeKernel.lookup ctx (positions index)).map _ = (kinds[index]?).map _
    rw [frame index]
    cases kinds[index]? <;> simp only [Option.map,Kind.syntax_rename]

theorem Kind.classified_sort (wf : UnifiedProgram.EnvWellFormed env) (kind : Kind) (sort : SortTag)
    (converted : Conv env kind.syntax sort.term) : ∃ level,kind = .base level ∧ sort = .type level.val := by
  cases kind with
  | base level =>
    cases sort with
    | prop =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .universe level.val) (op' := .prop) rfl rfl (by intro h; cases h) converted wf.admissible)
    | type value =>
      have same := converted.full_universe_injective wf.admissible
      exact ⟨level,rfl,congrArg SortTag.type same.symm⟩
  | arrow domain codomain =>
    cases sort with
    | prop =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .prop) rfl rfl (by intro h; cases h) converted wf.admissible)
    | type value =>
      exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .universe value) rfl rfl (by intro h; cases h) converted wf.admissible)

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds
