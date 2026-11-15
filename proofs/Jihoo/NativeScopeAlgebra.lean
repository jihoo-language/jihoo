import Jihoo.NativeSubstitution
import Jihoo.NativeConversion

/-! Raw scope algebra, independent of typing and result formation. It is
intended for genuine forward preservation from an explicit checked input. -/
namespace Jihoo.NativeKernel

theorem Term.Scoped.child {op : Op} {children : List Term} {depth index : Nat} {child : Term}
    (scope : (Term.node op children).Scoped depth)
    (selected : children[index]? = some child) : child.Scoped (depth + op.binders index) := by
  cases scope with
  | node children => exact children _ _ selected

theorem Term.Scoped.monotone {term : Term} {source target : Nat}
    (scope : term.Scoped source) (larger : source ≤ target) : term.Scoped target := by
  simpa only [Term.rename_id] using scope.rename (ρ := id) (fun index bound => Nat.lt_of_lt_of_le bound larger)

theorem Term.Scoped.leaf (depth : Nat) (op : Op) : (Term.node op []).Scoped depth :=
  .node (by intro index term selected; cases selected)

theorem Term.Scoped.nonbinding (nonbinding : ∀ index,op.binders index = 0)
    (scopes : ∀ child ∈ children,child.Scoped depth) : (Term.node op children).Scoped depth :=
  .node (by
    intro index child selected
    simpa only [nonbinding,Nat.add_zero] using scopes child (List.mem_of_getElem? selected))

theorem Term.Scoped.application {f a : Term} {depth : Nat}
    (function : f.Scoped depth) (argument : a.Scoped depth) : (Term.node .app [f,a]).Scoped depth := by
  apply Term.Scoped.nonbinding (by intro index; rfl)
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact function
  · rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · cases member

private theorem list_scopes (related : Conversion.ListRel
    (fun (first second : Term) => ∀ depth,first.Scoped depth → second.Scoped depth) first second) :
    ∀ (depth : Nat) (op : Op) (offset : Nat),
      (∀ (index : Nat) (child : Term),first[index]? = some child → child.Scoped (depth + op.binders (offset+index))) →
      ∀ (index : Nat) (child : Term),second[index]? = some child → child.Scoped (depth + op.binders (offset+index)) := by
  induction related with
  | nil => intros; contradiction
  | cons head tail ih =>
    intro depth op offset scopes index child selected
    cases index with
    | zero =>
      cases selected
      exact head _ (scopes 0 _ rfl)
    | succ index =>
      have rest := ih depth op (offset+1) (by
        intro index child selected
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using scopes (index+1) child selected)
      simpa only [Nat.add_assoc,Nat.add_comm 1 index] using rest index child selected

theorem Term.Scoped.node_transport (scope : (Term.node op first).Scoped depth)
    (related : Conversion.ListRel (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) :
    (Term.node op second).Scoped depth := by
  cases scope with
  | node scopes =>
    apply Term.Scoped.node
    have result := list_scopes related depth op 0 (by simpa only [Nat.zero_add] using scopes)
    simpa only [Nat.zero_add] using result

end Jihoo.NativeKernel
