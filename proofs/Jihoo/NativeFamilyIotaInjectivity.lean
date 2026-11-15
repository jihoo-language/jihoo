import Jihoo.NativeFamilyIotaChurchRosser

/-! Injectivity and separation in the genuine enlarged raw conversion follow
from its actual finite forward Church-Rosser theorem and its new rigid mask. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)

private theorem arithmetic_variable_shape (step : ACU.ArithmeticRed input result) :
    ∀ x,input = .var x → result = .var x := by
  induction step using ACU.ArithmeticRed.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro x same;exact same
  | trans _ _ first second => intro x same;exact second x (first x same)
  | nil => trivial
  | cons => trivial
  | _ => intro x same;cases same

private theorem mixed_variable_shape (step : ACU.MixedRed input result) :
    ∀ x,input = .var x → result = .var x := by
  induction step using ACU.MixedRed.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro x same;exact same
  | trans _ _ first second => intro x same;exact second x (first x same)
  | node => intro x same;cases same
  | arithmetic original => exact arithmetic_variable_shape original
  | compute original => intro x same;cases original <;> cases same
  | nil => trivial
  | cons => trivial

private theorem old_variable_shape (step : EnvironmentDelta.Forward env input result) :
    ∀ x,input = .var x → result = .var x := by
  induction step using EnvironmentDelta.Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro x same;exact same
  | trans _ _ first second => intro x same;exact second x (first x same)
  | node => intro x same;cases same
  | acu original => exact mixed_variable_shape original
  | delta => intro x same;cases same
  | nil => trivial
  | cons => trivial

theorem Forward.variable_shape (step : Forward env input result) :
    ∀ x,input = .var x → result = .var x := by
  induction step using Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro x same;exact same
  | trans _ _ first second => intro x same;exact second x (first x same)
  | node => intro x same;cases same
  | old original => exact old_variable_shape original
  | iota original => intro x same;cases original <;> cases same
  | nil => trivial
  | cons => trivial

private theorem joined_children (left : ListRel (Forward env) xs common) (right : ListRel (Forward env) ys common) :
    ListRel (Conv env) xs ys := by
  induction left generalizing ys with
  | nil => cases right;exact .nil
  | cons head tail ih => cases right with
    | cons head' tail' => exact .cons (Conv.ofForwardJoin head head') (ih tail')

theorem Conv.full_rigid_node_injective (converted : Conv env (.node op xs) (.node op' ys))
    (leftHead : rigid op = true) (rightHead : rigid op' = true) (admissible : EnvironmentDelta.Admissible env) :
    op = op' ∧ ListRel (Conv env) xs ys := by
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  obtain ⟨leftChildren,leftShape,leftKids⟩ := left.rigid_shape leftHead rfl
  obtain ⟨rightChildren,rightShape,rightKids⟩ := right.rigid_shape rightHead rfl
  obtain ⟨rfl,rfl⟩ := Term.node.inj (leftShape.symm.trans rightShape)
  exact ⟨rfl,joined_children leftKids rightKids⟩

theorem Conv.full_rigid_disjoint (leftHead : rigid op = true) (rightHead : rigid op' = true)
    (different : op ≠ op') (converted : Conv env (.node op xs) (.node op' ys))
    (admissible : EnvironmentDelta.Admissible env) : False :=
  different (converted.full_rigid_node_injective leftHead rightHead admissible).1

theorem Conv.full_variable_node_separate (head : rigid op = true)
    (converted : Conv env (.var x) (.node op xs)) (admissible : EnvironmentDelta.Admissible env) : False := by
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  have variableShape := left.variable_shape x rfl
  obtain ⟨children,node,kids⟩ := right.rigid_shape head rfl
  rw [variableShape] at node
  cases node

theorem Conv.full_variable_injective (converted : Conv env (.var x) (.var y)) (admissible : EnvironmentDelta.Admissible env) :
    x = y := by
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  exact Term.var.inj ((left.variable_shape x rfl).symm.trans (right.variable_shape y rfl))

theorem Conv.pi_injective (converted : Conv env (.pi erased domain body) (.pi erased' domain' body'))
    (admissible : EnvironmentDelta.Admissible env) :
    erased = erased' ∧ Conv env domain domain' ∧ Conv env body body' := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases head
  cases kids with
  | cons domainRelated tail => cases tail with
    | cons bodyRelated tail => exact ⟨rfl,domainRelated,bodyRelated⟩

theorem Conv.sort_injective {first second : SortTag} (converted : Conv env first.term second.term)
    (admissible : EnvironmentDelta.Admissible env) : first = second := by
  cases first <;> cases second
  all_goals obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  all_goals cases head
  all_goals rfl

theorem Conv.full_universe_injective (converted : Conv env (.univ first) (.univ second))
    (admissible : EnvironmentDelta.Admissible env) : first = second := by
  have same : SortTag.type first = SortTag.type second := converted.sort_injective admissible
  exact SortTag.type.inj same

theorem Conv.array_injective (converted : Conv env (.array a) (.array b)) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => exact first

theorem Conv.eq_injective (converted : Conv env (.eq a b) (.eq a' b')) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a a' ∧ Conv env b b' := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => cases rest with | cons second rest => exact ⟨first,second⟩

theorem Conv.lt_injective (converted : Conv env (.lt a b) (.lt a' b')) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a a' ∧ Conv env b b' := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => cases rest with | cons second rest => exact ⟨first,second⟩

theorem Conv.refine_injective (converted : Conv env (.refine a) (.refine b)) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => exact first

theorem Conv.buffer_injective (converted : Conv env (.buffer a) (.buffer b)) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => exact first

theorem Conv.ref_injective (converted : Conv env (.ref a) (.ref b)) (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases kids with | cons first rest => exact first

theorem Conv.ind_injective (converted : Conv env (.node (.ind family count) xs) (.node (.ind family' count') ys))
    (admissible : EnvironmentDelta.Admissible env) : family = family' ∧ count = count' ∧ ListRel (Conv env) xs ys := by
  obtain ⟨head,kids⟩ := converted.full_rigid_node_injective rfl rfl admissible
  cases head
  exact ⟨rfl,rfl,kids⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended

namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient

theorem Star.natural_shape (step : Star env term result) (view : ACU.Arithmetic term (.natural n)) :
    ACU.Arithmetic result (.natural n) := by
  induction step with
  | refl => exact view
  | cons first rest ih => exact ih (first.input view).natural_inv

end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient

namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

theorem Conv.natural_injective (converted : Conv env (.natural first) (.natural second))
    (admissible : EnvironmentDelta.Admissible env) : first = second := by
  obtain ⟨common,left,right⟩ := Quotient.projected_join converted admissible
  have leftView := left.natural_shape (n := first) (by simpa only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using ACU.Arithmetic.refl (.natural first))
  have rightView := right.natural_shape (n := second) (by simpa only [EnvironmentDelta.expand,EnvironmentDelta.expandArgs] using ACU.Arithmetic.refl (.natural second))
  exact ACU.Arithmetic.natural_injective (leftView.symm.trans rightView)

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
