import Jihoo.NativeLendRawBinding
import Jihoo.NativeFamilyIotaInjectivity

/-! The unconditional raw Lend equation has its own rigid mask and actual
finite forward shape theorem. Injectivity follows from its proved raw CR. -/
namespace Jihoo.NativeKernel.Environment.RawLend
open NativeKernel.Conversion (ListRel)

def lendHead : Op → Bool
  | .lend => true
  | _ => false

def rigid (op : Op) : Bool := FamilyIota.Extended.rigid op && !lendHead op

private theorem list_refl (terms : List Term) : ListRel (Forward env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons .refl ih

private theorem list_trans (first : ListRel (Forward env) xs ys) (second : ListRel (Forward env) ys zs) :
    ListRel (Forward env) xs zs := by
  induction first generalizing zs with
  | nil => cases second;exact .nil
  | cons head tail ih => cases second with
    | cons head' tail' => exact .cons (head.trans head') (ih tail')

private theorem list_old (related : ListRel (FamilyIota.Extended.Forward env) xs ys) :
    ListRel (Forward env) xs ys := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.old head) ih

theorem Forward.rigid_shape (step : Forward env input output) :
    ∀ {op xs},rigid op = true → input = .node op xs →
      ∃ ys,output = .node op ys ∧ ListRel (Forward env) xs ys := by
  induction step using Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro op xs head same;exact ⟨xs,same,list_refl xs⟩
  | trans _ _ first second =>
      intro op xs head same
      obtain ⟨ys,middle,firstKids⟩ := first head same
      obtain ⟨zs,last,secondKids⟩ := second head middle
      exact ⟨zs,last,list_trans firstKids secondKids⟩
  | node op kids _ => intro op' xs head same;cases same;exact ⟨_,rfl,kids⟩
  | old original =>
      intro op xs head same
      obtain ⟨ys,last,kids⟩ := original.rigid_shape (Bool.and_eq_true_iff.mp head).1 same
      exact ⟨ys,last,list_old kids⟩
  | lend owner reader continuation =>
      intro op xs head same
      cases same
      simp [rigid,lendHead] at head
  | nil => trivial
  | cons => trivial

theorem Forward.variable_shape (step : Forward env input result) :
    ∀ x,input = .var x → result = .var x := by
  induction step using Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro x same;exact same
  | trans _ _ first second => intro x same;exact second x (first x same)
  | node => intro x same;cases same
  | old original => exact original.variable_shape
  | lend => intro x same;cases same
  | nil => trivial
  | cons => trivial

private theorem joined_children (left : ListRel (Forward env) xs common) (right : ListRel (Forward env) ys common) :
    ListRel (Conv env) xs ys := by
  induction left generalizing ys with
  | nil => cases right;exact .nil
  | cons head tail ih => cases right with
    | cons head' tail' => exact .cons (head.toConv.trans head'.toConv.symm) (ih tail')

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


theorem Conv.natural_injective (converted : Conv env (.natural first) (.natural second))
    (admissible : EnvironmentDelta.Admissible env) : first = second := by
  have mapped : FamilyIota.Extended.Conv env (.natural first) (.natural second) := by
    simpa only [project,Term.natural,EnvironmentDelta.expand,EnvironmentDelta.expandArgs,unlend,unlendArgs,rebuild] using converted.projected admissible
  exact mapped.natural_injective admissible

end Jihoo.NativeKernel.Environment.RawLend
