import Jihoo.NativeFamilyIotaConversion

/-! Raw rigid-head facts for enlarged reduction and disjointness of genuine
family roots from old computation heads. No typing or CR assumption appears. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)

private theorem mixed_list_refl (terms : List Term) : ListRel ACU.MixedRed terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (.refl _) ih
private theorem mixed_list_trans (first : ListRel ACU.MixedRed xs ys) (second : ListRel ACU.MixedRed ys zs) :
    ListRel ACU.MixedRed xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons first rest ih => cases second with | cons next tail => exact .cons (.trans first next) (ih tail)

private theorem mixed_of_arithmetic_list (kids : ListRel ACU.ArithmeticRed xs ys) : ListRel ACU.MixedRed xs ys := by
  induction kids with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.arithmetic first) ih

/-- Actual forward reduction retains a rigid head syntactically, including its
child reduction derivations. This is stronger than conversion injectivity. -/
private theorem mixed_rigid_shape (step : ACU.MixedRed input output) :
    ∀ {op xs}, ACU.fullRigid op = true → input = .node op xs →
    ∃ ys, output = .node op ys ∧ ListRel ACU.MixedRed xs ys := by
  induction step using ACU.MixedRed.rec (motive_2 := fun _ _ _ => True) with
  | refl term => intro op xs rigid equality; exact ⟨xs,equality,mixed_list_refl xs⟩
  | trans first second ihfirst ihsecond =>
    intro op xs rigid equality
    obtain ⟨ys,middle,firstKids⟩ := ihfirst rigid equality
    obtain ⟨zs,last,secondKids⟩ := ihsecond rigid middle
    exact ⟨zs,last,mixed_list_trans firstKids secondKids⟩
  | node op kids _ =>
    intro op' xs rigid equality
    cases equality
    exact ⟨_,rfl,kids⟩
  | arithmetic step =>
    intro op xs rigid equality
    obtain ⟨ys,last,kids⟩ := step.rigid_shape (Bool.and_eq_true_iff.mp rigid).2 equality
    exact ⟨ys,last,mixed_of_arithmetic_list kids⟩
  | compute step =>
    intro op xs rigid equality
    cases step <;> cases equality <;> contradiction
  | nil => trivial
  | cons => trivial

private theorem forward_list_refl (terms : List Term) : ListRel (EnvironmentDelta.Forward env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons .refl ih

private theorem forward_list_trans (first : ListRel (EnvironmentDelta.Forward env) xs ys)
    (second : ListRel (EnvironmentDelta.Forward env) ys zs) : ListRel (EnvironmentDelta.Forward env) xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons first rest ih => cases second with | cons next tail => exact .cons (.trans first next) (ih tail)

private theorem forward_of_mixed_list (kids : ListRel ACU.MixedRed xs ys) :
    ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction kids with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.acu first) ih

/-- Delta cannot contract a rigid non-global head; every retained child has an actual forward path. -/
private theorem old_forward_rigid_shape (step : EnvironmentDelta.Forward env input output) :
    ∀ {op xs}, EnvironmentDelta.Basis.rigid op = true → input = .node op xs →
    ∃ ys, output = .node op ys ∧ ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction step using EnvironmentDelta.Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro op xs rigid equality; exact ⟨xs,equality,forward_list_refl xs⟩
  | trans first second ihfirst ihsecond =>
      intro op xs rigid equality
      obtain ⟨ys,middle,firstKids⟩ := ihfirst rigid equality
      obtain ⟨zs,last,secondKids⟩ := ihsecond rigid middle
      exact ⟨zs,last,forward_list_trans firstKids secondKids⟩
  | node op kids _ =>
      intro op' xs rigid equality
      cases equality
      exact ⟨_,rfl,kids⟩
  | delta found =>
      intro op xs rigid equality
      cases equality
      simp [EnvironmentDelta.Basis.rigid,GlobalEnvironment.ordinary] at rigid
  | acu step =>
      intro op xs rigid equality
      obtain ⟨ys,last,kids⟩ := mixed_rigid_shape step (Bool.and_eq_true_iff.mp rigid).2 equality
      exact ⟨ys,last,forward_of_mixed_list kids⟩
  | nil => trivial
  | cons => trivial

/-- Family computation heads cease to be rigid in the enlarged relation. -/
def familyHead : Op → Bool
  | .elim _ _ | .caseOf _ _ | .view _ _ _ | .drop _ => true
  | _ => false

def rigid (op : Op) : Bool := EnvironmentDelta.Basis.rigid op && !familyHead op

theorem root_nonrigid (step : Root env (.node op xs) result) : rigid op = false := by
  cases step <;> rfl

/-- Same-head family/legacy critical pairs do not exist, even for raw forged
metadata. Root/child overlaps are separate residual obligations. -/
theorem root_compute_disjoint (step : Root env term result) (old : ACU.Computes term other) : False := by
  cases step <;> cases old

theorem root_global_disjoint (step : Root env (.node (.global g) []) result) : False := by
  cases step

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

private theorem list_old (related : ListRel (EnvironmentDelta.Forward env) xs ys) :
    ListRel (Forward env) xs ys := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.old head) ih

/-- Pi/Ind/Ref/Buffer and every new rigid head retain all actual child paths
under the genuine enlarged finite forward relation. -/
theorem Forward.rigid_shape (step : Forward env input output) :
    ∀ {op xs},rigid op = true → input = .node op xs →
      ∃ ys,output = .node op ys ∧ ListRel (Forward env) xs ys := by
  induction step using Forward.rec (motive_2 := fun _ _ _ => True) with
  | refl => intro op xs head same;exact ⟨xs,same,list_refl xs⟩
  | trans first second ihfirst ihsecond =>
    intro op xs head same
    obtain ⟨ys,middle,firstKids⟩ := ihfirst head same
    obtain ⟨zs,last,secondKids⟩ := ihsecond head middle
    exact ⟨zs,last,list_trans firstKids secondKids⟩
  | node op kids _ => intro op' xs head same;cases same;exact ⟨_,rfl,kids⟩
  | old original =>
    intro op xs head same
    obtain ⟨ys,last,kids⟩ := old_forward_rigid_shape original (Bool.and_eq_true_iff.mp head).1 same
    exact ⟨ys,last,list_old kids⟩
  | iota root =>
    intro op xs head same
    rw [same] at root
    rw [root_nonrigid root] at head
    contradiction
  | nil => trivial
  | cons => trivial

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
