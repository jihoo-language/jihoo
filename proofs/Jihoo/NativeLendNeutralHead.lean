import Jihoo.NativeLendRawInjectivity
import Jihoo.NativeFamilyIotaNeutralCoherence

/-! Raw Lend expansion preserves free neutral heads. Unconditional macro
conversion cannot turn an open neutral application into a rigid binder
or a constructor. -/
namespace Jihoo.NativeKernel.Environment.RawLend

theorem project_neutralSpine (env : Environment) (head : Nat) (args : List Term) :
    project env (neutralSpine head args) = neutralSpine head (args.map (project env)) := by
  induction args with
  | nil => simp only [neutralSpine,List.map_nil,project,EnvironmentDelta.expand,unlend]
  | cons argument rest ih =>
    change project env (.node .app [neutralSpine head rest,argument]) =
      .node .app [neutralSpine head (rest.map (project env)),project env argument]
    simp only [project_ordinary (op := .app) (by rfl),List.map_cons,List.map_nil,rebuild,ih]

theorem Conv.neutralSpine_node_separate (admissible : EnvironmentDelta.Admissible env)
    (notApplication : op ≠ .app) (headRigid : rigid op = true) :
    ¬ Conv env (neutralSpine head args) (.node op children) := by
  intro converted
  have ordinary : GlobalEnvironment.ordinary op = true := by
    cases op <;> first | rfl | cases headRigid
  have notLend : op ≠ .lend := by intro same; subst op; cases headRigid
  have projected := converted.projected admissible
  rw [project_neutralSpine,project_ordinary ordinary,rebuild_other notLend] at projected
  exact FamilyIota.Extended.Conv.neutralSpine_node_separate admissible ordinary notApplication
    (Bool.and_eq_true_iff.mp headRigid).1 projected

private theorem original_arguments
    (converted : NativeKernel.Conversion.ListRel (FamilyIota.Extended.Conv env)
      (first.map (project env)) (second.map (project env))) :
    NativeKernel.Conversion.ListRel (Conv env) first second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => exact .nil
    | cons => cases converted
  | cons left rest ih =>
    cases second with
    | nil => cases converted
    | cons right tail =>
      cases converted with
      | cons heads tails =>
        exact .cons ((project_forward env left).toConv.trans ((Conv.old heads).trans
          (project_forward env right).toConv.symm)) (ih tails)

theorem Conv.neutralSpine_injective (admissible : EnvironmentDelta.Admissible env)
    (converted : Conv env (neutralSpine head first) (neutralSpine other second)) :
    head = other ∧ NativeKernel.Conversion.ListRel (Conv env) first second := by
  have projected := converted.projected admissible
  rw [project_neutralSpine,project_neutralSpine] at projected
  obtain ⟨head,children⟩ := FamilyIota.Extended.Conv.neutralSpine_injective admissible projected
  exact ⟨head,original_arguments children⟩

end Jihoo.NativeKernel.Environment.RawLend
