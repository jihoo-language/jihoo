import Jihoo.NativeCoreValueContexts

/-! Typed value changes in function positions and beneath binders. Arguments
and binder annotations retain their raw conversion witnesses, which the
dependent codomain and body context respectively require. -/
namespace Jihoo.NativeKernel.NativeCoreBinderPreservation

open Environment
open NativeCoreValueContexts (Change strict_effect_typing)
open NativeCorePureComputationNormal (GhostNormalization computeNormalization)

private def PiPremises (env : Environment) (ctx : Context) : Term → Term → Prop
  | .pi erased domain body, type =>
      ∃ s r : SortTag, LoanTyping.Binder env [] ctx erased domain s ∧
        LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true body r.term ∧
        LoanTyping.Conversion.Conv env (s.pi r).term type
  | _, _ => True

private theorem PiPremises.convert (view : PiPremises env ctx term A)
    (converted : LoanTyping.Conversion.Conv env A B) : PiPremises env ctx term B := by
  fun_cases PiPremises env ctx term A <;> simp only [PiPremises] at view ⊢
  obtain ⟨s, r, domain, body, original⟩ := view
  exact ⟨s, r, domain, body, original.trans converted⟩

private theorem pi_premises (typed : LoanTyping.HasType env loans ctx mode term type) :
    PiPremises env ctx term type := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => PiPremises env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case pi domain body _ _ =>
    cases domain with
    | intro typed allowed => exact ⟨_, _, .intro (typed.ghost []) allowed, body.ghost [], .refl _⟩
  case dataElim => split <;> trivial
  case convert => exact PiPremises.convert (by assumption) (by assumption)

private theorem change_scope (wf : UnifiedProgram.EnvWellFormed env)
    (domain : LoanTyping.GhostTransform env A A')
    (body : ∀ {ctx type}, LoanTyping.HasType env [] ctx true b type →
      LoanTyping.HasType env [] ctx true b' type)
    (binder : LoanTyping.Binder env [] ctx erased A s)
    (typed : LoanTyping.HasType env [] (⟨A, erased⟩ :: ctx) true b type) :
    LoanTyping.Binder env [] ctx erased A' s ∧
      LoanTyping.HasType env [] (⟨A', erased⟩ :: ctx) true b' type := by
  cases binder with
  | intro formed allowed =>
      exact ⟨.intro (domain.typed formed) (LoanTyping.binderAllowed_congr allowed domain.converted),
        (body typed).ghostContext wf ((LoanTyping.Ghost.ContextConversion.refl env ctx).extend
          domain.converted erased wf.closed)⟩

theorem pi_change (wf : UnifiedProgram.EnvWellFormed env) (domain : GhostNormalization env A A')
    (body : Change env B B') : Change env (.pi erased A B) (.pi erased A' B') := by
  have rebuild {A A' B B' : Term} (d : LoanTyping.GhostTransform env A A')
      (b : ∀ {ctx type}, LoanTyping.HasType env [] ctx true B type →
        LoanTyping.HasType env [] ctx true B' type)
      {ctx type} (typed : LoanTyping.HasType env [] ctx true (.pi erased A B) type) :
      LoanTyping.HasType env [] ctx true (.pi erased A' B') type := by
    obtain ⟨s, r, binding, range, principal⟩ := pi_premises typed
    obtain ⟨newBinding, newRange⟩ := change_scope wf d b binding range
    exact (LoanTyping.HasType.pi newBinding newRange).convert principal
  refine ⟨rebuild domain.raw body.raw, ?_⟩
  simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
  exact rebuild domain.expanded body.expanded

theorem lam_change (wf : UnifiedProgram.EnvWellFormed env) (domain : GhostNormalization env A A')
    (body : Change env b b') : Change env (.lam erased A b) (.lam erased A' b') := by
  have rebuild {A A' b b' : Term} (d : LoanTyping.GhostTransform env A A')
      (bodies : ∀ {ctx type}, LoanTyping.HasType env [] ctx true b type →
        LoanTyping.HasType env [] ctx true b' type)
      {ctx type} (typed : LoanTyping.HasType env [] ctx true (.lam erased A b) type) :
      LoanTyping.HasType env [] ctx true (.lam erased A' b') type := by
    obtain ⟨_, result, binding, source, principal⟩ := typed.lamView
    obtain ⟨newBinding, newBody⟩ := change_scope wf d bodies binding source
    have annotation : LoanTyping.Conversion.Conv env (.pi erased A' result) (.pi erased A result) :=
      .node (.pi erased) (.cons d.converted.symm (.cons (.refl _) .nil))
    exact (LoanTyping.HasType.lam newBinding newBody).convert (annotation.trans principal)
  refine ⟨rebuild domain.raw body.raw, ?_⟩
  simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
  exact rebuild domain.expanded body.expanded

theorem application_change (wf : UnifiedProgram.EnvWellFormed env) (funChange : Change env f f')
    (argChange : GhostNormalization env a a') : Change env (.app f a) (.app f' a') := by
  have rebuild {f f' a a' : Term} (functions : ∀ {ctx type}, LoanTyping.HasType env [] ctx true f type →
      LoanTyping.HasType env [] ctx true f' type) (arguments : LoanTyping.GhostTransform env a a')
      {ctx type} (typed : LoanTyping.HasType env [] ctx true (.app f a) type) :
      LoanTyping.HasType env [] ctx true (.app f' a') type := by
    obtain ⟨erased, A, B, funTyped, argTyped, _, principal⟩ := typed.appView
    have instantiated : LoanTyping.Conversion.Conv env (B.subst (single a')) (B.subst (single a)) := by
      apply RawLend.Conv.subst_congr wf.closed
      intro index
      cases index
      · exact arguments.converted.symm
      · exact .refl _
    have argument : LoanTyping.HasType env [] ctx (true || erased) a' A := by
      simpa only [Bool.true_or] using arguments.typed argTyped
    exact (LoanTyping.HasType.app (functions funTyped) argument (Or.inl rfl)).convert (instantiated.trans principal)
  refine ⟨rebuild funChange.raw argChange.raw, ?_⟩
  simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
  exact rebuild funChange.expanded argChange.expanded

theorem beta_change (wf : UnifiedProgram.EnvWellFormed env) :
    Change env (.app (.lam erased domain body) argument) (body.subst (single argument)) :=
  Change.iteration (.retained (computeNormalization wf (.beta erased domain body argument)))

theorem strict_application_change :
    Change env (.app (.strict effect f) a) (.strict effect (.app f a)) := by
  have rebuild {effect f a ctx type} (typed : LoanTyping.HasType env [] ctx true (.app (.strict effect f) a) type) :
      LoanTyping.HasType env [] ctx true (.strict effect (.app f a)) type := by
    obtain ⟨erased, _, _, function, argument, allowed, converted⟩ := typed.appView
    obtain ⟨_, effectTyped⟩ := strict_effect_typing function
    obtain ⟨_, fTyped, fConverted⟩ := function.principalView
    exact .strict effectTyped ((LoanTyping.HasType.app (fTyped.convert fConverted) argument allowed).convert converted)
  refine ⟨rebuild, ?_⟩
  simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs]
  exact rebuild

end Jihoo.NativeKernel.NativeCoreBinderPreservation
