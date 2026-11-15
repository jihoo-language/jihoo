import Jihoo.NativeLoanSubstitution

/-! Function inversion retains the original loan stack and mode. All shared
and loan-specific rules participate in the same mutual derivation induction. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

def FunctionView (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Term → Prop
  | .lam erased domain body, type =>
      ∃ sort result, Binder env loans ctx erased domain sort ∧
        HasType env loans (⟨domain, erased⟩ :: ctx) mode body result ∧
        Conversion.Conv env (.pi erased domain result) type
  | .app function argument, type =>
      ∃ erased domain result, HasType env loans ctx mode function (.pi erased domain result) ∧
        HasType env loans ctx (mode || erased) argument domain ∧
        applicationAllowed env mode domain argument ∧
        Conversion.Conv env (result.subst (single argument)) type
  | _, _ => True

theorem FunctionView.convert (view : FunctionView env loans ctx mode term first)
    (converted : Conversion.Conv env first second) : FunctionView env loans ctx mode term second := by
  fun_cases FunctionView env loans ctx mode term first <;> simp only [FunctionView] at view ⊢
  · obtain ⟨sort, result, domain, body, original⟩ := view
    exact ⟨sort, result, domain, body, original.trans converted⟩
  · obtain ⟨erased, domain, result, function, argument, allowed, original⟩ := view
    exact ⟨erased, domain, result, function, argument, allowed, original.trans converted⟩

theorem HasType.functionView (typed : HasType env loans ctx mode term type) :
    FunctionView env loans ctx mode term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost expression result _ =>
      FunctionView env stack context ghost expression result)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case lam domain body _ _ => exact ⟨_, _, domain, body, .refl _⟩
  case app function argument allowed _ _ => exact ⟨_, _, _, function, argument, allowed, .refl _⟩
  case dataElim found isData boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
    cases analysis <;> trivial
  case convert original converted ih => exact ih.convert converted

theorem HasType.lamView
    (typed : HasType env loans ctx mode (.lam erased domain body) type) :
    ∃ sort result, Binder env loans ctx erased domain sort ∧
      HasType env loans (⟨domain, erased⟩ :: ctx) mode body result ∧
      Conversion.Conv env (.pi erased domain result) type := typed.functionView

theorem HasType.appView
    (typed : HasType env loans ctx mode (.app function argument) type) :
    ∃ erased domain result, HasType env loans ctx mode function (.pi erased domain result) ∧
      HasType env loans ctx (mode || erased) argument domain ∧
      applicationAllowed env mode domain argument ∧
      Conversion.Conv env (result.subst (single argument)) type := typed.functionView

end Jihoo.NativeKernel.Environment.LoanTyping
