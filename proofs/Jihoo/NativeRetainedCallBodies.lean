import Jihoo.NativeCallResourceContracts
import Jihoo.NativeCodeRenaming

/-! An admitted call retains its original source body, context, code typing
and resource scope. This is the binding-preserving call boundary; no raw code
beta recheck or heap execution correspondence is asserted. -/
namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay Jihoo.Quantity NativeQuantity

set_option linter.unusedSimpArgs false

/-- Opening the syntactic source lambda prefix preserves code typing in the
original extended source context. Supplied arguments are not substituted. -/
theorem openHead_typed
    (openedHead : openHead fuel env ctx head supplied = some opened)
    (context : ContextFormed env ctx) (typed : HasType env ctx mode head type) :
    ContextFormed env opened.context ∧
      ∃ bodyType, HasType env opened.context mode opened.body bodyType := by
  induction fuel generalizing ctx head supplied opened type with
  | zero => simp [openHead] at openedHead
  | succ fuel ih =>
      simp only [openHead] at openedHead
      split at openedHead
      · rename_i erased domain body argument arguments
        split at openedHead
        · contradiction
        · cases resolved : ContextModes.resolve fuel env ctx erased domain with
          | none => simp [resolved] at openedHead
          | some binderMode =>
              cases rest : openHead fuel env (⟨domain,erased⟩ :: ctx) body arguments with
              | none => simp [resolved,rest] at openedHead
              | some next =>
                  simp only [resolved,rest,Bind.bind,Option.bind,Option.some.injEq] at openedHead
                  cases openedHead
                  obtain ⟨sort,bodyType,binder,bodyTyped,_⟩ := typed.lamView
                  exact ih (opened := next) rest (.cons context binder) bodyTyped
      · cases openedHead
        exact ⟨context,_,typed⟩

/-- The original resource check supplies the original code-typed source
body, its source context, all invoked scope contracts and every relevant
argument's code typing and resource certificate. For an unopened computed
callee the retained body is the callee expression itself. -/
theorem checked_app_retained_body_contracts
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened body bodyType,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      HasType env [] false (.app function argument) result ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      openHead fuel env [] head supplied = some opened ∧
      ContextFormed env opened.context ∧
      HasType env opened.context false opened.body bodyType ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      (∀ value ∈ runtimeArguments entries,
        (∃ domain, HasType env [] false value domain) ∧ ResourceSafe env value) := by
  obtain ⟨head,supplied,entries,result,opened,body,split,sourceTyped,replayed,
      openedHead,projected,bodyContract,arguments⟩ := checked_app_exact_source_contracts checked
  obtain ⟨signature,headTyped,_,_⟩ := CallReplay.infer_sound (CallReplay.checked_origin replayed).2
  obtain ⟨formed,bodyType,bodyTyped⟩ := openHead_typed openedHead .nil headTyped
  exact ⟨head,supplied,entries,result,opened,body,bodyType,split,sourceTyped,replayed,
    openedHead,formed,bodyTyped,projected,bodyContract,arguments⟩

/-- Keeping a source body beneath another runtime binding preserves its code
typing. The original invoked-body contract remains the call's resource
certificate; it is not replaced by a syntactic beta-reduct check. -/
theorem checked_app_retained_body_weaken
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (checked : checkResource (fuel + 1) env (.app function argument) = true)
    (inserted : Term) (erased : Bool) :
    ∃ (opened : Opened) (bodyType : Term),
      HasType env (⟨inserted,erased⟩ :: opened.context) false
        (opened.body.rename Nat.succ) (bodyType.rename Nat.succ) ∧
      ∃ head supplied, openHead fuel env [] head supplied = some opened := by
  obtain ⟨head,supplied,entries,result,opened,body,bodyType,split,sourceTyped,replayed,
      openedHead,formed,bodyTyped,projected,bodyContract,arguments⟩ :=
    checked_app_retained_body_contracts checked
  exact ⟨opened,bodyType,bodyTyped.modeWeaken wellFormed inserted erased,head,supplied,openedHead⟩

end Jihoo.NativeKernel.Environment.ContextQuantity
