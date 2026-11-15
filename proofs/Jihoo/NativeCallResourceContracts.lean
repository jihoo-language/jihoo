import Jihoo.NativeExactClosing

/-! Closed admitted calls supply their actual argument resource contracts and
opened-source body contract from the same original projection. No separate
function/argument checker run, bounded-checker monotonicity, or caller-supplied
body safety flag is assumed. Native heap/closure simulation remains separate. -/
namespace Jihoo.NativeKernel.Environment.CallReplay

/-- Runtime entries retain the same actual code typing check; erased entries
are absent, as determined by the original dependent signature replay. -/
theorem Steps.runtime_entry_typed
    (steps : Steps env ctx false signature arguments entries result)
    (member : entry ∈ entries) (relevant : entry.erased = false) :
    HasType env ctx false entry.value entry.domain := by
  induction steps with
  | nil => cases member
  | cons normalized checked application safe next ih =>
      rcases List.mem_cons.mp member with rfl | member
      · subst relevant
        exact Checker.check_sound checked
      · exact ih member

theorem Steps.runtime_argument_typed
    (steps : Steps env ctx false signature arguments entries result)
    (member : argument ∈ runtimeArguments entries) :
    ∃ domain, HasType env ctx false argument domain := by
  unfold runtimeArguments at member
  obtain ⟨entry,selected,found⟩ := List.mem_filterMap.mp member
  cases entry with
  | mk erased domain value =>
      cases erased with
      | true => simp at found
      | false =>
          simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq] at found
          subst argument
          exact ⟨domain,steps.runtime_entry_typed selected rfl⟩

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity CallReplay
variable {control : Control} {controls : List Control} {arguments : List Term}

/-- Closed source control evidence, obtained from the original admission. -/
def ClosedControlContract (control : Control) : Prop :=
  ControlScoped 0 control ∧ LocalScopes control

theorem ClosedControlContract.zero (contract : ClosedControlContract control) (resource : Nat) :
    control.demand resource = some 0 :=
  contract.1.demand_above contract.2 (Nat.zero_le _)

private theorem sequence_contracts
    (scope : ControlScoped 0 (sequence controls)) (locals : LocalScopes (sequence controls)) :
    ∀ control ∈ controls, ClosedControlContract control := by
  induction controls with
  | nil => intro control member; cases member
  | cons first rest ih =>
      intro control member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨scope.1,locals.1⟩
      · exact ih scope.2 locals.2 _ member

private theorem app_control_contracts
    (scope : ControlScoped 0 (if modes.isEmpty then callControl body runtime
      else .seq (sequence runtime) (.scopes modes body)))
    (locals : LocalScopes (if modes.isEmpty then callControl body runtime
      else .seq (sequence runtime) (.scopes modes body))) :
    BodyContract modes body ∧ ∀ control ∈ runtime, ClosedControlContract control := by
  cases modes with
  | nil =>
      change ControlScoped 0 (.seq body (sequence runtime)) at scope
      change LocalScopes (.seq body (sequence runtime)) at locals
      exact ⟨ControlScoped.bodyContract (modes := []) (body := body) scope.1 locals.1,sequence_contracts scope.2 locals.2⟩
  | cons mode modes =>
      change ControlScoped 0 (.seq (sequence runtime) (.scopes (mode :: modes) body)) at scope
      change LocalScopes (.seq (sequence runtime) (.scopes (mode :: modes) body)) at locals
      exact ⟨scope.2.bodyContract locals.2,sequence_contracts scope.1 locals.1⟩

/-- All original call certificates are retained. A nonempty opened source
lambda prefix gets its invoked BodyContract; for a computed head with no
opened lambdas, the empty-prefix contract describes the callee expression. -/
theorem checked_app_contracts
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened runtime body,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      partialOK fuel env [] entries result = true ∧
      openHead fuel env [] head supplied = some opened ∧
      (runtimeArguments entries).mapM (projectRaw fuel env []) = some runtime ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      (∀ control ∈ runtime, ClosedControlContract control) := by
  cases projected : project (fuel + 1) env [] (.app function argument) with
  | none => simp [checkResource,projected] at checked
  | some control =>
      have demand : control.demand 0 = some 0 := by
        simpa only [checkResource,projected,Option.any_some,beq_iff_eq] using checked
      have locals := demand_localScopes _ demand
      have scope := project_scope projected
      obtain ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,guarded,openedHead,arguments,bodyProjected,same⟩ :=
        app_origin (project_origin projected).1
      rw [same] at scope locals
      have contracts := app_control_contracts scope locals
      exact ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,guarded,openedHead,arguments,bodyProjected,contracts.1,contracts.2⟩

private theorem mapM_selected {visit : Term → Option Control}
    (mapped : arguments.mapM visit = some controls) (member : argument ∈ arguments) :
    ∃ control, visit argument = some control ∧ control ∈ controls := by
  induction arguments generalizing controls with
  | nil => cases member
  | cons first rest ih =>
      simp only [List.mapM_cons] at mapped
      obtain ⟨head,headFound,mapped⟩ := Option.bind_eq_some_iff.mp mapped
      obtain ⟨tail,tailFound,same⟩ := Option.bind_eq_some_iff.mp mapped
      cases same
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨head,headFound,by simp⟩
      · obtain ⟨control,found,selected⟩ := ih tailFound member
        exact ⟨control,found,by simp [selected]⟩

/-- Each relevant actual argument is independently resource-safe from its
already executed original projection; no child resource query is rerun. -/
theorem runtime_arguments_resourceSafe
    (mapped : (runtimeArguments entries).mapM (projectRaw fuel env []) = some controls)
    (contracts : ∀ control ∈ controls, ClosedControlContract control)
    (member : argument ∈ runtimeArguments entries) : ResourceSafe env argument := by
  obtain ⟨control,raw,selected⟩ := mapM_selected mapped member
  have contract := contracts control selected
  have projected : project fuel env [] argument = some control := by
    have scopeAccepted : scopeCheck 0 control = true := scopeCheck_correct.mpr contract.1
    simp only [project,raw,Bind.bind,Option.bind,List.length_nil,scopeAccepted,↓reduceIte]
  exact ⟨EnvironmentCaseQuantity.compileTable_valid,fuel,control,projected,contract.zero 0,contract.2,contract.1⟩

/-- Same-boundary admission of a closed call supplies both actual code typing
and actual resource safety of every relevant argument, plus the opened body
contract. Neither argument nor body safety is an input flag. -/
theorem checked_app_runtime_contracts
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened body,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      openHead fuel env [] head supplied = some opened ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      (∀ value ∈ runtimeArguments entries,
        (∃ domain, HasType env [] false value domain) ∧ ResourceSafe env value) := by
  obtain ⟨head,supplied,entries,result,opened,runtime,body,split,replayed,guarded,openedHead,mapped,bodyProjected,bodyContract,arguments⟩ :=
    checked_app_contracts checked
  have steps := (CallReplay.infer_sound (CallReplay.checked_origin replayed).2).choose_spec.2.1
  refine ⟨head,supplied,entries,result,opened,body,split,replayed,openedHead,bodyProjected,bodyContract,?_⟩
  intro value member
  exact ⟨steps.runtime_argument_typed member,runtime_arguments_resourceSafe mapped arguments member⟩

end Jihoo.NativeKernel.Environment.ContextQuantity

namespace Jihoo.NativeKernel.NativeQuantity

/-- Reassemble the exact original source tree from the actual spine parser.
No unrelated head/signature membership witness is supplied by the caller. -/
theorem splitSpine_reassembles
    (selected : splitSpine fuel source initial = some (head,supplied)) :
    Environment.applications head supplied = Environment.applications source initial := by
  induction fuel generalizing source initial head supplied with
  | zero => simp [splitSpine] at selected
  | succ fuel ih =>
      cases source with
      | var index =>
          simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
          obtain ⟨rfl,rfl⟩ := selected
          rfl
      | node op children =>
          cases op <;> try
            (simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
             obtain ⟨rfl,rfl⟩ := selected
             rfl)
          case app =>
            cases children with
            | nil =>
                simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
                obtain ⟨rfl,rfl⟩ := selected
                rfl
            | cons function rest =>
                cases rest with
                | nil =>
                    simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
                    obtain ⟨rfl,rfl⟩ := selected
                    rfl
                | cons argument tail =>
                    cases tail with
                    | nil =>
                        simp only [splitSpine] at selected
                        simpa only [Environment.applications,List.foldl_cons] using ih selected
                    | cons first tail =>
                        simp only [splitSpine,Option.some.injEq,Prod.mk.injEq] at selected
                        obtain ⟨rfl,rfl⟩ := selected
                        rfl

end Jihoo.NativeKernel.NativeQuantity

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity CallReplay

/-- A closed admitted application retains exact-source typing as well as the
same original runtime-argument resource/body certificates. -/
theorem checked_app_exact_source_contracts
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened body,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      HasType env [] false (.app function argument) result ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      openHead fuel env [] head supplied = some opened ∧
      projectRaw fuel env opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      (∀ value ∈ runtimeArguments entries,
        (∃ domain, HasType env [] false value domain) ∧ ResourceSafe env value) := by
  obtain ⟨head,supplied,entries,result,opened,body,split,replayed,openedHead,bodyProjected,bodyContract,arguments⟩ :=
    checked_app_runtime_contracts checked
  have applied := (CallReplay.infer_sound (CallReplay.checked_origin replayed).2).choose_spec.2.2
  have reassembled := NativeQuantity.splitSpine_reassembles split
  have original : HasType env [] false (.app function argument) result := by
    rw [reassembled] at applied
    exact applied
  exact ⟨head,supplied,entries,result,opened,body,split,original,replayed,openedHead,bodyProjected,bodyContract,arguments⟩

/-- Original successful checks survive later checked worlds through retained
prefix evidence. No executable code/resource checker is rerun in the extension. -/
theorem checked_app_runtime_contracts_in_extension
    (checked : checkResource (fuel + 1) before (.app function argument) = true)
    (extension : Extends before after) :
    ∃ head supplied entries result opened body,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      HasType after [] false (.app function argument) result ∧
      CallReplay.checked fuel before [] false head supplied = some (entries,result) ∧
      openHead fuel before [] head supplied = some opened ∧
      projectRaw fuel before opened.context opened.body = some body ∧
      BodyContract opened.modes body ∧
      (∀ value ∈ runtimeArguments entries,
        (∃ domain, HasType after [] false value domain) ∧ EnvironmentQuantity.Safe after value) := by
  obtain ⟨head,supplied,entries,result,opened,body,split,typed,replayed,openedHead,bodyProjected,bodyContract,arguments⟩ :=
    checked_app_exact_source_contracts checked
  refine ⟨head,supplied,entries,result,opened,body,split,typed.extend extension,replayed,openedHead,bodyProjected,bodyContract,?_⟩
  intro value member
  obtain ⟨⟨domain,typedArgument⟩,resource⟩ := arguments value member
  exact ⟨⟨domain,typedArgument.extend extension⟩,before,extension,resource,
    EnvironmentCaseQuantity.compileTable_valid.extend extension⟩

end Jihoo.NativeKernel.Environment.ContextQuantity
