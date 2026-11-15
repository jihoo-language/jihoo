import Jihoo.NativeCallBindingStores

/-! Original source slot permissions agree with the actual dependent call
replay. Erasure flags and dependent domain conversion are derived from the
same prefix, not supplied as certificates by a caller. -/
namespace Jihoo.NativeKernel.Environment.CallReplay

theorem Steps.entry_length (steps : Steps env ctx mode signature arguments entries result) :
    entries.length = arguments.length := by
  simpa only [List.length_map] using congrArg List.length steps.values

/-- Every original entry retains its actual ghost type, including erased
arguments that do not have an independent runtime code derivation. -/
theorem Steps.entry_ghost_typed (steps : Steps env ctx mode signature arguments entries result)
    (member : entry ∈ entries) : HasType env ctx true entry.value entry.domain := by
  induction steps with
  | nil => cases member
  | cons normalized checked allowed safe next ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact (Checker.check_sound checked).ghost
      · exact ih member

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- The exact raw source binder flags agree with the original actual replay
flags, in the native de Bruijn order. No source signature flag is guessed. -/
theorem Telescope.replay_erased_flags
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (steps : CallReplay.Steps env [] false actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    finalContext.map Binding.erased = (entries.map CallReplay.Argument.erased).reverse ++ ctx.map Binding.erased := by
  induction source generalizing values actualSignature arguments entries actualResult with
  | nil =>
      cases steps with
      | nil => rfl
      | cons => simp at arity
  | @cons ctx erased domain sort body count finalContext result binding tail ih =>
      cases steps with
      | nil => simp at arity
      | @cons fuel actualSignature actualErased actualDomain actualBody value rest entries actualResult
          normalized checked allowed safe next =>
          have converted := sameSignature.trans (Conversion.normalize?_sound normalized)
          have piConverted : Conversion.Conv env
              (.pi erased (domain.subst values) (body.subst (liftSubOne values)))
              (.pi actualErased actualDomain actualBody) := by
            simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
          obtain ⟨sameErased,domainConverted,bodyConverted⟩ :=
            piConverted.pi_injective history.wellFormed.admissible
          subst actualErased
          have nextSignature : Conversion.Conv env (body.subst (consValues value values))
              (actualBody.subst (single value)) := by
            simpa only [subst_lift_consValues] using
              bodyConverted.substitution (single value) history.wellFormed.closed
          have flags := ih (values := consValues value values) next nextSignature (by simpa using arity)
          simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using flags

theorem lookup_erased_eq (ctx : Context) (index : Nat) :
    (lookup ctx index).map Binding.erased = (ctx.map Binding.erased)[index]? := by
  induction ctx generalizing index with
  | nil => simp [lookup]
  | cons binding ctx ih =>
      cases index <;> simp [lookup,Option.map_map,Function.comp_def,ih]

/-- Every actual consumed source slot has its original flag, actual stored
argument, and a dependent annotation convertible to the actual replay domain.
Only actual non-erased entries obtain source-variable and value code typing. -/
def TypedSourceSlots (env : Environment) (ctx : Context) (values : Nat → Term)
    (entries : List CallReplay.Argument) : Prop :=
  ∀ index entry, entries[index]? = some entry → ∃ binding,
    lookup ctx (entries.length - 1 - index) = some binding ∧
    binding.erased = entry.erased ∧
    values (entries.length - 1 - index) = entry.value ∧
    Conversion.Conv env (binding.ty.subst values) entry.domain ∧
    (entry.erased = false →
      HasType env ctx false (.var (entries.length - 1 - index)) binding.ty ∧
      HasType env [] false entry.value entry.domain)

theorem Telescope.replay_source_slots
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (steps : CallReplay.Steps env [] false actualSignature arguments entries actualResult)
    (sameSignature : Conversion.Conv env (signature.subst values) actualSignature)
    (arity : arguments.length = count) :
    TypedSourceSlots env finalContext (pushValues values arguments) entries := by
  have store := source.close_typed_store history formed closing steps sameSignature arity
  have flags := source.replay_erased_flags history steps sameSignature arity
  intro index entry selected
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have reverseInside : entries.length - 1 - index < (entries.map CallReplay.Argument.erased).reverse.length := by
    simp only [List.length_reverse,List.length_map]
    omega
  have selectedFlag : (lookup finalContext (entries.length - 1 - index)).map Binding.erased = some entry.erased := by
    rw [lookup_erased_eq,flags,List.getElem?_append_left reverseInside]
    rw [List.getElem?_reverse' (i := entries.length - 1 - index) (j := index)
      (by simp only [List.length_map]; omega)]
    simp only [List.getElem?_map,selected,Option.map_some]
  obtain ⟨binding,found,sameFlag⟩ := Option.map_eq_some_iff.mp selectedFlag
  have selectedArgument : arguments[index]? = some entry.value := by
    rw [← steps.values,List.getElem?_map,selected]
    rfl
  have exactValue : pushValues values arguments (entries.length - 1 - index) = entry.value := by
    rw [steps.entry_length]
    exact pushValues_argument _ _ selectedArgument
  have stored := store.2.1 _ binding found
  rw [exactValue] at stored
  have member := List.mem_of_getElem? selected
  refine ⟨binding,found,sameFlag,exactValue,
    stored.unique history.wellFormed (steps.entry_ghost_typed member),?_⟩
  intro relevant
  exact ⟨.var found (Or.inr (sameFlag.trans relevant)),steps.runtime_entry_typed member relevant⟩

/-- Source slot permissions for a whole checked dependent call follow from
its original source function typing and outer typed store. -/
theorem Telescope.checkedCall_source_slots
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : Telescope env ctx signature count finalContext result)
    (formed : ContextFormed env ctx) (closing : Ghost.Substitution env ctx [] values)
    (sourceFunction : HasType env ctx mode function signature)
    (checked : CallReplay.checked fuel env [] false (function.subst values) arguments = some (entries,actualResult))
    (arity : arguments.length = count) :
    TypedSourceSlots env finalContext (pushValues values arguments) entries := by
  obtain ⟨actualSignature,actualFunction,steps,applied⟩ :=
    CallReplay.infer_sound (CallReplay.checked_origin checked).2
  have sourceClosed := sourceFunction.ghostSubstitution history.wellFormed closing
  exact source.replay_source_slots history formed closing steps
    (sourceClosed.unique history.wellFormed actualFunction.ghost) arity

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay NativeQuantity
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Original source slots obtain exactly the permissions of the relevant
actual arguments, and the original call supplies their ResourceSafe evidence.
Erased arguments retain ghost typing without fabricated code permission. -/
theorem checked_app_source_slot_permissions
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (checked : checkResource (fuel + 1) env (.app function argument) = true) :
    ∃ head supplied entries result opened leading trailing,
      splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      CallReplay.checked fuel env [] false head supplied = some (entries,result) ∧
      openHead fuel env [] head supplied = some opened ∧
      entries = leading ++ trailing ∧
      leading.map Argument.value = supplied.take opened.modes.length ∧
      TypedSourceSlots env opened.context
        (pushValues Term.var (supplied.take opened.modes.length)) leading ∧
      (∀ entry ∈ leading, entry.erased = false → ResourceSafe env entry.value) := by
  obtain ⟨head,supplied,entries,result,opened,body,bodyType,actualSignature,middle,
      leading,trailing,split,replayed,inferred,openedHead,formed,retained,projected,bodyContract,
      store,closedBody,aligned,left,right,entriesSplit,arguments⟩ :=
    checked_app_typed_binding_store history checked
  obtain ⟨signature,sourceType,telescope,converted,typed,bound⟩ :=
    openHead_source_telescope openedHead (Checker.infer_sound inferred)
  have closing : Ghost.Substitution env [] [] Term.var := by
    intro index binding found
    simp [lookup] at found
  have slots := telescope.replay_source_slots history .nil closing left
    (by simpa only [Term.subst_id] using converted.symm)
    (by simp only [List.length_take,Nat.min_eq_left bound])
  refine ⟨head,supplied,entries,result,opened,leading,trailing,split,replayed,openedHead,
    entriesSplit,left.values,slots,?_⟩
  intro entry member relevant
  have wholeMember : entry ∈ entries := by rw [entriesSplit]; exact List.mem_append_left _ member
  have runtime : entry.value ∈ runtimeArguments entries := by
    apply List.mem_filterMap.mpr
    exact ⟨entry,wholeMember,by simp [relevant]⟩
  exact (arguments _ runtime).2

end Jihoo.NativeKernel.Environment.ContextQuantity
