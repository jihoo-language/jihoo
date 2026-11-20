import Jihoo.NativeBindingMachineMutableClosedStoreLoadContinuation
import Jihoo.NativeFamilyIotaNeutralCoherence
import Jihoo.NativeLoanRawResourceOrigins
import Jihoo.NativeNeutralSpines

/-! The original resource projection yields the linear budget of the
retained Load callback. Convertible Buffer annotations resolve to linear
mode, including when the annotation needs genuine native computation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceModes
open Jihoo.Quantity

private theorem rigid_head_of_read (read : ContextModes.head env term = some mode) :
    ∃ op children, term = .node op children ∧ RawLend.rigid op = true := by
  cases term with
  | var => simp [ContextModes.head,NativeQuantity.binderMode] at read
  | node op children =>
      cases op <;> first
        | exact ⟨_,_,rfl,rfl⟩
        | simp [ContextModes.head,NativeQuantity.binderMode] at read

private theorem spine_has_neutral_head (spine : Spine env loans ctx term kind) :
    ∃ head arguments, term = neutralSpine head arguments := by
  induction spine with
  | var _ => exact ⟨_,[],rfl⟩
  | app _ _ ih =>
      obtain ⟨head,arguments,rfl⟩ := ih
      exact ⟨head,_ :: arguments,rfl⟩

private theorem unlend_spine (head : Nat) (arguments : List Term) :
    RawLend.unlend (neutralSpine head arguments) =
      neutralSpine head (arguments.map RawLend.unlend) := by
  induction arguments with
  | nil => simp only [neutralSpine,RawLend.unlend,List.map_nil]
  | cons argument rest ih =>
      simp only [neutralSpine,Term.app,RawLend.unlend,RawLend.rebuild,RawLend.unlendArgs,List.map_cons,ih]

private theorem neutral_buffer_separate (admissible : EnvironmentDelta.Admissible env)
    (converted : Conversion.Conv env (neutralSpine head arguments) (.buffer size)) : False := by
  have projected := converted.projected admissible
  simp only [RawLend.project,EnvironmentDelta.expand_neutralSpine,unlend_spine,
    Term.buffer,EnvironmentDelta.expand,EnvironmentDelta.expandArgs,RawLend.unlend,
    RawLend.unlendArgs,RawLend.rebuild] at projected
  exact FamilyIota.Extended.Conv.neutralSpine_node_separate admissible (op := .buffer)
    rfl (by intro same; cases same) rfl projected

/-- Resolution cannot classify a type convertible to Buffer as unlimited,
borrowed, or erased under the same admitted definitions. -/
theorem Resolved.convertible_buffer_linear (admissible : EnvironmentDelta.Admissible env)
    (resolved : Resolved env loans ctx false domain mode)
    (converted : Conversion.Conv env domain (.buffer size)) : mode = .linear := by
  cases resolved with
  | head normalized known =>
      obtain ⟨op,args,rfl,rigid⟩ := rigid_head_of_read known
      have buffer := (Conversion.normalize?_sound normalized).symm.trans converted
      obtain ⟨rfl,children⟩ := buffer.full_rigid_node_injective rigid rfl admissible
      cases children with
      | cons _ rest =>
          cases rest
          exact (Option.some.inj known).symm
  | abstract normalized spine =>
      obtain ⟨head,arguments,rfl⟩ := spine_has_neutral_head spine
      exact False.elim (neutral_buffer_separate admissible
        ((Conversion.normalize?_sound normalized).symm.trans converted))

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceModes

namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control} {count : Term}

private theorem lambda_resolved
    (checked : projectRaw (fuel+1) env loans ctx (.lam false domain body) = some control) :
    ∃ mode bodyControl,
      ResourceModes.Resolved env loans ctx false domain mode ∧
      projectRaw fuel env loans (⟨domain,false⟩ :: ctx) body = some bodyControl ∧
      control = .closure (.scope mode (functionTail body bodyControl)) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  split at checked
  · contradiction
  · obtain ⟨mode,resolved,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyControl,projected,same⟩ := Option.bind_eq_some_iff.mp checked
    exact ⟨mode,bodyControl,ResourceModes.resolve_sound resolved,projected,Option.some.inj same.symm⟩

private theorem lambda_resolved_any
    (checked : projectRaw fuel env loans ctx (.lam false domain body) = some control) :
    ∃ innerFuel mode bodyControl,
      ResourceModes.Resolved env loans ctx false domain mode ∧
      projectRaw innerFuel env loans (⟨domain,false⟩ :: ctx) body = some bodyControl ∧
      control = .closure (.scope mode (functionTail body bodyControl)) := by
  cases fuel with
  | zero => cases checked
  | succ innerFuel =>
      obtain ⟨mode,bodyControl,receipt⟩ := lambda_resolved checked
      exact ⟨innerFuel,mode,bodyControl,receipt⟩

/-- The actual Load quantity receipt opens exactly its two callback
binders. Any later leading lambda remains a returned closure. The
retained Buffer slot has demand one in this same receipt. -/
theorem projectRaw_load_callback_budget (admissible : EnvironmentDelta.Admissible env)
    (checked : projectRaw fuel env loans ctx
      (.load owner offset evidence (.lam false first (.lam false again body))) = some control)
    (demand : control.demand index = some uses)
    (ownerDomain : Conversion.Conv env again (.buffer (count.rename Nat.succ))) :
    ∃ bodyFuel receipt,
      projectRaw bodyFuel env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx) body = some receipt ∧
      let entered := reclose (functionTail body receipt)
      entered.demand 0 = some 1 ∧ LocalScopes entered ∧
      (∀ events, Jihoo.Quantity.Prefix entered events → events.count 0 ≤ 1) ∧
      (∀ events, Jihoo.Quantity.Finishes entered events → events.count 0 = 1) := by
  cases fuel with
  | zero => cases checked
  | succ outerFuel =>
      change (do
        let operands ← fields (projectRaw outerFuel env loans ctx)
          [owner,offset,evidence,.lam false first (.lam false again body)] [0,1]
        let callback ← fetch (projectRaw outerFuel env loans ctx)
          [owner,offset,evidence,.lam false first (.lam false again body)] 3
        some (.seq operands (.once (caseBody 2 callback)))) = some control at checked
      obtain ⟨operands,_,checked⟩ := Option.bind_eq_some_iff.mp checked
      obtain ⟨callback,projected,same⟩ := Option.bind_eq_some_iff.mp checked
      have firstProjected : projectRaw outerFuel env loans ctx
        (.lam false first (.lam false again body)) = some callback := projected
      obtain ⟨innerFuel,firstMode,inner,_,innerProjected,rfl⟩ := lambda_resolved_any firstProjected
      obtain ⟨bodyFuel,ownerMode,receipt,resolved,bodyProjected,rfl⟩ := lambda_resolved_any innerProjected
      have mode := resolved.convertible_buffer_linear admissible ownerDomain
      subst ownerMode
      have shape : control = .seq operands
          (.once (.scope firstMode (.scope .linear (reclose (functionTail body receipt))))) := by
        rw [← Option.some.inj same]
        rfl
      rw [shape] at demand
      have localBudget := NativeQuantity.demand_localScopes _ demand
      change LocalScopes operands ∧
        LocalScopes (.scope firstMode (.scope .linear (reclose (functionTail body receipt)))) at localBudget
      have ownerScope : LocalScopes (.scope .linear (reclose (functionTail body receipt))) := by
        cases firstMode
        · exact localBudget.2.2
        · exact localBudget.2.2
        · exact localBudget.2
        · exact localBudget.2
      change (reclose (functionTail body receipt)).demand 0 = some 1 ∧
        LocalScopes (reclose (functionTail body receipt)) at ownerScope
      exact ⟨bodyFuel,receipt,bodyProjected,ownerScope.1,ownerScope.2,
        fun _ prefixRun => prefixRun.count_le ownerScope.1,
        fun _ completed => completed.count_eq ownerScope.1⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

/-- Admission and actual callback entry establish a live unborrowed
Buffer at the closed source type, with exactly one projected use of
its returned source slot. The body has its original local context. -/
theorem checked_closed_store_load_entry_resources
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source =
      some ⟨type,storeLoadWith count offset fill value (.lam false first (.lam false again body))⟩)
    (sorted : LoanTyping.Checker.sort fuel env [] [] type = some (.type level))
    (fits : count*8+8 < 2^64) :
    let result := run 19 (initial (storeLoadWith count offset fill value (.lam false first (.lam false again body))))
    let code := storeLoadEntry count offset fill value first again body
    result.state.control = .evaluate code ∧ result.state.stack = [] ∧ result.state.pending = [] ∧
      BufferValue env result.state.heap.metadata (.owner 0) ((again.rename Nat.succ).subst code.origins) ∧
      freeGuard result.state.heap.metadata 0 = true ∧
      LoanClosingTyped env [] false code code.origins type ∧ ValueContext env code code.origins ∧
      OwnerSizes env result.state.heap.metadata code code.origins ∧
      ∃ bodyFuel receipt,
        LoanTyping.ResourceQuantity.projectRaw bodyFuel env [] code.context code.term = some receipt ∧
        let entered := reclose (functionTail body receipt)
        entered.demand 0 = some 1 ∧ LocalScopes entered ∧
        (∀ events, Jihoo.Quantity.Prefix entered events → events.count 0 ≤ 1) ∧
        (∀ events, Jihoo.Quantity.Finishes entered events → events.count 0 = 1) := by
  let program := storeLoadWith count offset fill value (.lam false first (.lam false again body))
  let result := run 19 (initial program)
  let code := storeLoadEntry count offset fill value first again body
  obtain ⟨_,entered,emptyStack,emptyPending,live,length,_,typedBody,values,sizes⟩ :=
    check_closed_store_load_entry history accepted sorted fits
  have ownerSize : OwnerSize env result.state.heap.metadata 0 ((again.rename Nat.succ).subst code.origins) :=
    sizes 0 ⟨again.rename Nat.succ,false⟩ 0 rfl rfl
  have ownerType := ownerSize.realization
  change LoanTyping.Conversion.Conv env (.buffer (.natural (result.state.heap.metadata.length 0))) _ at ownerType
  rw [length] at ownerType
  have physical : BufferValue env result.state.heap.metadata (.owner 0) ((again.rename Nat.succ).subst code.origins) :=
    ⟨0,count,rfl,live,length,ownerType⟩
  have guard : freeGuard result.state.heap.metadata 0 = true := by
    apply freeGuard_of_unborrowed
    intro token active
    have inventory := (initial_run_invariant program 19).2
    change ReaderInventory result.state.heap.metadata (readerFrames result.state.activeStack) at inventory
    obtain ⟨name,present⟩ := inventory.covered token 0 active
    change result.state.stack = [] at emptyStack
    change result.state.pending = [] at emptyPending
    simp [State.activeStack,emptyStack,emptyPending,readerFrames] at present
  obtain ⟨sort,typedType,typed,resources⟩ :=
    (LoanTyping.MixedProgram.checkDeclaration_sound accepted).valid.typing
  have rightSort := typedType.sort_unique history.wellFormed (second := .type level)
    (LoanTyping.Checker.sort_sound sorted)
  subst sort
  obtain ⟨_,_,resourceFuel,control,projected,demand,_,_⟩ := resources rfl
  obtain ⟨_,_,_,domain,_⟩ := LoanTyping.load_retained_body history.wellFormed typed
  obtain ⟨bodyFuel,receipt,bodyProjected,budget⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_load_callback_budget history.wellFormed.admissible
      (LoanTyping.ResourceQuantity.project_origin projected) demand domain
  exact ⟨entered,emptyStack,emptyPending,physical,guard,typedBody,values,sizes,
    bodyFuel,receipt,bodyProjected,budget⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
