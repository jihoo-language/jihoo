import Jihoo.NativeBindingMachineMutableNumeric
import Jihoo.NativeLoanLoadPreservation

/-! Local Load simulation from the original Loan64 derivation and its
quantity receipt. The owner world supplies physical liveness and length
agreement. Both callback activations are actual evaluator transitions. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def LoadOperands (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .load owner offset evidence _ => ∃ count,
      HasType env loans ctx mode owner (.buffer count) ∧
      HasType env loans ctx mode offset .u64 ∧ HasType env loans ctx true evidence (.lt offset count)
  | _ => True

theorem HasType.load_inputs
    (typed : HasType env loans ctx mode (.load owner offset evidence callback) result) :
    ∃ count, HasType env loans ctx mode owner (.buffer count) ∧
      HasType env loans ctx mode offset .u64 ∧ HasType env loans ctx true evidence (.lt offset count) := by
  suffices view : ∀ {term type}, HasType env loans ctx mode term type →
      LoadOperands env loans ctx mode term from view typed
  intro term type source
  apply HasType.rec (t := source)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => LoadOperands env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case load => exact ⟨_,by assumption,by assumption,by assumption⟩
  case dataElim => split <;> trivial

namespace ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {resource : Control}

/-- The owner operand of a literal Load has positive ownership demand, so
the already active source loans cannot include it. -/
theorem projectRaw_literal_load_inactive
    (checked : projectRaw (fuel+2) env loans ctx
      (.load (.var owner) (.natural offset) evidence continuation) = some resource)
    (budget : LoanBudget ctx.length loans resource) : Loans.active ctx.length loans owner = false := by
  simp only [projectRaw,Term.natural,Op.arity,erasedNode,fields,fetch,
    List.length_cons,List.length_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    bind,Option.bind,Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      cases erased : binding.erased with
      | true => simp [selected,erased] at checked
      | false =>
          cases projected : projectRaw (fuel+1) env loans ctx continuation with
          | none => simp [selected,erased,projected] at checked
          | some tail =>
              simp [selected,erased,projected] at checked
              rw [← checked] at budget
              apply Bool.eq_false_iff.mpr
              intro active
              have zero := budget.sequence.1.sequence.1 owner active
              simp [Control.demand] at zero

end ResourceQuantity
end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds
variable {resource : Jihoo.Quantity.Control}

/-- A typed named-owner Load with a literal `Decide` bound executes the actual
owned read and both callback activations. The closed callback body has the
requested result type when its retained slots are interpreted by the observed
integer and the original owner meaning. -/
theorem typed_literal_load (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (invariant : Invariant state) (numbers : StateNumbers state)
    (evaluating : state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env state.heap.metadata source meanings)
    (shape : actual.term = .load (.var owner) (.natural offset) (.decide (.natural offset) (.natural count))
      (.lam false first (.lam false again body)))
    (stored : actual.values[owner]? = some (some (.owner object)))
    (live : state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let payload := state.heap.cell object offset
    let value := Term.integer (decodeInteger payload)
    let origin := (actual.child (.var owner)).origin
    let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
    let nextMeanings := consValues (meanings (indices owner)) (consValues value (meanings ∘ indices))
    state.heap.metadata.length object = count ∧
      state.heap.load object offset = some payload ∧
      run 9 state = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin)],9⟩ ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type := by
  have sourceShape : source.term =
      .load (.var (indices owner)) (.natural offset) (.decide (.natural offset) (.natural count))
        ((Term.lam false first (.lam false again body)).rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  have closedOriginal : LoanTyping.HasType env [] [] true (actual.term.subst (meanings ∘ indices)) type := by
    have closed := typed.closed history
    rwa [← view.termEq,Term.subst_rename] at closed
  obtain ⟨closing,_,sourceTyped,_⟩ := typed
  rw [sourceShape] at sourceTyped checked
  obtain ⟨size,ownerTyped,_,bound⟩ := sourceTyped.load_inputs
  have sourceStored := (view.values owner).symm.trans stored
  have physicalTyped : OwnerSize env state.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      sizes.typed_variable history ownerTyped sourceStored
  have physical := physicalTyped.buffer_length history
  have closedEvidence : LoanTyping.HasType env [] [] true
      (.decide (.natural offset) (.natural count)) (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      bound.ghostSubstitution history.wellFormed closing
  have sizeConverted := (closedEvidence.principalView.lt_injective history.wellFormed.admissible).2
  have length := (physical.trans sizeConverted.symm).natural_injective history.wellFormed.admissible
  have limits := bound.literal_decide_limits history.wellFormed
  have inactive := LoanTyping.ResourceQuantity.projectRaw_literal_load_inactive checked budget
  have guard := (invariant.2.free_guard_iff invariant.1).mpr (coverage.inactive sourceStored inactive)
  have within : offset < state.heap.metadata.length object := length ▸ limits.2.2
  have read : state.heap.load object offset = some (state.heap.cell object offset) := by
    simp [SizedBufferHeap.IndexedState.load,live,guard,within]
  simp only [shape,Term.subst,substArgs,Op.binders,liftSub] at closedOriginal
  have finished := LoanTyping.load_ghost_finish history.wellFormed closedOriginal
    (decode_integer_bound (numbers.cells object offset))
  refine ⟨length,read,literal_load_steps state evaluating shape stored limits.1 read,?_⟩
  change LoanTyping.HasType env [] [] true
    (body.subst (consValues (meanings (indices owner))
      (consValues (.integer (decodeInteger (state.heap.cell object offset))) (meanings ∘ indices)))) type
  rw [continuation_actual_substitution]
  rw [← Lending.returned_owner_substitutions]
  exact finished

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
