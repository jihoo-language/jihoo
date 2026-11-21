import Jihoo.NativeBindingMachineMutableCheckedClosure

/-! The repeated callback opens the actual three checked scopes. Its
relevant accumulator and erased bound are retained at their original
positions in the projected body. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

open Jihoo.Quantity NativeQuantity

theorem iteration_callback_scopes
    (checked : projectRaw (fuel+3) env loans ctx
      (.lam false index (.lam true bound (.lam false accumulator body))) = some receipt) :
    ∃ indexMode accumulatorMode bodyReceipt,
      ResourceModes.Resolved env loans ctx false index indexMode ∧
      ResourceModes.Resolved env loans (⟨bound,true⟩ :: ⟨index,false⟩ :: ctx) false accumulator accumulatorMode ∧
      projectRaw fuel env loans (⟨accumulator,false⟩ :: ⟨bound,true⟩ :: ⟨index,false⟩ :: ctx) body = some bodyReceipt ∧
      caseBody 3 receipt = .scope indexMode (.scope .erased (.scope accumulatorMode (reclose (functionTail body bodyReceipt)))) := by
  obtain ⟨indexMode,_,indexResolved,afterIndex,shape⟩ := projectRaw_closure_origin checked
  obtain ⟨evidenceMode,_,evidenceResolved,afterEvidence,evidenceShape⟩ := projectRaw_closure_origin afterIndex
  obtain ⟨accumulatorMode,bodyReceipt,accumulatorResolved,projected,accumulatorShape⟩ :=
    projectRaw_closure_origin afterEvidence
  cases evidenceResolved
  refine ⟨indexMode,accumulatorMode,bodyReceipt,indexResolved,accumulatorResolved,projected,?_⟩
  rw [shape,evidenceShape,accumulatorShape]
  rfl

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
