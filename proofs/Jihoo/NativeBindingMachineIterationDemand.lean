import Jihoo.NativeBindingMachineMutableDemandSequence

/-! A repeated callback cannot consume an owner captured before the
iteration. Its receipt comes from the actual Fold or Loop projection,
including the three opened callback binders. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

open Jihoo.Quantity NativeQuantity

theorem fold_receipts
    (checked : projectRaw (fuel+1) env loans ctx (.fold count initial body) = some receipt) :
    ∃ setup callback,
      fields (projectRaw fuel env loans ctx) [count,initial,body] [0,1] = some setup ∧
      projectRaw fuel env loans ctx body = some callback ∧
      receipt = .seq setup (.repeat (caseBody 3 callback)) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,
    Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨setup,first,later⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨callback,bodyChecked,finished⟩ := Option.bind_eq_some_iff.mp later
  exact ⟨setup,callback,first,bodyChecked,(Option.some.inj finished).symm⟩

theorem loop_receipts
    (checked : projectRaw (fuel+1) env loans ctx (.loop count motive initial body) = some receipt) :
    ∃ setup callback,
      fields (projectRaw fuel env loans ctx) [count,motive,initial,body] [0,2] = some setup ∧
      projectRaw fuel env loans ctx body = some callback ∧
      receipt = .seq setup (.repeat (caseBody 3 callback)) := by
  simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,
    Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨setup,first,later⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨callback,bodyChecked,finished⟩ := Option.bind_eq_some_iff.mp later
  exact ⟨setup,callback,first,bodyChecked,(Option.some.inj finished).symm⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity

private theorem checked_repetition_zero
    (checked : (Control.repeat body).demand index = some demand) :
    body.demand index = some 0 ∧ demand = 0 := by
  change (body.demand index).bind (fun used => if used = 0 then some 0 else none) = some demand at checked
  obtain ⟨used,observed,finished⟩ := Option.bind_eq_some_iff.mp checked
  by_cases zero : used = 0
  · subst used
    exact ⟨observed,by simpa using finished.symm⟩
  · simp [zero] at finished

/-- Every captured owner has zero demand throughout all prefixes of the
repeated callback. Only the setup can consume such a slot, and it retains
the original distinct-allocation ownership world. -/
theorem OwnerDemandWorld.iteration
    (world : OwnerDemandWorld heap code (.seq setup (.repeat body)))
    (total : OwnerDemandWorld.Total code (.seq setup (.repeat body))) :
    OwnerDemandWorld heap code setup ∧ OwnerDemandWorld.Total code setup ∧
      ∀ index object, code.values[index]? = some (some (.owner object)) →
        body.demand index = some 0 ∧
        ∀ events, Prefix (.repeat body) events → index ∉ events := by
  obtain ⟨setupWorld,setupTotal,_,repeatTotal,_⟩ := world.sequence total
  refine ⟨setupWorld,setupTotal,?_⟩
  intro index object stored
  obtain ⟨amount,repeated⟩ := repeatTotal index object stored
  obtain ⟨bodyZero,empty⟩ := checked_repetition_zero repeated
  exact ⟨bodyZero,fun _ ran => erased_unreachable (empty ▸ repeated) ran⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
