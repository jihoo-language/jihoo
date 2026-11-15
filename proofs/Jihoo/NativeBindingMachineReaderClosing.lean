import Jihoo.NativeBindingMachineAllocatedArgument

/-! Actual reference entry keeps the full source Lend derivation, including its
specialized checked read. Canonical value closing and machine provenance are
independent. No arbitrary-argument callback or output-typing oracle is assumed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

/-- Both generic and specialized source Lend rules determine the reader's
actual annotation conversion and the checked specialized read. -/
theorem HasType.explicitLendReaderInputs (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) type) :
    ∃ ownerType valueType sort,
      HasType env [] ctx true owner ownerType ∧ Owned env ownerType ∧
      Binder env loans ctx false domain sort ∧ Conversion.Conv env domain (.ref ownerType) ∧
      HasType env [] ctx true (Lending.read owner readerBody) valueType ∧ Outlived env valueType := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  cases origin with
  | generic owner owned outlived reader continuation allowed =>
      obtain ⟨sort,result,binder,bodyTyped,readerConverted⟩ := reader.lamView
      have domainConverted := (readerConverted.pi_injective wf.admissible).2.1
      exact ⟨_,_,sort,owner.ghost [],owned,binder,domainConverted,
        reader_from_generic_checks wf owner owned reader,outlived⟩
  | dependentCode owner owned binder domain reader outlived first again continuation normalized shifted allowed =>
      exact ⟨_,_,_,owner.ghost [],owned,binder,domain,reader.ghost [],outlived⟩
  | dependentGhost owner owned binder domain reader outlived first again continuation normalized shifted =>
      exact ⟨_,_,_,owner.ghost [],owned,binder,domain,reader.ghost [],outlived⟩

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- The actual reference binder's value context and closed body typing follow
from the input Lend. Specialized source rules retain their checked read rather
than inventing typing of the original callback at arbitrary arguments. -/
theorem value_reader_closing
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) (token : Nat) :
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow (owner.subst code.origins)) (some (.reference token))
    let bodyMeanings := consValues (.borrow (owner.subst meanings)) meanings
    ∃ valueType, LoanTyping.Outlived env valueType ∧
      LoanTyping.HasType env [] [] true (bodyCode.term.subst bodyMeanings) (valueType.subst meanings) ∧
      ValueContext env bodyCode bodyMeanings := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨ownerType,valueType,sort,ownerTyped,owned,binder,domainConverted,readTyped,outlived⟩ :=
    source.explicitLendReaderInputs history.wellFormed
  have ownerClosed := ownerTyped.ghostSubstitution history.wellFormed closing
  have ownedClosed := owned.substitution meanings history.wellFormed.closed
  have borrowed : LoanTyping.HasType env [] [] true (.borrow (owner.subst meanings))
      (.ref (ownerType.subst meanings)) := .ghostBorrowOwned ownerClosed ownedClosed
  have domainClosed : LoanTyping.Conversion.Conv env (domain.subst meanings)
      (.ref (ownerType.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      domainConverted.substitution meanings history.wellFormed.closed
  have argumentTyped := borrowed.convert domainClosed.symm
  have argumentKind : ValueKind env (.reference token) (domain.subst meanings) :=
    ⟨ownerType.subst meanings,domainClosed.symm⟩
  have readClosed := readTyped.ghostSubstitution history.wellFormed closing
  have closesRead : readerBody.subst (consValues (.borrow (owner.subst meanings)) meanings) =
      (Lending.read owner readerBody).subst meanings :=
    reader_entry_origin ⟨code.term,code.context,meanings,code.values⟩ owner domain readerBody token
  rw [← closesRead] at readClosed
  refine ⟨valueType,outlived,readClosed,⟨context.closing.consValues argumentTyped,?_,?_⟩⟩
  · constructor
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.1 index actual stored
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.2 index actual stored
  · intro index binding actual selected stored
    cases index with
    | zero =>
        simp only [enter,lookup,Option.some.injEq] at selected
        subst binding
        have same : Value.reference token = actual := Option.some.inj (Option.some.inj stored)
        subst actual
        simpa only [shift_subst_consValues] using argumentKind
    | succ index =>
        obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
        subst binding
        simpa only [shift_subst_consValues] using context.kinds index previous actual found stored

/-- Actual named reader activation constructs its reference value context,
closed original body typing and source loan slots. The real reader inventory
supplies lease and owner liveness for arbitrary nested reader stacks. -/
theorem reachable_value_reader_activation (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sourceShape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (slots : LoanSlots code loans rest) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (controlShape : (run fuel (initial term)).state.control =
      .returned (.closure false domain readerBody code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerOrigin continuation :: rest) :
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
    let bodyMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
    let afterStack := .lendFinish token object (some (code.context.length-owner))
      ((Term.var owner).subst code.origins) bodyCode.origin continuation :: rest
    ∃ valueType, LoanTyping.Outlived env valueType ∧
      LoanTyping.HasType env [] [] true (bodyCode.term.subst bodyMeanings) (valueType.subst meanings) ∧
      ValueContext env bodyCode bodyMeanings ∧
      LoanSlots bodyCode (Loans.enter code.context.length owner loans) afterStack ∧
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,afterStack⟩,
          some (.activate false readerBody (.borrow ((Term.var owner).subst code.origins)))) := by
  obtain ⟨valueType,outlived,bodyTyped,bodyContext⟩ := value_reader_closing history typed context sourceShape token
  have readers := initial_run_readers_live term fuel
  rw [stackShape] at readers
  have leased := readers _ List.mem_cons_self token object (some (code.context.length-owner)) rfl
  refine ⟨valueType,outlived,bodyTyped,bodyContext,
    named_reader_body_slots code slots entered stored domain readerBody token readerOrigin continuation,
    leased,(initial_run_heap_valid term fuel).leased token object leased |>.2,?_⟩
  simp only [step,action,controlShape,stackShape,reader_activation_origin,Option.map_some,execute]

end Jihoo.NativeKernel.Environment.BindingMachine
