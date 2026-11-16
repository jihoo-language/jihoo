import Jihoo.NativeBindingMachineCanonicalView

/-! The original Lend checker types a canonical continuation with one result
binder, while the actual runtime retains result AND owner binders. Construct
that source/runtime view, its typing and authority at the real close boundary.
No supplied continuation typing, alias injectivity or output oracle is used. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem canonical_scalar_context
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (context : ValueContext env code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (scalar : LoanTyping.ScalarReadShape readerBody)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some control)
    (bounded : ValueReduction.signed64 value) (resultOrigin : Term) :
    ∃ type,
      LoanClosingTyped env loans false (canonicalContinuation code owner first body resultOrigin (.integer value))
        (consValues (.integer value) meanings) type ∧
      ValueContext env (canonicalContinuation code owner first body resultOrigin (.integer value))
        (consValues (.integer value) meanings) := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,sourceTyped,readTyped,
    binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,same⟩ :=
    LoanTyping.ResourceQuantity.dependent_raw_project_contract (shape ▸ checked)
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at bodyTyped
  have firstConverted := (scalar.read (.var owner)).result_conversion history.wellFormed readTyped
  have firstClosed : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    simpa only [Term.subst,substArgs] using firstConverted.substitution meanings history.wellFormed.closed
  let callback := code.child (.lam false first (body.rename (Jihoo.Quantity.openOwner (owner+1))))
  have functionTyped : LoanClosingTyped env loans false callback meanings
      (.pi false .i64 (result.subst (liftSubOne meanings))) := by
    refine ⟨context.closing,.pi false first result,.lam binder bodyTyped,?_⟩
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (RawLend.Conv.node (.pi false) (.cons firstClosed.symm (.cons (.refl (result.subst (liftSubOne meanings))) .nil)))
  have typed := enter_integer_closing history functionTyped bounded resultOrigin
  have callbackContext : ValueContext env callback meanings := context.child _
  have enteredContext := callbackContext.enter_integer history functionTyped bounded resultOrigin
  exact ⟨_,typed,enteredContext⟩

/-- Five actual transitions close and bind the real continuation. The same
original Lend query constructs canonical CODE typing at the original result
type, its value/size/loan contexts and exact recursive budget. Actual aliases
are mapped to source indices; they need no separate source loan permissions. -/
theorem reachable_canonical_scalar_handoff (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (scalar : LoanTyping.ScalarReadShape readerBody)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans control)
    (coverage : LoanCoverage code loans stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned (.integer value))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins) resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let actual := restoredContinuation code first again body ((Term.var owner).subst code.origins) resultOrigin object (.integer value)
    let source := canonicalContinuation code owner first body resultOrigin (.integer value)
    let sourceMeanings := consValues (.integer value) meanings
    run 5 (run fuel (initial term)).state =
      ⟨⟨closed,.evaluate actual,stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,
          .activate false body ((Term.var owner).subst code.origins)],5⟩ ∧
    CanonicalView actual source (Jihoo.Quantity.openOwner (owner+1)) ∧
    LoanClosingTyped env loans false source sourceMeanings type ∧
    ValueContext env source sourceMeanings ∧ OwnerSizes env closed source sourceMeanings ∧
    LoanSlots source loans stack ∧ LoanCoverage source loans stack ∧
    ReaderInventory closed (readerFrames stack) ∧ closed.heap.live object = true ∧
    ∃ rest, LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans source.context source.term = some rest ∧
      LoanTyping.ResourceQuantity.LoanBudget source.context.length loans rest := by
  have handoff := reachable_raw_scalar_value_lend_handoff term fuel code history typed context sizes shape scalar
    checked stored slots entered returned stackShape
  dsimp only at handoff
  obtain ⟨executed,nextContext,nextSizes,nextTyped,nextSlots,inventory,live,guard,aliases,resource⟩ := handoff
  have bounded := initial_run_integer_bound term fuel returned
  obtain ⟨canonicalType,canonicalTyped,canonicalContext⟩ := canonical_scalar_context history context shape scalar checked bounded resultOrigin
  have view := restored_canonical_view code stored first again body resultOrigin (.integer value)
  have related : ∀ index,
      consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings) index =
        consValues (.integer value) meanings (Jihoo.Quantity.openOwner (owner+1) index) := by
    intro index
    cases index with
    | zero => simp only [consValues,Term.subst,Jihoo.Quantity.openOwner]
    | succ index => rfl
  have closedEq := view.closed related
  rw [closedEq] at nextTyped
  have canonicalClosed := canonicalTyped.closed history
  have converted := canonicalClosed.unique history.wellFormed nextTyped
  obtain ⟨closing,localType,localTyped,originalConverted⟩ := canonicalTyped
  have originalTyped : LoanClosingTyped env loans false
      (canonicalContinuation code owner first body resultOrigin (.integer value))
      (consValues (.integer value) meanings) type :=
    ⟨closing,localType,localTyped,originalConverted.trans converted⟩
  have before := initial_reader_inventory term fuel
  rw [stackShape] at before
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at before
  have leased := before.live _ List.mem_cons_self
  have closedSizes := sizes.steps (.cons (.close leased) .nil)
  have canonicalSizes := closedSizes.enter_integer first (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin value
  have canonicalSlots := slots.enter entered false first (body.rename (Jihoo.Quantity.openOwner (owner+1))) resultOrigin (some (.integer value))
  have canonicalCoverage := coverage.enter_nonowner entered false first (body.rename (Jihoo.Quantity.openOwner (owner+1)))
    resultOrigin (some (.integer value)) (by intro object same; cases same)
  obtain ⟨reader,mode,rest,readProjected,restProjected,readBudget,restBudget,same⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_lend_budgets (shape ▸ checked) budget entered
  rw [LoanTyping.ResourceQuantity.restore_body_is_alias] at restProjected
  exact ⟨executed,view,originalTyped,canonicalContext,canonicalSizes,canonicalSlots,canonicalCoverage,inventory,live,
    rest,restProjected,restBudget⟩

end Jihoo.NativeKernel.Environment.BindingMachine
