import Jihoo.NativeBindingMachineMutableDynamicLoad
import Jihoo.NativeLoanCodeRenaming

/-! A successful owned Load transports the source value and size contexts
into the actual two-slot continuation and its single-owner source view. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

theorem restored_contexts
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (context : ValueContext env code meanings) (sizes : OwnerSizes env heap code meanings)
    (ownerTyped : LoanTyping.HasType env loans code.context false (.var owner) (.buffer size))
    (stored : code.values[owner]? = some (some (.owner object)))
    (first again body origin : Term) (number : Int)
    (closing : LoanTyping.Ghost.Substitution env
      (restoredContinuation code first again body origin (.integer number) object (.integer number)).context []
      (consValues (meanings owner) (consValues (.integer number) meanings))) :
    let next := restoredContinuation code first again body origin (.integer number) object (.integer number)
    let extended := consValues (meanings owner) (consValues (.integer number) meanings)
    ValueContext env next extended ∧ OwnerSizes env heap next extended := by
  let next := restoredContinuation code first again body origin (.integer number) object (.integer number)
  let extended := consValues (meanings owner) (consValues (.integer number) meanings)
  have ownerMeaning : LoanTyping.HasType env [] [] true (meanings owner) (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      ownerTyped.ghostSubstitution history.wellFormed context.closing
  have sizeMeaning : OwnerSize env heap object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      sizes.typed_variable history ownerTyped stored
  have slots : ∀ index binding value, lookup next.context index = some binding →
      next.values[index]? = some (some value) →
      ValueKind env value (binding.ty.subst extended) ∧
        ∀ queried, value = .owner queried → OwnerSize env heap queried (binding.ty.subst extended) := by
    intro index binding value selected present
    cases index with
    | zero =>
        have same : Value.owner object = value := Option.some.inj (Option.some.inj present)
        subst value
        have ownerClosed := closing 0 binding selected
        have positioned := sizeMeaning.convert (ownerMeaning.unique history.wellFormed ownerClosed)
        refine ⟨⟨_,positioned.realization⟩,?_⟩
        intro queried same
        cases same
        exact positioned
    | succ index =>
        cases index with
        | zero =>
            have same : Value.integer number = value := Option.some.inj (Option.some.inj present)
            subst value
            exact ⟨(closing 1 binding selected).principalView,by intro queried absent; cases absent⟩
        | succ index =>
            obtain ⟨previous,selectedPrevious,same⟩ := Option.map_eq_some_iff.mp selected
            obtain ⟨original,selectedOriginal,samePrevious⟩ := Option.map_eq_some_iff.mp selectedPrevious
            subst binding
            subst previous
            constructor
            · simpa only [extended,shift_subst_consValues] using
                context.kinds index original value selectedOriginal present
            · intro queried same
              subst value
              simpa only [extended,shift_subst_consValues] using
                sizes index original queried selectedOriginal present
  have scalar := context.scalars.enter_integer first (.lam false again body) (.integer number) number
  have carried : ScalarSlots next extended := by
    constructor
    · intro index actual present
      cases index with
      | zero => cases present
      | succ index => exact scalar.1 index actual present
    · intro index actual present
      cases index with
      | zero => cases present
      | succ index => exact scalar.2 index actual present
  exact ⟨⟨closing,carried,fun index binding value selected present =>
    (slots index binding value selected present).1⟩,
    fun index binding object selected present => (slots index binding (.owner object) selected present).2 object rfl⟩

private theorem canonical_contexts (code : Code) (first again body origin : Term) (number : Int)
    (object owner : Nat)
    (context : ValueContext env
      (restoredContinuation code first again body origin (.integer number) object (.integer number))
      (consValues (meanings owner) (consValues (.integer number) meanings)))
    (sizes : OwnerSizes env heap
      (restoredContinuation code first again body origin (.integer number) object (.integer number))
      (consValues (meanings owner) (consValues (.integer number) meanings))) :
    let alias := canonicalContinuation code owner first body (.integer number) (.integer number)
    let extended := consValues (.integer number) meanings
    ValueContext env alias extended ∧ OwnerSizes env heap alias extended := by
  let alias := canonicalContinuation code owner first body (.integer number) (.integer number)
  let restored := restoredContinuation code first again body origin (.integer number) object (.integer number)
  have shifted (index : Nat) (binding : Binding) (selected : lookup alias.context index = some binding) :
      lookup restored.context (index+1) = some ⟨binding.ty.rename Nat.succ,binding.erased⟩ := by
    change (lookup alias.context index).map _ = _
    rw [selected]
    rfl
  refine ⟨⟨?_,⟨?_,?_⟩,?_⟩,?_⟩
  · intro index binding selected
    simpa only [consValues,shift_subst_consValues] using context.closing (index+1) _ (shifted index binding selected)
  · intro index value selected
    exact context.scalars.1 (index+1) value selected
  · intro index value selected
    exact context.scalars.2 (index+1) value selected
  · intro index binding value selected stored
    simpa only [shift_subst_consValues] using context.kinds (index+1) _ value (shifted index binding selected) stored
  · intro index binding queried selected stored
    simpa only [shift_subst_consValues] using sizes (index+1) _ queried (shifted index binding selected) stored

theorem load_coverage
    (coverage : LoanCoverage code loans stack) (entered : Loans.Entered code.context.length loans)
    (absent : ¬ ObjectReader object stack) (first again body origin : Term) (number : Int) :
    LoanCoverage (restoredContinuation code first again body origin (.integer number) object (.integer number))
      loans stack := by
  have firstCoverage := coverage.enter_nonowner entered false first (.lam false again body)
    (.integer number) (some (.integer number)) (by intro queried same; cases same)
  have deeper : Loans.Entered (code.context.length+1) loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  intro index queried selected present
  cases index with
  | zero =>
      have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj selected))
      exact False.elim (absent (same ▸ present))
  | succ index =>
      have active := firstCoverage index queried selected present
      simpa only [restoredContinuation,enter,List.length_cons,Loans.active_weaken deeper] using active

/-- When the owner annotation is the original retained slot's annotation,
the existing CODE alias rule also transports open typing to the smaller context. -/
theorem canonical_load_alias_closing
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (entered : Loans.Entered code.context.length loans)
    (first again body origin : Term) (number : Int) (object owner : Nat)
    (selected : lookup (⟨first,false⟩ :: code.context) (owner+1) = some ⟨again,false⟩)
    (typed : LoanClosingTyped env loans false
      (restoredContinuation code first again body origin (.integer number) object (.integer number))
      (consValues (meanings owner) (consValues (.integer number) meanings)) type)
    (context : ValueContext env (canonicalContinuation code owner first body (.integer number) (.integer number))
      (consValues (.integer number) meanings)) :
    LoanClosingTyped env loans false (canonicalContinuation code owner first body (.integer number) (.integer number))
      (consValues (.integer number) meanings) type := by
  obtain ⟨_,localType,bodyTyped,resultType⟩ := typed
  have deeper : Loans.Entered (⟨first,false⟩ :: code.context).length loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have opened := bodyTyped.codeRenaming history.wellFormed (LoanTyping.CodeRenaming.instantiateVariable deeper selected)
  refine ⟨context.closing,localType.rename (Jihoo.Quantity.openOwner (owner+1)),opened,?_⟩
  rw [Term.subst_rename]
  have same : (fun index => consValues (.integer number) meanings
      (Jihoo.Quantity.openOwner (owner+1) index)) =
      consValues (meanings owner) (consValues (.integer number) meanings) := by
    funext index
    cases index <;> rfl
  rwa [same]

/-- The two actual Load callback applications preserve the complete value
and size contexts, including the original dependent Buffer length. The same
reader coverage holds in the retained callback and in its owner alias view. -/
theorem reachable_variable_load_contexts (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata source meanings)
    (indexErasure : (lookup actual.context index).map (·.erased) =
      (lookup source.context (indices index)).map (·.erased))
    (shape : actual.term = .load (.var owner) (.var index) evidence
      (.lam false first (.lam false again body)))
    (decideEvidence : evidence.subst (meanings ∘ indices) = .decide left right)
    (storedOwner : actual.values[owner]? = some (some (.owner object)))
    (live : (run fuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let state := (run fuel (initial term)).state
    ∃ offset,
      let payload := state.heap.cell object offset
      let value := Term.integer (decodeInteger payload)
      let origin := (actual.child (.var owner)).origin
      let next := restoredContinuation actual first again body origin value object (.integer (decodeInteger payload))
      let sourceFirst := first.rename indices
      let sourceAgain := again.rename (liftRenaming 1 indices)
      let sourceBody := body.rename (liftRenaming 2 indices)
      let sourceNext := restoredContinuation source sourceFirst sourceAgain sourceBody origin
        value object (.integer (decodeInteger payload))
      let sourceMeanings := consValues (meanings (indices owner)) (consValues value meanings)
      let sourceAlias := canonicalContinuation source (indices owner) sourceFirst sourceBody
        value (.integer (decodeInteger payload))
      let aliasMeanings := consValues value meanings
      let result := run 9 state
      result = ⟨⟨state.heap,.evaluate next,state.stack,state.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) value),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView next sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext sourceMeanings type ∧
      ValueContext env sourceNext sourceMeanings ∧ OwnerSizes env result.state.heap.metadata sourceNext sourceMeanings ∧
      LoanCoverage sourceNext loans result.state.activeStack ∧
      CanonicalView next sourceAlias (Jihoo.Quantity.openOwner (indices owner+1) ∘ liftRenaming 2 indices) ∧
      ValueContext env sourceAlias aliasMeanings ∧ OwnerSizes env result.state.heap.metadata sourceAlias aliasMeanings ∧
      LoanCoverage sourceAlias loans result.state.activeStack := by
  have handoff := reachable_typed_variable_load term fuel history evaluating view typed context sizes
    indexErasure shape decideEvidence storedOwner live coverage checked budget
  obtain ⟨offset,_,_,_,_,_,executed,nextView,resumed,_⟩ := handoff
  have sourceShape : source.term = .load (.var (indices owner)) (.var (indices index))
      (evidence.rename indices) ((Term.lam false first (.lam false again body)).rename indices) := by
    rw [← view.termEq,shape]
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨_,_,sourceTyped,_⟩ := typed
  rw [sourceShape] at sourceTyped checked
  obtain ⟨_,ownerTyped,_,_⟩ := sourceTyped.load_inputs
  have sourceStored := (view.values owner).symm.trans storedOwner
  have inactive := LoanTyping.ResourceQuantity.projectRaw_named_load_inactive checked budget
  have absent := coverage.inactive sourceStored inactive
  let state := (run fuel (initial term)).state
  let number := decodeInteger (state.heap.cell object offset)
  let origin := (actual.child (.var owner)).origin
  let sourceFirst := first.rename indices
  let sourceAgain := again.rename (liftRenaming 1 indices)
  let sourceBody := body.rename (liftRenaming 2 indices)
  have resumedClosing := resumed
  obtain ⟨closing,_,_,_⟩ := resumedClosing
  obtain ⟨nextContext,nextSizes⟩ := restored_contexts history context sizes ownerTyped sourceStored
    sourceFirst sourceAgain sourceBody origin number closing
  obtain ⟨aliasContext,aliasSizes⟩ := canonical_contexts source sourceFirst sourceAgain sourceBody origin number
    object (indices owner) nextContext nextSizes
  have sourceOrigin : origin = (Term.var (indices owner)).subst source.origins := by
    simpa only [origin,Code.origin,Code.child,Term.subst] using view.origins owner
  have restoreView := restored_canonical_view source sourceStored
    sourceFirst sourceAgain sourceBody (.integer number) (.integer number)
  rw [← sourceOrigin] at restoreView
  have aliasView := nextView.compose restoreView
  have nextCoverage := load_coverage coverage entered absent sourceFirst sourceAgain sourceBody origin number
  have aliasCoverage := coverage.enter_nonowner entered false sourceFirst
    (sourceBody.rename (Jihoo.Quantity.openOwner (indices owner+1))) (.integer number) (some (.integer number))
    (by intro queried same; cases same)
  have metadata := congrArg (fun result : Result => result.state.heap.metadata) executed
  have activeStack := congrArg (fun result : Result => result.state.activeStack) executed
  exact ⟨offset,executed,nextView,resumed,nextContext,metadata.symm ▸ nextSizes,activeStack.symm ▸ nextCoverage,
    aliasView,aliasContext,metadata.symm ▸ aliasSizes,activeStack.symm ▸ aliasCoverage⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
