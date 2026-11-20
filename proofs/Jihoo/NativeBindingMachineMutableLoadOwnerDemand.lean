import Jihoo.NativeBindingMachineMutableOwnerDemand
import Jihoo.NativeBindingMachineMutableLoadContexts

/-! A variable Load consumes its old owner slot before introducing the
same physical owner as the callback's returned slot. The original source
projection determines both the old alias's residual demand and the
unchanged demands for other captured owners. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control} {count : Term}

structure LoadDemand (before after : Control) (owner offset : Nat) : Prop where
  returned : after.demand 0 = some 1
  consumed : after.demand (owner+2) = some 0
  retained : ∀ index, index ≠ owner → index ≠ offset →
    before.demand index = after.demand (index+2)

private theorem variable_projection (checked : projectRaw fuel env loans ctx (.var index) = some control) :
    control = .use index := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      simp only [projectRaw] at checked
      obtain ⟨binding,_,checked⟩ := Option.bind_eq_some_iff.mp checked
      split at checked
      · contradiction
      · exact (Option.some.inj checked).symm

private theorem owner_lambda_projection
    (checked : projectRaw fuel env loans ctx (.lam false again body) = some control) :
    ∃ innerFuel ownerMode receipt,
      ResourceModes.Resolved env loans ctx false again ownerMode ∧
      projectRaw innerFuel env loans (⟨again,false⟩ :: ctx) body = some receipt ∧
      control = .closure (.scope ownerMode (functionTail body receipt)) := by
  cases fuel with
  | zero => cases checked
  | succ innerFuel =>
      simp only [projectRaw,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
        bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
      split at checked
      · contradiction
      · obtain ⟨mode,resolved,checked⟩ := Option.bind_eq_some_iff.mp checked
        obtain ⟨receipt,projected,same⟩ := Option.bind_eq_some_iff.mp checked
        exact ⟨innerFuel,mode,receipt,ResourceModes.resolve_sound resolved,projected,(Option.some.inj same).symm⟩

private theorem scalar_lambda_projection
    (checked : projectRaw fuel env loans ctx (.lam false first body) = some control) :
    ∃ innerFuel mode receipt,
      projectRaw innerFuel env loans (⟨first,false⟩ :: ctx) body = some receipt ∧
      control = .closure (.scope mode (functionTail body receipt)) := by
  cases fuel with
  | zero => cases checked
  | succ innerFuel =>
      obtain ⟨mode,receipt,projection⟩ := projectRaw_lambda_body checked
      exact ⟨innerFuel,mode,receipt,projection⟩

private theorem known_scope_valid (mode : BinderMode)
    (valid : LocalScopes (.scope mode (.scope .linear entered))) :
    ∀ query, (Control.scope mode (.scope .linear entered)).demand query = entered.demand (query+2) := by
  intro query
  cases mode with
  | linear =>
      obtain ⟨first,owner,_⟩ := valid
      have firstCount : entered.demand 1 = some 1 := by simpa [Control.demand,owner] using first
      simp [Control.demand,firstCount,owner,bind,Option.bind,Nat.add_assoc]
  | erased =>
      obtain ⟨first,owner,_⟩ := valid
      have firstCount : entered.demand 1 = some 0 := by simpa [Control.demand,owner] using first
      simp [Control.demand,firstCount,owner,bind,Option.bind,Nat.add_assoc]
  | unrestricted =>
      have owner : entered.demand 0 = some 1 := valid.1
      simp [Control.demand,owner,bind,Option.bind,Nat.add_assoc]
  | borrowed =>
      have owner : entered.demand 0 = some 1 := valid.1
      simp [Control.demand,owner,bind,Option.bind,Nat.add_assoc]

/-- Exact source quantity transfer for the original checked variable Load.
The older source owner slot survives in the callback context with zero
demand. The two introduced binders shift all other captures uniformly. -/
theorem projectRaw_variable_load_demand (admissible : EnvironmentDelta.Admissible env)
    (checked : projectRaw fuel env loans ctx
      (.load (.var owner) (.var offset) evidence (.lam false first (.lam false again body))) = some control)
    (one : control.demand owner = some 1)
    (ownerType : Conversion.Conv env again (.buffer (count.rename Nat.succ))) :
    ∃ bodyFuel rawReceipt,
      projectRaw bodyFuel env loans (⟨again,false⟩ :: ⟨first,false⟩ :: ctx) body = some rawReceipt ∧
      LoadDemand control (reclose (functionTail body rawReceipt)) owner offset := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      change (do
        let operands ← fields (projectRaw fuel env loans ctx)
          [.var owner,.var offset,evidence,.lam false first (.lam false again body)] [0,1]
        let callback ← fetch (projectRaw fuel env loans ctx)
          [.var owner,.var offset,evidence,.lam false first (.lam false again body)] 3
        some (.seq operands (.once (caseBody 2 callback)))) = some control at checked
      obtain ⟨operands,checkedOperands,checked⟩ := Option.bind_eq_some_iff.mp checked
      obtain ⟨callback,checkedCallback,same⟩ := Option.bind_eq_some_iff.mp checked
      simp only [fields,fetch,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.bind_some] at checkedOperands
      obtain ⟨ownerControl,ownerChecked,rest⟩ := Option.bind_eq_some_iff.mp checkedOperands
      obtain ⟨offsetControl,offsetChecked,tail⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨offsetPart,indexChecked,offsetTail⟩ := Option.bind_eq_some_iff.mp offsetChecked
      have offsetShape : offsetControl = .seq (.use offset) .pure := by
        rw [variable_projection indexChecked] at offsetTail
        exact (Option.some.inj offsetTail).symm
      rw [variable_projection ownerChecked,offsetShape] at tail
      change some (.seq (.use owner) (.seq (.use offset) .pure)) = some operands at tail
      cases tail
      have outer : projectRaw fuel env loans ctx (.lam false first (.lam false again body)) = some callback :=
        checkedCallback
      obtain ⟨innerFuel,firstMode,inner,innerProjected,rfl⟩ := scalar_lambda_projection outer
      obtain ⟨bodyFuel,ownerMode,bodyReceipt,resolved,bodyProjected,rfl⟩ := owner_lambda_projection innerProjected
      have isLinear := resolved.convertible_buffer_linear admissible ownerType
      subst ownerMode
      let entered := reclose (functionTail body bodyReceipt)
      have shape : control = .seq (.seq (.use owner) (.seq (.use offset) .pure))
          (.once (.scope firstMode (.scope .linear entered))) := by
        rw [← Option.some.inj same]
        rfl
      have scopes : LocalScopes (.scope firstMode (.scope .linear entered)) := by
        rw [shape] at one
        exact (NativeQuantity.demand_localScopes _ one).2
      have owns : entered.demand 0 = some 1 := by
        cases firstMode
        · exact scopes.2.1
        · exact scopes.2.1
        · exact scopes.1
        · exact scopes.1
      have demand (query : Nat) :
          control.demand query = (entered.demand (query+2)).map
            (fun remaining => (if owner = query then 1 else 0) +
              (if offset = query then 1 else 0) + remaining) := by
        rw [shape]
        change (some ((if owner = query then 1 else 0) + ((if offset = query then 1 else 0) + 0))).bind
          (fun consumed => ((Control.scope firstMode (.scope .linear entered)).demand query).bind
            (fun remaining => some (consumed + remaining))) = _
        rw [known_scope_valid firstMode scopes]
        cases remaining : entered.demand (query+2) <;> simp [Option.bind]
      have oldOwner : entered.demand (owner+2) = some 0 := by
        rw [demand] at one
        cases remains : entered.demand (owner+2) with
        | none => simp [remains] at one
        | some remaining =>
            simp only [remains,Option.map_some,ite_true,Option.some.injEq] at one
            have zero : remaining = 0 := by omega
            simp [zero]
      refine ⟨bodyFuel,bodyReceipt,bodyProjected,owns,oldOwner,?_⟩
      intro query notOwner notOffset
      rw [demand]
      cases remaining : entered.demand (query+2) <;> simp [Ne.symm notOwner,Ne.symm notOffset]

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open CodeKinds

/-- Shifting old captures under the two retained arguments preserves their
physical owner world. The new slot carries the only demand on the loaded
owner; every older slot holding the same allocation is retired. -/
theorem OwnerDemandWorld.load_handoff
    (world : OwnerDemandWorld heap code current)
    (selected : code.values[owner]? = some (some (.owner object)))
    (indexValue : code.values[offset]? = some (some (.natural position)))
    (one : current.demand owner = some 1)
    (demand : LoanTyping.ResourceQuantity.LoadDemand current entered owner offset)
    (first again body origin : Term) (integer : Int) :
    let next := restoredContinuation code first again body origin (.integer integer) object (.integer integer)
    OwnerDemandWorld heap next entered ∧
      ∀ original, code.values[original]? = some (some (.owner object)) →
        entered.demand (original+2) = some 0 := by
  let next := restoredContinuation code first again body origin (.integer integer) object (.integer integer)
  have notScalar (index queried : Nat) (stored : code.values[index]? = some (some (.owner queried))) :
      index ≠ offset := by
    intro same
    subst index
    rw [indexValue] at stored
    cases stored
  have otherPositive (index queried uses : Nat) (stored : code.values[index]? = some (some (.owner queried)))
      (positive : entered.demand (index+2) = some (uses+1)) :
      current.demand index = some (uses+1) := by
    have other : index ≠ owner := by
      intro same
      subst index
      rw [demand.consumed] at positive
      cases positive
    rw [demand.retained index other (notScalar index queried stored)]
    exact positive
  have zeroAliases (index : Nat) (alias : code.values[index]? = some (some (.owner object))) :
      entered.demand (index+2) = some 0 := by
    by_cases same : index = owner
    · exact same.symm ▸ demand.consumed
    · rw [← demand.retained index same (notScalar index object alias)]
      exact world.exclusive owner index object 0 (Ne.symm same) selected alias one
  refine ⟨⟨?_,?_⟩,zeroAliases⟩
  · intro index queried uses stored positive
    cases index with
    | zero =>
        have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
        rw [demand.returned] at positive
        have amount : 1 = uses+1 := Option.some.inj positive
        exact ⟨same ▸ (world.live_once owner object 0 selected one).1,by omega⟩
    | succ previous =>
        cases previous with
        | zero => cases stored
        | succ old =>
            exact world.live_once old queried uses stored (otherPositive old queried uses stored positive)
  · intro index alias queried uses separate stored aliased positive
    cases index with
    | zero =>
        have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
        subst queried
        cases alias with
        | zero => exact False.elim (separate rfl)
        | succ previous =>
            cases previous with
            | zero => cases aliased
            | succ old => exact zeroAliases old aliased
    | succ previous =>
        cases previous with
        | zero => cases stored
        | succ old =>
            cases alias with
            | zero =>
                have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj aliased))
                subst queried
                rw [zeroAliases old stored] at positive
                cases positive
            | succ aliasPrefix =>
                cases aliasPrefix with
                | zero => cases aliased
                | succ oldAlias =>
                    by_cases consumed : oldAlias = owner
                    · exact consumed.symm ▸ demand.consumed
                    · rw [← demand.retained oldAlias consumed (notScalar oldAlias queried aliased)]
                      have oldSeparate : old ≠ oldAlias := fun same => separate (by rw [same])
                      exact world.exclusive old oldAlias queried uses oldSeparate stored aliased
                        (otherPositive old queried uses stored positive)

/-- Actual variable Load preserves the owner-demand invariant across
canonical source aliases. The current source receipt supplies liveness;
the continuation obtains its genuine projection, typed context, and
exclusive demand at the returned owner slot. -/
theorem reachable_variable_load_preserves_owner_demand (term : Term) (fuel : Nat)
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
    (coverage : LoanCoverage source loans (run fuel (initial term)).state.activeStack)
    (entered : Loans.Entered source.context.length loans)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context
      source.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial term)).state.heap.metadata source receipt)
    (used : receipt.demand (indices owner) = some 1) :
    let before := (run fuel (initial term)).state
    let result := run 9 before
    ∃ offset,
      let payload := before.heap.cell object offset
      let number := decodeInteger payload
      let origin := (actual.child (.var owner)).origin
      let actualNext := restoredContinuation actual first again body origin (.integer number) object (.integer number)
      let sourceNext := restoredContinuation source (first.rename indices) (again.rename (liftRenaming 1 indices))
        (body.rename (liftRenaming 2 indices)) origin (.integer number) object (.integer number)
      let nextMeanings := consValues (meanings (indices owner)) (consValues (.integer number) meanings)
      result = ⟨⟨before.heap,.evaluate actualNext,before.stack,before.pending⟩,
        [.load object offset payload,.legacy (.activate false (.lam false again body) (.integer number)),
          .legacy (.activate false body origin)],9⟩ ∧
      CanonicalView actualNext sourceNext (liftRenaming 2 indices) ∧
      LoanClosingTyped env loans false sourceNext nextMeanings type ∧ ValueContext env sourceNext nextMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceNext nextMeanings ∧
      LoanCoverage sourceNext loans result.state.activeStack ∧
      ∃ bodyFuel rawReceipt,
        LoanTyping.ResourceQuantity.projectRaw bodyFuel env loans sourceNext.context sourceNext.term = some rawReceipt ∧
        let effective := NativeQuantity.reclose (NativeQuantity.functionTail sourceNext.term rawReceipt)
        effective.demand 0 = some 1 ∧ OwnerDemandWorld result.state.heap.metadata sourceNext effective ∧
        ∀ alias, source.values[alias]? = some (some (.owner object)) → effective.demand (alias+2) = some 0 := by
  let sourceFirst := first.rename indices
  let sourceAgain := again.rename (liftRenaming 1 indices)
  let sourceBody := body.rename (liftRenaming 2 indices)
  let before := (run fuel (initial term)).state
  have storedSourceOwner := (view.values owner).symm.trans storedOwner
  have live := (world.live_once (indices owner) object 0 storedSourceOwner used).1
  obtain ⟨storedPosition, storedIndex, _⟩ := reachable_typed_variable_load term fuel history evaluating view typed
    context sizes indexErasure shape decideEvidence storedOwner live coverage checked budget
  have storedSourceIndex : source.values[indices index]? = some (some (.natural storedPosition)) :=
    (view.values index).symm.trans storedIndex
  obtain ⟨offset, executed, nextView, nextTyped, nextContext, nextSizes, nextCoverage, _⟩ :=
    reachable_variable_load_contexts term fuel history evaluating view typed context sizes indexErasure shape
      decideEvidence storedOwner live coverage entered checked budget
  have sourceShape : source.term = .load (.var (indices owner)) (.var (indices index))
      (evidence.rename indices) (.lam false sourceFirst (.lam false sourceAgain sourceBody)) := by
    rw [← view.termEq,shape]
    simp only [sourceFirst,sourceAgain,sourceBody,Term.rename,renameArgs,Op.binders,liftRenaming]
  obtain ⟨_,localType,sourceTyped,_⟩ := typed
  rw [sourceShape] at sourceTyped checked
  obtain ⟨_,_,_,ownerType,_⟩ := LoanTyping.load_retained_body history.wellFormed sourceTyped
  obtain ⟨bodyFuel,rawReceipt,bodyChecked,demand⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_variable_load_demand history.wellFormed.admissible checked used ownerType
  let origin := (actual.child (.var owner)).origin
  let number := decodeInteger (before.heap.cell object offset)
  obtain ⟨nextWorld,oldAliases⟩ := world.load_handoff storedSourceOwner storedSourceIndex used demand
    sourceFirst sourceAgain sourceBody origin number
  have sameHeap := congrArg (fun result : Result => result.state.heap.metadata) executed
  change (run 9 before).state.heap.metadata = before.heap.metadata at sameHeap
  rw [← sameHeap] at nextWorld
  exact ⟨offset,executed,nextView,nextTyped,nextContext,nextSizes,nextCoverage,bodyFuel,rawReceipt,
    bodyChecked,demand.returned,nextWorld,oldAliases⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
