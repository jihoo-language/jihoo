import Jihoo.NativeLoanMixedPreservation
import Jihoo.NativeEnvironmentOperationalRoots

/-! The ordinary pure computation roots preserve the exact original type in
Loan64. The proof uses the actual Loan64 premises under result conversion,
including dependent branch evidence and converted refinement predicates. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def ComputationView (env : Environment) (ctx : Context) : Term → Term → Prop
  | .natural n, _ => n < 2^64
  | .uadd a b, T => HasType env [] ctx true a .u64 ∧ HasType env [] ctx true b .u64 ∧
      Conversion.Conv env .u64 T
  | .elements _ xs, _ => ∀ x ∈ xs, HasType env [] ctx true x .i64
  | .index a _ _, T => (∃ n, HasType env [] ctx true a (.array n) ∨
      HasType env [] ctx true a (.ref (.buffer n))) ∧ Conversion.Conv env .i64 T
  | .pack p a q, _ => HasType env [] ctx true a .u64 ∧ HasType env [] ctx true q (.app p a)
  | .witness s, _ => ∃ p, HasType env [] ctx true s (.refine p)
  | .transport f e p, T => ∃ a b, HasType env [] ctx true e (.eq a b) ∧
      HasType env [] ctx true p (.app f a) ∧ Conversion.Conv env (.app f b) T
  | .ifLt a b yes no, T => ∃ B, HasType env [] ctx true a .u64 ∧ HasType env [] ctx true b .u64 ∧
      HasType env [] (⟨.lt a b,true⟩ :: ctx) true yes (B.rename Nat.succ) ∧
      HasType env [] ctx true no B ∧ Conversion.Conv env B T
  | .ifEq a b yes no, T => ∃ B, HasType env [] ctx true a .u64 ∧ HasType env [] ctx true b .u64 ∧
      HasType env [] (⟨.eq a b,true⟩ :: ctx) true yes (B.rename Nat.succ) ∧
      HasType env [] ctx true no B ∧ Conversion.Conv env B T
  | .loop n motive init _, T => HasType env [] ctx true init (.app motive (.natural 0)) ∧
      Conversion.Conv env (.app motive n) T
  | .give erased motive owner value, T => ∃ A, HasType env [] ctx true owner A ∧
      HasType env [] ctx true value (.app motive owner) ∧ Conversion.Conv env (.back erased A motive) T
  | .take packed (.lam false owner (.lam erased value body)), T =>
      ∃ e A motive inferredOwner inferredErased inferredValue result normal outside,
        HasType env [] ctx true packed (.back e A motive) ∧
        HasType env [] ctx true (.lam false owner (.lam erased value body))
          (.pi false inferredOwner (.pi inferredErased inferredValue result)) ∧
        Conversion.Conv env owner A ∧ Conversion.Conv env value (takeResultType motive) ∧
        Conversion.Conv env result normal ∧ PartialRenaming.shift (-2) 0 normal = some outside ∧
        Conversion.Conv env outside T
  | _, _ => True

private theorem ComputationView.convert (view : ComputationView env ctx term type)
    (converted : Conversion.Conv env type result) : ComputationView env ctx term result := by
  fun_cases ComputationView env ctx term type <;> simp only [ComputationView] at view ⊢
  all_goals first
    | exact view
    | obtain ⟨a,b,original⟩ := view; exact ⟨a,b,original.trans converted⟩
    | obtain ⟨a,original⟩ := view; exact ⟨a,original.trans converted⟩
    | obtain ⟨a,b,c,original⟩ := view; exact ⟨a,b,c,original.trans converted⟩
    | obtain ⟨a,b,c,d,original⟩ := view; exact ⟨a,b,c,d,original.trans converted⟩
    | obtain ⟨a,b,c,d,e,original⟩ := view; exact ⟨a,b,c,d,e,original.trans converted⟩
    | obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,original⟩ := view
      exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,original.trans converted⟩

private theorem computation_view (typed : HasType env loans ctx mode term type) :
    ComputationView env ctx term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => ComputationView env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case uadd left right _ _ => exact ⟨left.ghost [],right.ghost [],.refl _⟩
  case elements _ _ values _ => exact fun value member => (values value member).ghost []
  case index array _ _ _ _ _ => exact ⟨⟨_,.inl (array.ghost [])⟩,.refl _⟩
  case borrowedIndex reference _ _ _ _ _ => exact ⟨⟨_,.inr (reference.ghost [])⟩,.refl _⟩
  case pack _ value proof _ _ _ => exact ⟨value.ghost [],proof.ghost []⟩
  case witness packed _ => exact ⟨_,packed.ghost []⟩
  case transport _ evidence proof _ _ _ => exact ⟨_,_,evidence.ghost [],proof.ghost [],.refl _⟩
  case ifLt left right yes no _ _ _ _ => exact ⟨_,left.ghost [],right.ghost [],yes.ghost [],no.ghost [],.refl _⟩
  case ifEq left right yes no _ _ _ _ => exact ⟨_,left.ghost [],right.ghost [],yes.ghost [],no.ghost [],.refl _⟩
  case loop _ _ _ init _ _ _ _ _ _ => exact ⟨init.ghost [],.refl _⟩
  case give owner _ _ _ value _ _ _ => exact ⟨_,owner.ghost [],value.ghost [],.refl _⟩
  case take packed continuation owner value result lowered _ _ _ =>
      exact ⟨_,_,_,_,_,_,_,_,_,packed.ghost [],continuation.ghost [],owner,value,result,lowered,.refl _⟩
  case dataElim => split <;> trivial
  case convert _ converted ih => exact ih.convert converted

theorem HasType.uadd_inputs (typed : HasType env loans ctx mode (.uadd left right) type) :
    HasType env [] ctx true left .u64 ∧ HasType env [] ctx true right .u64 ∧ Conversion.Conv env .u64 type :=
  computation_view typed

/-- The selected true arm receives the typed comparison of the original
operands. Its evidence binder keeps the exact source proposition. -/
theorem computed_ifLt_true_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.ifLt a b yes no) type)
    (leftNormalized : Conversion.Conv env a (.natural m)) (rightNormalized : Conversion.Conv env b (.natural n))
    (leftBound : m < 2^64) (rightBound : n < 2^64) (ordered : m < n) :
    HasType env [] ctx true (yes.subst (single (.decide a b))) type := by
  obtain ⟨_, left, right, yesTyped, _, converted⟩ := computation_view typed
  have evidence : HasType env [] ctx true (.decide a b) (.lt a b) :=
    .decideConverted left right leftNormalized rightNormalized leftBound rightBound ordered
  have instantiated := yesTyped.ghostInstantiate wf evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert converted

/-- Equal numeral observations make reflexivity inhabit the original
comparison, even when the two operands use different source syntax. -/
theorem computed_ifEq_true_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.ifEq a b yes no) type)
    (leftNormalized : Conversion.Conv env a (.natural n)) (rightNormalized : Conversion.Conv env b (.natural n)) :
    HasType env [] ctx true (yes.subst (single (.refl a))) type := by
  obtain ⟨_, left, _, yesTyped, _, converted⟩ := computation_view typed
  have operands := leftNormalized.trans rightNormalized.symm
  have evidence : HasType env [] ctx true (.refl a) (.eq a b) :=
    (HasType.refl left).convert (.node .eq (.cons (.refl _) (.cons operands .nil)))
  have instantiated := yesTyped.ghostInstantiate wf evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert converted

/-- All ordinary ACU computation roots, including evidence instantiation,
preserve the independently derived original Loan64 type. -/
theorem compute_ghost_preservation (wf : UnifiedProgram.EnvWellFormed env)
    (step : ACU.Computes input output) (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true output type := by
  cases step with
  | beta => exact typed.ghostBeta wf
  | sub a b p _ upper =>
      exact (HasType.natural (Nat.lt_of_le_of_lt (Nat.sub_le a b) upper)).convert typed.principalView
  | read count xs k p value selected =>
      obtain ⟨⟨n,array | reference⟩,converted⟩ := computation_view typed
      · exact ((computation_view array) _ (List.mem_of_getElem? selected)).convert converted
      · exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .array) (op' := .ref)
          rfl rfl (by intro same; cases same) reference.principalView wf.admissible)
  | witnessPack p a q =>
      obtain ⟨pred,packed⟩ := computation_view typed
      exact (computation_view packed).1.convert typed.principalView
  | proofPack p a =>
      obtain ⟨pred,packed,converted⟩ := typed.principalView
      have predicates := packed.principalView.refine_injective wf.admissible
      have witness : Conversion.Conv env (.witness (.pack p a output)) a :=
        (RawLend.Forward.old (.acu (.compute (.witnessPack p a output))) : RawLend.Forward env _ _).toConv
      have applied : Conversion.Conv env (.app p a) (.app pred (.witness (.pack p a output))) :=
        .node .app (.cons predicates (.cons witness.symm .nil))
      exact (computation_view packed).2.convert (applied.trans converted)
  | derefBorrow =>
      obtain ⟨domain,borrowed,result⟩ := typed.principalView
      obtain ⟨source,original,reference⟩ := borrowed.principalView
      exact (original.ghost []).convert ((reference.ref_injective wf.admissible).trans result)
  | borrowDeref =>
      obtain ⟨domain,dereferenced,result⟩ := typed.principalView
      obtain ⟨source,original,reference⟩ := dereferenced.principalView
      exact (original.ghost []).convert ((RawLend.Conv.node .ref (.cons reference .nil)).trans result)
  | transportRefl f a p =>
      obtain ⟨left,right,evidence,payload,result⟩ := computation_view typed
      obtain ⟨leftRelated,rightRelated⟩ := evidence.principalView.eq_injective wf.admissible
      have applied : Conversion.Conv env (.app f left) (.app f right) :=
        .node .app (.cons (.refl _) (.cons (leftRelated.symm.trans rightRelated) .nil))
      exact payload.convert (applied.trans result)
  | ifLtTrue m n yes no holds =>
      obtain ⟨B,left,right,yesTyped,noTyped,converted⟩ := computation_view typed
      have evidence : HasType env [] ctx true (.decide (.natural m) (.natural n)) (.lt (.natural m) (.natural n)) :=
        .decide (computation_view left) (computation_view right) holds
      have instantiated := yesTyped.ghostInstantiate wf evidence
      rw [Term.shift_subst_single] at instantiated
      exact instantiated.convert converted
  | ifLtFalse =>
      obtain ⟨B,noTyped,converted⟩ := typed.principalView
      exact (noTyped.ghost []).convert converted
  | ifEqTrue n yes no =>
      obtain ⟨B,left,right,yesTyped,noTyped,converted⟩ := computation_view typed
      have evidence : HasType env [] ctx true (.refl (.natural n)) (.eq (.natural n) (.natural n)) := .refl left
      have instantiated := yesTyped.ghostInstantiate wf evidence
      rw [Term.shift_subst_single] at instantiated
      exact instantiated.convert converted
  | ifEqFalse =>
      obtain ⟨B,noTyped,converted⟩ := typed.principalView
      exact (noTyped.ghost []).convert converted

/-- The actual forward path, lambda-shape condition and exact-type theorem
allow these roots to be lifted through the existing ordinary-node context
proof without traversing specialized Lend callbacks. -/
theorem compute_ghost_transform (wf : UnifiedProgram.EnvWellFormed env)
    (step : ACU.Computes input output) : GhostTransform env input output := by
  have forward : RawLend.Forward env input output := .old (.acu (.compute step))
  exact ⟨forward,raw_forward_lambda_shape forward,fun typed => compute_ghost_preservation wf step typed⟩

namespace ComputationEvaluation

/-- Individual ACU arithmetic roots. Context closure is handled by the same
guarded evaluation that also handles beta, Lend and family contractions. -/
inductive ArithmeticRoot : Term → Term → Prop where
  | assocRight (a b c : Term) :
      ArithmeticRoot (.uadd (.uadd a b) c) (.uadd a (.uadd b c))
  | assocLeft (a b c : Term) :
      ArithmeticRoot (.uadd a (.uadd b c)) (.uadd (.uadd a b) c)
  | comm (a b : Term) : ArithmeticRoot (.uadd a b) (.uadd b a)
  | zeroRight (a : Term) : ArithmeticRoot (.uadd a (.natural 0)) a
  | zeroLeft (a : Term) : ArithmeticRoot (.uadd (.natural 0) a) a
  | literalSplit (n : Nat) : n < AffineSum.wordLimit →
      ArithmeticRoot (.natural n) (ACU.compact (List.replicate n (.natural 1)))
  | literalAdd (m n : Nat) : m+n < AffineSum.wordLimit →
      ArithmeticRoot (.uadd (.natural m) (.natural n)) (.natural (m+n))

private theorem ArithmeticRoot.forward (step : ArithmeticRoot input output) : RawLend.Forward env input output := by
  apply RawLend.Forward.old
  apply FamilyIota.Extended.Forward.old
  apply EnvironmentDelta.Forward.acu
  apply ACU.MixedRed.arithmetic
  cases step with
  | assocRight => exact .assocRight _ _ _
  | assocLeft => exact .assocLeft _ _ _
  | comm => exact .comm _ _
  | zeroRight => exact .zeroRight _
  | zeroLeft => exact .zeroLeft _
  | literalSplit _ bound => exact .literalSplit _ bound
  | literalAdd _ _ bound => exact .literalAdd _ _ bound

private theorem compact_typed (typed : ∀ x ∈ xs, HasType env [] ctx true x .u64) :
    HasType env [] ctx true (ACU.compact xs) .u64 := by
  induction xs with
  | nil => exact .natural (by decide)
  | cons x xs ih =>
      cases xs with
      | nil => exact typed x (by simp)
      | cons y ys =>
          exact .uadd (typed x (by simp)) (ih (by intro z member; exact typed z (by simp [member])))

private theorem ArithmeticRoot.preserves (step : ArithmeticRoot input output)
    (typed : HasType env loans ctx mode input type) : HasType env [] ctx true output type := by
  cases step with
  | assocRight =>
      obtain ⟨left,right,converted⟩ := computation_view typed
      obtain ⟨a,b,_⟩ := computation_view left
      exact (HasType.uadd a (.uadd b right)).convert converted
  | assocLeft =>
      obtain ⟨left,right,converted⟩ := computation_view typed
      obtain ⟨b,c,_⟩ := computation_view right
      exact (HasType.uadd (.uadd left b) c).convert converted
  | comm =>
      obtain ⟨left,right,converted⟩ := computation_view typed
      exact (HasType.uadd right left).convert converted
  | zeroRight =>
      obtain ⟨left,_,converted⟩ := computation_view typed
      exact left.convert converted
  | zeroLeft =>
      obtain ⟨_,right,converted⟩ := computation_view typed
      exact right.convert converted
  | literalSplit n _ =>
      apply (compact_typed ?_).convert typed.principalView
      intro x member
      cases List.eq_of_mem_replicate member
      exact .natural (by decide)
  | literalAdd m n bound =>
      exact (HasType.natural bound).convert typed.principalView

/-- The composed typed source evaluator can interleave ordinary computation,
arithmetic, specialized Lend and family contractions beneath ordinary nodes.
Its Lend boundary has the same atomic callback discipline as FamilyEvaluation. -/
inductive Steps (env : Environment) : Term → Term → Prop where
  | family : FamilyEvaluation.Steps env input output → Steps env input output
  | compute : ACU.Computes input output → Steps env input output
  | arithmetic : ArithmeticRoot input output → Steps env input output
  | trans : Steps env input middle → Steps env middle output → Steps env input output
  | node (op : Op) : op ≠ .lend → NativeKernel.Conversion.ListRel (Steps env) xs ys →
      Steps env (.node op xs) (.node op ys)

private theorem transforms_forward
    (changes : NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) :
    NativeKernel.Conversion.ListRel (RawLend.Forward env) xs ys := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

theorem Steps.ghost_transform (history : ScopedProgram.History definitions declarations env)
    (steps : Steps env input output) : GhostTransform env input output := by
  induction steps using Steps.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (GhostTransform env) xs ys) with
  | family step => exact step.ghost_transform history
  | compute step => exact compute_ghost_transform history.wellFormed step
  | arithmetic step => exact ⟨step.forward,raw_forward_lambda_shape step.forward,step.preserves⟩
  | trans _ _ first second => exact first.trans second
  | node op notLend children ih =>
      exact ⟨.node op (transforms_forward ih),raw_forward_lambda_shape (.node op (transforms_forward ih)),
        fun typed => children_preservation history.wellFormed typed op _ rfl notLend _ ih⟩
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

end ComputationEvaluation

/-- Actual mixed-program admission supplies the checked prefix and family
data. Every composed evaluation yields a raw forward path and preserves the
exact original type of the complete Loan64 source derivation. -/
theorem MixedProgram.History.computation_preservation
    (history : MixedProgram.History definitions declarations env)
    (steps : ComputationEvaluation.Steps env input output)
    (typed : HasType env loans ctx mode input type) :
    RawLend.Forward env input output ∧ HasType env [] ctx true output type := by
  have transformed := steps.ghost_transform (ScopedProgram.History.ofLoanMixed history)
  exact ⟨transformed.forward,transformed.typed typed⟩

/-- The additional specified pure value roots preserve the original Loan64
type. Free and Strict operate on their pure result observations here. -/
theorem value_root_ghost_preservation (step : ValueReduction.Root input output)
    (typed : HasType env loans ctx mode input type) : HasType env [] ctx true output type := by
  cases step with
  | arithmetic op a b bound =>
      exact (HasType.integer bound.1 bound.2).convert typed.principalView
  | strict | free | foldZero =>
      obtain ⟨_,value,converted⟩ := typed.principalView
      exact (value.ghost []).convert converted
  | loopZero =>
      obtain ⟨value,converted⟩ := computation_view typed
      exact value.convert converted

/-- The existing executable pure value contractor preserves Loan64 typing
through each successful root contraction in a bounded run. -/
theorem value_run_ghost_preservation (fuel : Nat)
    (typed : HasType env loans ctx mode input type) :
    HasType env [] ctx true (ValueReduction.run fuel input) type := by
  induction fuel generalizing input loans mode with
  | zero => exact typed.ghost []
  | succ fuel ih =>
      simp only [ValueReduction.run]
      cases accepted : ValueReduction.contract input with
      | none => exact typed.ghost []
      | some result =>
          exact ih (value_root_ghost_preservation (ValueReduction.contract_sound accepted) typed)

private theorem back_components
    (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conversion.Conv env (.back e owner motive) (.back e' owner' motive')) :
    Conversion.Conv env owner owner' ∧ Conversion.Conv env motive motive' := by
  obtain ⟨_,children⟩ := converted.full_rigid_node_injective rfl rfl wf.admissible
  cases children with
  | cons owner tail =>
      cases tail with
      | cons motive _ => exact ⟨owner,motive⟩

/-- The pure Take/Give equation supplies both dependent continuation arguments
and retains the original requested type after eliminating the two binders. -/
theorem take_give_ghost_preservation (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.take (.give packedErased packedMotive actualOwner actualValue)
        (.lam false declaredOwner (.lam erased declaredValue body))) type) :
    HasType env [] ctx true
      (.app (.app (.lam false declaredOwner (.lam erased declaredValue body)) actualOwner) actualValue)
      type := by
  obtain ⟨e,A,motive,inferredOwner,inferredErased,inferredValue,result,normal,outside,
      packed,continuation,ownerChecked,valueChecked,resultNormalized,lowered,converted⟩ := computation_view typed
  obtain ⟨_,ownerTyped,valueTyped,packedConverted⟩ := computation_view packed
  obtain ⟨ownerRelated,motiveRelated⟩ := back_components wf packedConverted
  obtain ⟨_,innerType,_,inner,outerConverted⟩ := continuation.lamView
  obtain ⟨_,ownerBinder,innerConverted⟩ := outerConverted.pi_injective wf.admissible
  obtain ⟨_,_,_,_,valueConverted⟩ := inner.lamView
  obtain ⟨_,valueBinder,_⟩ := (valueConverted.trans innerConverted).pi_injective wf.admissible
  have ownerArgument := ownerTyped.convert (ownerRelated.trans (ownerChecked.symm.trans ownerBinder))
  have associatedType : Conversion.Conv env (.app packedMotive actualOwner) (.app motive actualOwner) :=
    .node .app (.cons motiveRelated (.cons (.refl _) .nil))
  have checkedValue : Conversion.Conv env (declaredValue.subst (single actualOwner))
      (.app motive actualOwner) := by
    simpa only [takeResultType,Term.subst,substArgs,Op.binders,liftSub,Term.shift_subst_single,single] using
      valueChecked.substitution (single actualOwner) wf.closed
  have valueArgument := valueTyped.convert (associatedType.trans
    (checkedValue.symm.trans (valueBinder.substitution (single actualOwner) wf.closed)))
  have application : HasType env [] ctx true
      (.app (.lam false declaredOwner (.lam erased declaredValue body)) actualOwner)
      (.pi inferredErased (inferredValue.subst (single actualOwner)) (result.subst (liftSub 1 (single actualOwner)))) := by
    have applied : HasType env [] ctx true
        (.app (.lam false declaredOwner (.lam erased declaredValue body)) actualOwner)
        ((Term.pi inferredErased inferredValue result).subst (single actualOwner)) :=
      .app continuation ownerArgument (Or.inl rfl)
    simpa only [Term.pi,Term.subst,substArgs,Op.binders,liftSub] using applied
  have resultType := (resultNormalized.substitution (liftSub 1 (single actualOwner)) wf.closed).substitution
    (single actualValue) wf.closed
  have outsideType : ((normal.subst (liftSub 1 (single actualOwner))).subst (single actualValue)) = outside := by
    rw [← load_result_reweakens lowered,Term.subst_comp,Term.subst_rename]
    calc
      _ = outside.subst Term.var := by
        congr 1
        funext index
        simp only [liftSub,liftSubOne,single,Term.rename,Term.subst]
      _ = outside := Term.subst_id _
  rw [outsideType] at resultType
  exact (HasType.app application valueArgument (Or.inl rfl)).convert (resultType.trans converted)

/-- Contract the two applications introduced by the pure Take/Give equation,
retaining the original type of Take at the fully instantiated body. -/
theorem take_give_ghost_finish (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.take (.give packedErased packedMotive actualOwner actualValue)
        (.lam false declaredOwner (.lam erased declaredValue body))) type) :
    HasType env [] ctx true
      ((body.subst (liftSub 1 (single actualOwner))).subst (single actualValue)) type := by
  have expanded := take_give_ghost_preservation wf typed
  have first : GhostTransform env
      (.app (.lam false declaredOwner (.lam erased declaredValue body)) actualOwner)
      (.lam erased (declaredValue.subst (single actualOwner))
        (body.subst (liftSub 1 (single actualOwner)))) := by
    simpa only [Term.lam,Term.subst,substArgs,Op.binders,liftSub] using
      (compute_ghost_transform wf (.beta false declaredOwner (.lam erased declaredValue body) actualOwner))
  have reduced := children_preservation wf expanded .app _ rfl (by decide) _
    (.cons first (.cons (.refl _) .nil))
  exact reduced.ghostBeta wf

end Jihoo.NativeKernel.Environment.LoanTyping
