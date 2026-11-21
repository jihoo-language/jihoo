import Jihoo.NativeLoanProofLoopUnrolling

/-! Finite Fold iteration constructs a term at the original accumulator
type. The checked body obtains the actual count bound at each index. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FoldUnrolling

open ProofLoop (lower_lift)

private def FoldView (env : Environment) (ctx : Context) : Term → Term → Prop
  | .fold count initial body, result => ∃ accumulator,
      HasType env [] ctx true count .u64 ∧ HasType env [] ctx true initial accumulator ∧
      HasType env [] ctx true body (foldAccumulatorBodyType count accumulator) ∧
      Conversion.Conv env accumulator result
  | _, _ => True

private theorem FoldView.convert (view : FoldView env ctx term old)
    (converted : Conversion.Conv env old next) : FoldView env ctx term next := by
  fun_cases FoldView env ctx term old <;> simp only [FoldView] at view ⊢
  all_goals first | exact view | skip
  obtain ⟨accumulator,count,initial,body,original⟩ := view
  exact ⟨accumulator,count,initial,body,original.trans converted⟩

private theorem fold_view (typed : HasType env loans ctx mode term type) : FoldView env ctx term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => FoldView env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case foldI64 count initial body _ _ _ _ =>
    exact ⟨.i64,count.ghost [],initial.ghost [],by simpa using body.ghost [],.refl _⟩
  case foldOwned count initial _ body _ _ _ _ =>
    exact ⟨_,count.ghost [],initial.ghost [],body.ghost [],.refl _⟩
  case dataElim => split <;> trivial
  case convert _ converted ih => exact ih.convert converted

private theorem lift_zero (replacements : Nat → Term) : liftSub 0 replacements = replacements := rfl

private theorem lift_twice (replacements : Nat → Term) :
    liftSub 1 (liftSub 1 replacements) = liftSub 2 replacements := rfl

private theorem step_result (count accumulator : Term) (i n : Nat)
    (countConverted : Conversion.Conv env count (.natural n)) (range : n < 2^64) (before : i < n)
    (bodyTyped : HasType env [] ctx true body (foldAccumulatorBodyType count accumulator))
    (previous : HasType env [] ctx true input accumulator) :
    HasType env [] ctx true
      (.app (.app (.app body (.natural i)) (.decide (.natural i) (.natural n))) input) accumulator := by
  let callbackTail := Term.pi true (.lt (.natural i) count)
    (.pi false (accumulator.rename Nat.succ) (accumulator.rename (fun index => index+2)))
  have firstType :
      ((Term.pi true (.lt (.var 0) (count.rename Nat.succ))
        (.pi false (accumulator.rename (fun index => index+2)) (accumulator.rename (fun index => index+3)))).subst
        (single (.natural i))) = callbackTail := by
    simp only [callbackTail,Term.pi,Term.lt,Term.subst,substArgs,Op.binders,lift_zero,lift_twice]
    rw [Term.shift_subst_single,lower_lift accumulator (.natural i) 1,lower_lift accumulator (.natural i) 2]
    rfl
  have first : HasType env [] ctx true (.app body (.natural i)) callbackTail := by
    rw [← firstType]
    exact .app bodyTyped (.natural (Nat.lt_trans before range)) (Or.inl rfl)
  have boundTyped : HasType env [] ctx true (.decide (.natural i) (.natural n)) (.lt (.natural i) count) := by
    have fact : HasType env [] ctx true (.decide (.natural i) (.natural n)) (.lt (.natural i) (.natural n)) :=
      HasType.decide (Nat.lt_trans before range) range before
    exact fact.convert (.node .lt (.cons (.refl _) (.cons countConverted.symm .nil)))
  let evidence := Term.decide (.natural i) (.natural n)
  have secondType :
      ((Term.pi false (accumulator.rename Nat.succ) (accumulator.rename (fun index => index+2))).subst
        (single evidence)) = .pi false accumulator (accumulator.rename Nat.succ) := by
    simp only [Term.pi,Term.subst,substArgs,Op.binders,lift_zero,Term.shift_subst_single,
      lower_lift accumulator evidence 1]
  have second : HasType env [] ctx true (.app (.app body (.natural i)) evidence)
      (.pi false accumulator (accumulator.rename Nat.succ)) := by
    rw [← secondType]
    exact .app first boundTyped (Or.inl rfl)
  have applied : HasType env [] ctx true (.app (.app (.app body (.natural i)) evidence) input)
      ((accumulator.rename Nat.succ).subst (single input)) :=
    .app second previous (Or.inl rfl)
  rw [Term.shift_subst_single] at applied
  exact applied

/-- A concrete unsigned count gives the original Fold result type at every
unrolled prefix. No typing of the unrolled body or result is supplied. -/
theorem unroll_preserves
    (typed : HasType env loans ctx mode (.fold count initial body) type)
    (converted : Conversion.Conv env count (.natural n)) (range : n < 2^64)
    (iterations : Nat) (within : iterations ≤ n) :
    HasType env [] ctx true (ProofLoop.unroll n initial body iterations) type := by
  obtain ⟨accumulator,_,initialTyped,bodyTyped,result⟩ := fold_view typed
  suffices prefixTyped : HasType env [] ctx true (ProofLoop.unroll n initial body iterations) accumulator by
    exact prefixTyped.convert result
  induction iterations with
  | zero => exact initialTyped
  | succ i ih =>
    change HasType env [] ctx true (.app (.app (.app body (.natural i)) (.decide (.natural i) (.natural n)))
      (ProofLoop.unroll n initial body i)) accumulator
    exact step_result count accumulator i n converted range (by omega) bodyTyped (ih (by omega))

end Jihoo.NativeKernel.Environment.LoanTyping.FoldUnrolling
