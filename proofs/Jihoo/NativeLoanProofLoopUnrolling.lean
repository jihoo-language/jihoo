import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeLoanComputationPreservation

/-! Loan64 source induction with a bounded numeral count. The original base
and checked step produce a finite term at the exact dependent Loop result.
This unrolling interprets proof iteration. Loop itself is neutral in raw
conversion, so only later computations of the unrolled term use RawLend. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofLoop

private def IterationView (env : Environment) (ctx : Context) : Term → Term → Prop
  | .natural value, _ => value < 2^64
  | .loop count motive initial body, type => ∃ proof : Bool,
      HasType env [] ctx true count .u64 ∧
      HasType env [] ctx true initial (.app motive (.natural 0)) ∧
      HasType env [] ctx true body (loopBodyType count motive proof) ∧
      Conversion.Conv env (.app motive count) type
  | _, _ => True

private theorem IterationView.convert (view : IterationView env ctx term first)
    (converted : Conversion.Conv env first second) : IterationView env ctx term second := by
  fun_cases IterationView env ctx term first <;> simp only [IterationView] at view ⊢
  all_goals first | exact view | skip
  obtain ⟨proof,count,initial,body,original⟩ := view
  exact ⟨proof,count,initial,body,original.trans converted⟩

private theorem iteration_view (typed : HasType env loans ctx mode term type) :
    IterationView env ctx term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => IterationView env ctx term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case loop motive allowed count initial body policy ihMotive ihCount ihInitial ihBody =>
    exact ⟨_,count.ghost [],initial.ghost [],body.ghost [],.refl _⟩
  case dataElim => split <;> trivial
  case convert typed converted ih => exact ih.convert converted

private theorem lower_lift (term argument : Term) (depth : Nat) :
    (term.rename (fun index => index+(depth+1))).subst (liftSub depth (single argument)) =
      term.rename (fun index => index+depth) := by
  have raised : term.rename (fun index => index+(depth+1)) =
      (term.rename Nat.succ).rename (fun index => index+depth) := by
    rw [Term.rename_comp]
    congr 1
    funext index
    omega
  rw [raised,Term.shift_subst,Term.shift_subst_single]

private theorem lift_zero (values : Nat → Term) : liftSub 0 values = values := rfl

private theorem lift_twice (values : Nat → Term) : liftSub 1 (liftSub 1 values) = liftSub 2 values := rfl

private def stepTail (count : Nat) (motive : Term) (proof : Bool) : Term :=
  .pi true (.lt (.var 0) ((Term.natural count).rename Nat.succ))
    (.pi proof (.app (motive.rename (fun index => index+2)) (.var 1))
      (.app (motive.rename (fun index => index+3)) (.uadd (.var 2) (.natural 1))))

private def boundTail (count : Nat) (motive : Term) (proof : Bool) (i : Nat) : Term :=
  .pi true (.lt (.natural i) (.natural count))
    (.pi proof (.app (motive.rename Nat.succ) (.natural i))
      (.app (motive.rename (fun index => index+2)) (.uadd (.natural i) (.natural 1))))

private def accumulatorTail (motive : Term) (proof : Bool) (i : Nat) : Term :=
  .pi proof (.app motive (.natural i))
    (.app (motive.rename Nat.succ) (.uadd (.natural i) (.natural 1)))

private theorem stepTail_instantiate (count : Nat) (motive : Term) (proof : Bool) (i : Nat) :
    (stepTail count motive proof).subst (single (.natural i)) = boundTail count motive proof i := by
  simp only [stepTail,boundTail,Term.pi,Term.lt,Term.app,Term.uadd,Term.natural,Term.subst,substArgs,
    Op.binders,Term.rename,renameArgs,lift_zero,lift_twice]
  rw [lower_lift motive (.natural i) 1,lower_lift motive (.natural i) 2]
  simp only [liftSub,liftSubOne,single,Term.rename,renameArgs]

private theorem boundTail_instantiate (motive : Term) (proof : Bool) (i : Nat)
    (evidence : Term) :
    ((Term.pi proof (.app (motive.rename Nat.succ) (.natural i))
      (.app (motive.rename (fun index => index+2)) (.uadd (.natural i) (.natural 1)))).subst
      (single evidence)) = accumulatorTail motive proof i := by
  simp only [accumulatorTail,Term.pi,Term.app,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,lift_zero]
  rw [Term.shift_subst_single,lower_lift motive evidence 1]

private theorem accumulator_instantiate (motive : Term) (i : Nat) (previous : Term) :
    ((Term.app (motive.rename Nat.succ) (.uadd (.natural i) (.natural 1))).subst (single previous)) =
      .app motive (.uadd (.natural i) (.natural 1)) := by
  simp only [Term.app,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,lift_zero,Term.shift_subst_single]

/-- Apply an actual step to each preceding index, its bound evidence, and the
previously constructed induction witness. The term is a mathematical witness
for bounded induction, without a conversion rule that expands Loop. -/
def unroll (count : Nat) (initial body : Term) : Nat → Term
  | 0 => initial
  | i+1 => .app (.app (.app body (.natural i)) (.decide (.natural i) (.natural count))) (unroll count initial body i)

private theorem unroll_index_typed (bound : count < 2^64)
    (initialTyped : HasType env [] ctx true initial (.app motive (.natural 0)))
    (bodyTyped : HasType env [] ctx true body (loopBodyType (.natural count) motive proof))
    (i : Nat) (within : i ≤ count) : HasType env [] ctx true (unroll count initial body i) (.app motive (.natural i)) := by
  induction i with
  | zero => exact initialTyped
  | succ i ih =>
    have before : i < count := by omega
    have valid : i < 2^64 := by omega
    have nextValid : i+1 < 2^64 := by omega
    have first : HasType env [] ctx true (.app body (.natural i)) (boundTail count motive proof i) := by
      rw [← stepTail_instantiate]
      exact HasType.app (e := false) (B := stepTail count motive proof) bodyTyped (.natural valid) (Or.inl rfl)
    let evidence := Term.decide (.natural i) (.natural count)
    have second : HasType env [] ctx true (.app (.app body (.natural i)) evidence) (accumulatorTail motive proof i) := by
      rw [← boundTail_instantiate motive proof i evidence]
      exact HasType.app (e := true) first (.decide valid bound before) (Or.inl rfl)
    have third : HasType env [] ctx true (unroll count initial body (i+1))
        (.app motive (.uadd (.natural i) (.natural 1))) := by
      rw [← accumulator_instantiate motive i (unroll count initial body i)]
      exact HasType.app (e := proof) second (ih (by omega)) (Or.inl rfl)
    have added : Conversion.Conv env (.uadd (.natural i) (.natural 1)) (.natural (i+1)) :=
      .old (.legacy (.add i 1 nextValid))
    exact third.convert (.node .app (.cons (.refl _) (.cons added .nil)))

/-- The actual base/step judgments, with bounds derived from the count's
successful observation, construct the complete original-type unrolling. -/
theorem unroll_typed (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.loop count motive initial body) type)
    (countConverted : Conversion.Conv env count (.natural n)) (bound : n < 2^64) :
    HasType env [] ctx true (unroll n initial body n) type := by
  obtain ⟨proof,_,init,step,original⟩ := iteration_view typed
  have stepConverted := loopBodyType_count_congr wf.closed motive proof countConverted
  have exactResult := unroll_index_typed bound init (step.convert stepConverted) n (Nat.le_refl _)
  have convertedBack : Conversion.Conv env (.app motive (.natural n)) (.app motive count) :=
    .node .app (.cons (.refl _) (.cons countConverted.symm .nil))
  exact exactResult.convert (convertedBack.trans original)

theorem literal_unroll_typed (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.loop (.natural n) motive initial body) type) :
    HasType env [] ctx true (unroll n initial body n) type := by
  obtain ⟨_,count,_,_,_⟩ := iteration_view typed
  exact unroll_typed wf typed (.refl _) (iteration_view count)

theorem observed_unroll_typed (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.loop count motive initial body) type)
    (observed : Conversion.normalize? env fuel count = some (.natural n)) (bound : n < 2^64) :
    HasType env [] ctx true (unroll n initial body n) type :=
  unroll_typed wf typed (Conversion.normalize?_sound observed) bound

/-- Subsequent typed computation in the actual mixed environment can expose
arithmetic evidence from the expanded induction. No typing of the residual
or semantic validity of the base or step is supplied by the caller. -/
theorem literal_residual_truth (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.loop (.natural n) motive initial body) type)
    (steps : ComputationEvaluation.Steps env (unroll n initial body n) residual)
    (supported : Semantics.LoanArithmetic.Supported residual) : Semantics.LoanArithmetic.Truth env type := by
  exact Semantics.LoanArithmetic.supported_truth history.wellFormed
    (history.computation_preservation steps (literal_unroll_typed history.wellFormed typed)).2 supported

theorem no_literal_residual_less_zero (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode (.loop (.natural n) motive initial body) (.lt index (.natural 0)))
    (steps : ComputationEvaluation.Steps env (unroll n initial body n) residual)
    (supported : Semantics.LoanArithmetic.Supported residual) : False := by
  exact Semantics.LoanArithmetic.no_supported_less_zero history.wellFormed
    (history.computation_preservation steps (literal_unroll_typed history.wellFormed typed)).2 supported

end Jihoo.NativeKernel.Environment.LoanTyping.ProofLoop
