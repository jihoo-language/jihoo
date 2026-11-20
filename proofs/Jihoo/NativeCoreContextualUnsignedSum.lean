import Jihoo.NativeCoreUnsignedSum
import Jihoo.NativeLoanContextualUnsignedCancellation

/-! Connect checked contextual cancellation to the live Core.sum
branch with a symbolic subtraction and a matching denominator under
Strict. The original Strict prefix is retained in the emitted graph. -/
namespace Jihoo.NativeKernel.NativeCoreContextualUnsignedSum

open NativeArena Environment NativeCoreGraph
open NativeCoreUnsignedCollect (Pool)
open Environment.LoanTyping.ContextualUnsignedCancellation (Expression CheckedForward)
open Environment.LoanTyping.PureHypothesisObservation (Entry ScalarExpr context)
open Environment.LoanTyping.OpenProofNormalization (Tree)
open Environment.LoanTyping.WideHypothesisObservation (Satisfies closing)

structure Inputs (arena : Arena) (left right numerator denominator evidence kept x y : Nat) : Prop where
  numeratorRow : arena[numerator]? = some (.var x)
  denominatorRow : arena[denominator]? = some (.var y)
  differenceRow : arena[left]? = some (.node .usub [numerator, denominator, evidence])
  strictRow : arena[right]? = some (.node .strict [kept, denominator])

private theorem reference_bound {arena : Arena} (found : arena[ref]? = some node) : ref < arena.size :=
  (Array.getElem?_eq_some_iff.mp found).1

private theorem same_variable
    (found : arena[ref]? = some (.var index)) (inBudget : initial+1 ≤ limit) :
    NativeCoreIdentical.runArena arena limit (depth+1) initial ref ref = (.ok true, initial+1) := by
  simp (config := { autoUnfold := true }) only [NativeCoreIdentical.runArena, found,
    Nat.not_lt.mpr inBudget, ite_false, ite_true, NativeCoreIdentical.runChildren] <;> rfl

private theorem remove_single
    (found : arena[ref]? = some (.var index)) (inBudget : initial+2 ≤ limit) :
    NativeCoreUnsignedCancellation.run arena limit (depth+1) initial [ref] [ref] =
      (.ok (some []), initial+2) := by
  have room : ¬limit < initial+1 := by omega
  have valid : ¬arena.size ≤ ref := Nat.not_le.mpr (reference_bound found)
  have same := same_variable (depth := depth) (initial := initial+1) found (by omega : initial+1+1 ≤ limit)
  simp (config := { autoUnfold := true }) only [NativeCoreUnsignedCancellation.run,
    NativeCoreUnsignedCancellation.tick, room, valid, Nat.succ_ne_zero, ite_false, same, Nat.add_assoc]

private theorem collect_initial (rows : Inputs arena left right numerator denominator evidence kept x y)
    (inBudget : initial+3 ≤ limit) :
    NativeCoreUnsignedCollect.runOperands arena limit (depth+2) initial left right =
      (.ok {atoms := #[left, denominator], pending := #[kept]}, initial+3) := by
  have first : ¬limit < initial+1 := by omega
  have second : ¬limit < initial+2 := by omega
  have third : ¬limit < initial+3 := by omega
  have leftValid : ¬arena.size ≤ left := Nat.not_le.mpr (reference_bound rows.differenceRow)
  have rightValid : ¬arena.size ≤ right := Nat.not_le.mpr (reference_bound rows.strictRow)
  have denomValid : ¬arena.size ≤ denominator := Nat.not_le.mpr (reference_bound rows.denominatorRow)
  simp (config := { autoUnfold := true }) only [NativeCoreUnsignedCollect.runOperands,
    NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick, rows.differenceRow,
    rows.strictRow, rows.denominatorRow, leftValid, rightValid, denomValid, first, second, third,
    Nat.succ_ne_zero, ite_false, Nat.add_assoc] <;> rfl

private theorem cancel_once (rows : Inputs arena left right numerator denominator evidence kept x y)
    (inBudget : initial+4 ≤ limit) :
    let before : Pool := {atoms := #[left, denominator], pending := #[kept]}
    NativeCoreUnsignedSumRounds.scan env runtime arena limit (depth+2) before [] before.atoms.toList initial =
      (.ok (some {atoms := #[numerator], pending := #[kept]}), initial+4) := by
  have first : ¬limit < initial+1 := by omega
  have last : ¬limit < initial+4 := by omega
  have numeratorInArena : ¬arena.size ≤ numerator := Nat.not_le.mpr (reference_bound rows.numeratorRow)
  have denominatorInArena : ¬arena.size ≤ denominator := Nat.not_le.mpr (reference_bound rows.denominatorRow)
  have removed : NativeCoreUnsignedCancellation.run arena limit (depth+2) (initial+1)
      [denominator] [denominator] = (.ok (some []), initial+3) :=
    remove_single (depth := depth+1) (initial := initial+1) rows.denominatorRow (by omega)
  simp (config := { autoUnfold := true }) only [NativeCoreUnsignedSumRounds.scan,
    NativeCoreUnsignedSumRounds.attempt, NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick,
    NativeCoreTrapAnalysis.graphMayTrap, rows.differenceRow, rows.denominatorRow, rows.numeratorRow,
    numeratorInArena, denominatorInArena, first, Nat.succ_ne_zero, ite_false, Nat.add_assoc]
  simp [removed, last, Nat.add_assoc] <;> rfl

private theorem rounds_exact (rows : Inputs arena left right numerator denominator evidence kept x y)
    (inBudget : initial+4 ≤ limit)
    (memoryFree : CoreEffectAnalysis.graphMemoryFree env arena (depth+2) left = true) :
    let before : Pool := {atoms := #[left, denominator], pending := #[kept]}
    NativeCoreUnsignedSumRounds.rounds env runtime arena limit (depth+2) before initial =
      (.ok ({atoms := #[numerator], pending := #[kept]}, 1), initial+4) := by
  have denominatorFree : CoreEffectAnalysis.graphMemoryFree env arena (depth+2) denominator = true := by
    simp only [CoreEffectAnalysis.graphMemoryFree, rows.denominatorRow]
  have roundDone := cancel_once (env := env) (runtime := runtime) (depth := depth) rows inBudget
  let before : Pool := {atoms := #[left, denominator], pending := #[kept]}
  let after : Pool := {atoms := #[numerator], pending := #[kept]}
  have enabled : before.atoms.toList.all (CoreEffectAnalysis.graphMemoryFree env arena (depth+2)) = true := by
    simp [before, memoryFree, denominatorFree]
  have stable : NativeCoreUnsignedSumRounds.scan env runtime arena limit (depth+2) after []
      after.atoms.toList (initial+4) = (.ok none, initial+4) := by
    simp (config := { autoUnfold := true }) only [after, NativeCoreUnsignedSumRounds.scan, rows.numeratorRow]
  change NativeCoreUnsignedSumRounds.rounds env runtime arena limit (depth+2) before initial = _
  simp only [NativeCoreUnsignedSumRounds.rounds, enabled, ite_true]
  have noMore : NativeCoreUnsignedSumRounds.runRounds env runtime arena limit (depth+2) 63
      after (initial+4) = (.ok (after, 0), initial+4) := by
    rw [NativeCoreUnsignedSumRounds.runRounds, stable]
  rw [NativeCoreUnsignedSumRounds.runRounds, roundDone]
  change ((NativeCoreUnsignedSumRounds.runRounds env runtime arena limit (depth+2) 63 after (initial+4)).1.map
    (fun (final,count) => (final, count+1)),
      (NativeCoreUnsignedSumRounds.runRounds env runtime arena limit (depth+2) 63 after (initial+4)).2) = _
  rw [noMore]
  rfl

private theorem finish_exact (found : arena[numerator]? = some (.var x))
    (capacity : arena.size < entryLimit) (inBudget : spent ≤ limit) :
    let after : Pool := {atoms := #[numerator], pending := #[kept]}
    NativeCoreUnsignedSum.finish runtime arena limit spent left right after =
      ⟨arena.push (.node .strict [kept, numerator]), .ok arena.size, some spent⟩ := by
  have ordered : NativeCoreUnsignedOrder.run runtime arena [numerator] (limit-spent) =
      some ([numerator], limit-spent) := by
    cases runtime <;> simp (config := { autoUnfold := true }) only [NativeCoreUnsignedOrder.run, found] <;> rfl
  have emitted : NativeCoreUnsignedCanonical.run runtime arena [numerator] (0 : BitVec 128) (limit-spent) =
      ⟨arena, .ok (some numerator), limit-spent⟩ := by
    simp only [NativeCoreUnsignedCanonical.run, ordered]
    cases runtime <;> rfl
  simp only [NativeCoreUnsignedSum.finish, emitted, Nat.sub_sub_self inBudget,
    NativeCorePureUnsignedSum.keepPrefixes, addNode, capacity, ite_true, NativeArena.allocate, Except.mapError]

/-- The actual post-operand run selects the sole subtraction, consumes the
matching occurrence, and appends Strict with the original prefix. The
run charges seven visits including the two identity/removal ticks. -/
theorem run_exact (rows : Inputs arena left right numerator denominator evidence kept x y)
    (inBudget : initial+7 ≤ limit) (capacity : arena.size < entryLimit)
    (memoryFree : CoreEffectAnalysis.graphMemoryFree env arena (depth+2) left = true) :
    NativeCoreUnsignedSum.run env runtime arena limit (depth+2) initial left right =
      ⟨arena.push (.node .strict [kept, numerator]), .ok arena.size, some (initial+7)⟩ := by
  have collected := collect_initial (depth := depth) rows (by omega : initial+3 ≤ limit)
  have reduced := rounds_exact (runtime := runtime) (initial := initial+3) rows (by omega) memoryFree
  have emitted := finish_exact (runtime := runtime) (spent := initial+3+4) (left := left) (right := right)
    (kept := kept) rows.numeratorRow capacity (by omega : initial+3+4 ≤ limit)
  simp only [NativeCoreUnsignedSum.run, collected, reduced, emitted]

def sourceTerm (x y : Nat) (proofTerm keptTerm : Term) : Term :=
  .uadd (.usub (.var x) (.var y) proofTerm) (.strict keptTerm (.var y))

def arithmeticSource (x y : Nat) (proofTerm : Term) : Expression :=
  .add (.subtract (.var x) (.var y) proofTerm) (.affine (.var y))

def arithmeticResult (x : Nat) : Expression := .affine (.var x)

structure Refines (env : Environment) (entries : List Entry) (after : Arena)
    (output x y : Nat) (proofTerm keptTerm type : Term) : Prop where
  represented : Represents after output (.strict keptTerm (.var x))
  typed : LoanTyping.HasType env [] (context entries) true (.strict keptTerm (.var x)) type
  contextual : CheckedForward env entries (arithmeticSource x y proofTerm) (arithmeticResult x) type
  sourceProjection : RawValue.Conv env (sourceTerm x y proofTerm keptTerm) (arithmeticSource x y proofTerm).term
  resultProjection : RawValue.Conv env (.strict keptTerm (.var x)) (arithmeticResult x).term

/-- Actual successful graph execution emits a typed Strict node. The
source and result project to a contextual cancellation derived from the
same checked UAdd and original erased evidence. -/
theorem checked_run_refines
    (rows : Inputs arena left right numerator denominator evidence kept x y)
    (proofRep : Represents arena evidence proofTerm) (keptRep : Represents arena kept keptTerm)
    (formed : LoanTyping.ResourceModes.contextOK fuel env [] (context entries) = true)
    (checked : LoanTyping.Checker.check fuel env [] (context entries) true
      (sourceTerm x y proofTerm keptTerm) type = true)
    (xScalar : ScalarExpr entries (.var x)) (yScalar : ScalarExpr entries (.var y))
    (evidenceTree : Tree entries proofTerm)
    (inBudget : initial+7 ≤ limit) (capacity : arena.size < entryLimit)
    (memoryFree : CoreEffectAnalysis.graphMemoryFree env arena (depth+2) left = true) :
    let finished := NativeCoreUnsignedSum.run env runtime arena limit (depth+2) initial left right
    finished.result = .ok arena.size ∧ finished.steps = some (initial+7) ∧
      Refines env entries finished.arena arena.size x y proofTerm keptTerm type := by
  have execution := run_exact (runtime := runtime) rows inBudget capacity memoryFree
  refine ⟨by rw [execution], by rw [execution], ?_⟩
  have original := LoanTyping.Checker.check_sound checked
  have leftRep : Represents arena left (.usub (.var x) (.var y) proofTerm) :=
    .node rows.differenceRow rfl (.cons (.var rows.numeratorRow) (.cons (.var rows.denominatorRow) (.cons proofRep .nil)))
  have rightRep : Represents arena right (.strict keptTerm (.var y)) :=
    .node rows.strictRow rfl (.cons keptRep (.cons (.var rows.denominatorRow) .nil))
  have typed := NativeCoreUnsignedSum.run_refines leftRep rightRep original (by rw [execution])
  rw [execution] at typed ⊢
  have frame : Prefix arena (arena.push (.node .strict [kept, numerator])) := Prefix.push _ _
  have represented : Represents (arena.push (.node .strict [kept, numerator])) arena.size (.strict keptTerm (.var x)) :=
    .node Array.getElem?_push_size rfl (.cons (keptRep.frame frame) (.cons ((Represents.var rows.numeratorRow).frame frame) .nil))
  obtain ⟨_, computed, typed⟩ := typed.typed
  have resultType := Represents.unique computed represented ▸ typed
  obtain ⟨subtraction, strictDenominator, converted⟩ := original.uadd_inputs
  have arithmeticTyped : LoanTyping.HasType env [] (context entries) true (arithmeticSource x y proofTerm).term type :=
    (LoanTyping.HasType.uadd subtraction strictDenominator.strict_tail).convert converted
  exact ⟨represented, resultType,
    ⟨LoanTyping.ResourceModes.contextOK_sound formed, arithmeticTyped, .cancel xScalar yScalar evidenceTree⟩,
    .node .uadd (.cons (.refl _) (.cons (.strict _ _) .nil)), .strict _ _⟩

/-- Any arithmetic predicate sees the same projected input and output
under every satisfying valuation of the original checked telescope. -/
theorem Refines.truth (wellFormed : UnifiedProgram.EnvWellFormed env)
    (refined : Refines env entries after output x y proofTerm keptTerm type)
    (valuation : Satisfies entries words) (predicate : Nat → Prop) :
    predicate (words x - words y + words y) ↔ predicate (words x) :=
  refined.contextual.preserves_truth wellFormed valuation predicate

/-- With bounded operands, actual input and output forms, including their
Strict prefixes, are convertible after the satisfying substitution. -/
theorem Refines.closed_conversion (wellFormed : UnifiedProgram.EnvWellFormed env)
    (refined : Refines env entries after output x y proofTerm keptTerm type)
    (valuation : Satisfies entries words) (bounded : words x < 2^64) :
    let values := closing entries words
    RawValue.Conv env ((sourceTerm x y proofTerm keptTerm).subst values)
      ((Term.strict keptTerm (.var x)).subst values) := by
  let values := closing entries words
  have input := refined.sourceProjection.substitution values wellFormed.admissible
  have output := refined.resultProjection.substitution values wellFormed.admissible
  exact input.trans ((refined.contextual.closed_conversion wellFormed valuation ⟨bounded, True.intro⟩).trans
    output.symm)

private def demoContext : List Entry :=
  [.less (.var 0) (.add (.var 1) (.literal 1)), .scalar false, .scalar false]

private def demoKept : Term := .uadd (.var 2) (.natural 1)

private def demoArena : Arena := #[.var 2, .var 1, .var 0, .node .usub [0, 1, 2],
  .node (.natural 1) [], .node .uadd [0, 4], .node .strict [5, 1]]

/-- The erased hypothesis supplies the checked subtraction bound. The
exact result node points to the original potentially trapping addition. -/
theorem checked_symbolic_sum_retains_trap :
    let result := NativeCoreUnsignedSum.run .empty false demoArena 7 8 0 3 6
    result.result = .ok 7 ∧ result.steps = some 7 ∧
      Refines .empty demoContext result.arena 7 2 1 (.var 0) demoKept .u64 := by
  have rows : Inputs demoArena 3 6 0 1 2 5 2 1 := ⟨rfl, rfl, rfl, rfl⟩
  have proofRep : Represents demoArena 2 (.var 0) := .var rfl
  have keptRep : Represents demoArena 5 demoKept :=
    .node rfl rfl (.cons (.var rfl) (.cons (.node rfl rfl .nil) .nil))
  exact checked_run_refines (depth := 6) (fuel := 48) rows proofRep keptRep
    (by cbv) (by cbv) (.var (.there (.there .here))) (.var (.there .here))
    (.arithmetic (.assume .here)) (by decide) (by decide) (by cbv)

end Jihoo.NativeKernel.NativeCoreContextualUnsignedSum
