import Jihoo.NativeLoanArithmeticProofConsistency

/-! Executable Loan64 proof normalization from the already proved contextual
rules. Raw Lend conversion can traverse callbacks that the source checker
types after specialization. This evaluator treats that callback boundary
atomically, while extending ordinary computation with family iota and delta. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofNormalization
open NativeKernel.Conversion (ListRel treeSize)

private theorem ordinary_contract (contracted : NativeKernel.Conversion.contract term = some result) :
    ACU.Computes term result ∨ ComputationEvaluation.ArithmeticRoot term result := by
  fun_cases NativeKernel.Conversion.contract term <;> simp_all [NativeKernel.Conversion.contract]
  all_goals try (split at contracted <;> simp_all <;> try (exact False.elim (by omega)))
  all_goals try (rcases contracted with ⟨bound,contracted⟩)
  all_goals try subst result
  all_goals first
    | exact .inl (.beta _ _ _ _)
    | exact .inr (.literalAdd _ _ (by change _ < 2^64; omega))
    | exact .inl (.sub _ _ _ (by omega) (by omega))
    | exact .inl (.read _ _ _ _ _ (by assumption))
    | exact .inl (.witnessPack _ _ _)
    | exact .inl (.proofPack _ _ _)
    | exact .inl (.derefBorrow _)
    | exact .inl (.borrowDeref _)
    | exact .inl (.transportRefl _ _ _)
    | exact .inl (.ifLtTrue _ _ _ _ (by omega))
    | exact .inl (.ifLtFalse _ _ _ _ (by omega))
    | exact .inl (.ifEqTrue _ _ _)
    | exact .inl (.ifEqFalse _ _ _ _ (by assumption))

def contract (env : Environment) : Term → Option Term
  | .node (.global index) [] => env.globals[index]?.map GlobalDeclaration.value
  | .lend owner (.lam false _ readerBody) (.lam false _ (.lam false _ body)) =>
      some (Lending.finish owner body (Lending.read owner readerBody))
  | .lend owner reader continuation =>
      if explicitCallbacks reader continuation then none
      else some (RawLend.desugar owner reader continuation)
  | term => (NativeKernel.Conversion.contract term).orElse (fun _ => FamilyIota.contract env term)

theorem contract_steps (contracted : contract env term = some result) :
    DeltaEvaluation.Steps env term result := by
  fun_cases contract env term
  · obtain ⟨declaration,found,rfl⟩ := Option.map_eq_some_iff.mp contracted
    exact .delta found
  · simp only [contract,Option.some.injEq] at contracted
    subst result
    exact .computation (.family (.pure (.atomic (.lend _ _ _ _ _ _))))
  · simp_all [contract]
  · rename_i generic
    simp_all only [contract,Bool.false_eq_true,↓reduceIte,Option.some.injEq]
    subst result
    exact .computation (.family (.pure (.generic _ _ _ (Bool.eq_false_iff.mpr generic))))
  · simp_all only [contract]
    cases ordinary : NativeKernel.Conversion.contract term with
    | none =>
      simp only [ordinary,Option.orElse_none] at contracted
      exact .computation (.family (FamilyEvaluation.contract_steps contracted))
    | some first =>
      simp only [ordinary,Option.orElse_some,Option.some.injEq] at contracted
      subst result
      rcases ordinary_contract ordinary with compute | arithmetic
      · exact .computation (.compute compute)
      · exact .computation (.arithmetic arithmetic)

/-- Exhaustion is reported as failure, including if a proposed contraction
exceeds the size allowance. Malformed Lend nodes are never descended into. -/
def normalize? (env : Environment) (budget : Nat) : Nat → Term → Option Term
  | 0, _ => none
  | fuel+1, term => do
    if treeSize term > budget then none else
      let rebuilt ← match term with
        | .var _ => some term
        | .node op children =>
          if op = .lend then some term
          else (children.mapM (normalize? env budget fuel)).map (.node op)
      if 4*(treeSize rebuilt+1)^2 > budget then none else
        match contract env rebuilt with
        | none => some rebuilt
        | some next => normalize? env budget fuel next

private theorem map_steps (normalizer : Term → Option Term)
    (sound : ∀ input output, normalizer input = some output → DeltaEvaluation.Steps env input output)
    (accepted : children.mapM normalizer = some results) :
    ListRel (DeltaEvaluation.Steps env) children results := by
  induction children generalizing results with
  | nil => simp only [List.mapM_nil,pure,Option.some.injEq] at accepted; subst results; exact .nil
  | cons child children ih =>
    simp only [List.mapM_cons] at accepted
    cases head : normalizer child with
    | none => simp [head] at accepted
    | some result =>
      simp only [head,Bind.bind,Option.bind] at accepted
      cases tail : children.mapM normalizer with
      | none => simp [tail] at accepted
      | some rest =>
        simp only [tail,pure,Option.some.injEq] at accepted
        subst results
        exact .cons (sound _ _ head) (ih tail)

theorem normalize?_steps (accepted : normalize? env budget fuel term = some result) :
    DeltaEvaluation.Steps env term result := by
  induction fuel generalizing term result with
  | zero => simp [normalize?] at accepted
  | succ fuel ih =>
    unfold normalize? at accepted
    split at accepted
    · contradiction
    have finish : ∀ rebuilt,
        (if 4*(treeSize rebuilt+1)^2 > budget then none else
          match contract env rebuilt with
          | none => some rebuilt
          | some next => normalize? env budget fuel next) = some result →
        DeltaEvaluation.Steps env rebuilt result := by
      intro rebuilt finished
      split at finished
      · contradiction
      cases contracted : contract env rebuilt with
      | none =>
        simp only [contracted,Option.some.injEq] at finished
        subst result
        exact .computation (.family .refl)
      | some next =>
        exact .trans (contract_steps contracted) (ih (by simpa only [contracted] using finished))
    cases term with
    | var => exact finish _ accepted
    | node op children =>
      by_cases lending : op = .lend
      · exact finish _ (by simpa only [lending,↓reduceIte,Bind.bind,Option.bind] using accepted)
      simp only [lending,↓reduceIte] at accepted
      cases descendants : children.mapM (normalize? env budget fuel) with
      | none => simp [descendants] at accepted
      | some rebuilt =>
        simp only [descendants,Option.map_some,Bind.bind,Option.bind] at accepted
        exact .trans (.node op lending (map_steps _ (fun _ _ found => ih found) descendants))
          (finish _ accepted)

/-- An actual successful run retains the original type from the mixed
program history, without checking the residual a second time. -/
theorem normalize?_preserves (history : MixedProgram.History definitions familyDeclarations env)
    (typed : HasType env loans ctx mode term type)
    (accepted : normalize? env budget fuel term = some result) :
    HasType env [] ctx true result type :=
  (history.delta_computation_preservation (normalize?_steps accepted) typed).2

theorem checked_global_truth (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (normalized : normalize? env budget fuel (.node (.global index) []) = some residual)
    (supported : Semantics.LoanArithmetic.Supported residual) :
    Semantics.LoanArithmetic.Truth env declaration.type :=
  Semantics.LoanArithmetic.checked_global_delta_residual_truth history found (normalize?_steps normalized) supported

theorem no_checked_global_less_zero (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (normalized : normalize? env budget fuel (.node (.global index) []) = some residual)
    (supported : Semantics.LoanArithmetic.Supported residual)
    (requested : RawLend.Conv env declaration.type (.lt left (.natural 0))) : False :=
  Semantics.LoanArithmetic.no_checked_global_delta_residual_less_zero history found
    (normalize?_steps normalized) supported requested

private def vector (index : Term) : Term := .node (.ind 0 1) [index]

private def proposition : FamilyDeclaration :=
  ⟨false,0,1,[vector (.natural 0),.pi false .u64 (.pi true (vector (.var 0))
    (vector (.uadd (.var 1) (.natural 1))))],0⟩

private def propositionEntry : CheckedFamily :=
  ⟨proposition,[⟨[],[.natural 0]⟩,
    ⟨[⟨false,.u64,none⟩,⟨true,vector (.var 0),some [.var 0]⟩],[.uadd (.var 1) (.natural 1)]⟩],false⟩

private def propositionType : Term := .lt (.natural 0) (.natural 1)
private def evidence : Term := .decide (.natural 0) (.natural 1)
private def branch : Term := .lam false .u64 (.lam true (vector (.var 0))
  (.lam true propositionType (.var 0)))

private def elimination : GlobalDeclaration :=
  ⟨propositionType,FamilyIota.elimTerm 0 (.lam false .u64 propositionType) [evidence,branch]
    (.node (.con 0 1 2) [.natural 0,.node (.con 0 0 0) []])⟩

private def eliminationEnvironment : Environment := ⟨#[elimination],#[propositionEntry]⟩

/-- The actual mixed checker admits the indexed proof family and exported
elimination. The executable path follows its recursive induction hypothesis
to the actual base evidence. -/
theorem checked_indexed_proof_elimination : Semantics.LoanArithmetic.Truth eliminationEnvironment propositionType := by
  have admitted : MixedProgram.checkProgram 64 64 [elimination] [proposition] = some eliminationEnvironment := by cbv
  have found : eliminationEnvironment.globals[0]? = some elimination := rfl
  have ran : normalize? eliminationEnvironment 200000 64 (.node (.global 0) []) = some evidence := by cbv
  exact checked_global_truth (MixedProgram.checkProgram_sound admitted) found ran
    (by simp [evidence,Semantics.LoanArithmetic.Supported])

end Jihoo.NativeKernel.Environment.LoanTyping.ProofNormalization
