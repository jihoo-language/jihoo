import Jihoo.NativeNumeralForward
import Jihoo.NativeLoanMixedPreservation
import Jihoo.NativeLoanDeltaPreservation

/-! Affine arithmetic evidence for Loan64. Substitution of mathematical
naturals and genuine raw conversion preserve the value of affine expressions.
The typing rules construct valid comparison evidence without a word bound on
an intermediate sum, a supplied interpretation, or a correctness oracle. -/
namespace Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
open AffineSum (Expr)
open EnvironmentDelta.NumeralForward (Represents family_forward_preserves)
open NativeKernel.Conversion (ListRel)

private theorem represented_unique (first : Represents term a) (second : Represents term b) : a = b := by
  induction first generalizing b with
  | natural => cases second; rfl
  | add left right ihLeft ihRight =>
    cases second with
    | add otherLeft otherRight => rw [ihLeft otherLeft,ihRight otherRight]

private theorem raw_forward_represents (steps : RawLend.Forward env input output) :
    ∀ {value}, Represents input value → Represents output value := by
  induction steps using RawLend.Forward.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys) with
  | old steps => exact family_forward_preserves steps
  | lend => intro _ represented; cases represented
  | refl => intro _ represented; exact represented
  | trans _ _ first second => intro _ represented; exact second (first represented)
  | node op children ih =>
    intro value represented
    cases represented with
    | natural => cases ih; exact .natural _
    | add left right =>
      cases ih with
      | cons alongLeft rest => cases rest with
        | cons alongRight rest => cases rest; exact .add (alongLeft left) (alongRight right)
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

private theorem evaluated_represents (expr : Expr) (assignment : Nat → Nat) :
    Represents (expr.toTerm.subst (fun i => .natural (assignment i))) (expr.eval assignment) := by
  induction expr with
  | var index => simpa only [Expr.toTerm,Term.subst,Expr.eval] using Represents.natural (assignment index)
  | literal value =>
    simpa only [Expr.toTerm,Term.subst,substArgs,Term.natural,Expr.eval] using Represents.natural value
  | add left right ihLeft ihRight =>
    simpa only [Expr.toTerm,Term.subst,substArgs,Term.uadd,Op.binders,liftSub,Expr.eval] using
      Represents.add ihLeft ihRight

/-- Conversion in the entire Loan64 theory preserves mathematical affine
values, including under valuations containing naturals larger than U64.
The closing substitution is used in the raw equational theory. -/
theorem affine_conversion_value (wf : UnifiedProgram.EnvWellFormed env) (left right : Expr)
    (converted : RawLend.Conv env left.toTerm right.toTerm) (assignment : Nat → Nat) :
    left.eval assignment = right.eval assignment := by
  have closed := converted.substitution (fun i => .natural (assignment i)) wf.closed
  obtain ⟨_,leftSteps,rightSteps⟩ := closed.church_rosser wf.admissible
  exact represented_unique
    (raw_forward_represents leftSteps (evaluated_represents left assignment))
    (raw_forward_represents rightSteps (evaluated_represents right assignment))

private def Affine (term : Term) : Prop := ∃ expr : Expr, expr.toTerm = term

/-- Only the operands of the algebraic proof constructors need affine
syntax. The checked Decide rule can expose arbitrary operands as numerals. -/
def Supported : Term → Prop
  | .decide _ _ => True
  | .zeroLe a => Affine a
  | .ltAdd a b c proof | .ltCancel a b c proof => Affine a ∧ Affine b ∧ Affine c ∧ Supported proof
  | .ltLe a b c first second => Affine a ∧ Affine b ∧ Affine c ∧ Supported first ∧ Supported second
  | .strict _ rest | .free _ rest | .node (.drop _) [_,rest] => Supported rest
  | .ifLt _ _ _ rest | .ifEq _ _ _ rest => Supported rest
  | .absurd _ proof => Supported proof
  | _ => False
termination_by term => sizeOf term

def Truth (env : Environment) (type : Term) : Prop :=
  ∃ left right : Expr, RawLend.Conv env (.lt left.toTerm right.toTerm) type ∧
    ∀ assignment, left.eval assignment < right.eval assignment

private theorem Truth.convert (truth : Truth env type)
    (converted : RawLend.Conv env type other) : Truth env other := by
  obtain ⟨left,right,original,valid⟩ := truth
  exact ⟨left,right,original.trans converted,valid⟩

/-- A realized affine proposition holds at every mathematical assignment. -/
theorem Truth.affine_less (wf : UnifiedProgram.EnvWellFormed env) (left right : Expr)
    (truth : Truth env (.lt left.toTerm right.toTerm)) (assignment : Nat → Nat) :
    left.eval assignment < right.eval assignment := by
  obtain ⟨actualLeft,actualRight,converted,ordered⟩ := truth
  obtain ⟨leftConv,rightConv⟩ := converted.lt_injective wf.admissible
  rw [← affine_conversion_value wf actualLeft left leftConv assignment,
      ← affine_conversion_value wf actualRight right rightConv assignment]
  exact ordered assignment

private theorem Truth.less_zero_impossible (wf : UnifiedProgram.EnvWellFormed env)
    (truth : Truth env (.lt term (.natural 0))) : False := by
  obtain ⟨left,right,converted,ordered⟩ := truth
  have rightConv : RawLend.Conv env right.toTerm (.literal 0 : Expr).toTerm :=
    (converted.lt_injective wf.admissible).2
  have value := affine_conversion_value wf right (.literal 0) rightConv (fun _ => 0)
  have impossible := ordered (fun _ => 0)
  rw [value] at impossible
  exact Nat.not_lt_zero _ impossible

/-- Reflect the actual derivation. In particular LtCancel derives order from
its actual input proof and cancels the same mathematical value on each side,
even when their sum does not fit in a word. -/
theorem supported_truth (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term type) (supported : Supported term) : Truth env type := by
  revert supported
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term type _ => Supported term → Truth env type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (simp only [Supported] at *)
  case decide =>
    rename_i leftBound rightBound ordered supported
    exact ⟨.literal _,.literal _,.refl _,fun _ => ordered⟩
  case decideConverted =>
    rename_i leftTyped rightTyped leftConv rightConv leftBound rightBound ordered ihLeft ihRight supported
    exact ⟨.literal _,.literal _,.node .lt (.cons leftConv.symm (.cons rightConv.symm .nil)),fun _ => ordered⟩
  case zeroLe =>
    rename_i typed ih supported
    obtain ⟨value,rfl⟩ := supported
    exact ⟨.literal 0,.add value (.literal 1),.refl _,fun _ => Nat.zero_lt_succ _⟩
  case ltAdd =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof supported
    obtain ⟨⟨left,rfl⟩,⟨right,rfl⟩,⟨step,rfl⟩,proofSupported⟩ := supported
    refine ⟨.add left step,.add right step,.refl _,fun assignment => ?_⟩
    have ordered := (ihProof proofSupported).affine_less wf left right assignment
    exact Nat.add_lt_add_right ordered _
  case ltCancel =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof supported
    obtain ⟨⟨left,rfl⟩,⟨right,rfl⟩,⟨step,rfl⟩,proofSupported⟩ := supported
    refine ⟨left,right,.refl _,fun assignment => ?_⟩
    have ordered := (ihProof proofSupported).affine_less wf (.add left step) (.add right step) assignment
    exact Nat.lt_of_add_lt_add_right ordered
  case ltLe =>
    rename_i leftTyped middleTyped rightTyped lowerTyped upperTyped ihLeft ihMiddle ihRight ihLower ihUpper supported
    obtain ⟨⟨left,rfl⟩,⟨middle,rfl⟩,⟨right,rfl⟩,lowerSupported,upperSupported⟩ := supported
    refine ⟨left,right,.refl _,fun assignment => ?_⟩
    have lower := (ihLower lowerSupported).affine_less wf left middle assignment
    have upper := (ihUpper upperSupported).affine_less wf middle (.add right (.literal 1)) assignment
    simp only [Expr.eval] at upper
    omega
  case strict => rename_i first rest ihFirst ihRest supported; exact ihRest supported
  case free => rename_i owner rest ihOwner ihRest supported; exact ihRest supported
  case drop => rename_i found boxed owner rest ihOwner ihRest supported; exact ihRest supported
  case ifLt => rename_i left right yes no ihLeft ihRight ihYes ihNo supported; exact ihNo supported
  case ifEq => rename_i left right yes no ihLeft ihRight ihYes ihNo supported; exact ihNo supported
  case absurd =>
    rename_i target proof allowed ihTarget ihProof supported
    exact False.elim ((ihProof supported).less_zero_impossible wf)
  case convert => rename_i typed converted ih supported; exact (ih supported).convert converted
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches supported
    cases analysis <;> simp [Supported] at supported

theorem no_supported_less_zero (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term (.lt left (.natural 0)))
    (supported : Supported term) : False := (supported_truth wf typed supported).less_zero_impossible wf

/-- Evaluate through the independently proved typed contextual path from the
real mixed history. Only the actual residual needs arithmetic syntax. Raw
normalization success alone does not supply this typing-preserving path. -/
theorem checked_residual_truth (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (steps : LoanTyping.FamilyEvaluation.Steps env term residual) (supported : Supported residual) :
    Truth env type := supported_truth history.wellFormed (history.contextual_preservation steps typed).2 supported

theorem no_checked_residual_less_zero (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans ctx mode term (.lt left (.natural 0)))
    (steps : LoanTyping.FamilyEvaluation.Steps env term residual) (supported : Supported residual) : False :=
  (checked_residual_truth history typed steps supported).less_zero_impossible history.wellFormed

theorem checked_declaration_truth (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env source = some expanded)
    (supported : Supported expanded.value) : Truth env expanded.type := by
  obtain ⟨_,_,typed,_⟩ := (LoanTyping.MixedProgram.checkDeclaration_sound checked).valid.typing
  exact supported_truth history.wellFormed typed supported

/-- The actual mixed history supplies the global's type. Transparent unfolding
and contextual computation can reach an affine proof even when its starting
syntax is a global or a non-arithmetic computation. -/
theorem checked_global_delta_residual_truth
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (steps : LoanTyping.DeltaEvaluation.Steps env (.node (.global index) []) residual)
    (supported : Supported residual) : Truth env declaration.type := by
  have typed : LoanTyping.HasType env [] [] true (.node (.global index) []) declaration.type := by
    have renamed : LoanTyping.HasType env [] [] true (.node (.global index) [])
        (declaration.type.rename id) := .global found
    simpa only [Term.rename_id] using renamed
  exact supported_truth history.wellFormed (history.delta_computation_preservation steps typed).2 supported

theorem no_checked_global_delta_residual_less_zero
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (steps : LoanTyping.DeltaEvaluation.Steps env (.node (.global index) []) residual)
    (supported : Supported residual)
    (requested : RawLend.Conv env declaration.type (.lt left (.natural 0))) : False :=
  ((checked_global_delta_residual_truth history found steps supported).convert requested).less_zero_impossible
    history.wellFormed

private def shiftedEvidence : Term :=
  let zero := Term.natural 0
  let one := Term.natural 1
  let step := Term.natural (2^64-1)
  .ltCancel zero one step (.ltAdd zero one step (.zeroLe zero))

private def cancellationProof : GlobalDeclaration :=
  ⟨.lt (.natural 0) (.natural 1),
    .ltLe (.natural 0) (.natural 1) (.natural 1) shiftedEvidence (.decide (.natural 1) (.natural 2))⟩

private theorem cancellation_supported : Supported cancellationProof.value := by
  simp only [cancellationProof,shiftedEvidence,Supported]
  exact ⟨⟨.literal 0,rfl⟩,⟨.literal 1,rfl⟩,⟨.literal 1,rfl⟩,
    ⟨⟨.literal 0,rfl⟩,⟨.literal 1,rfl⟩,⟨.literal _,rfl⟩,
      ⟨⟨.literal 0,rfl⟩,⟨.literal 1,rfl⟩,⟨.literal _,rfl⟩,⟨.literal 0,rfl⟩⟩⟩,trivial⟩

example : Truth Environment.empty (.lt (.natural 0) (.natural 1)) := by
  have checked : LoanTyping.MixedProgram.checkDeclaration 64 64 Environment.empty cancellationProof =
      some cancellationProof := by cbv
  exact checked_declaration_truth LoanTyping.MixedProgram.History.empty checked cancellation_supported

private def cancellationWorld : Environment := ⟨#[cancellationProof],#[]⟩

example : Truth cancellationWorld (.lt (.natural 0) (.natural 1)) := by
  have checked : LoanTyping.MixedProgram.checkProgram 64 64 [cancellationProof] [] = some cancellationWorld := by cbv
  have found : cancellationWorld.globals[0]? = some cancellationProof := rfl
  exact checked_global_delta_residual_truth (LoanTyping.MixedProgram.checkProgram_sound checked) found
    (.delta found) cancellation_supported

end Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
