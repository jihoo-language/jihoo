import Jihoo.NativeKindValueEvaluation

/-! A real raw-env checker input need not return a displayed inferred kind
spine even in an authentic checked world. This is not a counterexample to
whole-program source-expansion coverage or native runtime soundness. The same
argument has a genuine canonical gate trace and a safe observed value. -/
namespace Jihoo.NativeKernel.Environment.InferredKindCoverageBoundary
open CodeKinds

def delayedKind : Nat → Term
  | 0 => .univ 0
  | n+1 => .app (.lam false .u64 (delayedKind n)) (.natural 0)
def environment : Environment := ⟨#[⟨.univ 1,delayedKind 3⟩],#[]⟩
def aliasTerm : Term := .node (.global 0) []
def argument : Term := .app (.lam false aliasTerm (.var 0)) .u64
def consumer : Term := .lam false (.univ 0) (.natural 0)

theorem authentic_history :
    UnifiedProgram.UnifiedProgramChecked [⟨.univ 1,delayedKind 3⟩] [] environment :=
  UnifiedProgram.checkProgram_sound (by cbv : UnifiedProgram.checkProgram 64 128
    [⟨.univ 1,delayedKind 3⟩] [] = some environment)

theorem actual_raw_inference_retains_residual :
    Checker.infer 4 environment [] false argument = some (delayedKind 1) := by cbv

theorem residual_inferred_kind_is_not_displayed : Jihoo.NativeKernel.kindOf (delayedKind 1) = false := rfl

theorem actual_raw_checked_call_accepted :
    CallReplay.checked 5 environment [] false consumer [argument] =
      some ([⟨false,.univ 0,argument⟩],.u64) := by cbv

/-- This actual raw argument has the authentic canonical gate trace, so the
inferred kind-spine route is a sufficient route and not a necessary one. -/
theorem actual_argument_canonical_gate_trace : ArgumentAtKind environment (.type 0) argument :=
  ⟨4,.univ 0,by cbv,by cbv,by cbv⟩

theorem no_displayed_inferred_kind_witness :
    ¬ ∃ actual, Checker.infer 4 environment [] false argument = some actual ∧
      Jihoo.NativeKernel.kindOf actual = true := by
  rintro ⟨actual,inferred,kinded⟩
  have same := Option.some.inj (actual_raw_inference_retains_residual.symm.trans inferred)
  subst actual
  exact Bool.false_ne_true kinded

/-- The alternative actual gate trace transports to the evaluated value
without a second code check or any input-spine completeness assumption. -/
theorem actual_argument_value_safe : Realizes environment (.type 0) .u64 := by
  apply (actual_argument_canonical_gate_trace.realizes authentic_history).forward authentic_history
  apply EnvironmentDelta.Forward.acu
  apply ACU.MixedRed.compute
  simpa [argument,Term.subst,single] using ACU.Computes.beta false aliasTerm (.var 0) .u64

def inlineArgument : Term := .app (.lam false (delayedKind 3) (.var 0)) .u64

/-- Inlining removes the shallow alias-budget behavior: the actual checker
requires sufficient source traversal fuel and then emits a displayed kind. -/
theorem actual_inline_argument_emits_displayed_kind :
    Checker.infer 64 .empty [] false inlineArgument = some (.univ 0) := by cbv

theorem actual_inline_small_budget_rejected :
    Checker.infer 4 .empty [] false inlineArgument = none := by cbv

end Jihoo.NativeKernel.Environment.InferredKindCoverageBoundary
