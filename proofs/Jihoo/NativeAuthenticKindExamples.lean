import Jihoo.NativeTraceInterpretation
import Jihoo.NativeKindRealizationExamples

namespace Jihoo.NativeKernel.Environment.AuthenticKindExamples
open CodeKinds KindRealizationExamples

def familyAlias : Environment := ⟨#[⟨.univ 1,familyKind.term⟩],#[]⟩
def aliasTerm : Term := .node (.global 0) []

theorem authentic_alias_history :
    UnifiedProgram.UnifiedProgramChecked [⟨.univ 1,familyKind.term⟩] [] familyAlias :=
  UnifiedProgram.checkProgram_sound (by cbv :
    UnifiedProgram.checkProgram 64 128 [⟨.univ 1,familyKind.term⟩] [] = some familyAlias)

theorem neutral_argument_checked_at_raw_alias : ArgumentAtKind familyAlias familyKind neutralFamily :=
  ⟨64,aliasTerm,by cbv,by cbv,by cbv⟩

/-- The actual raw-alias trace suffices, without canonical checker replay. -/
theorem constructed_alias_closing :
    TraceInterpretation familyAlias [⟨aliasTerm,false⟩] (fun _ => neutralFamily) :=
  TraceInterpretation.single authentic_alias_history
    (by cbv : Checker.binder 64 familyAlias [] false aliasTerm = some (.type 1))
    (by cbv : Checker.check 64 familyAlias [] false neutralFamily aliasTerm = true)
    (by cbv : Conversion.normalize? familyAlias 64 aliasTerm = some familyKind.term)
    (by cbv : Checker.applicationOK 64 familyAlias false aliasTerm neutralFamily = true)

theorem all_typed_indices_nonowning_from_alias (typed : HasType familyAlias [] true index .u64) :
    ¬ Owned familyAlias (.app neutralFamily index) ∧ PiSeparated familyAlias (.app neutralFamily index) := by
  have realized := (neutral_argument_checked_at_raw_alias.realizes authentic_alias_history).index typed
  exact ⟨realized.not_owned authentic_alias_history,realized.nonFunction authentic_alias_history⟩

def later : Environment := ⟨familyAlias.globals.push ⟨.u64,.natural 0⟩,#[]⟩

theorem authentic_later_history :
    UnifiedProgram.UnifiedProgramChecked [⟨.univ 1,familyKind.term⟩,⟨.u64,.natural 0⟩] [] later :=
  UnifiedProgram.checkProgram_sound (by cbv :
    UnifiedProgram.checkProgram 64 128 [⟨.univ 1,familyKind.term⟩,⟨.u64,.natural 0⟩] [] = some later)

theorem original_argument_realizes_in_later_world : Realizes later familyKind neutralFamily :=
  neutral_argument_checked_at_raw_alias.realizes_in_extension
    (Extends.pushGlobal familyAlias ⟨.u64,.natural 0⟩) authentic_later_history

theorem forged_owner_alias_gate_rejected :
    Checker.applicationOK 64 familyAlias false aliasTerm
      (.lam false .u64 (.buffer (.var 0))) = false := by cbv

/-- Bounded success can retain an uncontracted input at fuel zero. It is not
an output-normality or canonicality certificate. -/
def hiddenKind : Term := .app (.lam false .u64 (.univ 0)) (.natural 0)

theorem inner_bounded_kind_residual :
    ACU.Bounded.normalize 0 200000 hiddenKind = some hiddenKind := by cbv

theorem outer_zero_budget_refuses_kind :
    Conversion.normalize? .empty 0 hiddenKind = none := by cbv

theorem outer_zero_budget_argument_refused :
    Checker.applicationOK 0 .empty false hiddenKind (.buffer (.natural 0)) = false := by cbv

theorem canonical_kind_forbids_same_owner_argument :
    Checker.applicationOK 0 .empty false (.univ 0) (.buffer (.natural 0)) = false := by cbv

theorem sufficient_budget_reveals_kind_guard :
    Checker.applicationOK 32 .empty false hiddenKind (.buffer (.natural 0)) = false := by cbv

end Jihoo.NativeKernel.Environment.AuthenticKindExamples
