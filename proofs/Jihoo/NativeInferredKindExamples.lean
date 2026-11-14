import Jihoo.NativeInferredKindArguments
import Jihoo.NativeSmallTelescopeExamples

namespace Jihoo.NativeKernel.Environment.InferredKindExamples
open CodeKinds ClosingTelescopeExamples SmallTelescopeExamples ContextReplayExamples

/-- The same three-binder call now closes without EntriesClassified or an
externally supplied canonical-domain normalizer output. -/
theorem actual_three_binder_input_inference_closing :
    ∃ values, RealizedInterpretation .empty indexedIdentityContext values ∧
      Conversion.Conv .empty .u64 ((Term.app (.var 2) (.var 1)).subst values) := by
  apply close_inferred_kind_then_small (fuel := 63) empty_history (RealizedInterpretation.nil Term.var)
    (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false
      (.pi false .u64 (.univ 0)) = some (.type 1))) arbitrary_family_small_telescope
    (Checker.check_sound indexed_identity_checked)
    (entries := identityEntries) (argumentType := .pi false .u64 (.univ 0))
  · simpa only [Term.subst_id,identityArguments] using indexed_identity_actual_checked_call
  · cbv
  · rfl
  · rfl

def scalarAlias : Term := .node (.global 0) []
def familyAlias : Term := .node (.global 1) []
def aliasEnvironment : Environment :=
  ⟨#[⟨.univ 0,.u64⟩,⟨.univ 1,.pi false .u64 (.univ 0)⟩],#[]⟩
def aliasedFamily : Term := .lam false scalarAlias .u64

theorem alias_history : UnifiedProgram.UnifiedProgramChecked
    [⟨.univ 0,.u64⟩,⟨.univ 1,.pi false scalarAlias (.univ 0)⟩] [] aliasEnvironment :=
  UnifiedProgram.checkProgram_sound (by cbv : UnifiedProgram.checkProgram 64 128
    [⟨.univ 0,.u64⟩,⟨.univ 1,.pi false scalarAlias (.univ 0)⟩] [] = some aliasEnvironment)

theorem argument_actual_inference_is_raw_alias :
    Checker.infer 63 aliasEnvironment [] false aliasedFamily = some (.pi false scalarAlias (.univ 0)) := by cbv

theorem inferred_type_has_kind_spine_but_is_not_canonical_first_order :
    Jihoo.NativeKernel.kindOf (.pi false scalarAlias (.univ 0)) = true ∧
      firstOrderKind (.pi false scalarAlias (.univ 0)) = false := by cbv

/-- The target canonical output is derived from raw actual input inference,
comparison, and the actual gate; no target normalizer trace is an input. -/
theorem raw_alias_kind_argument_from_actual_input :
    ArgumentAtKind aliasEnvironment (.index false (.type 0)) aliasedFamily := by
  apply ArgumentAtKind.of_inferred_kind alias_history argument_actual_inference_is_raw_alias
    (by rfl) (domain := familyAlias) (by cbv) (by cbv)
  exact .delta (env := aliasEnvironment) (index := 1)
    (declaration := ⟨.univ 1,.pi false .u64 (.univ 0)⟩) rfl

def aliasSourceFunction : Term := .lam false familyAlias
  (.lam true .u64 (.lam false (.app (.var 1) (.var 0)) (.var 0)))
def aliasSourceSignature : Term := .pi false familyAlias
  (.pi true .u64 (.pi false (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1))))
def aliasContext : Context := [⟨.app (.var 1) (.var 0),false⟩,⟨.u64,true⟩,⟨familyAlias,false⟩]
def aliasArguments : List Term := [aliasedFamily,.strict owner (.natural 0),.natural 7]
def aliasEntries : List CallReplay.Argument :=
  [⟨false,.pi false .u64 (.univ 0),aliasedFamily⟩,
    ⟨true,.u64,.strict owner (.natural 0)⟩,⟨false,.u64,.natural 7⟩]

theorem alias_small_tail : SmallTelescope aliasEnvironment [⟨familyAlias,false⟩]
    suffixSignature 2 aliasContext (.app (.var 2) (.var 1)) := by
  apply SmallTelescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 aliasEnvironment
    [⟨familyAlias,false⟩] true .u64 = some (.type 0))) (Or.inr rfl)
  apply SmallTelescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 aliasEnvironment
    [⟨.u64,true⟩,⟨familyAlias,false⟩] false (.app (.var 1) (.var 0)) = some (.type 0))) (Or.inr rfl)
  exact .nil

theorem actual_raw_alias_three_binder_closing :
    ∃ values, RealizedInterpretation aliasEnvironment aliasContext values ∧
      Conversion.Conv aliasEnvironment .u64 ((Term.app (.var 2) (.var 1)).subst values) := by
  apply close_inferred_kind_then_small (fuel := 63) alias_history (RealizedInterpretation.nil Term.var)
    (Checker.binder_sound (by cbv : Checker.binder 64 aliasEnvironment [] false familyAlias = some (.type 1)))
    alias_small_tail
    (Checker.check_sound (by cbv : Checker.check 64 aliasEnvironment [] false aliasSourceFunction aliasSourceSignature = true))
    (entries := aliasEntries) (argumentType := .pi false scalarAlias (.univ 0))
    (argument := aliasedFamily) (rest := [.strict owner (.natural 0),.natural 7])
  · cbv
  · exact argument_actual_inference_is_raw_alias
  · rfl
  · rfl

theorem same_unified_raw_alias_three_binder_call :
    (UnifiedProgram.checkProgram 64 128
      [⟨.univ 0,.u64⟩,⟨.univ 1,.pi false scalarAlias (.univ 0)⟩,
       ⟨.u64,applications aliasSourceFunction aliasArguments⟩] []).isSome = true := by cbv

def twoKindSignature : Term := .pi false (.univ 0) (.pi false (.univ 0)
  (.pi false (.var 1) (.pi false (.var 1) (.var 2))))
def twoKindFunction : Term := .lam false (.univ 0) (.lam false (.univ 0)
  (.lam false (.var 1) (.lam false (.var 1) (.var 0))))
def twoKindContext : Context :=
  [⟨.var 1,false⟩,⟨.var 1,false⟩,⟨.univ 0,false⟩,⟨.univ 0,false⟩]
def twoKindArguments : List Term := [.u64,.i64,.natural 7,.integer 3]
def twoKindEntries : List CallReplay.Argument :=
  [⟨false,.univ 0,.u64⟩,⟨false,.univ 0,.i64⟩,⟨false,.u64,.natural 7⟩,⟨false,.i64,.integer 3⟩]

def twoKindTelescope : InputTelescope .empty [] twoKindSignature 4 twoKindContext (.var 2) := by
  apply InputTelescope.kind (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false
    (.univ 0) = some (.type 1)))
  apply InputTelescope.kind (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    [⟨.univ 0,false⟩] false (.univ 0) = some (.type 1)))
  apply InputTelescope.small (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    [⟨.univ 0,false⟩,⟨.univ 0,false⟩] false (.var 1) = some (.type 0))) (Or.inr rfl)
  apply InputTelescope.small (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    [⟨.var 1,false⟩,⟨.univ 0,false⟩,⟨.univ 0,false⟩] false (.var 1) = some (.type 0))) (Or.inr rfl)
  exact .nil

theorem two_kind_actual_inputs : twoKindTelescope.Inputs 64 twoKindArguments := by
  refine ⟨⟨.univ 0,by cbv,rfl⟩,⟨⟨.univ 0,by cbv,rfl⟩,?_⟩⟩
  rfl

/-- Multiple fresh positive kind parameters close in one uniform actual-call
proof, followed by dependent ordinary binders of different actual types. -/
theorem two_kind_four_binder_checked_closing :
    ∃ values, RealizedInterpretation .empty twoKindContext values ∧
      Conversion.Conv .empty .i64 ((Term.var 2).subst values) := by
  apply twoKindTelescope.close_checkedCall (fuel := 64) empty_history (RealizedInterpretation.nil Term.var)
    (Checker.check_sound (by cbv : Checker.check 64 .empty [] false twoKindFunction twoKindSignature = true))
    (entries := twoKindEntries) (arguments := twoKindArguments)
  · cbv
  · exact two_kind_actual_inputs

end Jihoo.NativeKernel.Environment.InferredKindExamples
