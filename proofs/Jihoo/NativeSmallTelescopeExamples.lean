import Jihoo.NativeSmallTelescopeClosure
import Jihoo.NativeClosingTelescopeExamples

namespace Jihoo.NativeKernel.Environment.SmallTelescopeExamples
open CodeKinds ClosingTelescopeExamples ContextReplayExamples

/-- The already admitted computed family interprets the one outer kind binder. -/
def familyValues : Nat → Term := consValues computedScalarFamily Term.var

theorem computed_family_closing :
    RealizedInterpretation .empty [⟨.pi false .u64 (.univ 0),false⟩] familyValues := by
  apply (RealizedInterpretation.nil Term.var).cons empty_history
    (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false
      (.pi false .u64 (.univ 0)) = some (.type 1)))
    (by cbv; exact (Checker.check_sound (by cbv : Checker.check 64 .empty [] false computedScalarFamily
      (.pi false .u64 (.univ 0)) = true)).ghost)
  intro kind converted
  have same := Kind.conv_injective empty_history.wellFormed.admissible
    (first := .index false (.type 0)) converted
  cases same
  exact (show Admitted .empty (.index false (.type 0)) computedScalarFamily from
    ⟨64,by cbv,by cbv⟩).realizes empty_history

def suffixSignature : Term := .pi true .u64
  (.pi false (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1)))
def suffixFunction : Term := .lam true .u64 (.lam false (.app (.var 1) (.var 0)) (.var 0))

theorem arbitrary_family_small_telescope :
    SmallTelescope .empty [⟨.pi false .u64 (.univ 0),false⟩] suffixSignature 2
      indexedIdentityContext (.app (.var 2) (.var 1)) := by
  apply SmallTelescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    [⟨.pi false .u64 (.univ 0),false⟩] true .u64 = some (.type 0))) (Or.inr rfl)
  apply SmallTelescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    indexedFinalContext false (.app (.var 1) (.var 0)) = some (.type 0))) (Or.inr rfl)
  exact .nil

theorem actual_unplain_index_small_closing :
    ∃ values, RealizedInterpretation .empty indexedIdentityContext values ∧
      Conversion.Conv .empty .u64 ((Term.app (.var 2) (.var 1)).subst values) := by
  apply arbitrary_family_small_telescope.close_checkedCall (fuel := 64) empty_history computed_family_closing
    (Checker.check_sound (by cbv : Checker.check 64 .empty [⟨.pi false .u64 (.univ 0),false⟩]
      false suffixFunction suffixSignature = true))
    (entries := [⟨true,.u64,.strict owner (.natural 0)⟩,⟨false,.u64,.natural 7⟩])
    (arguments := [.strict owner (.natural 0),.natural 7])
  · cbv
  · rfl

theorem actual_above_word_small_closing :
    ∃ values, RealizedInterpretation .empty indexedIdentityContext values ∧
      Conversion.Conv .empty .u64 ((Term.app (.var 2) (.var 1)).subst values) := by
  apply arbitrary_family_small_telescope.close_checkedCall (fuel := 64) empty_history computed_family_closing
    (Checker.check_sound (by cbv : Checker.check 64 .empty [⟨.pi false .u64 (.univ 0),false⟩]
      false suffixFunction suffixSignature = true))
    (entries := [⟨true,.u64,.uadd (.natural (2^64-1)) (.natural (2^64-1))⟩,⟨false,.u64,.natural 7⟩])
    (arguments := [.uadd (.natural (2^64-1)) (.natural (2^64-1)),.natural 7])
  · cbv
  · rfl

def ownerAliasEnvironment : Environment := ⟨#[⟨.univ 0,owner⟩],#[]⟩
def ownerAlias : Term := .node (.global 0) []
def ownerSignature : Term := .pi false ownerAlias ownerAlias
def ownerFunction : Term := .lam false ownerAlias (.var 0)

theorem owner_alias_history :
    UnifiedProgram.UnifiedProgramChecked [⟨.univ 0,owner⟩] [] ownerAliasEnvironment :=
  UnifiedProgram.checkProgram_sound (by cbv : UnifiedProgram.checkProgram 64 128
    [⟨.univ 0,owner⟩] [] = some ownerAliasEnvironment)

theorem owner_alias_small_telescope : SmallTelescope ownerAliasEnvironment [] ownerSignature 1
    [⟨ownerAlias,false⟩] ownerAlias := by
  apply SmallTelescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 ownerAliasEnvironment
    [] false ownerAlias = some (.type 0))) (Or.inr rfl)
  exact .nil

/-- The raw source annotation remains an alias to an owned Buffer. Domain
classification follows from its authentic Type0 formation, without a flag. -/
theorem actual_owned_alias_small_closing :
    ∃ values, RealizedInterpretation ownerAliasEnvironment [⟨ownerAlias,false⟩] values ∧
      Conversion.Conv ownerAliasEnvironment owner (ownerAlias.subst values) := by
  apply owner_alias_small_telescope.close_checkedCall (fuel := 64) owner_alias_history (RealizedInterpretation.nil Term.var)
    (Checker.check_sound (by cbv : Checker.check 64 ownerAliasEnvironment [] false ownerFunction ownerSignature = true))
    (entries := [⟨false,owner,allocated⟩]) (arguments := [allocated])
  · cbv
  · rfl

end Jihoo.NativeKernel.Environment.SmallTelescopeExamples
