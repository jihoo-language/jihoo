import Jihoo.NativeClosingResourceSemantics
import Jihoo.NativeAuthenticKindExamples
import Jihoo.NativeContextReplayExamples

namespace Jihoo.NativeKernel.Environment.ClosingTelescopeExamples
open CodeKinds ContextReplayExamples

def genericSignature : Term := .pi false (.univ 0) (.pi false (.var 0) (.var 1))
def genericFinalContext : Context := [⟨.var 0,false⟩,⟨.univ 0,false⟩]
def genericEntries : List CallReplay.Argument := [⟨false,.univ 0,.u64⟩,⟨false,.u64,.natural 7⟩]

theorem empty_history : UnifiedProgram.UnifiedProgramChecked [] [] .empty :=
  UnifiedProgram.checkProgram_sound (by cbv : UnifiedProgram.checkProgram 64 128 [] [] = some .empty)

theorem generic_telescope :
    Telescope .empty [] genericSignature 2 genericFinalContext (.var 1) := by
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 .empty [] false (.univ 0) = some (.type 1)))
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 .empty [⟨.univ 0,false⟩] false (.var 0) = some (.type 0)))
  exact .nil

theorem generic_actual_trace :
    CanonicalSteps .empty genericSignature [.u64,.natural 7] genericEntries .u64 := by
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.of_kind (kind := .type 0) (value := .u64) empty_history rfl (by cbv))
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.u64 empty_history.wellFormed.admissible)
  cbv
  exact .nil

/-- Both dependent binders receive their actual closed values. -/
theorem genuine_generic_two_binder_closing :
    ∃ values, RealizedInterpretation .empty genericFinalContext values ∧
      Conversion.Conv .empty .u64 ((Term.var 1).subst values) := by
  apply generic_telescope.close empty_history (RealizedInterpretation.nil Term.var) generic_actual_trace
  · simpa only [Term.subst_id] using FamilyIota.Extended.Conv.refl genericSignature
  · rfl

theorem genuine_replay_matches_checked_entries :
    CallReplay.Steps .empty [] false genericSignature [.u64,.natural 7] genericEntries .u64 :=
  generic_actual_trace.replayed

def indexedSignature : Term := .pi false (.pi false .u64 (.univ 0))
  (.pi true .u64 (.app (.var 1) (.var 0)))
def indexedFinalContext : Context := [⟨.u64,true⟩,⟨.pi false .u64 (.univ 0),false⟩]
def indexedEntries : List CallReplay.Argument :=
  [⟨false,.pi false .u64 (.univ 0),KindRealizationExamples.neutralFamily⟩,
    ⟨true,.u64,.strict owner (.natural 0)⟩]

theorem indexed_telescope :
    Telescope .empty [] indexedSignature 2 indexedFinalContext (.app (.var 1) (.var 0)) := by
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 .empty [] false (.pi false .u64 (.univ 0)) = some (.type 1)))
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 .empty [⟨.pi false .u64 (.univ 0),false⟩] true .u64 = some (.type 0)))
  exact .nil

theorem indexed_actual_trace :
    CanonicalSteps .empty indexedSignature
      [KindRealizationExamples.neutralFamily,.strict owner (.natural 0)] indexedEntries
      (.app KindRealizationExamples.neutralFamily (.strict owner (.natural 0))) := by
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.of_kind (kind := .index false (.type 0)) (value := KindRealizationExamples.neutralFamily) empty_history rfl (by cbv))
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.u64 empty_history.wellFormed.admissible)
  cbv
  exact .nil

/-- The arbitrary typed index can have raw unplain syntax; ghost checking is
retained for the erased index, with the real code application gate. -/
theorem genuine_erased_index_two_binder_closing :
    ∃ values, RealizedInterpretation .empty indexedFinalContext values ∧
      Conversion.Conv .empty (.app KindRealizationExamples.neutralFamily (.strict owner (.natural 0)))
        ((Term.app (.var 1) (.var 0)).subst values) := by
  apply indexed_telescope.close empty_history (RealizedInterpretation.nil Term.var) indexed_actual_trace
  · simpa only [Term.subst_id] using FamilyIota.Extended.Conv.refl indexedSignature
  · rfl

/-- Complete two-binder semantic closure for every genuinely ghost-typed
index. This includes above-word addition trees and raw unplain memory syntax. -/
theorem all_typed_indices_closing (typed : HasType .empty [] true index .u64) :
    RealizedInterpretation .empty indexedFinalContext
      (consValues index (consValues KindRealizationExamples.neutralFamily Term.var)) := by
  have familyClosing : RealizedInterpretation .empty
      [⟨(.pi false .u64 (.univ 0)),false⟩]
      (consValues KindRealizationExamples.neutralFamily Term.var) := by
    apply (RealizedInterpretation.nil Term.var).cons empty_history
      (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false
        (.pi false .u64 (.univ 0)) = some (.type 1)))
      (by simpa only [Term.subst_id,KindRealizationExamples.familyKind,Kind.term] using (Checker.check_sound KindRealizationExamples.neutral_family_checked).ghost)
    intro kind converted
    have same := Kind.conv_injective empty_history.wellFormed.admissible
      (first := .index false (.type 0)) converted
    cases same
    exact KindRealizationExamples.neutral_family_admitted.realizes empty_history
  apply familyClosing.cons empty_history
    (Checker.binder_sound (by cbv : Checker.binder 64 .empty
      [⟨(.pi false .u64 (.univ 0)),false⟩] true .u64 = some (.type 0)))
    (by simpa only [Term.subst,substArgs] using typed)
  intro kind converted
  exact False.elim (by
    cases kind with
    | type level =>
        exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
          (by intro same; cases same) converted empty_history.wellFormed.admissible
    | index erased rest =>
        exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
          (by intro same; cases same) converted empty_history.wellFormed.admissible)

open AuthenticKindExamples

def aliasSignature : Term := .pi false aliasTerm
  (.pi true .u64 (.app (.var 1) (.var 0)))
def aliasFinalContext : Context := [⟨.u64,true⟩,⟨aliasTerm,false⟩]

theorem alias_telescope :
    Telescope familyAlias [] aliasSignature 2 aliasFinalContext (.app (.var 1) (.var 0)) := by
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 familyAlias [] false aliasTerm = some (.type 1)))
  apply Telescope.cons (Checker.binder_sound (by cbv :
    Checker.binder 64 familyAlias [⟨aliasTerm,false⟩] true .u64 = some (.type 0)))
  exact .nil

theorem alias_actual_trace :
    CanonicalSteps familyAlias aliasSignature
      [KindRealizationExamples.neutralFamily,.strict owner (.natural 0)] indexedEntries
      (.app KindRealizationExamples.neutralFamily (.strict owner (.natural 0))) := by
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.of_kind (kind := .index false (.type 0))
      (value := KindRealizationExamples.neutralFamily) authentic_alias_history rfl (by cbv))
  apply CanonicalSteps.cons (fuel := 64) (by cbv) (by cbv) (by cbv) (by cbv)
    (DomainCanonical.u64 authentic_alias_history.wellFormed.admissible)
  cbv
  exact .nil

/-- Two binders close from a real checked alias world; the source context keeps
its raw alias while the actual replay checks normalized domains. -/
theorem genuine_alias_two_binder_closing :
    ∃ values, RealizedInterpretation familyAlias aliasFinalContext values ∧
      Conversion.Conv familyAlias (.app KindRealizationExamples.neutralFamily (.strict owner (.natural 0)))
        ((Term.app (.var 1) (.var 0)).subst values) := by
  apply alias_telescope.close authentic_alias_history (RealizedInterpretation.nil Term.var) alias_actual_trace
  · simpa only [Term.subst_id] using FamilyIota.Extended.Conv.refl aliasSignature
  · rfl

def indexedIdentitySignature : Term := .pi false (.pi false .u64 (.univ 0))
  (.pi true .u64 (.pi false (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1))))
def indexedIdentity : Term := .lam false (.pi false .u64 (.univ 0))
  (.lam true .u64 (.lam false (.app (.var 1) (.var 0)) (.var 0)))
def indexedIdentityContext : Context := ⟨.app (.var 1) (.var 0),false⟩ :: indexedFinalContext
def computedScalarFamily : Term := .app (.lam false .u64 (.lam false .u64 .u64)) (.natural 0)
def identityArguments : List Term := [computedScalarFamily,.strict owner (.natural 0),.natural 7]
def identityEntries : List CallReplay.Argument :=
  [⟨false,.pi false .u64 (.univ 0),computedScalarFamily⟩,
    ⟨true,.u64,.strict owner (.natural 0)⟩,⟨false,.u64,.natural 7⟩]

theorem indexed_identity_telescope : Telescope .empty [] indexedIdentitySignature 3
    indexedIdentityContext (.app (.var 2) (.var 1)) := by
  apply Telescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false
    (.pi false .u64 (.univ 0)) = some (.type 1)))
  apply Telescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 .empty
    [⟨.pi false .u64 (.univ 0),false⟩] true .u64 = some (.type 0)))
  apply Telescope.cons (Checker.binder_sound (by cbv : Checker.binder 64 .empty indexedFinalContext
    false (.app (.var 1) (.var 0)) = some (.type 0)))
  exact .nil

theorem indexed_identity_checked : Checker.check 64 .empty [] false indexedIdentity indexedIdentitySignature = true := by cbv

theorem indexed_identity_actual_checked_call :
    CallReplay.checked 64 .empty [] false indexedIdentity identityArguments = some (identityEntries,.u64) := by cbv

theorem indexed_identity_entries_classified : EntriesClassified .empty identityEntries := by
  apply EntriesClassified.cons (Or.inl ⟨.index false (.type 0),rfl⟩)
  apply EntriesClassified.cons (DomainClassified.u64 empty_history.wellFormed.admissible)
  apply EntriesClassified.cons (DomainClassified.u64 empty_history.wellFormed.admissible)
  exact .nil

/-- A real closed, typed function and the actual checked call now construct the
whole three-binder closure. No final closing interpretation is an input. -/
theorem actual_checked_three_binder_closing :
    ∃ values, RealizedInterpretation .empty indexedIdentityContext values ∧
      Conversion.Conv .empty .u64 ((Term.app (.var 2) (.var 1)).subst values) := by
  apply indexed_identity_telescope.close_checkedCall empty_history (RealizedInterpretation.nil Term.var)
    (Checker.check_sound indexed_identity_checked)
  · simpa only [Term.subst_id] using indexed_identity_actual_checked_call
  · exact indexed_identity_entries_classified
  · rfl

/-- The exact source application is admitted by the same unified program gate. -/
theorem same_unified_three_binder_computed_family :
    (UnifiedProgram.checkProgram 64 128
      [⟨.u64,applications indexedIdentity identityArguments⟩] []).isSome = true := by cbv

end Jihoo.NativeKernel.Environment.ClosingTelescopeExamples
