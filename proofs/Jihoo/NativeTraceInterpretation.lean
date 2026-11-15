import Jihoo.NativeAuthenticKindArguments
import Jihoo.NativeContextModeSoundness
import Jihoo.NativeContextInterpretation

/-! Admissible closure can retain actual code checks at raw, dependent kind
annotations and their original program prefixes. Canonical checker completeness
and rerunning old checks in a larger world are unnecessary. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

structure TraceInterpretation (env : Environment) (ctx : Context) (values : Nat → Term) : Prop where
  formed : ContextFormed env ctx
  typed : Ghost.Substitution env ctx [] values
  arguments : ∀ index kind, LookupKind env ctx index kind → OriginArgument env kind (values index)

theorem Interpretation.traced (closing : Interpretation env ctx values) :
    TraceInterpretation env ctx values :=
  ⟨closing.formed,closing.typed,fun index kind lookup =>
    (closing.arguments index kind lookup).argumentAtKind.origin⟩

theorem SemanticSpine.realizes_trace
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : SemanticSpine env ctx term kind) (closing : TraceInterpretation env ctx values) :
    Realizes env kind (term.subst values) := by
  induction source with
  | @var index kind lookup =>
      simpa only [Term.subst] using (closing.arguments index kind lookup).realizes history
  | @app function erased result argument head typed ih =>
      have closedIndex : HasType env [] true (argument.subst values) .u64 := by
        simpa only [Term.subst,substArgs] using typed.ghostSubstitution history.wellFormed closing.typed
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using ih.index closedIndex

theorem Spine.realizes_trace_in_extension (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (source : Spine before ctx term kind) (closing : TraceInterpretation after ctx values) :
    Realizes after kind (term.subst values) :=
  (source.semantic.extend extension).realizes_trace history closing

/-- A one-binder closing interpretation is constructed from exactly the raw
binder check and actual application trace, including aliased kind annotations. -/
theorem TraceInterpretation.single {kind : Kind}
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (binding : Checker.binder fuel env [] erased domain = some sort)
    (checked : Checker.check fuel env [] false value domain = true)
    (normalized : Conversion.normalize? env fuel domain = some kind.term)
    (application : Checker.applicationOK fuel env false domain value = true) :
    TraceInterpretation env [⟨domain,erased⟩] (fun _ => value) := by
  have binder := Checker.binder_sound binding
  have domainScope : domain.Scoped 0 := by
    cases binder with
    | intro typed allowed => exact typed.term_scoped
  have converted : Conversion.Conv env (domain.rename Nat.succ) kind.term := by
    simpa only [closed_rename domainScope] using Conversion.normalize?_sound normalized
  have known : LookupKind env [⟨domain,erased⟩] 0 kind :=
    ⟨⟨domain.rename Nat.succ,erased⟩,rfl,converted,
      .convert (.var rfl (Or.inl rfl)) converted⟩
  refine ⟨.cons .nil binder,?_,?_⟩
  · intro index selected found
    cases index with
    | zero =>
        simp only [lookup,Option.some.injEq] at found
        subst selected
        simpa only [closed_rename domainScope,closed_subst domainScope] using
          (Checker.check_sound checked).ghost
    | succ index => simp [lookup] at found
  · intro index other found
    have lookupFound := found.choose_spec.1
    have indexZero : index = 0 := by
      cases index with
      | zero => rfl
      | succ index => simp [lookup] at lookupFound
    subst index
    have same := known.unique history.wellFormed.admissible found
    subst other
    exact (show ArgumentAtKind env kind value from
      ⟨fuel,domain,checked,normalized,application⟩).origin

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.ContextModes
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem Resolved.unrestricted_not_owned_trace
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (resolved : Resolved before ctx false domain .unrestricted)
    (closing : TraceInterpretation after ctx values) : ¬ Owned after (domain.subst values) := by
  cases resolved with
  | head normalized known =>
      obtain ⟨op,children,rfl,unowned⟩ := head_unrestricted known
      have converted := (Conversion.normalize?_sound normalized).extend extension
      have shifted := converted.substitution values history.wellFormed.closed
      intro owned
      exact (unowned.extend extension).not_owned history.wellFormed.admissible
        (by simpa only [Term.subst] using owned.congr shifted)
  | abstract normalized spine =>
      intro owned
      have represented := spine.realizes_trace_in_extension extension history closing
      exact represented.not_owned history
        (owned.congr (((Conversion.normalize?_sound normalized).extend extension).substitution
          values history.wellFormed.closed))

end Jihoo.NativeKernel.Environment.ContextModes

namespace Jihoo.NativeKernel.Environment.CallReplay
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem ResultShape.closed_nonFunction_trace
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (shape : ResultShape before ctx result) (closing : TraceInterpretation after ctx values) :
    PiSeparated after (result.subst values) := by
  cases shape with
  | @rigid op children converted head =>
      have reduced := (converted.extend extension).substitution values history.wellFormed.closed
      have witnessed : nonFunction after (result.subst values) := by
        apply FamilyIota.Extended.NonFunction.of_conversion reduced
        apply FamilyIota.Extended.NonFunction.ofHead
        simpa only [Term.subst,FamilyIota.Extended.nonFunctionHead] using head
      intro erased domain body pi
      exact witnessed.not_pi pi history.wellFormed.admissible
  | abstract converted spine =>
      have represented := (spine.realizes_trace_in_extension extension history closing).nonFunction history
      intro erased domain body pi
      exact represented erased domain body
        (.trans (.symm ((converted.extend extension).substitution values history.wellFormed.closed)) pi)

end Jihoo.NativeKernel.Environment.CallReplay

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay
open Jihoo.Quantity
variable {control : Control}
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem app_interpreted_result_trace
    (projected : projectRaw (fuel + 1) before ctx (.app function argument) = some control)
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (closing : TraceInterpretation after ctx values) :
    ∃ head supplied entries result signature,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ContextFormed before ctx ∧ SignatureTrace after ctx false signature supplied entries result ∧
      HasType after ctx false (applications head supplied) result ∧
      (entries.any (ownsArgument before) = false ∨ PiSeparated after (result.subst values)) := by
  obtain ⟨head,supplied,entries,result,signature,split,formed,typed,steps,applied,guarded⟩ :=
    app_authenticated projected
  refine ⟨head,supplied,entries,result,signature,split,formed,
    steps.signatureTrace.extend extension,applied.extend extension,?_⟩
  rcases guarded with noOwner | represented
  · exact Or.inl noOwner
  · exact Or.inr (represented.closed_nonFunction_trace extension history closing)

end Jihoo.NativeKernel.Environment.ContextQuantity
