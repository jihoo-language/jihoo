import Jihoo.NativeKindPrefixInterpretation
import Jihoo.NativeCallReplayExtension

/-! Representation of actual code arguments checked at their raw dependent
annotation. The canonical kind comes from the same bounded domain-normalizer
trace. No second canonical-type checker run or executable completeness theorem
is needed. Successful origin traces survive later checked prefixes. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
open Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- All fields are successful executable checks, rather than plainness flags. -/
def ArgumentAtKind (env : Environment) (kind : Kind) (value : Term) : Prop :=
  ∃ fuel domain,
    Checker.check fuel env [] false value domain = true ∧
    Conversion.normalize? env fuel domain = some kind.term ∧
    Checker.applicationOK fuel env false domain value = true

theorem normalizedKindArgument_plain {kind : Kind}
    (normalized : Conversion.normalize? env fuel domain = some kind.term)
    (accepted : Checker.applicationOK fuel env false domain value = true) :
    plain env (Conversion.normalize env fuel value) = true := by
  have gate : globalFree kind.term = true ∧
      plain env (Conversion.normalize env fuel value) = true := by
    simpa only [Checker.applicationOK,normalized,Bool.false_or,Kind.kindOf,
      Bool.not_true,Bool.false_or,Kind.firstOrder,Bool.true_and,Bool.and_eq_true] using accepted
  exact gate.2

theorem ArgumentAtKind.typed (accepted : ArgumentAtKind env kind value) :
    HasType env [] false value kind.term := by
  obtain ⟨fuel,domain,checked,normalized,application⟩ := accepted
  exact .convert (Checker.check_sound checked) (Conversion.normalize?_sound normalized)

theorem Admitted.argumentAtKind (accepted : Admitted env kind value) : ArgumentAtKind env kind value := by
  obtain ⟨fuel,checked,application⟩ := accepted
  cases normalized : Conversion.normalize? env fuel kind.term with
  | none => simp [Checker.applicationOK,normalized] at application
  | some normal =>
      have same := kind.normalize?_fixed normalized
      subst normal
      exact ⟨fuel,kind.term,checked,normalized,application⟩

theorem Kind.conv_injective {first second : Kind} (admissible : EnvironmentDelta.Admissible env)
    (converted : Conversion.Conv env first.term second.term) : first = second := by
  induction first generalizing second with
  | type level =>
      cases second with
      | type other =>
          have heads := (converted.full_rigid_node_injective rfl rfl admissible).1
          cases heads
          rfl
      | index erased result =>
          exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) converted admissible)
  | index erased result ih =>
      cases second with
      | type level =>
          exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) converted admissible)
      | index other rest =>
          obtain ⟨same,_,bodies⟩ := converted.pi_injective admissible
          cases same
          exact congrArg (Kind.index erased) (ih bodies)

theorem LookupKind.unique (admissible : EnvironmentDelta.Admissible env)
    (first : LookupKind env ctx index kind) (second : LookupKind env ctx index other) : kind = other := by
  obtain ⟨binding,selected,converted,typed⟩ := first
  obtain ⟨otherBinding,otherSelected,otherConverted,otherTyped⟩ := second
  have same : binding = otherBinding := Option.some.inj (selected.symm.trans otherSelected)
  subst otherBinding
  exact Kind.conv_injective admissible (.trans (.symm converted) otherConverted)

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.EnvironmentDelta

theorem Forward.extend (extension : Environment.Extends before after)
    (step : Forward before input output) : Forward after input output := by
  induction step using Forward.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Forward after) xs ys) with
  | refl => exact .refl
  | delta found => exact .delta (extension.globals _ _ found)
  | acu step => exact .acu step
  | trans _ _ first second => exact .trans first second
  | node op children ih => exact .node op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.EnvironmentDelta

namespace Jihoo.NativeKernel.Environment.CodeKinds
open Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

private theorem normalizedValueForward (env : Environment) (fuel : Nat) (value : Term) :
    EnvironmentDelta.Forward env value (Conversion.normalize env fuel value) := by
  change EnvironmentDelta.Forward env value ((Conversion.normalize? env fuel value).getD value)
  cases normalized : Conversion.normalize? env fuel value with
  | none => exact .refl
  | some normal => exact Conversion.normalize?_forward normalized

/-- Actual older-prefix execution is retained; the bounded checker need not
be rerun in the larger world. -/
theorem ArgumentAtKind.realizes_in_extension
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (accepted : ArgumentAtKind before kind value) : Realizes after kind value := by
  obtain ⟨fuel,domain,checked,normalized,application⟩ := accepted
  have typed : HasType after [] true value kind.term :=
    (HasType.convert (Checker.check_sound checked) (Conversion.normalize?_sound normalized)).ghost.extend extension
  have forward := (normalizedValueForward before fuel value).extend extension
  have transformed := typed.ghostForward history forward
  have isPlain := plain.extend extension (normalizedKindArgument_plain normalized application)
  exact ⟨typed,_,forward,PlainIndices.of_familyPlain transformed.term_wellFormed
    (plain_familyPlain isPlain) (Bool.and_eq_true_iff.mp isPlain).1⟩

theorem ArgumentAtKind.realizes
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (accepted : ArgumentAtKind env kind value) : Realizes env kind value :=
  accepted.realizes_in_extension (Extends.refl _) history

/-- Authentic execution evidence, with its actual earlier environment. -/
def OriginArgument (env : Environment) (kind : Kind) (value : Term) : Prop :=
  ∃ origin, Extends origin env ∧ ArgumentAtKind origin kind value

theorem ArgumentAtKind.origin (accepted : ArgumentAtKind env kind value) : OriginArgument env kind value :=
  ⟨env,Extends.refl _,accepted⟩

theorem OriginArgument.extend (extension : Extends before after)
    (accepted : OriginArgument before kind value) : OriginArgument after kind value := by
  obtain ⟨origin,prior,trace⟩ := accepted
  exact ⟨origin,prior.trans extension,trace⟩

theorem OriginArgument.realizes
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (accepted : OriginArgument env kind value) : Realizes env kind value := by
  obtain ⟨origin,extension,trace⟩ := accepted
  exact trace.realizes_in_extension extension history

end Jihoo.NativeKernel.Environment.CodeKinds
