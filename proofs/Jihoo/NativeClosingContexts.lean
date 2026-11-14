import Jihoo.NativeTraceInterpretation

/-! Binding algebra for constructing complete closing interpretations one actual
argument at a time. Canonical-domain trace obligations remain explicit: a
successful bounded normalizer is not assumed to return a normal form. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

def consValues (value : Term) (values : Nat → Term) : Nat → Term
  | 0 => value
  | index + 1 => values index

theorem shift_subst_consValues (term : Term) (value : Term) (values : Nat → Term) :
    (term.rename Nat.succ).subst (consValues value values) = term.subst values := by
  rw [Term.subst_rename]
  rfl

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.Ghost
open CodeKinds

theorem Substitution.consValues
    (closing : Ghost.Substitution env ctx [] values)
    (argument : HasType env [] true value (domain.subst values)) :
    Ghost.Substitution env (⟨domain,erased⟩ :: ctx) [] (consValues value values) := by
  intro index binding selected
  cases index with
  | zero =>
      simp only [lookup,Option.some.injEq] at selected
      subst binding
      simpa only [CodeKinds.consValues,shift_subst_consValues] using argument
  | succ index =>
      simp only [lookup] at selected
      obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [CodeKinds.consValues,shift_subst_consValues] using closing index original found

end Jihoo.NativeKernel.Environment.Ghost

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- Removing the new binder transports an actual old lookup kind. -/
theorem LookupKind.tail (closed : Conversion.Closed env)
    (found : LookupKind env (⟨domain,erased⟩ :: ctx) (index + 1) kind) :
    LookupKind env ctx index kind := by
  obtain ⟨binding,selected,converted,typed⟩ := found
  simp only [lookup] at selected
  obtain ⟨original,lookupOriginal,same⟩ := Option.map_eq_some_iff.mp selected
  subst binding
  have unshifted := converted.substitution (single (.natural 0)) closed
  have actual : Conversion.Conv env original.ty kind.term := by
    simpa only [Term.shift_subst_single,Kind.subst] using unshifted
  exact ⟨original,lookupOriginal,actual,.convert (.var lookupOriginal (Or.inl rfl)) actual⟩

theorem LookupKind.head (closed : Conversion.Closed env)
    (found : LookupKind env (⟨domain,erased⟩ :: ctx) 0 kind) :
    Conversion.Conv env domain kind.term := by
  obtain ⟨binding,selected,converted,typed⟩ := found
  simp only [lookup,Option.some.injEq] at selected
  subst binding
  simpa only [Term.shift_subst_single,Kind.subst] using
    converted.substitution (single (.natural 0)) closed

/-- This constructor separates typed closing from its actual code-kind gate.
The latter is executable origin evidence, not an external plainness flag. -/
theorem TraceInterpretation.cons
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : TraceInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (argument : HasType env [] true value (domain.subst values))
    (kindArguments : ∀ kind, Conversion.Conv env domain kind.term → OriginArgument env kind value) :
    TraceInterpretation env (⟨domain,erased⟩ :: ctx) (consValues value values) := by
  refine ⟨.cons closing.formed binding,closing.typed.consValues argument,?_⟩
  intro index kind found
  cases index with
  | zero => exact kindArguments kind (found.head history.wellFormed.closed)
  | succ index => exact closing.arguments index kind (found.tail history.wellFormed.closed)

/-- A known canonical source kind has a unique representation after conversion. -/
theorem TraceInterpretation.cons_kind {kind : Kind}
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : TraceInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (sourceKind : Conversion.Conv env domain kind.term)
    (accepted : OriginArgument env kind value) :
    TraceInterpretation env (⟨domain,erased⟩ :: ctx) (consValues value values) := by
  have transformed := sourceKind.substitution values history.wellFormed.closed
  have aligned : Conversion.Conv env (domain.subst values) kind.term := by
    simpa only [Kind.subst] using transformed
  apply closing.cons history binding ((accepted.realizes history).typed.convert aligned.symm)
  intro other converted
  have same : kind = other := Kind.conv_injective history.wellFormed.admissible
    (.trans sourceKind.symm converted)
  cases same
  exact accepted

theorem TraceInterpretation.cons_nonkind
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (closing : TraceInterpretation env ctx values)
    (binding : Binder env ctx erased domain sort)
    (argument : HasType env [] true value (domain.subst values))
    (nonkind : ∀ kind : Kind, ¬ Conversion.Conv env domain kind.term) :
    TraceInterpretation env (⟨domain,erased⟩ :: ctx) (consValues value values) :=
  closing.cons history binding argument (fun kind converted => False.elim (nonkind kind converted))

end Jihoo.NativeKernel.Environment.CodeKinds
