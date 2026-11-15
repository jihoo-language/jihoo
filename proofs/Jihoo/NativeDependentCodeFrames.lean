import Jihoo.NativeDependentFamilyContexts
import Jihoo.NativeProjectedContextCoherence

/-! Lookup frames isolate the actual universe, family and observation slots
from an arbitrary prefix of native binders. Prefix annotations may contain
effects; they need not be replaced by convertible pure annotations. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)
variable {parameters familyCount observationCount : Nat}
variable {levels : Fin parameters → Fin 32} {signatures : Fin familyCount → Signature parameters}
variable {observed : Fin observationCount → Mono parameters}

structure LookupFrame (levels : Fin parameters → Fin 32)
    (signatures : Fin familyCount → Signature parameters) (observed : Fin observationCount → Mono parameters)
    (offset : Nat) (ctx : Context) : Prop where
  parameters : ParametersIn levels (offset+observationCount+familyCount) ctx
  families : ∀ index,lookup ctx (offset+observationCount+index.val) =
    some ⟨(signatures index).term (offset+observationCount+familyCount),false⟩
  observations : ∀ index,lookup ctx (offset+index.val) =
    some ⟨(observed index).syntax (offset+observationCount+familyCount),false⟩

/-- No formation or conversion of the newly added raw annotation is needed
to retain the original classified slots beneath it. -/
theorem LookupFrame.extend (frame : LookupFrame levels signatures observed offset ctx) (binding : Binding) :
    LookupFrame levels signatures observed (offset+1) (binding :: ctx) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.parameters.extend binding
  · intro index
    have same : offset+1+observationCount+index.val = (offset+observationCount+index.val)+1 := by omega
    rw [same]
    change (lookup ctx (offset+observationCount+index.val)).map _ = _
    rw [frame.families index]
    simp only [Option.map,Signature.term_shift,Nat.add_assoc,Nat.add_comm]
  · intro index
    have same : offset+1+index.val = (offset+index.val)+1 := by omega
    rw [same]
    change (lookup ctx (offset+index.val)).map _ = _
    rw [frame.observations index]
    simp only [Option.map,MultiUniverse.Mono.syntax_shift,Nat.add_assoc,Nat.add_comm]

theorem LookupFrame.of_context (familyList : List (Signature parameters)) (observations : List (Mono parameters))
    (Γ : List (TypeCode parameters familyList.length observations.length)) :
    LookupFrame levels familyList.get observations.get Γ.length (context levels familyList observations Γ) := by
  refine ⟨context_parameters familyList observations Γ,?_,?_⟩
  · intro index
    exact (Slot.ofFin familyList index).context_family_lookup observations Γ
  · intro index
    exact (Slot.ofFin observations index).context_observation_lookup familyList Γ

theorem TypeCode.formed_in (A : TypeCode parameters familyCount observationCount)
    (frame : LookupFrame levels signatures observed offset ctx) (valid : A.Valid signatures observed) :
    HasType env ctx true (A.syntax offset) (.univ (A.level levels signatures)) := by
  induction A generalizing offset ctx with
  | parameter index =>
    simpa only [TypeCode.syntax,TypeCode.instantiate,TypeCode.level,Nat.add_assoc] using
      (HasType.var (frame.parameters index) (Or.inl rfl) :
        HasType env ctx true (.var (offset+observationCount+familyCount+index.val)) (.univ (levels index).val))
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [TypeCode.syntax_arrow]
    exact .pi (s := .type (A.level levels signatures)) (r := .type (B.level levels signatures))
      (.intro (ha frame valid.1) (Or.inl (by intro h; cases h)))
      (hb (frame.extend ⟨A.syntax offset,false⟩) valid.2)
  | fiber family observation =>
    have functionTyped : HasType env ctx true (.var (offset+observationCount+family.val))
        ((signatures family).term (offset+observationCount+familyCount)) :=
      .var (frame.families family) (Or.inl rfl)
    have argumentTyped : HasType env ctx true (.var (offset+observation.val))
        ((observed observation).syntax (offset+observationCount+familyCount)) :=
      .var (frame.observations observation) (Or.inl rfl)
    rw [valid] at argumentTyped
    have applied := HasType.app functionTyped argumentTyped (Or.inl rfl)
    simpa only [TypeCode.syntax,TypeCode.instantiate,TypeCode.level,Signature.term,
      Term.univ,Term.subst,substArgs,Nat.add_assoc] using applied

/-- Validity is reconstructed from the actual native derivation, including
the equality between an observation's carrier and its family's true input. -/
theorem TypeCode.valid_of_typed_in (A : TypeCode parameters familyCount observationCount)
    (wf : UnifiedProgram.EnvWellFormed env) (frame : LookupFrame levels signatures observed offset ctx)
    (typed : HasType env ctx mode (A.syntax offset) type) : A.Valid signatures observed := by
  induction A generalizing offset ctx mode type with
  | parameter => trivial
  | natural => trivial
  | arrow A B ha hb =>
    rw [TypeCode.syntax_arrow] at typed
    obtain ⟨domainSort,resultSort,binder,bodyTyped,converted⟩ := typed.piView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    exact ⟨ha frame domainTyped,hb (frame.extend ⟨A.syntax offset,false⟩) bodyTyped⟩
  | fiber family observation =>
    change HasType env ctx mode
      (.app (.var (offset+(observationCount+family.val))) (.var (offset+observation.val))) type at typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨functionBinding,functionFound,functionConverted⟩ := functionTyped.principalView
    have selected := frame.families family
    rw [Nat.add_assoc] at selected
    rw [selected] at functionFound
    cases functionFound
    have components := functionConverted.pi_injective wf.admissible
    obtain ⟨argumentBinding,argumentFound,argumentConverted⟩ := argumentTyped.principalView
    rw [frame.observations observation] at argumentFound
    cases argumentFound
    exact MultiUniverse.Mono.syntax_injective wf (.trans argumentConverted components.2.1.symm)

theorem TypeCode.classify_in (A : TypeCode parameters familyCount observationCount)
    (wf : UnifiedProgram.EnvWellFormed env) (frame : LookupFrame levels signatures observed offset ctx)
    (typed : HasType env ctx mode (A.syntax offset) type) :
    A.Valid signatures observed ∧ Conv env (.univ (A.level levels signatures)) type := by
  have valid := A.valid_of_typed_in wf frame typed
  exact ⟨valid,(A.formed_in frame valid).unique wf typed⟩

/-- Every pure code's source syntax is fixed by the concrete value projection. -/
theorem TypeCode.project_syntax (A : TypeCode parameters familyCount observationCount) :
    ValueErasure.project env (A.syntax offset) = A.syntax offset := by
  induction A generalizing offset with
  | parameter index => exact ValueErasure.project_variable _ _
  | natural => exact ValueErasure.project_ordinary_node (by rfl) []
  | arrow A B ha hb => rw [TypeCode.syntax_arrow,ValueErasure.project_pi,ha,hb]
  | fiber family observation =>
    change ValueErasure.project env (.app (.var _) (.var _)) = _
    rw [ValueErasure.project_application,ValueErasure.project_variable,ValueErasure.project_variable]
    rfl

theorem TypeCode.projected_injective (wf : UnifiedProgram.EnvWellFormed env)
    {A B : TypeCode parameters familyCount observationCount}
    (related : ValueErasure.Coherent env (A.syntax offset) (B.syntax offset)) : A = B := by
  unfold ValueErasure.Coherent at related
  rw [TypeCode.project_syntax,TypeCode.project_syntax] at related
  exact TypeCode.syntax_injective wf related

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
