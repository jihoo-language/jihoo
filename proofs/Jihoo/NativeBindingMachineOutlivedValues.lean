import Jihoo.NativeBindingMachineCanonicalVariables
import Jihoo.NativeLoanPolicyTransport

/-! The full source Outlived policy excludes runtime references and captured
closures from the current binding machine's value representations. This is
a property of the value interpretation; its all-control preservation remains
separate. Canonical variable execution constructs that interpretation from
the input source judgment instead of assuming a returned-value certificate. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private theorem outlived_nonFunction_head
    (allowed : Lending.outlivedHead env term = true) : RawLend.nonFunctionHead term = true := by
  cases term with
  | var => simp [Lending.outlivedHead] at allowed
  | node op arguments =>
      cases op <;> simp_all [Lending.outlivedHead,RawLend.nonFunctionHead,RawLend.nonFunctionOp]

private theorem outlived_excludes_head
    (admissible : EnvironmentDelta.Admissible env) (allowed : Outlived env type)
    (rigid : RawLend.rigid op = true)
    (excluded : ∀ arguments, Lending.outlivedHead env (.node op arguments) = false)
    (converted : Conversion.Conv env (.node op arguments) type) : False := by
  obtain ⟨normal,normalConverted,head⟩ := allowed
  have related := converted.trans normalConverted
  cases normal with
  | var => simp [Lending.outlivedHead] at head
  | node other children =>
      have otherRigid := RawLend.nonFunctionOp_rigid (outlived_nonFunction_head head)
      have same := (related.full_rigid_node_injective rigid otherRigid admissible).1
      subst other
      rw [excluded] at head
      cases head

theorem Outlived.reference_excluded (admissible : EnvironmentDelta.Admissible env)
    (allowed : Outlived env type) (converted : Conversion.Conv env (.ref domain) type) : False :=
  outlived_excludes_head admissible allowed rfl (fun _ => rfl) converted

theorem Outlived.function_excluded (admissible : EnvironmentDelta.Admissible env)
    (allowed : Outlived env type) (converted : Conversion.Conv env (.pi erased domain body) type) : False :=
  outlived_excludes_head admissible allowed rfl (fun _ => rfl) converted

theorem Outlived.sort_excluded (admissible : EnvironmentDelta.Admissible env)
    (allowed : Outlived env type) (sort : SortTag)
    (converted : Conversion.Conv env sort.term type) : False := by
  cases sort
  all_goals exact outlived_excludes_head admissible allowed rfl (fun _ => rfl) converted

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- The original complete Lend judgment supplies Outlived for the actual
reader-result annotation after canonical value closing. No policy certificate
for the returned value or continuation annotation is assumed. -/
theorem LoanClosingTyped.reader_domain_outlived
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode code meanings type)
    (shape : code.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) :
    LoanTyping.Outlived env (first.subst meanings) := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨ownerType,valueType,ownerTyped,readTyped,firstConverted,againConverted⟩ :=
    source.explicitLendValueDomains history.wellFormed
  obtain ⟨otherOwner,otherValue,sort,otherOwnerTyped,owned,binder,domainConverted,otherReadTyped,outlived⟩ :=
    source.explicitLendReaderInputs history.wellFormed
  have sameType := readTyped.unique history.wellFormed otherReadTyped
  have allowed := LoanTyping.Outlived.of_conversion (firstConverted.trans sameType) outlived
  exact allowed.substitution history.wellFormed.closed meanings

/-- Only scalar, array and owned Buffer values can realize an Outlived type in the
current machine. In particular no returned closure can hide a reader token. -/
theorem ValueKind.outlived_shape (admissible : EnvironmentDelta.Admissible env)
    (kind : ValueKind env value type) (allowed : LoanTyping.Outlived env type) :
    (∃ number, value = .natural number) ∨ (∃ number, value = .integer number) ∨
      (∃ object, value = .owner object) ∨ (∃ elements, value = .array elements) := by
  cases value with
  | natural number => exact Or.inl ⟨number,rfl⟩
  | integer number => exact Or.inr (Or.inl ⟨number,rfl⟩)
  | owner object => exact Or.inr (Or.inr (Or.inl ⟨object,rfl⟩))
  | array elements => exact Or.inr (Or.inr (Or.inr ⟨elements,rfl⟩))
  | reference =>
      obtain ⟨domain,converted⟩ := kind
      exact False.elim (allowed.reference_excluded admissible converted)
  | closure =>
      obtain ⟨domain,body,converted⟩ := kind
      exact False.elim (allowed.function_excluded admissible converted)
  | typeCode =>
      obtain ⟨sort,converted⟩ := kind
      exact False.elim (allowed.sort_excluded admissible sort converted)

/-- The full original canonical source variable judgment, value context and
Outlived policy construct a real reference/closure-free returned value. The
actual slot, selected value, successful step and result kind are outputs. -/
theorem reachable_canonical_outlived_variable (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (context : ValueContext env source meanings) (aligned : CodeAligned source)
    (allowed : LoanTyping.Outlived env type)
    (shape : actual.term = .var index) :
    ∃ value, actual.values[index]? = some (some value) ∧ ValueKind env value type ∧
      ((∃ number, value = .natural number) ∨ (∃ number, value = .integer number) ∨
        (∃ object, value = .owner object) ∨ (∃ elements, value = .array elements)) ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.returned value,(run fuel (initial term)).state.stack⟩,none) := by
  obtain ⟨value,stored,kind,next⟩ := reachable_canonical_variable_kind
    term fuel history evaluating view typed context aligned shape
  exact ⟨value,stored,kind,kind.outlived_shape history.wellFormed.admissible allowed,next⟩

end Jihoo.NativeKernel.Environment.BindingMachine
