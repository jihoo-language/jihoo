import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeUnifiedProgram
import Jihoo.NativeLoanTypeUniqueness
import Jihoo.NativeLoanDataMotiveCongruence

/-! Family-iota metadata derived from the same independently checked program
history. Scoped signatures alone do not establish unchanged parameters. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
open UnifiedProgram

/-- Leading parameters are literal erased U64 fields and their normalized
constructor-result indices convert to the original parameter variables. -/
def Parameters (env : Environment) (params : Nat) (signature : Signature) : Prop :=
  params ≤ signature.fields.length ∧ ∀ j < params,
    ∃ field index,signature.fields[j]? = some field ∧ field.erased = true ∧
      field.recursive = none ∧ field.domain = .u64 ∧ signature.result[j]? = some index ∧
      Conversion.Conv env index (.var (signature.fields.length - 1 - j))

private theorem variable_index (checked : Families.IndexChecked env self ctx (.var x) normal) :
    Conversion.Conv env normal (.var x) := by
  obtain ⟨_,expanded,expansion,_,converted,_⟩ := checked
  cases expansion with
  | var => exact .old converted.symm

theorem telescope_parameters (checked : Families.TelescopeChecked env self declaration fields source signature) :
    Parameters env declaration.params signature := by
  induction checked with
  | field formed rest ih => exact ih
  | result arity length checked parameters =>
    constructor
    · dsimp only
      by_cases zero : declaration.params = 0
      · simp only [zero,Nat.zero_le]
      · obtain ⟨field,found,_,_,_,_⟩ := parameters (declaration.params - 1) (by omega)
        have inside := (List.getElem?_eq_some_iff.mp found).1
        omega
    · intro j inside
      obtain ⟨field,found,erased,recursive,domain,index⟩ := parameters j inside
      obtain ⟨normalIndex,normalFound,typed⟩ := checked.left index
      exact ⟨field,normalIndex,found,erased,recursive,domain,normalFound,variable_index typed⟩

theorem telescope_result_arity (checked : Families.TelescopeChecked env self declaration fields source signature) :
    signature.result.length = declaration.arity := by
  induction checked with
  | field formed rest ih => exact ih
  | result _ length indices _ => exact indices.length.symm.trans length

theorem Parameters.extend (parameters : Parameters before params signature) (extension : Extends before after) :
    Parameters after params signature := by
  refine ⟨parameters.1,?_⟩
  intro j inside
  obtain ⟨field,index,found,erased,recursive,domain,indexFound,converted⟩ := parameters.2 j inside
  exact ⟨field,index,found,erased,recursive,domain,indexFound,converted.extend extension⟩

/-- Authentic lookup API: there is no signature or normalization callback
premise. The earlier family proof is extracted from checked history itself. -/
theorem signature_metadata {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature) :
    SignatureScoped signature ∧ signature.result.length = entry.declaration.arity ∧
      Parameters env entry.declaration.params signature := by
  obtain ⟨defs,families,earlier,source,prior,size,checked,extension⟩ := history.family_prefix found
  obtain ⟨term,sourceFound,telescope⟩ := checked.signatures.right sigFound
  refine ⟨history.wellFormed.signatures _ _ found _ (List.mem_of_getElem? sigFound),?_,?_⟩
  · simpa only [checked.declaration] using telescope_result_arity telescope
  · rw [checked.declaration]
    exact (telescope_parameters telescope).extend extension

/-- The actual de Bruijn field substitution reads fields in declaration
order. No ground evaluator or normalization-commutation assumption is needed. -/
theorem parameterAt_field {j : Nat} (selected : values[j]? = some value) :
    parameterAt 0 0 values (values.length - 1 - j) = value := by
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have reversed : values.reverse[values.length - 1 - j]? = some value :=
    (List.getElem?_reverse' (by omega)).trans selected
  simp only [parameterAt,Nat.not_lt_zero,↓reduceIte,Nat.sub_zero,reversed,
    Option.map_some,Option.getD_some,Nat.add_zero]
  exact Term.rename_id value

/-- Applying real constructor fields preserves each authenticated parameter
in the normalized result indices, modulo the installed full conversion. -/
theorem Parameters.instantiate (parameters : Parameters env params signature)
    (closed : Conversion.Closed env) (size : values.length = signature.fields.length)
    {j : Nat} (inside : j < params) (selected : values[j]? = some value) :
    ∃ index,signature.result[j]? = some index ∧
      Conversion.Conv env (index.subst (parameterAt 0 0 values)) value := by
  obtain ⟨field,index,_,_,_,_,found,converted⟩ := parameters.2 j inside
  refine ⟨index,found,?_⟩
  have instantiated := converted.substitution (parameterAt 0 0 values) closed
  simpa only [Term.subst,← size,parameterAt_field selected] using instantiated

/-- The public instance derives all metadata and closedness from actual
checked history; callers supply only concrete lookups and field values. -/
theorem signature_parameter_instance {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (size : values.length = signature.fields.length) (inside : j < entry.declaration.params)
    (selected : values[j]? = some value) :
    ∃ index,signature.result[j]? = some index ∧
      Conversion.Conv env (index.subst (parameterAt 0 0 values)) value :=
  (signature_metadata history found sigFound).2.2.instantiate history.wellFormed.closed size inside selected

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
