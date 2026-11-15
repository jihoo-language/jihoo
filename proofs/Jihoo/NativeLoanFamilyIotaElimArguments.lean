import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeLoanFamilyIotaRecursiveArguments

/-! Actual recursive constructor fields for general indexed Elim. Their
unchanged parameter prefix and boxed layout come from checked source metadata. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem related_of_lookup (size : xs.length = ys.length)
    (lookup : ∀ (j : Nat) a b,xs[j]? = some a → ys[j]? = some b → Conversion.Conv env a b) :
    Conversion.ListRel (Conversion.Conv env) xs ys := by
  induction xs generalizing ys with
  | nil => have empty : ys = [] := List.length_eq_zero_iff.mp size.symm;subst ys;exact .nil
  | cons x xs ih => cases ys with
    | nil => simp at size
    | cons y ys =>
      exact .cons (lookup 0 x y rfl rfl)
        (ih (Nat.succ.inj size) (fun j a b left right => lookup (j+1) a b left right))

theorem recursive_field_argument {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (arguments : Arguments env [] ctx true entry.declaration.data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length)
    (fieldFound : signature.fields[j]? = some field) (valueFound : values[j]? = some value)
    (recursive : field.recursive = some indices) :
    HasType env [] ctx true value (.node (.ind family entry.declaration.arity)
      (indices.map (Term.subst (fieldSubstitution (values.take j))))) := by
  have shape := signature_recursive_metadata history found sigFound j field fieldFound
  have typed := arguments_field_at history.wellFormed arguments size fieldFound valueFound
  rw [(shape.2 indices recursive).1] at typed
  simpa only [Term.subst,substArgs_dataInd] using typed

theorem recursive_parameter_alignment {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature} {values : List Term}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true) (size : values.length = signature.fields.length)
    (fieldFound : signature.fields[j]? = some field) (recursive : field.recursive = some indices) :
    Conversion.ListRel (Conversion.Conv env)
      ((indices.map (Term.subst (fieldSubstitution (values.take j)))).take entry.declaration.params)
      (values.take entry.declaration.params) := by
  have metadata := signature_metadata history found sigFound
  have shape := signature_recursive_metadata history found sigFound j field fieldFound
  obtain ⟨domain,indexSize,erased,parameterShape⟩ := shape.2 indices recursive
  obtain ⟨bound,parameters⟩ := parameterShape dataIs
  have arityBound : entry.declaration.params ≤ entry.declaration.arity := by
    have resultBound := metadata.2.2.result_bound
    omega
  have valueBound : entry.declaration.params ≤ values.length := by have p := metadata.2.2.1;omega
  have prefixSize : (values.take j).length = j := by
    have inside := (List.getElem?_eq_some_iff.mp fieldFound).1
    simp only [List.length_take,Nat.min_eq_left (by omega : j ≤ values.length)]
  apply related_of_lookup
  · simp only [List.length_take,List.length_map,indexSize,Nat.min_eq_left arityBound,Nat.min_eq_left valueBound]
  · intro k normal actual normalFound actualFound
    have inside := (List.getElem?_eq_some_iff.mp actualFound).1
    simp only [List.length_take,Nat.min_eq_left valueBound] at inside
    obtain ⟨index,indexFound,converted⟩ := parameters k inside
    have sameNormal : normal = index.subst (fieldSubstitution (values.take j)) := by
      simp only [List.getElem?_take,inside,↓reduceIte,List.getElem?_map,indexFound,Option.map_some,Option.some.injEq] at normalFound
      exact normalFound.symm
    subst normal
    have prefixFound : (values.take j)[k]? = some actual := by
      have before : k < j := by omega
      simp only [List.getElem?_take,before,↓reduceIte]
      simpa only [List.getElem?_take,inside,↓reduceIte] using actualFound
    have selected := fieldSubstitution_selected prefixFound
    rw [prefixSize] at selected
    have instantiated := converted.substitution (fieldSubstitution (values.take j)) history.wellFormed.closed
    simpa only [Term.subst,selected] using instantiated

/-- An authentic recursive data field forces the real family heap-layout bit.
A flat family therefore cannot silently discard a recursive hypothesis. -/
theorem recursive_data_is_boxed {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true)
    (fieldFound : signature.fields[j]? = some field) (recursive : field.recursive = some indices) :
    entry.boxed = true := by
  have shape := signature_recursive_metadata history found sigFound j field fieldFound
  have erased := (shape.2 indices recursive).2.2.1
  rw [dataIs] at erased
  obtain ⟨defs,families,earlier,source,prior,size,checked,extension⟩ := history.family_prefix found
  have sourceData : source.data = true := by rw [← checked.declaration];exact dataIs
  rw [checked.layout,sourceData,Bool.and_true]
  apply List.any_eq_true.mpr
  refine ⟨signature,List.mem_of_getElem? sigFound,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨field,List.mem_of_getElem? fieldFound,?_⟩
  simp only [FamilyEnvironment.heapField,erased,Bool.not_true,recursive,Option.isSome_some,Bool.true_or,Bool.not_false,Bool.true_and]

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
