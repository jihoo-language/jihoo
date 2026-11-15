import Jihoo.NativeLoanFamilyIotaRecursiveMetadata

/-! Typed recursive fields extracted from real constructor argument derivations.
Parameter alignment uses the checked recursive-field equations, not a callback. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem drop_selected {α : Type} {xs : List α} {j : Nat} {x : α} (found : xs[j]? = some x) : xs.drop j = x :: xs.drop (j+1) := by
  induction xs generalizing j with
  | nil => simp at found
  | cons head xs ih => cases j with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found;subst x;rfl
    | succ j => exact ih found

/-- A selected real constructor field has its declared dependent domain
instantiated by precisely the actual preceding values. -/
theorem arguments_field_at {family j : Nat} {signature : Signature}
    (wf : UnifiedProgram.EnvWellFormed env)
    (arguments : Arguments env [] ctx true data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length)
    (fieldFound : signature.fields[j]? = some field) (valueFound : values[j]? = some value) :
    HasType env [] ctx true value (field.domain.subst (fieldSubstitution (values.take j))) := by
  have bound := (List.getElem?_eq_some_iff.mp fieldFound).1
  have valueBound : j ≤ values.length := by omega
  have prefixSize : (values.take j).length = j := by simp only [List.length_take,Nat.min_eq_left valueBound]
  have leading := consume_signature_leading family signature j (values.take j) (by omega) prefixSize
  have remaining := arguments_drop_leading wf (values.take j) (values := values.drop j)
    (by simpa only [List.take_append_drop] using arguments) leading
  rw [drop_selected fieldFound,drop_selected valueFound] at remaining
  simp only [List.map_cons,closeDataFields,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at remaining
  exact (arguments_pi_view wf remaining).1

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

/-- When View is admitted (arity equals parameters), a recursive self field
has exactly the outer constructor's actual parameter instance. -/
theorem recursive_view_argument {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true) (arity : entry.declaration.arity = entry.declaration.params)
    (arguments : Arguments env [] ctx true entry.declaration.data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length)
    (fieldFound : signature.fields[j]? = some field) (valueFound : values[j]? = some value)
    (recursive : field.recursive = some indices) :
    HasType env [] ctx true value (.node (.ind family entry.declaration.arity) (values.take entry.declaration.params)) := by
  have shape := signature_recursive_metadata history found sigFound j field fieldFound
  obtain ⟨domain,indexSize,erased,parameterShape⟩ := shape.2 indices recursive
  obtain ⟨bound,parameters⟩ := parameterShape dataIs
  have metadata := signature_metadata history found sigFound
  have valueBound : entry.declaration.params ≤ values.length := by have p := metadata.2.2.1;omega
  have prefixSize : (values.take j).length = j := by
    have inside := (List.getElem?_eq_some_iff.mp valueFound).1
    simp only [List.length_take,Nat.min_eq_left (by omega : j ≤ values.length)]
  have related : Conversion.ListRel (Conversion.Conv env)
      (indices.map (Term.subst (fieldSubstitution (values.take j)))) (values.take entry.declaration.params) := by
    apply related_of_lookup
    · simp only [List.length_map,indexSize,arity,List.length_take,Nat.min_eq_left valueBound]
    · intro k normal actual normalFound actualFound
      have inside := (List.getElem?_eq_some_iff.mp actualFound).1
      simp only [List.length_take,Nat.min_eq_left valueBound] at inside
      obtain ⟨index,indexFound,converted⟩ := parameters k inside
      have sameNormal : normal = index.subst (fieldSubstitution (values.take j)) := by
        simp only [List.getElem?_map,indexFound,Option.map_some,Option.some.injEq] at normalFound
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
  have typed := arguments_field_at history.wellFormed arguments size fieldFound valueFound
  rw [domain] at typed
  simp only [Term.subst,substArgs_dataInd] at typed
  exact .convert typed (.node _ related)

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
