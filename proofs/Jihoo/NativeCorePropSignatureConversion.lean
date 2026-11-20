import Jihoo.NativeLoanContextualPreservation
import Jihoo.NativeEnvironmentBindingAlgebra
import Jihoo.NativeFamilyEnvironment

/-! An observed normalized constructor signature may use different
representatives for its domains and indices. Converted representatives
produce a convertible proposition case type at the same binder order. -/
namespace Jihoo.NativeKernel.Environment

open NativeKernel.Conversion (ListRel)
open FamilyEnvironment (RelList)

inductive RecursiveIndexConversion (env : Environment) : Option (List Term) → Option (List Term) → Prop where
  | none : RecursiveIndexConversion env none none
  | some : ListRel (RawLend.Conv env) a b → RecursiveIndexConversion env (some a) (some b)

structure FieldConversion (env : Environment) (first second : Field) : Prop where
  erasure : first.erased = second.erased
  domain : RawLend.Conv env first.domain second.domain
  recursive : RecursiveIndexConversion env first.recursive second.recursive

structure SignatureConversion (env : Environment) (first second : Signature) : Prop where
  fields : RelList (FieldConversion env) first.fields second.fields
  result : ListRel (RawLend.Conv env) first.result second.result

private def RecursiveFieldConversion (env : Environment) (first second : Nat × List Term) : Prop :=
  first.1 = second.1 ∧ ListRel (RawLend.Conv env) first.2 second.2

private theorem related_length (related : RelList P first second) : first.length = second.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem renamed_indices (closed : EnvironmentDelta.Basis.Closed env) (rename : Nat → Nat)
    (related : ListRel (RawLend.Conv env) first second) :
    ListRel (RawLend.Conv env) (first.map fun t => t.rename rename) (second.map fun t => t.rename rename) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.renaming rename closed) ih

private theorem application_spines (callee : RawLend.Conv env F G) (related : ListRel (RawLend.Conv env) first second) :
    RawLend.Conv env (applications F first) (applications G second) := by
  induction related generalizing F G with
  | nil => exact callee
  | cons head _ ih => exact ih (.node .app (.cons callee (.cons head .nil)))

private theorem aligned_recursive_fields (fields : RelList (FieldConversion env) first second) (offset : Nat) :
    RelList (RecursiveFieldConversion env)
      ((first.zipIdx offset).filterMap fun (field,j) => field.recursive.map fun xs => (j,xs))
      ((second.zipIdx offset).filterMap fun (field,j) => field.recursive.map fun xs => (j,xs)) := by
  induction fields generalizing offset with
  | nil => exact .nil
  | @cons a b first second head _ ih =>
    simp only [List.zipIdx_cons,List.filterMap_cons]
    have paired := head.recursive
    cases source : a.recursive <;> cases target : b.recursive <;> rw [source,target] at paired
    · exact ih _
    · cases paired
    · cases paired
    · cases paired with
      | some indices => exact .cons ⟨rfl,indices⟩ (ih _)

private theorem converted_hypotheses (closed : EnvironmentDelta.Basis.Closed env)
    (motive : RawLend.Conv env M N) (bodies : RawLend.Conv env A B)
    (recursive : RelList (RecursiveFieldConversion env) first second) (fields offset : Nat) :
    RawLend.Conv env (hypothesisTelescope fields offset first M A) (hypothesisTelescope fields offset second N B) := by
  induction recursive generalizing offset with
  | nil => exact bodies
  | cons related _ ih =>
    simp only [hypothesisTelescope,List.zipIdx_cons,List.foldr_cons,hypothesisType]
    obtain ⟨position,indices⟩ := related
    rw [position]
    exact .node (.pi true) (.cons (application_spines (motive.renaming _ closed) (renamed_indices closed _ indices))
      (.cons (ih (offset+1)) .nil))

private theorem converted_field_domains (bodies : RawLend.Conv env A B) (related : RelList (FieldConversion env) first second) :
    RawLend.Conv env (first.foldr (fun field rest => .pi field.erased field.domain rest) A)
      (second.foldr (fun field rest => .pi field.erased field.domain rest) B) := by
  induction related with
  | nil => exact bodies
  | cons head _ ih =>
    simp only [List.foldr_cons,head.erasure]
    exact .node (.pi _) (.cons head.domain (.cons ih .nil))

/-- The recursive field positions and erasures agree, while both stored
field domains and result indices may normalize to different representatives. -/
theorem SignatureConversion.prop_case (closed : EnvironmentDelta.Basis.Closed env)
    (signature : SignatureConversion env first second) (motive : RawLend.Conv env M N) :
    RawLend.Conv env (propCaseType first M) (propCaseType second N) := by
  rw [propCaseType_eq,propCaseType_eq]
  have fields := related_length signature.fields
  have recursive : RelList (RecursiveFieldConversion env) (recursiveFields first.fields) (recursiveFields second.fields) :=
    aligned_recursive_fields signature.fields 0
  have hypotheses := related_length recursive
  have results : RawLend.Conv env
      (applications (M.rename fun x => x+first.fields.length+(recursiveFields first.fields).length)
        (first.result.map fun term => term.rename fun x => x+(recursiveFields first.fields).length))
      (applications (N.rename fun x => x+second.fields.length+(recursiveFields second.fields).length)
        (second.result.map fun term => term.rename fun x => x+(recursiveFields second.fields).length)) := by
    rw [fields,hypotheses]
    exact application_spines (motive.renaming _ closed) (renamed_indices closed _ signature.result)
  rw [fields] at results ⊢
  exact converted_field_domains (converted_hypotheses closed motive results recursive _ 0) signature.fields

private def expandField (env : Environment) (field : Field) : Field :=
  ⟨field.erased,EnvironmentDelta.expand env field.domain,field.recursive.map (EnvironmentDelta.expandArgs env)⟩

/-- The exact pass-through delta expansion of the separately stored field
and index roots. Its recursive field positions remain those of the source. -/
def expandSignature (env : Environment) (signature : Signature) : Signature :=
  ⟨signature.fields.map (expandField env),EnvironmentDelta.expandArgs env signature.result⟩

private theorem expand_applications (env : Environment) (callee : Term) (args : List Term) :
    EnvironmentDelta.expand env (applications callee args) =
      applications (EnvironmentDelta.expand env callee) (EnvironmentDelta.expandArgs env args) := by
  induction args generalizing callee with
  | nil => simp only [applications,List.foldl_nil,EnvironmentDelta.expandArgs]
  | cons first rest ih =>
    change EnvironmentDelta.expand env (applications (.app callee first) rest) = _
    rw [ih]
    simp only [Term.app,EnvironmentDelta.expand_node_cons,EnvironmentDelta.expandArgs,applications,List.foldl_cons]

private theorem expansion_renamed_indices (admissible : EnvironmentDelta.Admissible env)
    (values : List Term) (rename : Nat → Nat) :
    EnvironmentDelta.expandArgs env (values.map fun value => value.rename rename) =
      (EnvironmentDelta.expandArgs env values).map fun value => value.rename rename := by
  induction values with
  | nil => simp only [EnvironmentDelta.expandArgs,List.map_nil]
  | cons head tail ih =>
    simp only [List.map_cons,EnvironmentDelta.expandArgs,EnvironmentDelta.expand_renaming admissible,ih]

private theorem expanded_recursive_fields (env : Environment) (fields : List Field) (offset : Nat) :
    ((fields.map (expandField env)).zipIdx offset).filterMap (fun (field,index) => field.recursive.map fun values => (index,values)) =
      ((fields.zipIdx offset).filterMap (fun (field,index) => field.recursive.map fun values => (index,values))).map
        (fun (index,values) => (index,EnvironmentDelta.expandArgs env values)) := by
  induction fields generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,List.zipIdx_cons,List.filterMap_cons,expandField]
    cases head.recursive <;> simp [ih]

private theorem expand_hypotheses (admissible : EnvironmentDelta.Admissible env) (count offset : Nat)
    (recursive : List (Nat × List Term)) (motive result : Term) :
    EnvironmentDelta.expand env (hypothesisTelescope count offset recursive motive result) =
      hypothesisTelescope count offset (recursive.map fun (index,values) => (index,EnvironmentDelta.expandArgs env values))
        (EnvironmentDelta.expand env motive) (EnvironmentDelta.expand env result) := by
  induction recursive generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨index,values⟩ := head
    simp only [hypothesisTelescope,List.zipIdx_cons,List.foldr_cons,List.map_cons,Term.pi,
      EnvironmentDelta.expand_node_cons,EnvironmentDelta.expandArgs,hypothesisType]
    rw [expand_applications,EnvironmentDelta.expand_renaming admissible,expansion_renamed_indices admissible]
    have body := ih (offset+1)
    simpa only [hypothesisTelescope,Term.pi,hypothesisType] using congrArg
      (fun rest => Term.node (.pi true) [(applications ((EnvironmentDelta.expand env motive).rename (fun x => x+count+offset))
        ((EnvironmentDelta.expandArgs env values).map fun term => term.rename (fun x => x+(count+offset-index)))),rest]) body

private theorem expand_field_domains (env : Environment) (fields : List Field) (body : Term) :
    EnvironmentDelta.expand env (fields.foldr (fun field rest => .pi field.erased field.domain rest) body) =
      (fields.map (expandField env)).foldr (fun field rest => .pi field.erased field.domain rest) (EnvironmentDelta.expand env body) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.map_cons,List.foldr_cons,expandField,Term.pi,EnvironmentDelta.expand_node_cons,EnvironmentDelta.expandArgs,ih]

/-- Expanding the actual arena's generated case type is equivalent to
expanding its stored declaration fields and motive before construction. -/
theorem expand_prop_case_type (admissible : EnvironmentDelta.Admissible env) (signature : Signature) (motive : Term) :
    EnvironmentDelta.expand env (propCaseType signature motive) =
      propCaseType (expandSignature env signature) (EnvironmentDelta.expand env motive) := by
  rw [propCaseType_eq,propCaseType_eq,expand_field_domains,expand_hypotheses admissible]
  simp only [expandSignature,List.length_map,recursiveFields,expanded_recursive_fields]
  rw [expand_applications,EnvironmentDelta.expand_renaming admissible,expansion_renamed_indices admissible]

end Jihoo.NativeKernel.Environment
