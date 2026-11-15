import Jihoo.NativeLoanFamilyIotaViewPreservation

/-! Recursive field shape and parameter equations are recovered from the
actual checked declaration, including exclusion of forged ordinary self fields. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
open UnifiedProgram
set_option linter.unusedSimpArgs false

/-- The actual stored recursive classification and unchanged parameter prefix. -/
def RecursiveShape (env : Environment) (family : Nat) (declaration : FamilyDeclaration)
    (position : Nat) (field : Field) : Prop :=
  (∀ count indices,field.domain = .node (.ind family count) indices → field.recursive = some indices) ∧
  ∀ indices,field.recursive = some indices →
    field.domain = .node (.ind family declaration.arity) indices ∧ indices.length = declaration.arity ∧
    field.erased = !declaration.data ∧
    (declaration.data = true → declaration.params ≤ position ∧ ∀ j < declaration.params,
      ∃ index,indices[j]? = some index ∧ Conversion.Conv env index (.var (position-1-j)))

private theorem variable_index
    (checked : Families.IndexChecked env self ctx (.var x) normal) :
    Conversion.Conv env normal (.var x) := by
  obtain ⟨_,_,expansion,_,converted,_⟩ := checked
  cases expansion with
  | var => exact .old converted.symm

private theorem field_shape
    (checked : Families.FieldChecked env env.families.size declaration ctx erased source field) :
    RecursiveShape env env.families.size declaration ctx.length field := by
  cases checked with
  | ordinary free expansion sourceForm converted normalForm allowed =>
    constructor
    · intro count indices shape
      cases normalForm with
      | intro typed gate =>
        dsimp only at shape
        rw [shape] at typed
        obtain ⟨entry,found,_⟩ := typed.principalView
        simp at found
    · intro indices classified
      contradiction
  | recursive count size indices erased parameters =>
    subst count
    constructor
    · intro count indices' shape
      have same := Term.node.inj shape
      exact congrArg some same.2
    · intro normals classified
      cases classified
      refine ⟨rfl,indices.length.symm.trans size,erased,?_⟩
      intro data
      obtain ⟨bound,parameters⟩ := parameters data
      refine ⟨bound,?_⟩
      intro j inside
      obtain ⟨normal,found,checked⟩ := indices.left (parameters j inside)
      exact ⟨normal,found,variable_index checked⟩

theorem RecursiveShape.extend (shape : RecursiveShape before family declaration position field)
    (extension : Extends before after) : RecursiveShape after family declaration position field := by
  refine ⟨shape.1,?_⟩
  intro indices classified
  obtain ⟨domain,size,erased,parameters⟩ := shape.2 indices classified
  refine ⟨domain,size,erased,?_⟩
  intro data
  obtain ⟨bound,parameters⟩ := parameters data
  refine ⟨bound,?_⟩
  intro j inside
  obtain ⟨index,found,converted⟩ := parameters j inside
  exact ⟨index,found,converted.extend extension⟩

private theorem telescope_shapes
    (checked : Families.TelescopeChecked env env.families.size declaration fields source signature)
    (prior : ∀ j field,fields[j]? = some field → RecursiveShape env env.families.size declaration j field) :
    ∀ j field,signature.fields[j]? = some field → RecursiveShape env env.families.size declaration j field := by
  induction checked with
  | @field fields erased domain field rest signature checked tail ih =>
    apply ih
    intro j selected found
    by_cases earlier : j < fields.length
    · simp only [List.getElem?_append,earlier,↓reduceIte] at found
      exact prior j selected found
    · simp only [List.getElem?_append,earlier,↓reduceIte] at found
      have last : j = fields.length := by
        have inside := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_singleton] at inside
        omega
      subst j
      simp only [Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at found
      subst selected
      simpa only [Families.fieldContext,FamilyEnvironment.fieldContext_length] using field_shape checked
  | result => exact prior

/-- Every stored field's recursive shape is authenticated by the original
source telescope and transported through the real environment prefix. -/
theorem signature_recursive_metadata {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature) :
    ∀ j field,signature.fields[j]? = some field → RecursiveShape env family entry.declaration j field := by
  obtain ⟨defs,families,earlier,source,prior,size,checked,extension⟩ := history.family_prefix found
  obtain ⟨term,sourceFound,telescope⟩ := checked.signatures.right sigFound
  intro j field fieldFound
  have shape := telescope_shapes telescope (by intro _ _ impossible;simp at impossible) j field fieldFound
  rw [size,← checked.declaration] at shape
  exact shape.extend extension

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
