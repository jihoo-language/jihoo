import Jihoo.NativeCoreIdentical
import Jihoo.NativeCoreConstructorTelescopeAlignment
import Jihoo.NativeLoanMixedAdmission

/-! Native constructor roots are read from the original packed declaration
graph. The actual mixed history supplies the matching normalized signature
and the relation between its written and checked telescopes. -/
namespace Jihoo.NativeKernel.NativeCoreConstructorTelescopeAlignment

open NativeArena NativeFamilyWire Environment
open EnvironmentDelta (expand)

private theorem declared_family_lookup {index : Nat} {source : FamilyDeclaration}
    (history : ScopedProgram.History definitions declarations env)
    (selected : declarations[index]? = some source) :
    ∃ entry, env.families[index]? = some entry ∧ entry.declaration = source := by
  induction history with
  | empty => cases selected
  | definition _ _ ih => exact ih selected
  | @family definitions declarations env latest added history checked ih =>
    by_cases earlier : index < declarations.length
    · have old : declarations[index]? = some source := by
        simpa only [List.getElem?_append_left earlier] using selected
      obtain ⟨entry,found,matching⟩ := ih old
      exact ⟨entry,(Environment.Extends.pushFamily env added).families index entry found,matching⟩
    · have inside := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_append,List.length_singleton] at inside
      have last : index = declarations.length := by omega
      subst index
      have same : latest = source := by simpa using selected
      refine ⟨added,?_,checked.declaration.trans same⟩
      rw [← history.familyLength]
      exact Array.getElem?_push_size ..

private theorem family_root_lookup {index : Nat} {row : FamilyRoots}
    (rows : RepresentsFamilies arena familyRows terms)
    (selected : familyRows[index]? = some row) :
    ∃ source, terms[index]? = some source ∧ RepresentsFamily arena row source := by
  induction rows generalizing index with
  | nil => cases selected
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      cases selected
      exact ⟨_,rfl,first⟩
    | succ index => exact ih selected

/-- The written family row and the checked table use the same declaration
width and kind. -/
theorem checked_family_layout {family : Nat} {row : FamilyRoots}
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies arena familyRows familyTerms)
    (selected : familyRows[family]? = some row) :
    ∃ entry, env.families[family]? = some entry ∧ entry.declaration.data = row.data ∧
      entry.declaration.params = row.params ∧ entry.declaration.arity = row.arity := by
  obtain ⟨source,foundSource,represented⟩ := family_root_lookup rows selected
  have declared : (familyTerms.map NativeLoanMixedAdmission.declaration)[family]? =
      some (NativeLoanMixedAdmission.declaration source) := by
    simp only [List.getElem?_map,foundSource,Option.map_some]
  obtain ⟨entry,found,original⟩ := declared_family_lookup history declared
  exact ⟨entry,found,by simpa only [original,NativeLoanMixedAdmission.declaration] using represented.1,
    by simpa only [original,NativeLoanMixedAdmission.declaration] using represented.2.1,
    by simpa only [original,NativeLoanMixedAdmission.declaration] using represented.2.2.1⟩

/-- The checked family supplies the parameter width and exact case count. -/
theorem checked_family_widths {family : Nat} {row : FamilyRoots}
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies arena familyRows familyTerms)
    (selected : familyRows[family]? = some row) (found : env.families[family]? = some entry) :
    row.params ≤ row.arity ∧ row.constructors.length = entry.signatures.length := by
  obtain ⟨source,foundSource,represented⟩ := family_root_lookup rows selected
  have declared : (familyTerms.map NativeLoanMixedAdmission.declaration)[family]? =
      some (NativeLoanMixedAdmission.declaration source) := by
    simp only [List.getElem?_map,foundSource,Option.map_some]
  obtain ⟨actual,actualFound,original⟩ := declared_family_lookup history declared
  have same := Option.some.inj (actualFound.symm.trans found)
  subst actual
  obtain ⟨_,_,_,_,_,_,checked,_⟩ := history.family_prefix found
  have metadata := checked.metadata.2.2.1
  rw [← checked.declaration,original] at metadata
  have signatures := FamilyEnvironment.RelList.length checked.signatures
  rw [← checked.declaration,original] at signatures
  exact ⟨by simpa only [NativeLoanMixedAdmission.declaration,represented.2.1,represented.2.2.1] using metadata,
    (NativeCoreIdentical.represented_length represented.2.2.2.2).trans signatures⟩

private theorem constructor_root_lookup {index root : Nat}
    (rows : RepresentsList arena refs terms) (selected : refs[index]? = some root) :
    ∃ term, terms[index]? = some term ∧ Represents arena root term := by
  induction rows using RepresentsList.rec (motive_1 := fun _ _ _ => True) generalizing index with
  | var | node => trivial
  | nil => cases selected
  | cons first rest _ ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      cases selected
      exact ⟨_,rfl,first⟩
    | succ index => exact ih selected

theorem checked_constructor_root {family constructor root : Nat} {row : FamilyRoots}
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies arena familyRows familyTerms)
    (selected : familyRows[family]? = some row)
    (read : row.constructors[constructor]? = some root) :
    ∃ entry signature source,
      env.families[family]? = some entry ∧ entry.signatures[constructor]? = some signature ∧
        entry.declaration.data = row.data ∧ Represents arena root source ∧
        RawLend.Conv env (expand env source) (signatureTerm family signature) := by
  obtain ⟨familySource,foundSource,represented⟩ := family_root_lookup rows selected
  have declared : (familyTerms.map NativeLoanMixedAdmission.declaration)[family]? =
      some (NativeLoanMixedAdmission.declaration familySource) := by
    simp only [List.getElem?_map,foundSource,Option.map_some]
  obtain ⟨entry,found,original⟩ := declared_family_lookup history declared
  obtain ⟨source,constructorFound,sourceRep⟩ := constructor_root_lookup represented.2.2.2.2 read
  have written : entry.declaration.constructors[constructor]? = some source := by
    simpa only [original,NativeLoanMixedAdmission.declaration] using constructorFound
  obtain ⟨_,_,_,actual,_,_,checked,_⟩ := history.family_prefix found
  have length := FamilyEnvironment.RelList.length checked.signatures
  rw [← checked.declaration] at length
  have bound := (List.getElem?_eq_some_iff.mp written).1
  have within : constructor < entry.signatures.length := by omega
  let signature := entry.signatures[constructor]
  have signatureFound : entry.signatures[constructor]? = some signature := List.getElem?_eq_getElem within
  exact ⟨entry,signature,source,found,signatureFound,
    by simpa only [original,NativeLoanMixedAdmission.declaration] using represented.1,
    sourceRep,admitted_constructor_signature_conversion history found written signatureFound⟩

end Jihoo.NativeKernel.NativeCoreConstructorTelescopeAlignment
