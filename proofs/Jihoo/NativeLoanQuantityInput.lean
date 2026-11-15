import Jihoo.NativeLoanQuantity
import Jihoo.NativeFamilyWire

/-! Exact one-declaration native input with the complete loan-aware typing
and recursive resource gate. Scope is checked on original type/value syntax.
Proof declarations are erased; code declarations use the actual resource query.
General environments and families remain supported by the underlying checker
and resource projector; this strict byte entry currently has an empty family table. -/
namespace Jihoo.NativeKernel.NativeLoanQuantityInput
open NativeFamilyWire Environment

def checkDeclaration (fuel quantityFuel : Nat) (declaration : GlobalDeclaration) : Bool :=
  if scopeCheck 0 declaration.type = true ∧ scopeCheck 0 declaration.value = true then
    match LoanTyping.Checker.sort fuel empty [] [] declaration.type with
    | none => false
    | some sort => LoanTyping.Checker.check fuel empty [] [] (decide (sort = .prop)) declaration.value declaration.type &&
        (decide (sort = .prop) || LoanTyping.ResourceQuantity.checkResource quantityFuel empty declaration.value)
  else false

theorem checkDeclaration_sound (checked : checkDeclaration fuel quantityFuel declaration = true) :
    declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type ∧
        (sort = .prop ∨ LoanTyping.ResourceQuantity.ResourceSafe empty declaration.value) := by
  unfold checkDeclaration at checked
  split at checked
  · rename_i scopes
    cases inferred : LoanTyping.Checker.sort fuel empty [] [] declaration.type with
    | none => simp [inferred] at checked
    | some sort =>
        simp only [inferred] at checked
        obtain ⟨typed,resource⟩ := Bool.and_eq_true_iff.mp checked
        refine ⟨scopeCheck_sound scopes.1,scopeCheck_sound scopes.2,sort,LoanTyping.Checker.sort_sound inferred,
          LoanTyping.Checker.check_sound typed,?_⟩
        rcases Bool.or_eq_true_iff.mp resource with erased | code
        · exact Or.inl (of_decide_eq_true erased)
        · exact Or.inr (LoanTyping.ResourceQuantity.checkResource_sound code)
  · contradiction

def checkSnapshot (fuel quantityFuel : Nat) (snapshot : Snapshot) : Bool :=
  match decodeProgram snapshot with
  | some ([declaration],[]) => checkDeclaration fuel quantityFuel declaration
  | _ => false

theorem checkSnapshot_sound (checked : checkSnapshot fuel quantityFuel snapshot = true) :
    ∃ declaration, decodeProgram snapshot = some ([declaration],[]) ∧
      declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type ∧
        (sort = .prop ∨ LoanTyping.ResourceQuantity.ResourceSafe empty declaration.value) := by
  unfold checkSnapshot at checked
  split at checked
  · rename_i declaration decoded
    exact ⟨declaration,decoded,checkDeclaration_sound checked⟩
  · contradiction

def checkBytes (fuel quantityFuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some snapshot => checkSnapshot fuel quantityFuel snapshot

theorem checkBytes_sound (checked : checkBytes fuel quantityFuel bytes = true) :
    ∃ snapshot declaration, encodeSnapshot snapshot = bytes ∧
      NativeWire.graphValid snapshot.arena = true ∧ NativeArena.Backward snapshot.arena ∧
      NativeProgramWire.RepresentsDefinitions snapshot.arena snapshot.definitions [declaration] ∧
      RepresentsFamilies snapshot.arena snapshot.families [] ∧
      declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type ∧
        (sort = .prop ∨ LoanTyping.ResourceQuantity.ResourceSafe empty declaration.value) := by
  cases decoded : decodeSnapshot bytes with
  | none => simp [checkBytes,decoded] at checked
  | some snapshot =>
      obtain ⟨declaration,program,typeScoped,valueScoped,sort,typeFormed,valueTyped,resource⟩ := checkSnapshot_sound
        (by simpa only [checkBytes,decoded] using checked)
      obtain ⟨valid,backwards,definitions,families⟩ := decodeProgram_sound program
      exact ⟨snapshot,declaration,decodeSnapshot_exact decoded,structureValid_graph valid,
        backwards,definitions,families,typeScoped,valueScoped,sort,typeFormed,valueTyped,resource⟩

theorem checkBytes_encode (fuel quantityFuel : Nat) (snapshot : Snapshot) :
    checkBytes fuel quantityFuel (encodeSnapshot snapshot) = checkSnapshot fuel quantityFuel snapshot := by
  simp only [checkBytes,decodeSnapshot_encode]

end Jihoo.NativeKernel.NativeLoanQuantityInput
