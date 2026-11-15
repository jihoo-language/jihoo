import Jihoo.NativeLoanCheckerSoundness
import Jihoo.NativeFamilyWire
import Jihoo.NativeScopeCheck

/-! Exact canonical native input for one closed declaration without families.
This entry point proves loan-aware typing, not resource or whole-program
admission. The full checker itself accepts arbitrary supplied environments. -/
namespace Jihoo.NativeKernel.NativeLoanTypingInput
open NativeFamilyWire Environment

def checkDeclaration (fuel : Nat) (declaration : GlobalDeclaration) : Bool :=
  if scopeCheck 0 declaration.type = true ∧ scopeCheck 0 declaration.value = true then
    match LoanTyping.Checker.sort fuel empty [] [] declaration.type with
    | none => false
    | some sort => LoanTyping.Checker.check fuel empty [] [] (decide (sort = .prop))
        declaration.value declaration.type
  else false

theorem checkDeclaration_sound (checked : checkDeclaration fuel declaration = true) :
    declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type := by
  unfold checkDeclaration at checked
  split at checked
  · rename_i scopes
    cases inferred : LoanTyping.Checker.sort fuel empty [] [] declaration.type with
    | none => simp [inferred] at checked
    | some sort =>
        exact ⟨scopeCheck_sound scopes.1,scopeCheck_sound scopes.2,sort,LoanTyping.Checker.sort_sound inferred,
          LoanTyping.Checker.check_sound (by simpa only [inferred] using checked)⟩
  · contradiction

def checkSnapshot (fuel : Nat) (snapshot : Snapshot) : Bool :=
  match decodeProgram snapshot with
  | some ([declaration],[]) => checkDeclaration fuel declaration
  | _ => false

theorem checkSnapshot_sound (checked : checkSnapshot fuel snapshot = true) :
    ∃ declaration, decodeProgram snapshot = some ([declaration],[]) ∧
      declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type := by
  unfold checkSnapshot at checked
  split at checked
  · rename_i declaration decoded
    exact ⟨declaration,decoded,checkDeclaration_sound checked⟩
  · contradiction

def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some snapshot => checkSnapshot fuel snapshot

theorem checkBytes_sound (checked : checkBytes fuel bytes = true) :
    ∃ snapshot declaration, encodeSnapshot snapshot = bytes ∧
      NativeWire.graphValid snapshot.arena = true ∧ NativeArena.Backward snapshot.arena ∧
      NativeProgramWire.RepresentsDefinitions snapshot.arena snapshot.definitions [declaration] ∧
      RepresentsFamilies snapshot.arena snapshot.families [] ∧
      declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
      ∃ sort : SortTag, LoanTyping.HasType empty [] [] true declaration.type sort.term ∧
        LoanTyping.HasType empty [] [] (decide (sort = .prop)) declaration.value declaration.type := by
  cases decoded : decodeSnapshot bytes with
  | none => simp [checkBytes,decoded] at checked
  | some snapshot =>
      obtain ⟨declaration,program,typeScoped,valueScoped,sort,typeFormed,valueTyped⟩ := checkSnapshot_sound
        (by simpa only [checkBytes,decoded] using checked)
      obtain ⟨valid,backwards,definitions,families⟩ := decodeProgram_sound program
      exact ⟨snapshot,declaration,decodeSnapshot_exact decoded,structureValid_graph valid,
        backwards,definitions,families,typeScoped,valueScoped,sort,typeFormed,valueTyped⟩

theorem checkBytes_encode (fuel : Nat) (snapshot : Snapshot) :
    checkBytes fuel (encodeSnapshot snapshot) = checkSnapshot fuel snapshot := by
  simp only [checkBytes,decodeSnapshot_encode]

end Jihoo.NativeKernel.NativeLoanTypingInput
