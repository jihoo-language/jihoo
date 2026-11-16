import Jihoo.NativeLoanGlobalChecking
import Jihoo.NativeFamilyWire

/-! Exact canonical version-6 input for sequential loan-aware global typing.
Every declaration is expanded against its actual checked prefix. Families,
runtime quantities, native parser fidelity and heap execution are separate. -/
namespace Jihoo.NativeKernel.NativeLoanGlobalInput
open NativeFamilyWire Environment

def checkSnapshot (fuel : Nat) (snapshot : Snapshot) : Option Environment :=
  match decodeProgram snapshot with
  | some (definitions, []) => LoanTyping.Program.checkProgram fuel definitions
  | _ => none

theorem checkSnapshot_sound (checked : checkSnapshot fuel snapshot = some env) :
    ∃ definitions, decodeProgram snapshot = some (definitions, []) ∧
      LoanTyping.Program.ProgramChecked definitions env := by
  unfold checkSnapshot at checked
  split at checked
  · rename_i definitions decoded
    exact ⟨definitions, decoded, LoanTyping.Program.checkProgram_sound checked⟩
  · contradiction

def checkBytes (fuel : Nat) (bytes : ByteArray) : Option Environment :=
  match decodeSnapshot bytes with
  | none => none
  | some snapshot => checkSnapshot fuel snapshot

/-- Acceptance binds actual sequential checking, expansion and loan typing
to these exact bytes and every graph node, including unused nodes. -/
theorem checkBytes_sound (checked : checkBytes fuel bytes = some env) :
    ∃ snapshot definitions, encodeSnapshot snapshot = bytes ∧
      NativeWire.graphValid snapshot.arena = true ∧ NativeArena.Backward snapshot.arena ∧
      NativeProgramWire.RepresentsDefinitions snapshot.arena snapshot.definitions definitions ∧
      RepresentsFamilies snapshot.arena snapshot.families [] ∧
      LoanTyping.Program.ProgramChecked definitions env ∧
      UnifiedProgram.EnvWellFormed env ∧
      env.globals.size = definitions.length ∧ env.families = #[] := by
  cases decoded : decodeSnapshot bytes with
  | none => simp [checkBytes, decoded] at checked
  | some snapshot =>
      obtain ⟨definitions, program, history⟩ := checkSnapshot_sound
        (by simpa only [checkBytes, decoded] using checked)
      obtain ⟨valid, backwards, definitionsMeaning, familiesMeaning⟩ := decodeProgram_sound program
      exact ⟨snapshot, definitions, decodeSnapshot_exact decoded, structureValid_graph valid,
        backwards, definitionsMeaning, familiesMeaning, history, history.wellFormed,
        history.size, history.noFamilies⟩

theorem checkBytes_encode (fuel : Nat) (snapshot : Snapshot) :
    checkBytes fuel (encodeSnapshot snapshot) = checkSnapshot fuel snapshot := by
  simp only [checkBytes, decodeSnapshot_encode]

theorem checkBytes_trailing (fuel : Nat) (snapshot : Snapshot) (byte : UInt8) :
    checkBytes fuel ((encodeSnapshot snapshot).push byte) = none := by
  simp [checkBytes, decodeSnapshot, encodeSnapshot, ByteArray.data_push,
    parseSnapshot_encode]

/-- The byte interface retains the existing decoder's aggregate work bound;
the expansion budget counts all selected declaration occurrences. -/
theorem checkSnapshot_bounds (checked : checkSnapshot fuel snapshot = some env) :
    ∃ definitions, decodeProgram snapshot = some (definitions, []) ∧
      definitions.length ≤ 1024 ∧ snapshot.arena.size ≤ 4096 ∧
      ∃ work, expansionWork snapshot = some work ∧ work ≤ 200000 := by
  obtain ⟨definitions, decoded, _⟩ := checkSnapshot_sound checked
  obtain ⟨count, _, nodes, work⟩ := decodeProgram_bounds decoded
  exact ⟨definitions, decoded, count, nodes, work⟩

end Jihoo.NativeKernel.NativeLoanGlobalInput
