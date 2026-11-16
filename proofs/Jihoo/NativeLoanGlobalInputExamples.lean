import Jihoo.NativeLoanGlobalInput
import Jihoo.NativeLoanGlobalExamples

namespace Jihoo.NativeKernel.NativeLoanGlobalInput.Examples
open NativeFamilyWire Environment.LoanTyping

/-- The original two-declaration program: a dependent Lend function, then a
call through global 0 with an allocated owner. All arena edges are backward. -/
def snapshot : Snapshot :=
  ⟨[⟨15, 14⟩, ⟨2, 19⟩], [],
    #[.node (.natural 2) [], .node .buffer [0], .node .i64 [],
      .node .ref [1], .var 0, .node (.natural 0) [], .node .decide [5, 0],
      .node .index [4, 5, 6], .node (.lam false) [3, 7], .var 1,
      .node .free [4, 9], .node (.lam false) [1, 10], .node (.lam false) [2, 11],
      .node .lend [4, 8, 12], .node (.lam false) [1, 13], .node (.pi false) [1, 2],
      .node (.integer 0) [], .node .alloc [0, 16], .node (.global 0) [],
      .node .app [18, 17]]⟩

theorem original_loan_program_decoded :
    decodeProgram snapshot = some (GlobalExamples.sources, []) := by cbv

theorem exact_sequential_loan_program_accepted :
    checkBytes 64 (encodeSnapshot snapshot) = some GlobalExamples.result := by
  rw [checkBytes_encode]
  cbv

theorem exact_sequential_loan_program_history :
    Program.ProgramChecked GlobalExamples.sources GlobalExamples.result := by
  obtain ⟨definitions, decoded, history⟩ := checkSnapshot_sound
    (by simpa only [checkBytes_encode] using exact_sequential_loan_program_accepted)
  rw [original_loan_program_decoded] at decoded
  cases decoded
  exact history

theorem self_reference_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with arena := snapshot.arena.set! 18 (.node (.global 1) []) }) = none := by
  rw [checkBytes_encode]
  cbv

theorem forward_reference_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with definitions := [⟨2, 19⟩, ⟨15, 14⟩] }) = none := by
  rw [checkBytes_encode]
  cbv

theorem unbound_source_variable_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with arena := snapshot.arena.set! 9 (.var 99) }) = none := by
  rw [checkBytes_encode]
  cbv

theorem unreachable_malformed_node_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with arena := snapshot.arena.push (.node .uadd []) }) = none := by
  rw [checkBytes_encode]
  cbv

theorem missing_declaration_root_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with definitions := [⟨15, 14⟩, ⟨2, 99⟩] }) = none := by
  rw [checkBytes_encode]
  cbv

theorem family_table_rejected : checkBytes 64 (encodeSnapshot
    { snapshot with families := [⟨true, 0, 0, 0, [1]⟩] }) = none := by
  rw [checkBytes_encode]
  cbv

theorem exhausted_checker_rejected : checkBytes 0 (encodeSnapshot snapshot) = none := by
  rw [checkBytes_encode]
  cbv

theorem trailing_byte_rejected :
    checkBytes 64 ((encodeSnapshot snapshot).push 0) = none :=
  checkBytes_trailing 64 snapshot 0

end Jihoo.NativeKernel.NativeLoanGlobalInput.Examples
