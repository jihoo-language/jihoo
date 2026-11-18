import Jihoo.NativeCoreGraphState

/-! The signature and representation tables associated with the three
`Core.extend` cursors. Inference can append tentative family rows before a
later error. The epilogue restores exactly the committed rows and visibility.
The contents of each signature are parameters of this cache model. -/
namespace Jihoo.NativeKernel.NativeCoreGraph

def restoreRows (checked : Nat) (rows : List α) : List α :=
  if checked < rows.length then restoreRows checked rows.dropLast else rows
termination_by rows.length
decreasing_by simp only [List.length_dropLast]; omega

/-- Repeatedly popping uncommitted rows retains exactly the checked prefix. -/
theorem restoreRows_eq_take (checked : Nat) (rows : List α) :
    restoreRows checked rows = rows.take checked := by
  rw [restoreRows]
  split
  · rename_i extra
    rw [restoreRows_eq_take, List.dropLast_eq_take, List.take_take]
    have fits : checked ≤ rows.length - 1 := by omega
    rw [Nat.min_eq_left fits]
  · rename_i checkedAll
    exact (List.take_of_length_le (Nat.le_of_not_gt checkedAll)).symm
termination_by rows.length
decreasing_by simp only [List.length_dropLast]; omega

structure DeclarationTables (σ : Type) where
  signatures : List σ
  boxed : List Bool
  visible : Nat
  visibleFamilies : Nat

def DeclarationTables.restore (checked : Cursors) (tables : DeclarationTables σ) : DeclarationTables σ :=
  ⟨restoreRows checked.families tables.signatures, restoreRows checked.families tables.boxed,
    checked.definitions, checked.families⟩

private theorem restoreRows_append (rows pending : List α) :
    restoreRows rows.length (rows ++ pending) = rows := by
  rw [restoreRows_eq_take, List.take_append_of_le_length (Nat.le_refl rows.length), List.take_length]

/-- Inference can append to both tables without changing any previously
committed row. Restoration removes exactly the tentative rows. -/
theorem DeclarationTables.restore_prefix {old attempted : DeclarationTables σ}
    (signatureSize : old.signatures.length = checked.families)
    (boxedSize : old.boxed.length = checked.families)
    (signatures : old.signatures.IsPrefix attempted.signatures)
    (boxed : old.boxed.IsPrefix attempted.boxed) :
    attempted.restore checked = old.restore checked := by
  obtain ⟨newSignatures, signatureAppend⟩ := signatures
  obtain ⟨newBoxed, boxedAppend⟩ := boxed
  have keptSignatures : restoreRows checked.families attempted.signatures =
      restoreRows checked.families old.signatures := by
    rw [← signatureSize, ← signatureAppend, restoreRows_append, restoreRows_eq_take, List.take_length]
  have keptBoxed : restoreRows checked.families attempted.boxed = restoreRows checked.families old.boxed := by
    rw [← boxedSize, ← boxedAppend, restoreRows_append, restoreRows_eq_take, List.take_length]
  simp only [DeclarationTables.restore, keptSignatures, keptBoxed]

def finishTables (before after : CheckState) (tables : DeclarationTables σ)
    (result : Except (ExtendError ε) Unit) : DeclarationTables σ :=
  match result with
  | .error _ => tables.restore before.checked
  | .ok () => ⟨tables.signatures, tables.boxed, after.checked.definitions, after.checked.families⟩

/-- The native failure epilogue leaves both checked cursors and earlier
table rows intact, regardless of how many tentative rows were appended. -/
theorem extend_failure_restores_tables
    {old attempted : DeclarationTables σ}
    (signatureSize : old.signatures.length = state.checked.families)
    (boxedSize : old.boxed.length = state.checked.families)
    (signatures : old.signatures.IsPrefix attempted.signatures)
    (boxed : old.boxed.IsPrefix attempted.boxed)
    (failed : (extend state infer).2 = .error reason) :
    let next := extend state infer
    next.1.checked = state.checked ∧
      finishTables state next.1 attempted next.2 = old.restore state.checked := by
  refine ⟨extend_failure_keeps_checked failed, ?_⟩
  simp only [failed, finishTables]
  exact DeclarationTables.restore_prefix signatureSize boxedSize signatures boxed

/-- After success, the actual post-inference tables remain in place and
visibility advances together with the checked cursors. -/
theorem extend_success_commits_tables (attempted : DeclarationTables σ)
    (succeeded : (extend state infer).2 = .ok ()) :
    let next := extend state infer
    let tables := finishTables state next.1 attempted next.2
    tables.signatures = attempted.signatures ∧ tables.boxed = attempted.boxed ∧
      tables.visible = next.1.snapshot.definitions.length ∧
      tables.visibleFamilies = next.1.snapshot.families.length := by
  have committed := extend_commit succeeded
  simp [succeeded, finishTables, committed, Cursors.complete]

end Jihoo.NativeKernel.NativeCoreGraph
