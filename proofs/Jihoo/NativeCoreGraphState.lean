import Jihoo.NativeCoreGraph

/-! Graph inspection and atomic cursor commit for incremental `Core.extend`.
The checker inspects the user-provided suffix, runs inference, then inspects
nodes created during inference before advancing the three checked cursors.
The inference callback records the arena left on success or failure. Its
typing, declaration ordering, and temporary signature tables are separate
from the graph and cursor guarantees. -/
namespace Jihoo.NativeKernel.NativeCoreGraph
open NativeArena

structure Cursors where
  nodes : Nat
  definitions : Nat
  families : Nat

def Cursors.complete (snapshot : NativeFamilyWire.Snapshot) : Cursors :=
  ⟨snapshot.arena.size, snapshot.definitions.length, snapshot.families.length⟩

structure CheckState where
  snapshot : NativeFamilyWire.Snapshot
  checked : Cursors

structure SnapshotPrefix (before after : NativeFamilyWire.Snapshot) : Prop where
  arena : Prefix before.arena after.arena
  definitions : before.definitions.IsPrefix after.definitions
  families : before.families.IsPrefix after.families

theorem SnapshotPrefix.trans (first : SnapshotPrefix before middle)
    (second : SnapshotPrefix middle after) : SnapshotPrefix before after :=
  ⟨first.arena.trans second.arena, first.definitions.trans second.definitions,
    first.families.trans second.families⟩

inductive ExtendError (ε : Type) where
  | inputGraph (reason : Error)
  | inference (reason : ε)
  | generatedGraph (reason : Error)

def extend (state : CheckState) (infer : NativeFamilyWire.Snapshot → Arena × Except ε Unit) :
    CheckState × Except (ExtendError ε) Unit :=
  match checkGraph state.snapshot.arena state.checked.nodes with
  | .error reason => (state, .error (.inputGraph reason))
  | .ok () =>
      let inferred := infer state.snapshot
      let snapshot := { state.snapshot with arena := inferred.1 }
      let after := { state with snapshot }
      match inferred.2 with
      | .error reason => (after, .error (.inference reason))
      | .ok () =>
          match checkGraph snapshot.arena state.snapshot.arena.size with
          | .error reason => (after, .error (.generatedGraph reason))
          | .ok () => ({ after with checked := Cursors.complete snapshot }, .ok ())

variable {ε : Type} {state : CheckState}
  {infer : NativeFamilyWire.Snapshot → Arena × Except ε Unit}

/-- Both suffixes are examined in order. The second scan starts at the
arena length recorded before inference. -/
theorem extend_ok_iff (state : CheckState)
    (infer : NativeFamilyWire.Snapshot → Arena × Except ε Unit) :
    (extend state infer).2 = .ok () ↔
      checkGraph state.snapshot.arena state.checked.nodes = .ok () ∧
      (infer state.snapshot).2 = .ok () ∧
      checkGraph (infer state.snapshot).1 state.snapshot.arena.size = .ok () := by
  cases first : checkGraph state.snapshot.arena state.checked.nodes with
  | error reason => simp [extend, first]
  | ok success =>
      cases success
      cases typed : (infer state.snapshot).2 with
      | error reason => simp [extend, first, typed]
      | ok success =>
          cases success
          cases generated : checkGraph (infer state.snapshot).1 state.snapshot.arena.size with
          | error reason => simp [extend, first, typed, generated]
          | ok success => cases success; simp [extend, first, typed, generated]

theorem extend_commit (succeeded : (extend state infer).2 = .ok ()) :
    let snapshot := { state.snapshot with arena := (infer state.snapshot).1 }
    (extend state infer).1 = ⟨snapshot, Cursors.complete snapshot⟩ := by
  obtain ⟨first, typed, generated⟩ := (extend_ok_iff _ _).mp succeeded
  simp [extend, first, typed, generated]

/-- A failed call leaves its three checked cursors unchanged, even when
inference has appended nodes before the error. -/
theorem extend_failure_keeps_checked (failed : (extend state infer).2 = .error reason) :
    (extend state infer).1.checked = state.checked := by
  cases first : checkGraph state.snapshot.arena state.checked.nodes with
  | error reason => simp [extend, first]
  | ok success =>
      cases success
      cases typed : (infer state.snapshot).2 with
      | error reason => simp [extend, first, typed]
      | ok success =>
          cases success
          cases generated : checkGraph (infer state.snapshot).1 state.snapshot.arena.size with
          | error reason => simp [extend, first, typed, generated]
          | ok success => cases success; simp [extend, first, typed, generated] at failed

/-- Both successful and failed calls preserve old node and declaration
positions when the inference arena grows by appending. -/
theorem extend_snapshot_prefix
    (appended : Prefix state.snapshot.arena (infer state.snapshot).1) :
    SnapshotPrefix state.snapshot (extend state infer).1.snapshot := by
  cases first : checkGraph state.snapshot.arena state.checked.nodes with
  | error reason => exact ⟨by simp [extend, first, Prefix.refl], by simp [extend, first],
      by simp [extend, first]⟩
  | ok success =>
      cases success
      cases typed : (infer state.snapshot).2 with
      | error reason => exact ⟨by simpa [extend, first, typed] using appended,
          by simp [extend, first, typed], by simp [extend, first, typed]⟩
      | ok success =>
          cases success
          cases generated : checkGraph (infer state.snapshot).1 state.snapshot.arena.size with
          | error reason => exact ⟨by simpa [extend, first, typed, generated] using appended,
              by simp [extend, first, typed, generated], by simp [extend, first, typed, generated]⟩
          | ok success =>
              cases success
              exact ⟨by simpa [extend, first, typed, generated] using appended,
                by simp [extend, first, typed, generated], by simp [extend, first, typed, generated]⟩

private theorem backward_prefix (preserved : Prefix before after) (valid : Backward after) :
    Backward before :=
  fun id node found => valid id node (preserved.lookup found)

/-- Under a previously checked immutable prefix, the two suffix inspections
establish exactly the same graph property as scanning the entire final
arena. This equivalence keeps the inference success premise explicit. -/
theorem extend_cached_ok_iff (state : CheckState)
    (infer : NativeFamilyWire.Snapshot → Arena × Except ε Unit)
    (preserved : SnapshotPrefix cached state.snapshot)
    (checked : state.checked = Cursors.complete cached)
    (cachedValid : Backward cached.arena)
    (appended : Prefix state.snapshot.arena (infer state.snapshot).1) :
    (extend state infer).2 = .ok () ↔
      (infer state.snapshot).2 = .ok () ∧
        (infer state.snapshot).1.size ≤ entryLimit ∧ Backward (infer state.snapshot).1 := by
  rw [extend_ok_iff, checked]
  change checkGraph state.snapshot.arena cached.arena.size = .ok () ∧ _ ∧ _ ↔ _
  rw [checkGraph_extend preserved.arena cachedValid]
  constructor
  · intro ⟨⟨_, inputValid⟩, typed, generated⟩
    exact ⟨typed, (checkGraph_extend appended inputValid).mp generated⟩
  · intro ⟨typed, cap, valid⟩
    have inputValid := backward_prefix appended valid
    exact ⟨⟨Nat.le_trans appended.size_le cap, inputValid⟩, typed,
      (checkGraph_extend appended inputValid).mpr ⟨cap, valid⟩⟩

private theorem prefix_lookup {before after : List α} {index : Nat}
    (preserved : before.IsPrefix after)
    (found : before[index]? = some value) : after[index]? = some value := by
  obtain ⟨suffix, rfl⟩ := preserved
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem decodeRoot_frame (preserved : Prefix before after)
    (decoded : NativeProgramWire.decodeRoot before roots = some definition) :
    NativeProgramWire.decodeRoot after roots = some definition := by
  cases type : decode 128 before roots.typeRoot <;>
    cases value : decode 128 before roots.valueRoot <;>
    simp [NativeProgramWire.decodeRoot, type, value] at decoded
  subst definition
  simp [NativeProgramWire.decodeRoot, decode_frame_exact type preserved,
    decode_frame_exact value preserved]

private theorem mapM_frame {original updated : α → Option β} {roots : List α}
    (preserved : ∀ {root term}, original root = some term → updated root = some term)
    (decoded : roots.mapM original = some terms) : roots.mapM updated = some terms := by
  induction roots generalizing terms with
  | nil => exact decoded
  | cons root roots ih =>
      cases head : original root <;>
        cases tail : roots.mapM original <;>
        simp [List.mapM_cons, head, tail] at decoded
      subst terms
      simp [List.mapM_cons, preserved head, ih tail]

private theorem decodeFamily_frame (preserved : Prefix before after)
    (decoded : NativeFamilyWire.decodeFamily before roots = some family) :
    NativeFamilyWire.decodeFamily after roots = some family := by
  cases constructors : roots.constructors.mapM (decode 128 before) with
  | none => simp [NativeFamilyWire.decodeFamily, constructors] at decoded
  | some terms =>
      simp [NativeFamilyWire.decodeFamily, constructors] at decoded
      subst family
      simp [NativeFamilyWire.decodeFamily,
        mapM_frame (fun h => decode_frame_exact h preserved) constructors]

/-- An earlier definition keeps its wire roots and exact decoded terms. -/
theorem SnapshotPrefix.definition_frame {index : Nat} (preserved : SnapshotPrefix before after)
    (found : before.definitions[index]? = some roots)
    (decoded : NativeProgramWire.decodeRoot before.arena roots = some definition) :
    after.definitions[index]? = some roots ∧
      NativeProgramWire.decodeRoot after.arena roots = some definition :=
  ⟨prefix_lookup preserved.definitions found, decodeRoot_frame preserved.arena decoded⟩

/-- An earlier family keeps its metadata and exact decoded constructor
telescope, including the declaration position of its dependencies. -/
theorem SnapshotPrefix.family_frame {index : Nat} (preserved : SnapshotPrefix before after)
    (found : before.families[index]? = some roots)
    (decoded : NativeFamilyWire.decodeFamily before.arena roots = some family) :
    after.families[index]? = some roots ∧
      NativeFamilyWire.decodeFamily after.arena roots = some family :=
  ⟨prefix_lookup preserved.families found, decodeFamily_frame preserved.arena decoded⟩

/-- Exact-byte acceptance of the cached snapshot supplies the earlier mixed
history. Its definition and constructor roots still decode to the same
checked sources after any append-only inference outcome. -/
theorem extend_frames_admitted_dependencies
    (accepted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel
      (NativeFamilyWire.encodeSnapshot cached) = true)
    (preserved : SnapshotPrefix cached state.snapshot)
    (appended : Prefix state.snapshot.arena (infer state.snapshot).1) :
    let snapshot := (extend state infer).1.snapshot
    ∃ definitions families env,
      SnapshotPrefix cached snapshot ∧
      cached.definitions.mapM (NativeProgramWire.decodeRoot snapshot.arena) = some definitions ∧
      cached.families.mapM (NativeFamilyWire.decodeFamily snapshot.arena) = some families ∧
      Environment.LoanTyping.MixedProgram.History definitions
        (families.map NativeLoanMixedAdmission.declaration) env ∧
      UnifiedProgram.EnvWellFormed env := by
  rw [NativeLoanMixedAdmission.checkBytes_encode] at accepted
  obtain ⟨definitions, families, env, decoded, history, wellFormed⟩ :=
    NativeLoanMixedAdmission.checkSnapshot_sound accepted
  have frame := preserved.trans (extend_snapshot_prefix appended)
  unfold NativeFamilyWire.decodeProgram at decoded
  split at decoded
  · contradiction
  · cases defs : cached.definitions.mapM (NativeProgramWire.decodeRoot cached.arena) <;>
      cases fams : cached.families.mapM (NativeFamilyWire.decodeFamily cached.arena) <;>
      simp [defs, fams] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    exact ⟨_, _, env, frame, mapM_frame (decodeRoot_frame frame.arena) defs,
      mapM_frame (decodeFamily_frame frame.arena) fams, history, wellFormed⟩

end Jihoo.NativeKernel.NativeCoreGraph
