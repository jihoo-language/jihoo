import Jihoo.NativeCorePureComputationNormal

/-! Delta is a recursive visit of the authentic earlier definition's raw
graph root. Every such visit preserves the exact expanded term used to
check the program, even after the arena has grown. -/
namespace Jihoo.NativeKernel.NativeCoreNestedAliases

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress EarlyExtension ExpandedNormalization RefinesFor
  runWithEarlyExtension runWithEarlyExtension_progress runWithEarlyExtension_refinesFrom expandedRules)

theorem frame_definitions (aligned : RepresentsDefinitions base roots definitions)
    (kept : Prefix base arena) : RepresentsDefinitions arena roots definitions := by
  induction aligned with
  | nil => exact .nil
  | cons row _ ih => exact .cons ⟨row.1.frame kept, row.2.frame kept⟩ ih

/-- The root tick has already been charged by the shared driver. A
visible definition reuses its existing raw value reference. -/
def follow (roots : List Roots) (visible : Nat) (visit : State → Nat → Outcome Nat)
    (state : State) (root index : Nat) : Outcome Nat :=
  if index < visible then
    match roots[index]? with
    | some row => visit state row.valueRoot
    | none => ⟨state, .error (.outsideFragment root)⟩
  else ⟨state, .error (.invisibleGlobal root)⟩

def extension (roots : List Roots) (visible : Nat) : EarlyExtension where
  accepts
    | .global _ => true
    | _ => false
  finish visit _ _ root state op refs :=
    match op with
    | .global index =>
        match refs with
        | [] => follow roots visible visit state root index
        | _ => ⟨state, .error (.outsideFragment root)⟩
    | _ => ⟨state, .error (.outsideFragment root)⟩

theorem follow_progress (metered : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (follow roots visible visit state root index) := by
  unfold follow
  split
  · split
    · exact metered _ _
    · exact Progress.atState _ _
  · exact Progress.atState _ _

theorem extension_metered (roots : List Roots) (visible : Nat) : (extension roots visible).Metered := by
  intro visit limit depth root state op refs accepted metered
  cases op <;> try contradiction
  case global index =>
    cases refs
    · exact follow_progress metered
    · exact Progress.atState _ _

theorem follow_relates (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (.global index) []))
    (transfer : ∀ {input middle output}, EnvironmentDelta.expand env input = EnvironmentDelta.expand env middle →
      relation middle output → relation input output)
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      RefinesFor relation state term (visit state ref) selected)
    (success : (follow roots visible visit state root index).result = .ok selected) :
    RefinesFor relation state (.node (.global index) []) (follow roots visible visit state root index) selected := by
  by_cases enabled : index < visible
  · cases found : roots[index]? with
    | none => simp [follow, enabled, found] at success
    | some row =>
        simp only [follow, enabled, ite_true, found] at success ⊢
        obtain ⟨body, bodyRep, expanded⟩ := NativeCoreGlobalNormal.alias_target
          (frame_definitions aligned onBase) history (.node read rfl .nil) read rfl found
        obtain ⟨kept, backward, residual, held, typed⟩ := visitor onBase bodyRep success
        exact ⟨kept, backward, residual, held, transfer expanded typed⟩
  · simp [follow, enabled] at success

theorem follow_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (read : state.arena[root]? = some (.node (.global index) []))
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected →
      RefinesFor (ExpandedNormalization env) state term (visit state ref) selected)
    (success : (follow roots visible visit state root index).result = .ok selected) :
    RefinesFor (ExpandedNormalization env) state (.node (.global index) [])
      (follow roots visible visit state root index) selected :=
  follow_relates (relation := ExpandedNormalization env) history aligned onBase read
    (fun same proof => by simpa only [ExpandedNormalization, same] using proof) visitor success

theorem extension_soundFor (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions)
    (transfer : ∀ {input middle output}, EnvironmentDelta.expand env input = EnvironmentDelta.expand env middle →
      relation middle output → relation input output) :
    (extension roots visible).SoundFrom base relation := by
  intro visit limit depth root state op refs terms selected accepts onBase read represented size visitor success
  cases op <;> try contradiction
  case global index =>
    cases represented with
    | nil => exact follow_relates history aligned onBase read transfer visitor success
    | cons => cases size

theorem extension_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    (extension roots visible).SoundFrom base (ExpandedNormalization env) :=
  extension_soundFor (relation := ExpandedNormalization env) history aligned
    (fun same proof => by simpa only [ExpandedNormalization, same] using proof)

def run (roots : List Roots) (visible limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runWithEarlyExtension (extension roots visible) limit depth state root

theorem run_progress (roots : List Roots) (visible limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run roots visible limit depth state root) :=
  runWithEarlyExtension_progress (extension_metered roots visible) limit depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root term)
    (success : (run roots visible limit depth state root).result = .ok selected) :
    RefinesFor (ExpandedNormalization env) state term (run roots visible limit depth state root) selected :=
  runWithEarlyExtension_refinesFrom (expandedRules history.wellFormed)
    (extension_sound history aligned) onBase source success

/-- Use exactly the earlier global prefix of an admitted definition at
every recursive visit, including under binders and after substitution. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, transformed⟩ := run_refines history aligned (.refl _) source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, transformed.typed typed⟩

namespace Examples

private def global (index : Nat) : Term := .node (.global index) []
private def seven : Term := .natural 7
private def signature (annotation : Term) : Term := .pi false annotation (.eq (.var 0) (.var 0))
private def proofFunction (annotation discriminant : Term) : Term :=
  .lam false annotation (.ifEq discriminant seven (.refl (.var 1)) (.refl (.var 0)))

private def definitions : List GlobalDeclaration :=
  [⟨.univ 0, .u64⟩, ⟨global 0, seven⟩, ⟨global 0, global 1⟩,
    ⟨signature (global 0), proofFunction (global 0) (global 2)⟩, ⟨.eq (global 2) (global 2), .app (global 3) (global 2)⟩]

private def env : Environment :=
  ⟨#[⟨.univ 0, .u64⟩, ⟨.u64, seven⟩, ⟨.u64, seven⟩, ⟨signature .u64, proofFunction .u64 seven⟩,
    ⟨.eq seven seven, .app (proofFunction .u64 seven) seven⟩], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1, 0⟩, ⟨3, 2⟩, ⟨3, 4⟩, ⟨9, 13⟩, ⟨15, 16⟩]
  families := []
  arena := #[.node .u64 [], .node (.universe 0) [], .node (.natural 7) [], .node (.global 0) [],
    .node (.global 1) [], .node (.global 2) [], .var 0, .var 1, .node .eq [6, 6],
    .node (.pi false) [3, 8], .node .refl [7], .node .refl [6], .node .ifEq [5, 2, 10, 11],
    .node (.lam false) [3, 12], .node (.global 3) [], .node .eq [5, 5], .node .app [14, 5]]

private def start : State := ⟨snapshot.arena, 0⟩
private def newRows : Arena :=
  #[.node .refl [2], .var 0, .node .refl [18], .node (.lam false) [0, 19], .node .refl [2]]

/-- A checked application follows a function global, its universe-valued
annotation and its conditional discriminant, then independently follows the
argument's alias. All rewrites share the clock and committed arena. -/
theorem checked_aliases_inside_application :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run snapshot.definitions 4 64 24 start 16 = ⟨⟨snapshot.arena ++ newRows, 22⟩, .ok 21⟩ ∧
    LoanTyping.HasType env [] [] true (.refl seven) (.eq seven seven) := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have computed : run snapshot.definitions 4 64 24 start 16 = ⟨⟨snapshot.arena ++ newRows, 22⟩, .ok 21⟩ := by cbv
  have history : LoanTyping.MixedProgram.History definitions [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have found : snapshot.definitions[4]? = some ⟨15, 16⟩ := rfl
  obtain ⟨entry, raw, lookup, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  have equality : entry = ⟨.eq seven seven, .app (proofFunction .u64 seven) seven⟩ :=
    Option.some.inj (lookup.symm.trans rfl)
  subst entry
  obtain ⟨_, _, residual, held, changed⟩ := run_refines history aligned (.refl _) represented.2
    (congrArg Outcome.result computed)
  rw [computed] at held
  have expected : Represents (snapshot.arena ++ newRows) 21 (.refl seven) := decode_sound (fuel := 3) rfl
  have result := changed.typed typed
  rw [held.unique expected] at result
  refine ⟨admitted, computed, ?_⟩
  simpa only [seven, EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using result

/-- The callee's unresolved alias is rejected before visiting its argument. -/
theorem nested_visibility_rejects_before_operands :
    run snapshot.definitions 3 64 24 start 16 = ⟨⟨snapshot.arena, 2⟩, .error (.invisibleGlobal 14)⟩ := by cbv

end Examples

end Jihoo.NativeKernel.NativeCoreNestedAliases
