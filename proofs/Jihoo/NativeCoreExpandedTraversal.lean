import Jihoo.NativeCoreBinderTraversal
import Jihoo.NativeCoreNestedAliases

/-! The same typed value and binder visits use independent conversion
evidence in dependent positions. Both visits follow authentic globals in
the current arena and preserve the original transparently expanded type. -/
namespace Jihoo.NativeKernel.NativeCoreExpandedTraversal

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress RefinesFor ExpandedNormalization GhostNormalization)
open NativeCoreValueContexts (Change signature)
open NativeCoreValueTraversal (Extension FrameRules)
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta (expand expandArgs expand_node_cons)

def ExpandedChange (env : Environment) (a b : Term) : Prop :=
  ∀ {ctx type}, LoanTyping.HasType env [] ctx true (expand env a) type →
    LoanTyping.HasType env [] ctx true (expand env b) type

private theorem on_expansion (wf : UnifiedProgram.EnvWellFormed env) (change : ExpandedChange env a b) :
    Change env (expand env a) (expand env b) := by
  refine ⟨fun typed => change typed, ?_⟩
  simp only [EnvironmentDelta.expand_idempotent wf.admissible]
  exact fun typed => change typed

private theorem on_expanded_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (change : ExpandedNormalization env a b) : GhostNormalization env (expand env a) (expand env b) := by
  refine ⟨change, ?_⟩
  simpa only [EnvironmentDelta.expand_idempotent wf.admissible] using change

private theorem expanded_operands (wf : UnifiedProgram.EnvWellFormed env)
    (moves : ListRel (ExpandedChange env) xs ys) :
    ListRel (Change env) (expandArgs env xs) (expandArgs env ys) := by
  induction moves with
  | nil => simp only [expandArgs]; exact .nil
  | cons head _ rest => simp only [expandArgs]; exact .cons (on_expansion wf head) rest

theorem frameRules (wf : UnifiedProgram.EnvWellFormed env) : FrameRules env (ExpandedChange env) where
  fromChange change := change.expanded
  trans first second := by
    intro ctx type typed
    exact second (first typed)
  strict a b := by
    simp only [ExpandedChange, expand_node_cons, expandArgs]
    exact (Change.strict (on_expansion wf a) (on_expansion wf b)).raw
  uniform := by
    intro op inputs xs ys found changes
    have ordinary : GlobalEnvironment.ordinary op = true := by
      cases op <;> first | rfl | contradiction
    unfold ExpandedChange
    rw [EnvironmentDelta.expand_ordinary ordinary, EnvironmentDelta.expand_ordinary ordinary]
    intro ctx type typed
    exact (Change.uniform found (expanded_operands wf changes)).raw typed

theorem binderRules (wf : UnifiedProgram.EnvWellFormed env) :
    NativeCoreBinderTraversal.Rules (ExpandedNormalization env) (ExpandedChange env) where
  same _ := by
    intro ctx type typed
    exact typed
  trans first second := by
    intro ctx type typed
    exact second (first typed)
  beta rest := by
    intro ctx type typed
    exact rest ((NativeCoreBinderPreservation.beta_change wf).expanded typed)
  strictApplication := by
    intro effect fn arg result rest ctx type typed
    have middle := NativeCoreBinderPreservation.strict_application_change.expanded typed
    simp only [expand_node_cons, expandArgs] at middle ⊢
    obtain ⟨_, effectTyped⟩ := NativeCoreValueContexts.strict_effect_typing middle
    obtain ⟨_, application, converted⟩ := middle.principalView
    have applied : LoanTyping.HasType env [] ctx true (expand env (.app fn arg)) type := by
      simp only [expand_node_cons, expandArgs]
      exact application.convert converted
    exact .strict effectTyped (rest applied)
  application f a := by
    simp only [ExpandedChange, expand_node_cons, expandArgs]
    exact (NativeCoreBinderPreservation.application_change wf (on_expansion wf f)
      (on_expanded_conversion wf a)).raw
  pi := by
    intro erased A A' B B' domain body
    simp only [ExpandedChange, expand_node_cons, expandArgs]
    exact (NativeCoreBinderPreservation.pi_change (erased := erased) wf
      (on_expanded_conversion wf domain) (on_expansion wf body)).raw
  lam := by
    intro erased A A' b b' domain body
    simp only [ExpandedChange, expand_node_cons, expandArgs]
    exact (NativeCoreBinderPreservation.lam_change (erased := erased) wf
      (on_expanded_conversion wf domain) (on_expansion wf body)).raw

def extensionWithRaw (rawAt : Nat → Nat → State → Nat → Outcome Nat) (roots : List Roots)
    (visible : Nat) : Extension :=
  let aliases := NativeCoreNestedAliases.extension roots visible
  let binders := NativeCoreBinderTraversal.extensionWithRaw rawAt
  { accepts := fun op => aliases.accepts op || binders.accepts op
    walk := fun visit limit depth root state op refs =>
      if aliases.accepts op then aliases.finish visit limit depth root state op refs
      else binders.walk visit limit depth root state op refs }

theorem extensionWithRaw_metered (roots : List Roots) (visible : Nat)
    (rawMetered : ∀ limit depth state root, Progress limit state (rawAt limit depth state root)) :
    (extensionWithRaw rawAt roots visible).Metered := by
  intro visit limit depth root state op refs accepted metered
  by_cases alias : (NativeCoreNestedAliases.extension roots visible).accepts op = true
  · simp only [extensionWithRaw, ite_eq_left alias]
    exact NativeCoreNestedAliases.extension_metered roots visible (depth := depth) alias metered
  · simp only [extensionWithRaw, ite_eq_right alias]
    exact NativeCoreBinderTraversal.extensionWithRaw_metered rawMetered
      (by simpa [extensionWithRaw, alias] using accepted) metered

theorem extensionWithRaw_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions)
    (rawSound : ∀ limit depth, NativeCoreBinderTraversal.VisitsFrom base (ExpandedNormalization env) (rawAt limit depth)) :
    (extensionWithRaw rawAt roots visible).SoundFrom base (ExpandedChange env) := by
  intro visit limit depth root state op refs terms selected accepted onBase read represented arity visitor success
  by_cases alias : (NativeCoreNestedAliases.extension roots visible).accepts op = true
  · simp only [extensionWithRaw, ite_eq_left alias] at success ⊢
    have transfer {input middle output} (same : expand env input = expand env middle)
        (step : ExpandedChange env middle output) : ExpandedChange env input output := by
      intro ctx type typed
      rw [same] at typed
      exact step typed
    have sound : (NativeCoreNestedAliases.extension roots visible).SoundFrom base (ExpandedChange env) :=
      NativeCoreNestedAliases.extension_soundFor (relation := ExpandedChange env) (visible := visible)
        history aligned (fun same step => transfer same step)
    exact sound alias onBase read represented arity visitor success
  · simp only [extensionWithRaw, ite_eq_right alias] at success ⊢
    exact NativeCoreBinderTraversal.extensionWithRaw_sound (binderRules history.wellFormed) rawSound
      (by simpa [extensionWithRaw, alias] using accepted) onBase read represented arity visitor success

def extension (roots : List Roots) (visible : Nat) : Extension :=
  extensionWithRaw (NativeCoreNestedAliases.run roots visible) roots visible

theorem extension_metered (roots : List Roots) (visible : Nat) : (extension roots visible).Metered :=
  extensionWithRaw_metered roots visible (NativeCoreNestedAliases.run_progress roots visible)

theorem extension_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) : (extension roots visible).SoundFrom base (ExpandedChange env) := by
  apply extensionWithRaw_sound history aligned
  intro limit depth state root input selected onBase represented accepted
  obtain ⟨kept, backward, value⟩ := NativeCoreNestedAliases.run_refines history aligned onBase represented accepted
  exact ⟨kept, backward, value⟩

def run (env : Environment) (roots : List Roots) (visible limit : Nat) : Nat → State → Nat → Outcome Nat :=
  NativeCoreValueTraversal.runWithFallback (extension roots visible)
    (NativeCoreNestedAliases.run roots visible limit) env limit

theorem run_progress (env : Environment) (roots : List Roots) (visible limit depth : Nat)
    (state : State) (root : Nat) : Progress limit state (run env roots visible limit depth state root) :=
  NativeCoreValueTraversal.runWithFallback_progress (extension_metered roots visible)
    (NativeCoreNestedAliases.run_progress roots visible limit) env depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root input)
    (success : (run env roots visible limit depth state root).result = .ok selected) :
    RefinesFor (ExpandedChange env) state input (run env roots visible limit depth state root) selected := by
  apply NativeCoreValueTraversal.runWithFallback_refines (frameRules history.wellFormed)
    (extension_sound history aligned) _ onBase source success
  intro depth state root input selected initial source done
  obtain ⟨kept, backward, residual, held, step⟩ := NativeCoreNestedAliases.run_refines history aligned initial source done
  exact ⟨kept, backward, residual, held, step.preserves⟩

/-- Every recursive visit uses the selected definition's authentic earlier
prefix and keeps its original expanded checked type. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run env snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, changed⟩ := run_refines history aligned (.refl _) source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, changed typed⟩

namespace Examples

private def global (index : Nat) : Term := .node (.global index) []
private def five : Term := .integer 5
private def eight : Term := .integer 8
private def function (type factor : Term) : Term :=
  .lam false type (.arith .mul (.var 0) factor)
private def source (factor callee argument : Term) : Term := .strict (.arith .add factor factor) (.app callee argument)
private def definitions : List GlobalDeclaration :=
  [⟨.univ 0, .i64⟩, ⟨global 0, five⟩, ⟨global 0, eight⟩, ⟨global 0, global 2⟩,
    ⟨.pi false (global 0) (global 0), function (global 0) (global 1)⟩,
    ⟨global 0, source (global 1) (global 4) (global 3)⟩]
private def env : Environment :=
  ⟨#[⟨.univ 0, .i64⟩, ⟨.i64, five⟩, ⟨.i64, eight⟩, ⟨.i64, eight⟩,
    ⟨.pi false .i64 .i64, function .i64 five⟩, ⟨.i64, source five (function .i64 five) eight⟩], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨0, 1⟩, ⟨2, 3⟩, ⟨2, 4⟩, ⟨2, 5⟩, ⟨10, 9⟩, ⟨2, 15⟩]
  families := []
  arena := #[.node (.universe 0) [], .node .i64 [], .node (.global 0) [], .node (.integer 5) [],
    .node (.integer 8) [], .node (.global 2) [], .var 0, .node (.global 1) [],
    .node (.arith .mul) [6, 7], .node (.lam false) [2, 8], .node (.pi false) [2, 2],
    .node (.global 4) [], .node (.global 3) [], .node .app [11, 12], .node (.arith .add) [7, 7],
    .node .strict [14, 13]]

private def start : State := ⟨snapshot.arena, 0⟩
private def committed : Arena := #[.node (.integer 10) [], .node (.arith .mul) [6, 3],
  .node (.lam false) [1, 17], .node (.arith .mul) [4, 3]]
private def finished : Arena := (snapshot.arena ++ committed).push (.node (.integer 40) [])

/-- The callee and its arithmetic body use the typed visitor; the universe
annotation and argument use the conversion visitor. Both follow globals
through the same growing arena before beta reentry folds the product. -/
theorem checked_delta_through_typed_beta :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env snapshot.definitions 5 25 20 start 15 = ⟨⟨finished, 25⟩, .ok 20⟩ ∧
    LoanTyping.HasType env [] [] true (.integer 40) .i64 := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have observed : run env snapshot.definitions 5 25 20 start 15 = ⟨⟨finished, 25⟩, .ok 20⟩ := by cbv
  have history : LoanTyping.MixedProgram.History definitions [] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have found : snapshot.definitions[5]? = some ⟨2, 15⟩ := rfl
  obtain ⟨entry, _, lookup, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  have same : entry = ⟨.i64, source five (function .i64 five) eight⟩ := Option.some.inj (lookup.symm.trans rfl)
  subst entry
  obtain ⟨_, _, residual, held, change⟩ := run_refines history aligned (.refl _) represented.2
    (congrArg Outcome.result observed)
  rw [observed] at held
  have exactResult : Represents finished 20 (.integer 40) := decode_sound (fuel := 2) rfl
  have result := change typed
  rw [held.unique exactResult] at result
  exact ⟨admitted, observed, by simpa only [expand, expandArgs] using result⟩

theorem budget_and_visibility_keep_committed_rows :
    run env snapshot.definitions 5 24 20 start 15 =
      ⟨⟨snapshot.arena ++ committed, 25⟩, .error (.tick (.stepLimit 3))⟩ ∧
    run env snapshot.definitions 4 25 20 start 15 =
      ⟨⟨snapshot.arena.push (.node (.integer 10) []), 8⟩, .error (.invisibleGlobal 11)⟩ := by
  constructor <;> cbv

end Examples

end Jihoo.NativeKernel.NativeCoreExpandedTraversal
