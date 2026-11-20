import Jihoo.NativeCoreBinderPreservation
import Jihoo.NativeCoreValueAliases

/-! A typed recursive visitor under Pi and Lam, through ordinary pure
application, and through the native application of a Strict function. -/
namespace Jihoo.NativeKernel.NativeCoreBinderTraversal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCoreValueContexts (Change)
open NativeCoreValueTraversal (Extension Refines emptyPrefix)
open NativeCoreBinderPreservation (pi_change lam_change application_change beta_change strict_application_change)
open NativeCorePureComputationNormal (Outcome Progress GhostNormalization nodeResult nodeResult_exact
  nodeResult_progress finishApplication finishApplication_progress finishApplication_relatesFrom RefinesFor)
open NativeCoreCaseStrict (append append_refines append_progress)

abbrev VisitsFrom (base : Arena) (relation : Term → Term → Prop) (visit : State → Nat → Outcome Nat) : Prop :=
  ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term → (visit state ref).result = .ok selected →
    let output := visit state ref
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ relation term residual

abbrev Visits (relation : Term → Term → Prop) (visit : State → Nat → Outcome Nat) : Prop :=
  ∀ {state ref term selected}, Represents state.arena ref term → (visit state ref).result = .ok selected →
    let output := visit state ref
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧ relation term residual

structure Rules (converted changed : Term → Term → Prop) : Prop where
  same : ∀ term, changed term term
  trans : ∀ {a b c}, changed a b → changed b c → changed a c
  beta : ∀ {erased domain body argument result}, changed (body.subst (single argument)) result →
    changed (.app (.lam erased domain body) argument) result
  strictApplication : ∀ {effect fn arg result}, changed (.app fn arg) result →
    changed (.app (.strict effect fn) arg) (.strict effect result)
  application : ∀ {f f' a a'}, changed f f' → converted a a' → changed (.app f a) (.app f' a')
  pi : ∀ {erased A A' B B'}, converted A A' → changed B B' → changed (.pi erased A B) (.pi erased A' B')
  lam : ∀ {erased A A' b b'}, converted A A' → changed b b' → changed (.lam erased A b) (.lam erased A' b')

private theorem rules (wf : UnifiedProgram.EnvWellFormed env) : Rules (GhostNormalization env) (Change env) :=
  ⟨fun _ => ⟨id, id⟩, Change.trans, fun rest => (beta_change wf).trans rest,
    fun rest => strict_application_change.trans (Change.strict ⟨id, id⟩ rest),
    application_change wf, pi_change wf, lam_change wf⟩

private def operands (first second : State → Nat → Outcome Nat) (state : State) (a b : Nat) :
    Outcome (Nat × Nat) :=
  (first state a).next fun after a' =>
    (second after b).next fun after b' => ⟨after, .ok (a', b')⟩

private theorem operands_progress (first : ∀ state ref, Progress limit state (visitFirst state ref))
    (second : ∀ state ref, Progress limit state (visitSecond state ref)) :
    Progress limit state (operands visitFirst visitSecond state a b) :=
  (first _ _).next (fun _ => (second _ _).next (fun _ => Progress.atState _ _))

private theorem operands_relates (onBase : Prefix base state.arena)
    (first : VisitsFrom base leftRelation left) (second : VisitsFrom base rightRelation right)
    (aRep : Represents state.arena a inputA) (bRep : Represents state.arena b inputB)
    (success : (operands left right state a b).result = .ok (a', b')) :
    let output := operands left right state a b
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ outA outB, Represents output.state.arena a' outA ∧ Represents output.state.arena b' outB ∧
        leftRelation inputA outA ∧ rightRelation inputB outB := by
  unfold operands at success ⊢
  obtain ⟨selectedA, foundA, visitsA⟩ := Outcome.next_success success
  rw [visitsA] at success ⊢
  obtain ⟨selectedB, foundB, visitsB⟩ := Outcome.next_success success
  rw [visitsB] at success ⊢
  have same : (selectedA, selectedB) = (a', b') := Except.ok.inj success
  cases same
  obtain ⟨firstKept, firstBackward, outA, leftRep, leftChange⟩ := first onBase aRep foundA
  obtain ⟨secondKept, secondBackward, outB, rightRep, rightChange⟩ := second (onBase.trans firstKept) (bRep.frame firstKept) foundB
  exact ⟨firstKept.trans secondKept, fun old => secondBackward (firstBackward old), outA, outB,
    leftRep.frame secondKept, rightRep, leftChange, rightChange⟩

private theorem binary (represented : RepresentsList arena refs terms) (size : refs.length = 2) :
    ∃ a b x y, refs = [a, b] ∧ terms = [x, y] ∧ Represents arena a x ∧ Represents arena b y := by
  cases represented with
  | nil => cases size
  | cons first rest =>
      cases rest with
      | nil => cases size
      | cons second rest =>
          cases rest with
          | nil => exact ⟨_, _, _, _, rfl, rfl, first, second⟩
          | cons => cases size

private def applyUnderStrict (visit : State → Nat → Outcome Nat) (state : State)
    (effect function argument : Nat) : Outcome Nat :=
  (append state .app [function, argument]).next fun after applied =>
    (visit after applied).next fun after result => append after .strict [effect, result]

private theorem applyUnderStrict_progress (visitor : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (applyUnderStrict visit state effect f a) :=
  (append_progress _ _ _).next (fun _ => (visitor _ _).next (fun _ => append_progress _ _ _))

private theorem applyUnderStrict_refines (rules : Rules converted changed) (onBase : Prefix base state.arena)
    (visitor : VisitsFrom base changed visit)
    (effectRep : Represents state.arena effect effectTerm) (functionRep : Represents state.arena f function)
    (argumentRep : Represents state.arena a argument)
    (success : (applyUnderStrict visit state effect f a).result = .ok selected) :
    RefinesFor changed state (.app (.strict effectTerm function) argument) (applyUnderStrict visit state effect f a) selected := by
  unfold applyUnderStrict at success ⊢
  obtain ⟨inner, assembled, commits⟩ := Outcome.next_success success
  rw [commits] at success ⊢
  obtain ⟨kept, backward, applied⟩ := append_refines (.cons functionRep (.cons argumentRep .nil)) rfl assembled
  obtain ⟨result, visited, continues⟩ := Outcome.next_success success
  rw [continues] at success ⊢
  obtain ⟨later, preserved, output, held, step⟩ := visitor (onBase.trans kept) applied visited
  obtain ⟨last, saved, exactResult⟩ :=
    append_refines (.cons (effectRep.frame (kept.trans later)) (.cons held .nil)) rfl success
  exact ⟨kept.trans (later.trans last), fun old => saved (preserved (backward old)), _, exactResult,
    rules.strictApplication step⟩

private def finishApp (visit : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (before : List Nat) (f a : Nat) : Outcome Nat :=
  match state.arena[f]? with
  | some (.node .strict [effect, function]) => applyUnderStrict visit state effect function a
  | _ => finishApplication visit limit depth root state before [f, a]

private theorem finishApp_progress (visitor : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (finishApp visit limit depth root state before f a) := by
  unfold finishApp
  split
  · exact applyUnderStrict_progress visitor
  · exact finishApplication_progress visitor _ _ _

private theorem finishApp_refines (rules : Rules converted changed) (onBase : Prefix base state.arena)
    (visitor : VisitsFrom base changed visit)
    (read : state.arena[root]? = some (.node .app before))
    (function : Represents state.arena f fTerm) (argument : Represents state.arena a aTerm)
    (success : (finishApp visit limit depth root state before f a).result = .ok selected) :
    RefinesFor changed state (.app fTerm aTerm) (finishApp visit limit depth root state before f a) selected := by
  unfold finishApp at success ⊢
  split at success
  · rename_i effect functionRef chosen
    have shaped : ∃ effectTerm callee, fTerm = .strict effectTerm callee ∧
        Represents state.arena effect effectTerm ∧ Represents state.arena functionRef callee := by
      cases function with
      | var found => simp [found] at chosen
      | node found arity children =>
          rw [found] at chosen
          cases chosen
          obtain ⟨_, _, _, _, refs, rfl, left, right⟩ := binary children arity
          cases refs
          exact ⟨_, _, rfl, left, right⟩
    obtain ⟨_, _, rfl, effectRep, functionRep⟩ := shaped
    exact applyUnderStrict_refines rules onBase visitor effectRep functionRep argument success
  · obtain ⟨kept, backward, value⟩ := finishApplication_relatesFrom (relation := changed) onBase read function argument
      visitor rules.same rules.beta success
    exact ⟨kept, backward, value⟩

private def walkApp (visit raw : State → Nat → Outcome Nat) (limit depth root : Nat)
    (state : State) (f a : Nat) : Outcome Nat :=
  (operands visit raw state f a).next fun after found =>
    finishApp visit limit depth root after [f, a] found.1 found.2

private theorem walkApp_refines (rules : Rules converted changed) (onBase : Prefix base state.arena)
    (visitor : VisitsFrom base changed visit) (rawVisitor : VisitsFrom base converted raw)
    (read : state.arena[root]? = some (.node .app [f, a]))
    (fRep : Represents state.arena f fTerm) (aRep : Represents state.arena a aTerm)
    (success : (walkApp visit raw limit depth root state f a).result = .ok selected) :
    RefinesFor changed state (.app fTerm aTerm) (walkApp visit raw limit depth root state f a) selected := by
  unfold walkApp at success ⊢
  obtain ⟨⟨callee, operand⟩, found, continues⟩ := Outcome.next_success success
  rw [continues] at success ⊢
  obtain ⟨kept, backward, newFun, newArg, calleeRep, argRep, funChange, argChange⟩ :=
    operands_relates onBase visitor rawVisitor fRep aRep found
  obtain ⟨later, preserves, result, resultRep, step⟩ :=
    finishApp_refines rules (onBase.trans kept) visitor (kept.lookup read) calleeRep argRep success
  exact ⟨kept.trans later, fun old => preserves (backward old), result, resultRep,
    rules.trans (rules.application funChange argChange) step⟩

private def walkBinder (visit raw : State → Nat → Outcome Nat) (root : Nat) (state : State)
    (op : Op) (domain body : Nat) : Outcome Nat :=
  (operands raw visit state domain body).next fun after found =>
    nodeResult after root op [domain, body] [found.1, found.2]

private theorem walkBinder_progress
    (visitor : ∀ state ref, Progress limit state (visit state ref))
    (rawVisitor : ∀ state ref, Progress limit state (raw state ref)) :
    Progress limit state (walkBinder visit raw root state op domain body) := by
  unfold walkBinder
  apply (operands_progress rawVisitor visitor).next
  intro found
  exact nodeResult_progress _ _ _ _ _ _

private theorem walkBinder_refines
    (make : ∀ {A A' b b'}, converted A A' → changed b b' →
      changed (.node op [A, b]) (.node op [A', b']))
    (onBase : Prefix base state.arena)
    (visitor : VisitsFrom base changed visit) (rawVisitor : VisitsFrom base converted raw)
    (size : op.arity = 2) (read : state.arena[root]? = some (.node op [domain, body]))
    (dRep : Represents state.arena domain A) (bRep : Represents state.arena body b)
    (success : (walkBinder visit raw root state op domain body).result = .ok selected) :
    RefinesFor changed state (.node op [A, b]) (walkBinder visit raw root state op domain body) selected := by
  unfold walkBinder at success ⊢
  obtain ⟨⟨annotation, value⟩, found, continues⟩ := Outcome.next_success success
  rw [continues] at success ⊢
  obtain ⟨kept, backward, newDomain, newBody, annotationRep, valueRep, domainChange, bodyChange⟩ :=
    operands_relates onBase rawVisitor visitor dRep bRep found
  obtain ⟨later, preserved, held⟩ := nodeResult_exact (kept.lookup read)
    (.cons annotationRep (.cons valueRep .nil)) size.symm success
  exact ⟨kept.trans later, fun old => preserved (backward old), _, held, make domainChange bodyChange⟩

private def withPair (state : State) (root : Nat) (visit : Nat → Nat → Outcome Nat) : List Nat → Outcome Nat
  | [a, b] => visit a b
  | _ => ⟨state, .error (.outsideFragment root)⟩

private theorem withPair_progress (visitor : ∀ a b, Progress limit state (visit a b)) :
    Progress limit state (withPair state root visit refs) := by
  unfold withPair
  split
  · exact visitor _ _
  · exact Progress.atState _ _

def extensionWithRaw (rawAt : Nat → Nat → State → Nat → Outcome Nat) : Extension where
  accepts
    | .app | .pi _ | .lam _ => true
    | _ => false
  walk visit limit depth root state op refs :=
    let raw := rawAt limit depth
    match op with
    | .app => withPair state root (walkApp visit raw limit depth root state) refs
    | .pi erased => withPair state root (walkBinder visit raw root state (.pi erased)) refs
    | .lam erased => withPair state root (walkBinder visit raw root state (.lam erased)) refs
    | _ => ⟨state, .error (.outsideFragment root)⟩

theorem extensionWithRaw_metered (metered : ∀ limit depth state root, Progress limit state (rawAt limit depth state root)) :
    (extensionWithRaw rawAt).Metered := by
  intro visit limit depth root state op refs accepted visitor
  have raw := metered limit depth
  cases op <;> try contradiction
  case app =>
    apply withPair_progress
    intro f a
    unfold walkApp
    apply (operands_progress visitor raw).next
    intro found
    exact finishApp_progress visitor
  case pi | lam =>
    exact withPair_progress (fun _ _ => walkBinder_progress visitor raw)

theorem extensionWithRaw_sound (rules : Rules converted changed)
    (rawVisitor : ∀ limit depth, VisitsFrom base converted (rawAt limit depth)) :
    (extensionWithRaw rawAt).SoundFrom base changed := by
  intro visit limit depth root state op refs terms selected accepted onBase read represented arity visitor success
  have raw : VisitsFrom base converted (rawAt limit depth) := rawVisitor limit depth
  have visits : VisitsFrom base changed visit := by
    intro _ _ _ _ prior source done
    obtain ⟨kept, backward, value⟩ := visitor prior source done
    exact ⟨kept, backward, value⟩
  cases op <;> try contradiction
  case app =>
    obtain ⟨_, _, _, _, rfl, rfl, funRep, argRep⟩ := binary represented arity
    exact walkApp_refines rules onBase visits raw read funRep argRep success
  case pi erased =>
    obtain ⟨_, _, _, _, rfl, rfl, domain, body⟩ := binary represented arity
    exact walkBinder_refines (rules.pi (erased := erased)) onBase visits raw rfl read domain body success
  case lam erased =>
    obtain ⟨_, _, _, _, rfl, rfl, domain, body⟩ := binary represented arity
    exact walkBinder_refines (rules.lam (erased := erased)) onBase visits raw rfl read domain body success

def extension (env : Environment) (families : List NativeFamilyWire.FamilyRoots) : Extension :=
  extensionWithRaw (NativeCoreIterationReentry.runNested env families)

theorem extension_metered (env : Environment) (families : List NativeFamilyWire.FamilyRoots) :
    (extension env families).Metered :=
  extensionWithRaw_metered (NativeCoreIterationReentry.runNested_progress env families)

theorem extension_sound {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env) :
    (extension env families).Sound env := by
  have raw (limit depth : Nat) :
      VisitsFrom #[] (GhostNormalization env) (NativeCoreIterationReentry.runNested env families limit depth) := by
    intro _ _ _ _ _ input done
    obtain ⟨kept, backward, value⟩ := NativeCoreIterationReentry.runNested_refines history input done
    exact ⟨kept, backward, value⟩
  intro visit limit depth root state op refs terms selected accepted read represented arity visitor success
  exact extensionWithRaw_sound (rules history.wellFormed) raw accepted (emptyPrefix _) read
    represented arity (fun _ input done => visitor input done) success

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  NativeCoreValueTraversal.runWith (extension env families) env families limit depth state root

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Progress limit state (run env families limit depth state root) :=
  NativeCoreValueTraversal.runWith_progress (extension_metered env families) env families limit depth state root

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root input) (success : (run env families limit depth state root).result = .ok selected) :
    Refines env state input (run env families limit depth state root) selected :=
  NativeCoreValueTraversal.runWith_refines (extension_sound history) history source success

/-- Dispatch a chain of transparent definitions before entering the
recursive value and binder visitor with its exact remaining depth. -/
def runThroughAliases (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (roots : List NativeProgramWire.Roots) (visible limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  NativeCoreValueAliases.runWith (run env families limit) roots visible limit depth state root

theorem runThroughAliases_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots)
    (roots : List NativeProgramWire.Roots) (visible limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (runThroughAliases env families roots visible limit depth state root) :=
  NativeCoreValueAliases.runWith_progress (run_progress env families limit)

/-- Recover and retain the declaration type from exact-byte mixed
admission during normalization through the covered function positions. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : NativeProgramWire.Roots},
        snapshot.definitions[index]? = some row →
        (runThroughAliases env snapshot.families snapshot.definitions index limit depth
          ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := runThroughAliases env snapshot.families snapshot.definitions index limit depth
          ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, typedVisit⟩ := NativeCoreValueAliases.runWith_refines
    (visit := run env snapshot.families limit) aligned history (fun rep done => run_refines history rep done)
    source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, typedVisit (typed.ghost [])⟩

namespace Examples

private def smallSum : Term := .arith .add (.integer 1) (.integer 2)
private def overflow : Term := .arith .add (.integer (2^63-1)) (.integer 1)
private def seven : Term := .natural 7
private def argument : Term := .app (.lam false .u64 (.var 0)) seven
private def function : Term := .lam false .u64 (.strict smallSum (.refl (.var 0)))
private def application : GlobalDeclaration := ⟨.eq argument argument, .app function argument⟩
private def wrapped : GlobalDeclaration := ⟨.eq argument argument, .app (.strict overflow function) argument⟩
private def domain : Term := .app (.lam false .u64 .u64) seven
private def quantifier : GlobalDeclaration := ⟨.prop, .pi false domain (.eq (.strict smallSum (.var 0)) (.var 0))⟩
private def env : Environment := ⟨#[application, wrapped, quantifier], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨12, 13⟩, ⟨12, 17⟩, ⟨1, 22⟩]
  families := []
  arena := #[.node .u64 [], .node .prop [], .var 0, .node (.integer 1) [], .node (.integer 2) [],
    .node (.natural 7) [], .node (.arith .add) [3, 4], .node .refl [2], .node .strict [6, 7],
    .node (.lam false) [0, 8], .node (.lam false) [0, 2], .node .app [10, 5], .node .eq [11, 11],
    .node .app [9, 11], .node (.integer (2^63-1)) [], .node (.arith .add) [14, 3],
    .node .strict [15, 9], .node .app [16, 11], .node (.lam false) [0, 0],
    .node .app [18, 5], .node .strict [6, 2], .node .eq [20, 2], .node (.pi false) [19, 21]]

private def start : State := ⟨snapshot.arena, 0⟩
private def functionRows : Arena := #[.node (.integer 3) [], .node (.lam false) [0, 7]]
private def appliedArena := (snapshot.arena ++ functionRows).push (.node .refl [5])
private def wrappedRows : Arena := #[.node .strict [15, 24], .node .app [24, 5], .node .refl [5],
  .node .strict [15, 27]]
private def wrappedArena := snapshot.arena ++ functionRows ++ wrappedRows
private def quantifierRows : Arena := #[.node (.integer 3) [], .node .eq [2, 2], .node (.pi false) [0, 24]]
private def quantifierArena := snapshot.arena ++ quantifierRows

private theorem checkedHistory : LoanTyping.MixedProgram.History [application, wrapped, quantifier] [] env :=
  LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)

/-- The lambda body loses a nontrapping Strict before beta. A separately
normalized argument occurs twice in the original dependent result type. -/
theorem checked_dependent_application :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env [] 22 24 start 13 = ⟨⟨appliedArena, 22⟩, .ok 25⟩ ∧
    run env [] 20 24 start 13 = ⟨⟨appliedArena, 21⟩, .error (.tick (.stepLimit 25))⟩ ∧
    LoanTyping.HasType env [] [] true (.refl seven) application.type := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have executed : run env [] 22 24 start 13 = ⟨⟨appliedArena, 22⟩, .ok 25⟩ := by cbv
  have input : Represents snapshot.arena 13 application.value := decode_sound (fuel := 12) rfl
  have typed := (checkedHistory.global_typing (index := 0) (declaration := application) rfl).choose_spec.2
  obtain ⟨_, _, _, actual, change⟩ := run_refines checkedHistory input (congrArg Outcome.result executed)
  rw [executed] at actual
  have chosen : Represents appliedArena 25 (.refl seven) := decode_sound (fuel := 3) rfl
  exact ⟨admitted, executed, by cbv, actual.unique chosen ▸ change.raw (typed.ghost [])⟩

/-- The overflowing strict function has an appended application and a
reentry at child depth before the prefix is put back around the result. -/
theorem checked_strict_function_reentry :
    run env [] 32 24 start 17 = ⟨⟨wrappedArena, 32⟩, .ok 28⟩ ∧
    LoanTyping.HasType env [] [] true (.strict overflow (.refl seven)) wrapped.type := by
  have executed : run env [] 32 24 start 17 = ⟨⟨wrappedArena, 32⟩, .ok 28⟩ := by cbv
  have input : Represents snapshot.arena 17 wrapped.value := decode_sound (fuel := 12) rfl
  have typed := (checkedHistory.global_typing (index := 1) (declaration := wrapped) rfl).choose_spec.2
  obtain ⟨_, _, _, actual, change⟩ := run_refines checkedHistory input (congrArg Outcome.result executed)
  rw [executed] at actual
  have chosen : Represents wrappedArena 28 (.strict overflow (.refl seven)) := decode_sound (fuel := 6) rfl
  exact ⟨executed, actual.unique chosen ▸ change.raw (typed.ghost [])⟩

/-- The raw domain conversion changes an actual dependent binder, and the
body simplifies under its corresponding context extension. -/
theorem checked_pi_moves_body_context :
    run env [] 15 24 start 22 = ⟨⟨quantifierArena, 15⟩, .ok 25⟩ ∧
    LoanTyping.HasType env [] [] true (.pi false .u64 (.eq (.var 0) (.var 0))) .prop := by
  have executed : run env [] 15 24 start 22 = ⟨⟨quantifierArena, 15⟩, .ok 25⟩ := by cbv
  have input : Represents snapshot.arena 22 quantifier.value := decode_sound (fuel := 12) rfl
  have typed := (checkedHistory.global_typing (index := 2) (declaration := quantifier) rfl).choose_spec.2
  obtain ⟨_, _, _, actual, change⟩ := run_refines checkedHistory input (congrArg Outcome.result executed)
  rw [executed] at actual
  have chosen : Represents quantifierArena 25 (.pi false .u64 (.eq (.var 0) (.var 0))) :=
    decode_sound (fuel := 5) rfl
  exact ⟨executed, actual.unique chosen ▸ change.raw (typed.ghost [])⟩

private def aliasSnapshot : NativeFamilyWire.Snapshot where
  definitions := snapshot.definitions ++ [⟨12, 23⟩]
  families := snapshot.families
  arena := snapshot.arena.push (.node (.global 0) [])

private def aliasEnv : Environment :=
  { env with globals := env.globals.push ⟨application.type, .node (.global 0) []⟩ }

/-- A genuinely admitted alias enters the same dependent application
visitor with one tick and one depth level already spent. -/
theorem checked_alias_enters_dependent_application :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot aliasSnapshot) = true ∧
    runThroughAliases aliasEnv [] aliasSnapshot.definitions 3 23 25 ⟨aliasSnapshot.arena, 0⟩ 23 =
      ⟨⟨aliasSnapshot.arena ++ #[.node (.integer 3) [], .node (.lam false) [0, 7], .node .refl [5]], 23⟩,
        .ok 26⟩ := by
  constructor
  · rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  · cbv

end Examples

end Jihoo.NativeKernel.NativeCoreBinderTraversal
