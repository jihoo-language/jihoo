import Jihoo.NativeLoanPureProofObservation

/-! Expose checked transparent globals in ghost evidence from the original
source syntax. The earlier mixed declaration supplies the stored annotation
and body derivation used by bounded expansion and structural replay. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureGlobalObservation

open NativeKernel.Conversion (treeSize)
open Semantics.PureArithmetic (Recognized UniversalTruth)

private theorem reference_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx expression type) :
    ∀ {index : Nat} {declaration : GlobalDeclaration}, expression = .node (.global index) [] →
      env.globals[index]? = some declaration → RawValue.Conv env declaration.type type := by
  induction typed with
  | native original =>
      intro index declaration shape found
      cases shape
      obtain ⟨selected, selectedFound, converted⟩ := original.principalView
      have same : selected = declaration := Option.some.inj (selectedFound.symm.trans found)
      subst selected
      rw [Environment.closed_rename (wf.globals index declaration found).1] at converted
      exact .old converted
  | convert _ _ converted ih =>
      intro index declaration shape found
      exact (ih shape found).trans converted
  | pi | lam | app => intro index declaration shape _; cases shape

/-- Transparent delta preserves an independently formed requested type in
any local context, even when the stored body needs the expanded conversion. -/
theorem delta_preserves {env : Environment} {declaration : GlobalDeclaration} {index : Nat} {sort : SortTag}
    (history : PureMixedAdmission.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (typed : PureTyping.HasType env ctx (.node (.global index) []) requested)
    (formed : HasType env [] ctx true requested sort.term) :
    PureTyping.HasType env ctx declaration.value requested := by
  obtain ⟨_, _, stored⟩ := history.slotTyping index declaration found
  have weakening : Ghost.Substitution env [] ctx Term.var := by
    intro index binding absent
    cases absent
  have weakened : PureTyping.HasType env ctx declaration.value declaration.type :=
    by simpa only [Term.subst_id] using stored.ghostSubstitution history.wellFormed weakening
  exact .convert weakened formed (reference_conversion history.wellFormed typed rfl found)

/-- The source and expanded terms are kept paired so replay can recover the
actual stored type of each transparent global under its local binder. -/
def expand? (env : Environment) (limits : PureProofObservation.Limits) (source requested : Term) :
    Option (Term × SortTag) := do
  let (expanded, _) ← GlobalEnvironment.expandWork limits.typingFuel env.globals limits.budget source
  let inferred ← PureMixedAdmission.inferExpandedGhost limits.typingFuel env limits.typingFuel source expanded
  let sort ← Checker.sort limits.typingFuel env [] [] requested
  if PureTyping.Checker.equal env limits.conversionFuel limits.budget inferred requested then
    some (expanded, sort)
  else none

theorem expand?_sound (history : PureMixedAdmission.History definitions familyDeclarations env)
    (accepted : expand? env limits source requested = some (expanded, sort)) :
    GlobalEnvironment.Expansion env.globals source expanded ∧ RawLend.Forward env source expanded ∧
      treeSize expanded ≤ limits.budget ∧ HasType env [] [] true requested sort.term ∧
      PureTyping.HasType env [] expanded requested := by
  unfold expand? at accepted
  obtain ⟨⟨body, remaining⟩, expandedAt, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨inferred, replayed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨requestedSort, formed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i aligned
    cases accepted
    have expansion := GlobalEnvironment.expandWork_sound expandedAt
    have path := EnvironmentDelta.expand_forward env source
    rw [EnvironmentDelta.expansion_eq_expand expansion] at path
    have within := GlobalEnvironment.expandWork_budget expandedAt
    have requestedFormed := Checker.sort_sound formed
    have bodyTyped := PureMixedAdmission.inferExpandedGhost_sound history.wellFormed history.slotTyping replayed
    exact ⟨expansion, .old (.old path), by omega, requestedFormed,
      .convert bodyTyped requestedFormed (PureTyping.Checker.equal_sound aligned)⟩
  · contradiction

def observe? (env : Environment) (limits : PureProofObservation.Limits) (fuel : Nat)
    (source requested : Term) : Option (Term × Term) := do
  let (expanded, _) ← expand? env limits source requested
  let residual ← PureProofObservation.observe? env limits [] fuel expanded
  pure (expanded, residual)

/-- A successful handoff records actual delta reachability and retains the
exact requested type through the existing bounded typed observer. -/
theorem observe?_sound (history : PureMixedAdmission.History definitions familyDeclarations env)
    (observed : observe? env limits fuel source requested = some (expanded, residual)) :
    RawLend.Forward env source expanded ∧ PureTyping.HasType env [] expanded requested ∧
      PureTyping.HasType env [] residual requested ∧ Recognized env residual := by
  unfold observe? at observed
  obtain ⟨⟨body, sort⟩, checked, observed⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨result, replayed, observed⟩ := Option.bind_eq_some_iff.mp observed
  cases observed
  obtain ⟨_, path, _, _, typed⟩ := expand?_sound history checked
  obtain ⟨retained, recognized⟩ := PureProofObservation.observe?_sound history.wellFormed typed replayed
  exact ⟨path, typed, retained, recognized⟩

/-- The original source with transparent references can be interpreted using
an admitted version-6 environment, with no caller-supplied body derivation. -/
theorem checked_arithmetic_truth (accepted : PureMixedAdmission.checkBytes admissionLimits bytes = some env)
    (observed : observe? env limits fuel source requested = some (expanded, residual)) : UniversalTruth env requested := by
  obtain ⟨_, _, _, _, _, history, wf, _⟩ := PureMixedAdmission.checkBytes_sound accepted
  obtain ⟨_, _, typed, recognized⟩ := observe?_sound history observed
  exact Semantics.PureArithmetic.recognized_fundamental wf typed recognized

theorem rejects_false_inequality (history : PureMixedAdmission.History definitions familyDeclarations env)
    (unordered : ¬ left < right) :
    observe? env limits fuel source (.lt (.natural left) (.natural right)) = none := by
  cases observed : observe? env limits fuel source (.lt (.natural left) (.natural right)) with
  | none => rfl
  | some pair =>
      obtain ⟨expanded, residual⟩ := pair
      obtain ⟨_, _, typed, recognized⟩ := observe?_sound history observed
      exact False.elim (Semantics.PureArithmetic.no_false_numeral_inequality history.wellFormed typed recognized unordered)

private def definition : GlobalDeclaration := ⟨PureFreeBoundary.annotation, PureFreeBoundary.body⟩
private def world : Environment := ⟨#[definition], #[]⟩
private def source : Term := .lam false .u64 (.app (.node (.global 0) []) (.var 0))
private def expanded : Term := .lam false .u64 (.app PureFreeBoundary.body (.var 0))
private def limits : PureProofObservation.Limits := ⟨32, 32, 8192⟩

/-- A source lambda calls an admitted transparent proof definition under its
binder. After expansion, raw checking loses the exact Free-dependent type;
replay reads it from the earlier definition and interprets the whole lambda. -/
theorem checked_global_under_binder :
    Checker.check 32 world [] [] true source PureFreeBoundary.annotation = true ∧
    Checker.check 32 world [] [] true expanded PureFreeBoundary.annotation = false ∧
    observe? world limits 12 source PureFreeBoundary.annotation = some (expanded, expanded) ∧
      UniversalTruth world PureFreeBoundary.annotation := by
  have accepted : PureMixedAdmission.checkProgram ⟨32, 32, 32, 8192⟩ [definition] [] = some world := by cbv
  have history := PureMixedAdmission.checkProgram_sound accepted
  have observed : observe? world limits 12 source PureFreeBoundary.annotation = some (expanded, expanded) := by cbv
  obtain ⟨_, _, typed, recognized⟩ := observe?_sound history observed
  exact ⟨by cbv, by cbv, observed, Semantics.PureArithmetic.recognized_fundamental history.wellFormed typed recognized⟩

end Jihoo.NativeKernel.Environment.LoanTyping.PureGlobalObservation
