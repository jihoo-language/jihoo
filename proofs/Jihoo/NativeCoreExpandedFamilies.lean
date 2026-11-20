import Jihoo.NativeCoreExpandedTraversal
import Jihoo.NativeCoreRecursiveView

/-! Case, Elim and View share recursive delta with the typed value and binder
walker. The original dependent operands retain expanded conversion; the
application spine emitted by iota reenters the same typed visitor. -/
namespace Jihoo.NativeKernel.NativeCoreExpandedFamilies

open NativeArena NativeProgramWire Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress RefinesFor ExpandedNormalization expandedRules computeNormalization
  runWithExtensions runWithExtensions_progress runWithExtensions_refinesFrom
  visitOperands visitOperands_progress visitOperands_relatesFrom)
open NativeCoreValueTraversal (Extension)
open NativeCoreExpandedTraversal (ExpandedChange frameRules)
open NativeCoreElimNormal (FamilyRules iota_normalization)

variable {families : List NativeFamilyWire.FamilyRoots}

/-- Every conversion position, including an induction hypothesis passed
to a branch as an argument, visits globals and eliminators recursively. -/
def raw (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible limit : Nat) : Nat → State → Nat → Outcome Nat :=
  runWithExtensions (NativeCoreRecursiveView.extension env families) (NativeCoreNestedAliases.extension roots visible) limit

theorem raw_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible limit depth : Nat)
    (state : State) (root : Nat) : Progress limit state (raw env families roots visible limit depth state root) :=
  runWithExtensions_progress (NativeCoreRecursiveView.extension_metered env families)
    (NativeCoreNestedAliases.extension_metered roots visible) limit depth state root

theorem raw_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root term)
    (success : (raw env families roots visible limit depth state root).result = .ok selected) :
    RefinesFor (ExpandedNormalization env) state term (raw env families roots visible limit depth state root) selected :=
  runWithExtensions_refinesFrom (expandedRules history.wellFormed)
    (NativeCoreRecursiveView.extension_soundFrom (FamilyRules.expanded (ScopedProgram.History.ofLoanMixed history))
      (expandedRules history.wellFormed).compute)
    (NativeCoreNestedAliases.extension_sound history aligned) onBase source success

private theorem typedRules (history : ScopedProgram.History definitions declarations env) :
    FamilyRules env (ExpandedChange env) where
  same _ := by intro _ _ typed; exact typed
  trans first second := by intro _ _ typed; exact second (first typed)
  contract step := (iota_normalization history step).expanded.preserves

def familyExtension (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible : Nat) : Extension where
  accepts := (NativeCoreRecursiveView.extension env families).accepts
  walk visit limit depth root state op before :=
    (visitOperands (raw env families roots visible limit depth) state before).next fun next after =>
      (NativeCoreRecursiveView.extension env families).finish visit limit depth root next op before after

theorem familyExtension_metered (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible : Nat) :
    (familyExtension env families roots visible).Metered := by
  intro visit limit depth root state op before accepted metered
  change Progress limit state
    ((visitOperands (raw env families roots visible limit depth) state before).next
      (fun next after => (NativeCoreRecursiveView.extension env families).finish visit limit depth root next op before after))
  apply (visitOperands_progress (raw_progress env families roots visible limit depth) state before).next
  intro after
  exact NativeCoreRecursiveView.extension_metered env families (depth := depth) (before := before) accepted metered

theorem familyExtension_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    (familyExtension env families roots visible).SoundFrom base (ExpandedChange env) := by
  intro visit limit depth root state op refs terms selected accepted onBase read represented width visitor done
  simp only [familyExtension] at done ⊢
  obtain ⟨refs', visited, branch⟩ := Outcome.next_success done
  rw [branch] at done ⊢
  obtain ⟨kept, backward, length, terms', represented', changed⟩ :=
    visitOperands_relatesFrom (relation := ExpandedNormalization env) onBase represented
      (fun prior child result => by
        obtain ⟨kept, backward, value⟩ := raw_refines history aligned prior child result
        exact ⟨kept, backward, value⟩) visited
  have sound : (NativeCoreRecursiveView.extension env families).SoundFrom base (ExpandedChange env) :=
    NativeCoreRecursiveView.extension_soundFrom (typedRules (ScopedProgram.History.ofLoanMixed history))
      (fun step => (computeNormalization history.wellFormed step).expanded.preserves)
  obtain ⟨ordinary, nonglobal⟩ := sound.1 accepted
  have normalizeChildren := (expandedRules history.wellFormed).node ordinary nonglobal changed
  obtain ⟨later, preserved, residual, exactRep, reduced⟩ :=
    sound.2 accepted (onBase.trans kept) (kept.lookup read) represented' (length.trans width) visitor done
  exact ⟨kept.trans later, fun valid => preserved (backward valid), residual, exactRep,
    fun typed => reduced (normalizeChildren.preserves typed)⟩

def extension (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible : Nat) : Extension :=
  (familyExtension env families roots visible).orElse
    (NativeCoreExpandedTraversal.extensionWithRaw (raw env families roots visible) roots visible)

theorem extension_metered (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible : Nat) :
    (extension env families roots visible).Metered :=
  Extension.orElse_metered (familyExtension_metered env families roots visible)
    (NativeCoreExpandedTraversal.extensionWithRaw_metered roots visible (raw_progress env families roots visible))

theorem extension_sound (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) :
    (extension env families roots visible).SoundFrom base (ExpandedChange env) := by
  apply Extension.orElse_soundFrom (familyExtension_sound history aligned)
  apply NativeCoreExpandedTraversal.extensionWithRaw_sound history aligned
  intro limit depth state ref term selected prior represented done
  obtain ⟨kept, backward, value⟩ := raw_refines history aligned prior represented done
  exact ⟨kept, backward, value⟩

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible limit : Nat) : Nat → State → Nat → Outcome Nat :=
  NativeCoreValueTraversal.runWithFallback (extension env families roots visible) (raw env families roots visible limit) env limit

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (roots : List Roots) (visible limit depth : Nat)
    (state : State) (root : Nat) : Progress limit state (run env families roots visible limit depth state root) :=
  NativeCoreValueTraversal.runWithFallback_progress (extension_metered env families roots visible)
    (raw_progress env families roots visible limit) env depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root input)
    (success : (run env families roots visible limit depth state root).result = .ok selected) :
    RefinesFor (ExpandedChange env) state input (run env families roots visible limit depth state root) selected := by
  apply NativeCoreValueTraversal.runWithFallback_refines (frameRules history.wellFormed)
    (extension_sound history aligned) _ onBase source success
  intro depth state root term selected prior represented accepted
  obtain ⟨kept, backwards, residual, held, changed⟩ := raw_refines history aligned prior represented accepted
  exact ⟨kept, backwards, residual, held, changed.preserves⟩

/-- Byte admission supplies both the constructor signatures and the exact
original expanded type at each stored declaration. -/
theorem admitted_program_preserves
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.families snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result =
          .ok selected →
        let output := run env snapshot.families snapshot.definitions index limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, familyTerms, env, exactBytes, _, backward, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  refine ⟨snapshot, definitions, familyTerms, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, _, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history found
  obtain ⟨kept, preserved, residual, held, change⟩ := run_refines history aligned (.refl _) source.2 success
  exact ⟨entry, residual, read, kept, preserved backward, held, change typed⟩

namespace Examples

private theorem keeps_type
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions)
    (rowFound : roots[index]? = some row) (entryFound : env.globals[index]? = some entry)
    (computed : (run env families roots index limit depth state row.valueRoot).result = .ok selected)
    (expected : Represents (run env families roots index limit depth state row.valueRoot).state.arena selected value) :
    LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env value) entry.type := by
  obtain ⟨entry', _, read, represented, original⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history rowFound
  have same : entry' = entry := Option.some.inj (read.symm.trans entryFound)
  subst entry'
  obtain ⟨_, _, result, exactRep, change⟩ := run_refines history aligned (.refl _) represented.2 computed
  exact exactRep.unique expected ▸ change original

namespace Case

private def count : Term := .natural 2
private def alias : Term := .node (.global 0) []
private def box : Term := .node (.ind 0 0) []
private def buffer : Term := .buffer count
private def allocation : Term := .alloc count (.integer 0)
private def source (size : Term) : Term :=
  .strict (.integer 0) (FamilyIota.caseTerm 0 (.lam false box (.buffer size))
    [.lam false (.buffer size) (.var 0)] (.node (.con 0 0 1) [.alloc size (.integer 0)]))
private def entry : GlobalDeclaration := ⟨buffer, source count⟩
private def definitions : List GlobalDeclaration := [⟨.u64, count⟩, ⟨.buffer alias, source alias⟩]
private def family : FamilyDeclaration := ⟨true, 0, 0, [.pi false buffer box], 0⟩
private def env : Environment :=
  ⟨#[⟨.u64, count⟩, entry], #[⟨family, [⟨[⟨false, buffer, none⟩], []⟩], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1, 0⟩, ⟨6, 12⟩]
  families := [⟨true, 0, 0, 0, [14]⟩]
  arena := #[.node (.natural 2) [], .node .u64 [], .node (.integer 0) [], .node (.global 0) [],
    .node .alloc [3, 2], .node (.ind 0 0) [], .node .buffer [3], .node (.lam false) [5, 6],
    .var 0, .node (.lam false) [6, 8], .node (.con 0 0 1) [4], .node (.caseOf 0 1) [7, 9, 10],
    .node .strict [2, 11], .node .buffer [0], .node (.pi false) [13, 5]]

private def committed : Arena := snapshot.arena ++ #[.node .buffer [0], .node (.lam false) [5, 15],
  .node .buffer [0], .node (.lam false) [17, 8], .node .alloc [0, 2], .node (.con 0 0 1) [19],
  .node .app [18, 19]]
private def evaluated := run env snapshot.families snapshot.definitions 1 96 32 ⟨snapshot.arena, 0⟩ 12

/-- Case visits a global in each dependent operand, then the typed
Strict parent receives the allocation returned by iota and beta. -/
theorem checked_case_reenters_typed_visitor :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    evaluated = ⟨⟨committed, 33⟩, .ok 19⟩ ∧ LoanTyping.HasType env [] [] true allocation buffer := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have history : LoanTyping.MixedProgram.History definitions [family] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have executed : evaluated = ⟨⟨committed, 33⟩, .ok 19⟩ := by cbv
  have result : Represents evaluated.state.arena 19 allocation := by
    rw [executed]
    exact decode_sound (fuel := 5) rfl
  have typed := keeps_type history aligned (show snapshot.definitions[1]? = some ⟨6, 12⟩ from rfl)
    (show env.globals[1]? = some entry from rfl) (congrArg Outcome.result executed) result
  exact ⟨admitted, executed,
    by simpa only [entry, allocation, count, EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using typed⟩

end Case

namespace Elim

private def zero : Term := .natural 0
private def proposition : Term := .node (.ind 0 0) []
private def motive : Term := .eq zero zero
private def evidence : Term := .refl zero
private def branch : Term := .lam true proposition (.lam true motive (.var 0))
private def leaf : Term := .node (.con 0 0 0) []
private def parent (child : Term) : Term := .node (.con 0 1 1) [child]
private def source (base : Term) : Term := FamilyIota.elimTerm 0 motive [base, branch] (parent (parent leaf))
private def requested : Term := .eq (.uadd zero zero) zero
private def entry : GlobalDeclaration := ⟨requested, source evidence⟩
private def definitions : List GlobalDeclaration := [⟨motive, evidence⟩, ⟨requested, source (.node (.global 0) [])⟩]
private def family : FamilyDeclaration := ⟨false, 0, 0, [proposition, .pi true proposition proposition], 0⟩
private def env : Environment :=
  ⟨#[⟨motive, evidence⟩, entry], #[⟨family, [⟨[], []⟩, ⟨[⟨true, proposition, some []⟩], []⟩], false⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨1, 2⟩, ⟨13, 14⟩]
  families := [⟨false, 0, 0, 0, [3, 11]⟩]
  arena := #[.node (.natural 0) [], .node .eq [0, 0], .node .refl [0],
    .node (.ind 0 0) [], .var 0, .node (.lam true) [1, 4], .node (.lam true) [3, 5],
    .node (.con 0 0 0) [], .node (.con 0 1 1) [7], .node (.con 0 1 1) [8],
    .node (.global 0) [], .node (.pi true) [3, 3], .node .uadd [0, 0],
    .node .eq [12, 0], .node (.elim 0 2) [1, 10, 6, 9]]

private def committed : Arena := snapshot.arena ++ #[.node .app [6, 8], .node (.elim 0 2) [1, 2, 6, 8],
  .node .app [15, 16], .node .app [6, 7], .node (.elim 0 2) [1, 2, 6, 7], .node .app [18, 19]]
private def evaluated := run env snapshot.families snapshot.definitions 1 180 32 ⟨snapshot.arena, 0⟩ 14

/-- The base proof is a prior global. Both generated induction
hypotheses enter the conversion visitor when passed as actual arguments. -/
theorem checked_recursive_elim_uses_global_base :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    evaluated.result = .ok 2 ∧ evaluated.state.arena = committed ∧
    LoanTyping.HasType env [] [] true evidence requested := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have history : LoanTyping.MixedProgram.History definitions [family] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have exactRef : evaluated.result = .ok 2 := by cbv
  have exactArena : evaluated.state.arena = committed := by cbv
  have result : Represents evaluated.state.arena 2 evidence := by
    rw [exactArena]
    exact decode_sound (fuel := 5) rfl
  have typed := keeps_type history aligned (show snapshot.definitions[1]? = some ⟨13, 14⟩ from rfl)
    (show env.globals[1]? = some entry from rfl) exactRef result
  exact ⟨admitted, exactRef, exactArena,
    by simpa only [entry, evidence, zero, EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using typed⟩

end Elim

namespace View

private def box : Term := .node (.ind 0 0) []
private def base : Term := .natural 7
private def branch : Term := .lam false (.ref box) (.lam false .u64 (.var 0))
private def leaf : Term := .node (.con 0 0 0) []
private def parent (child : Term) : Term := .node (.con 0 1 1) [child]
private def source (leafArm : Term) : Term :=
  .eq (FamilyIota.viewTerm true 0 .u64 [leafArm, branch] (.borrow (parent (parent leaf)))) base
private def entry : GlobalDeclaration := ⟨.prop, source base⟩
private def definitions : List GlobalDeclaration := [⟨.u64, base⟩, ⟨.prop, source (.node (.global 0) [])⟩]
private def family : FamilyDeclaration := ⟨true, 0, 0, [box, .pi false box box], 0⟩
private def env : Environment :=
  ⟨#[⟨.u64, base⟩, entry], #[⟨family, [⟨[], []⟩, ⟨[⟨false, box, some []⟩], []⟩], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨0, 6⟩, ⟨14, 15⟩]
  families := [⟨true, 0, 0, 0, [1, 12]⟩]
  arena := #[.node .u64 [], .node (.ind 0 0) [], .node .ref [1], .var 0,
    .node (.lam false) [0, 3], .node (.lam false) [2, 4], .node (.natural 7) [],
    .node (.con 0 0 0) [], .node (.con 0 1 1) [7], .node (.con 0 1 1) [8],
    .node .borrow [9], .node (.global 0) [], .node (.pi false) [1, 1],
    .node (.view true 0 2) [0, 11, 5, 10], .node .prop [], .node .eq [13, 6]]

private def committed : Arena := snapshot.arena ++ #[.node .borrow [8], .node .app [5, 16], .node .borrow [8],
  .node (.view true 0 2) [0, 6, 5, 18], .node .app [17, 19],
  .node .borrow [7], .node .app [5, 21], .node .borrow [7],
  .node (.view true 0 2) [0, 6, 5, 23], .node .app [22, 24], .node .eq [6, 6]]
private def evaluated := run env snapshot.families snapshot.definitions 1 512 64 ⟨snapshot.arena, 0⟩ 15

/-- The original View visits its global leaf arm. Both generated View
hypotheses use the constructor telescope in the same growing arena. -/
theorem checked_recursive_view_uses_global_arm :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    evaluated = ⟨⟨committed, 81⟩, .ok 26⟩ ∧ LoanTyping.HasType env [] [] true (.eq base base) .prop := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have history : LoanTyping.MixedProgram.History definitions [family] env :=
    LoanTyping.MixedProgram.checkProgram_sound (fuel := 64) (quantityFuel := 128) (by cbv)
  have aligned : RepresentsDefinitions snapshot.arena snapshot.definitions definitions := decodeRoots_sound (by cbv)
  have executed : evaluated = ⟨⟨committed, 81⟩, .ok 26⟩ := by cbv
  have result : Represents evaluated.state.arena 26 (.eq base base) := by
    rw [executed]
    exact decode_sound (fuel := 5) rfl
  have typed := keeps_type history aligned (show snapshot.definitions[1]? = some ⟨14, 15⟩ from rfl)
    (show env.globals[1]? = some entry from rfl) (congrArg Outcome.result executed) result
  exact ⟨admitted, executed,
    by simpa only [entry, base, EnvironmentDelta.expand, EnvironmentDelta.expandArgs] using typed⟩

end View

end Examples

end Jihoo.NativeKernel.NativeCoreExpandedFamilies
