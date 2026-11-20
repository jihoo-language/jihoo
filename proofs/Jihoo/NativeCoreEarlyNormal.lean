import Jihoo.NativeCoreRecursiveView
import Jihoo.NativeCoreCaseStrict

/-! Pure Drop selects its original continuation. Pure Lend emits the four
native rows before reentry. The raw Lend spine applies to every represented
callback. The typed joint walk uses the generic rule when neither the
literal callbacks nor their transparent expansions are specialized. -/
namespace Jihoo.NativeKernel.NativeCoreEarlyNormal

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress Refines EarlyExtension GhostNormalization
  runWithExtensions runWithExtensions_progress runWithExtensions_refines)
open NativeCoreCaseStrict (append append_refines append_progress)
open NativeCoreElimNormal (iota_normalization)

def assembleLend (state : State) (owner reader continuation : Nat) : Outcome Nat :=
  (append state .borrow [owner]).next fun next borrowed =>
    (append next .app [reader, borrowed]).next fun next read =>
      (append next .app [continuation, read]).next fun next continued =>
        append next .app [continued, owner]

/-- Each row commits before the next append. All four preserve the input
clock, and a failed allocation leaves the earlier part of the spine. -/
theorem assembleLend_progress (state : State) (owner reader continuation : Nat) :
    Progress limit state (assembleLend state owner reader continuation) := by
  unfold assembleLend
  apply (append_progress state .borrow [owner]).next
  intro borrowed
  apply (append_progress _ .app [reader, borrowed]).next
  intro read
  apply (append_progress _ .app [continuation, read]).next
  intro continued
  exact append_progress _ _ _

/-- The exact four native appends represent the unconditional raw Lend
expansion. Both occurrences of the owner use its original reference. -/
theorem assembleLend_refines
    (ownerRep : Represents state.arena ownerRef owner)
    (readerRep : Represents state.arena readerRef reader)
    (continuationRep : Represents state.arena continuationRef continuation)
    (success : (assembleLend state ownerRef readerRef continuationRef).result = .ok selected) :
    let output := assembleLend state ownerRef readerRef continuationRef
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      Represents output.state.arena selected (RawLend.desugar owner reader continuation) := by
  unfold assembleLend at success ⊢
  obtain ⟨borrowed, first, afterFirst⟩ := Outcome.next_success success
  rw [afterFirst] at success ⊢
  obtain ⟨read, second, afterSecond⟩ := Outcome.next_success success
  rw [afterSecond] at success ⊢
  obtain ⟨continued, third, afterThird⟩ := Outcome.next_success success
  rw [afterThird] at success ⊢
  obtain ⟨keepFirst, backFirst, borrowedRep⟩ := append_refines (.cons ownerRep .nil) rfl first
  obtain ⟨keepSecond, backSecond, readRep⟩ := append_refines
    (.cons (readerRep.frame keepFirst) (.cons borrowedRep .nil)) rfl second
  have keepRead := keepFirst.trans keepSecond
  obtain ⟨keepThird, backThird, appliedRep⟩ := append_refines
    (.cons (continuationRep.frame keepRead) (.cons readRep .nil)) rfl third
  have keepApplied := keepRead.trans keepThird
  obtain ⟨keepFourth, backFourth, resultRep⟩ := append_refines
    (.cons appliedRep (.cons (ownerRep.frame keepApplied) .nil)) rfl success
  exact ⟨keepApplied.trans keepFourth, fun old => backFourth (backThird (backSecond (backFirst old))),
    resultRep⟩

def reenterLend (visit : State → Nat → Outcome Nat) (state : State) (owner reader continuation : Nat) : Outcome Nat :=
  (assembleLend state owner reader continuation).next visit

theorem reenterLend_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (reenterLend visit state owner reader continuation) :=
  (assembleLend_progress _ _ _ _).next (fun ref => metered _ ref)

private theorem reenterLend_refines
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (ownerRep : Represents state.arena ownerRef owner)
    (readerRep : Represents state.arena readerRef reader)
    (continuationRep : Represents state.arena continuationRef continuation)
    (success : (reenterLend visit state ownerRef readerRef continuationRef).result = .ok selected) :
    Refines env state (RawLend.desugar owner reader continuation)
      (reenterLend visit state ownerRef readerRef continuationRef) selected := by
  unfold reenterLend at success ⊢
  obtain ⟨spine, prepared, done⟩ := Outcome.next_success success
  rw [done] at success ⊢
  obtain ⟨kept, backward, spineRep⟩ := assembleLend_refines ownerRep readerRep continuationRep prepared
  obtain ⟨later, preserves, output, represented, normalized⟩ := visitor spineRep success
  exact ⟨kept.trans later, fun old => preserves (backward old), output, represented, normalized⟩

/-- Raw expansion and reentry apply even to explicit dependent callbacks.
The representation and forward equation are independent of whether the
intermediate applications have a source typing derivation. -/
theorem reenterLend_forward
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (ownerRep : Represents state.arena ownerRef owner)
    (readerRep : Represents state.arena readerRef reader)
    (continuationRep : Represents state.arena continuationRef continuation)
    (success : (reenterLend visit state ownerRef readerRef continuationRef).result = .ok selected) :
    let output := reenterLend visit state ownerRef readerRef continuationRef
    Prefix state.arena output.state.arena ∧ (Backward state.arena → Backward output.state.arena) ∧
      ∃ residual, Represents output.state.arena selected residual ∧
        RawLend.Forward env (.lend owner reader continuation) residual := by
  obtain ⟨kept, backward, residual, represented, normalized⟩ :=
    reenterLend_refines visitor ownerRep readerRep continuationRep success
  exact ⟨kept, backward, residual, represented, (RawLend.Forward.lend owner reader continuation).trans normalized.raw.forward⟩

private def genericSyntax (env : Environment) (arena : Arena) (reader continuation : Nat) : Bool :=
  match decode 128 arena reader, decode 128 arena continuation with
  | some reader, some continuation =>
      !LoanTyping.explicitCallbacks reader continuation &&
        !LoanTyping.explicitCallbacks (EnvironmentDelta.expand env reader) (EnvironmentDelta.expand env continuation)
  | _, _ => false

private theorem genericSyntax_sound (readerRep : Represents arena readerRef reader)
    (contRep : Represents arena continuationRef continuation)
    (accepted : genericSyntax env arena readerRef continuationRef = true) :
    LoanTyping.explicitCallbacks reader continuation = false ∧
      LoanTyping.explicitCallbacks (EnvironmentDelta.expand env reader) (EnvironmentDelta.expand env continuation) = false := by
  cases readerRead : decode 128 arena readerRef with
  | none => simp [genericSyntax, readerRead] at accepted
  | some rawReader =>
      cases contRead : decode 128 arena continuationRef with
      | none => simp [genericSyntax, readerRead, contRead] at accepted
      | some rawCont =>
          rw [readerRep.unique (decode_sound readerRead), contRep.unique (decode_sound contRead)]
          simpa [genericSyntax, readerRead, contRead] using accepted

private theorem lendNormalization (wf : UnifiedProgram.EnvWellFormed env)
    (generic : LoanTyping.explicitCallbacks reader continuation = false)
    (expanded : LoanTyping.explicitCallbacks (EnvironmentDelta.expand env reader)
      (EnvironmentDelta.expand env continuation) = false) :
    GhostNormalization env (.lend owner reader continuation) (RawLend.desugar owner reader continuation) := by
  refine ⟨(LoanTyping.Evaluation.Steps.generic _ _ _ generic).ghost_transform wf, ?_⟩
  simpa only [Term.lend, RawLend.desugar, Term.app, Term.borrow, EnvironmentDelta.expand, EnvironmentDelta.expandArgs]
    using (LoanTyping.Evaluation.Steps.generic (EnvironmentDelta.expand env owner)
      (EnvironmentDelta.expand env reader) (EnvironmentDelta.expand env continuation) expanded).ghost_transform wf

private def finishLend (env : Environment) (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) :
    List Nat → Outcome Nat
  | [owner, reader, continuation] =>
      if genericSyntax env state.arena reader continuation then
        reenterLend visit state owner reader continuation
      else ⟨state, .error (.outsideFragment root)⟩
  | _ => ⟨state, .error (.outsideFragment root)⟩

private def finishDrop (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) : List Nat → Outcome Nat
  | [_, rest] => visit state rest
  | _ => ⟨state, .error (.outsideFragment root)⟩

def extension (env : Environment) : EarlyExtension where
  accepts
    | .lend | .drop _ => true
    | _ => false
  finish visit _ _ root state op refs :=
    match op with
    | .lend => finishLend env visit root state refs
    | .drop _ => finishDrop visit root state refs
    | _ => ⟨state, .error (.outsideFragment root)⟩

def run (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  runWithExtensions (NativeCoreRecursiveView.extension env families) (extension env) limit depth state root

private theorem finishLend_progress (metered : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (finishLend env visit root state refs) := by
  simp only [finishLend]
  repeat' first
    | exact Progress.atState _ _
    | exact reenterLend_progress metered
    | split

private theorem finishDrop_progress (metered : ∀ state root, Progress limit state (visit state root)) :
    Progress limit state (finishDrop visit root state refs) := by
  simp only [finishDrop]
  split
  · exact metered _ _
  · exact Progress.atState _ _

theorem extension_metered (env : Environment) : (extension env).Metered := by
  intro visit limit depth root state op refs accepted metered
  cases op <;> try contradiction
  case lend => exact finishLend_progress metered
  case drop family => exact finishDrop_progress metered

private theorem finishLend_refines (wf : UnifiedProgram.EnvWellFormed env)
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (operands : RepresentsList state.arena refs terms) (length : refs.length = 3)
    (success : (finishLend env visit root state refs).result = .ok selected) :
    Refines env state (.node .lend terms) (finishLend env visit root state refs) selected := by
  cases operands with
  | nil => cases length
  | cons ownerRep tail =>
      cases tail with
      | nil => cases length
      | @cons readerRef reader _ _ readerRep tail =>
          cases tail with
          | nil => cases length
          | @cons continuationRef continuation _ _ continuationRep rest =>
              cases rest with
              | cons => cases length
              | nil =>
                  by_cases generic : genericSyntax env state.arena readerRef continuationRef = true
                  · simp only [finishLend, ite_eq_left generic] at success ⊢
                    obtain ⟨kept, backward, output, represented, normalization⟩ :=
                      reenterLend_refines visitor ownerRep readerRep continuationRep success
                    obtain ⟨raw, expanded⟩ := genericSyntax_sound readerRep continuationRep generic
                    exact ⟨kept, backward, output, represented, (lendNormalization wf raw expanded).trans normalization⟩
                  · simp [finishLend, generic] at success

private theorem finishDrop_refines (history : ScopedProgram.History definitions declarations env)
    (visitor : ∀ {state ref term selected}, Represents state.arena ref term →
      (visit state ref).result = .ok selected → Refines env state term (visit state ref) selected)
    (operands : RepresentsList state.arena refs terms) (length : refs.length = 2)
    (success : (finishDrop visit root state refs).result = .ok selected) :
    Refines env state (.node (.drop family) terms) (finishDrop visit root state refs) selected := by
  cases operands with
  | nil => cases length
  | @cons ownerRef owner _ _ ownerRep tail =>
      cases tail with
      | nil => cases length
      | @cons restRef rest _ _ restRep tail =>
          cases tail with
          | cons => cases length
          | nil =>
              obtain ⟨kept, backward, output, represented, normalization⟩ := visitor restRep success
              exact ⟨kept, backward, output, represented,
                (iota_normalization history (.drop family owner rest)).trans normalization⟩

theorem extension_sound (history : ScopedProgram.History definitions declarations env) :
    (extension env).Sound env := by
  intro visit limit depth root state op refs terms selected accepted read represented size visitor success
  cases op <;> try contradiction
  case lend => exact finishLend_refines history.wellFormed visitor represented size success
  case drop family => exact finishDrop_refines history visitor represented size success

theorem run_progress (env : Environment) (families : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Progress limit state (run env families limit depth state root) :=
  runWithExtensions_progress (NativeCoreRecursiveView.extension_metered env families) (extension_metered env)
    limit depth state root

theorem run_refines {families : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (run env families limit depth state root).result = .ok selected) :
    Refines env state term (run env families limit depth state root) selected :=
  runWithExtensions_refines history.wellFormed
    (NativeCoreRecursiveView.extension_sound (ScopedProgram.History.ofLoanMixed history))
    (extension_sound (ScopedProgram.History.ofLoanMixed history)) source success

namespace Examples

private def ownerType : Term := .buffer (.natural 2)
private def readerType : Term := .pi false (.ref ownerType) .u64
private def contType : Term := .pi false .u64 (.pi false ownerType .u64)
private def seven : Term := .natural 7
private def quantified (word : Term) : Term :=
  .pi false ownerType (.pi false readerType (.pi false contType (.eq word seven)))
private def source : Term := quantified (.lend (.var 2) (.var 1) (.var 0))
private def target : Term := quantified (RawLend.desugar (.var 2) (.var 1) (.var 0))
private def env : Environment := ⟨#[⟨.prop, source⟩], #[]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨16, 15⟩]
  families := []
  arena := #[.node (.natural 2) [], .node .buffer [0], .node .ref [1], .node .u64 [],
    .node (.pi false) [2, 3], .node (.pi false) [1, 3], .node (.pi false) [3, 5],
    .var 2, .var 1, .var 0, .node .lend [7, 8, 9], .node (.natural 7) [], .node .eq [10, 11],
    .node (.pi false) [6, 12], .node (.pi false) [4, 13], .node (.pi false) [1, 14], .node .prop []]

private def spineRows : Arena := #[.node .borrow [7], .node .app [8, 17],
  .node .app [9, 18], .node .app [19, 7]]
private def resultRows : Arena := #[.node .eq [20, 11], .node (.pi false) [6, 21],
  .node (.pi false) [4, 22], .node (.pi false) [1, 23]]

/-- The admitted quantified proposition uses generic reader and continuation
variables. Lend emits four rows under those binders and returns a proposition. -/
theorem checked_generic_lend_reenters_at_original_type :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env [] 64 32 ⟨snapshot.arena, 0⟩ 15 =
      ⟨⟨snapshot.arena ++ spineRows ++ resultRows, 27⟩, .ok 24⟩ ∧
    LoanTyping.HasType env [] [] true target .prop := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨.prop, source⟩] [] = some env := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound installed
  have original := (history.global_typing (index := 0) (declaration := ⟨.prop, source⟩) rfl).choose_spec.2
  have sourceRep : Represents snapshot.arena 15 source := decode_sound (fuel := 20) rfl
  have computed : run env [] 64 32 ⟨snapshot.arena, 0⟩ 15 =
      ⟨⟨snapshot.arena ++ spineRows ++ resultRows, 27⟩, .ok 24⟩ := by cbv
  obtain ⟨_, _, residual, represented, change⟩ := run_refines history sourceRep (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents (snapshot.arena ++ spineRows ++ resultRows) 24 target := decode_sound (fuel := 20) rfl
  have kept := change.raw.typed original
  rw [represented.unique expected] at kept
  exact ⟨admitted, computed, kept⟩

theorem reentry_limit_keeps_lend_spine :
    run env [] 18 32 ⟨snapshot.arena, 0⟩ 15 =
      ⟨⟨snapshot.arena ++ spineRows, 19⟩, .error (.tick (.stepLimit 20))⟩ := by cbv

end Examples

namespace DropExample

private def box : Term := .node (.ind 0 0) []
private def buffer : Term := .buffer (.natural 2)
private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def owner : Term := .strict allocation (.node (.con 0 0 1) [allocation])
private def word : Term := .natural 7
private def source : Term := .eq (.node (.drop 0) [owner, word]) word
private def family : FamilyDeclaration := ⟨true, 0, 0, [.pi false buffer box], 0⟩
private def signature : Signature := ⟨[⟨false, buffer, none⟩], []⟩
private def env : Environment := ⟨#[⟨.prop, source⟩], #[⟨family, [signature], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨11, 10⟩]
  families := [⟨true, 0, 0, 0, [5]⟩]
  arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
    .node (.ind 0 0) [], .node .buffer [0], .node (.pi false) [4, 3],
    .node (.con 0 0 1) [2], .node .strict [2, 6], .node (.natural 7) [],
    .node (.drop 0) [7, 8], .node .eq [9, 8], .node .prop []]

private def resultArena : Arena := snapshot.arena.push (.node .eq [8, 8])

/-- Pure Drop enters the actual continuation directly, even when the typed
owner contains Strict. The rejecting tick also points at the continuation. -/
theorem checked_drop_skips_owner :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env snapshot.families 4 12 ⟨snapshot.arena, 0⟩ 10 = ⟨⟨resultArena, 4⟩, .ok 12⟩ ∧
    run env snapshot.families 2 12 ⟨snapshot.arena, 0⟩ 10 =
      ⟨⟨snapshot.arena, 3⟩, .error (.tick (.stepLimit 8))⟩ ∧
    LoanTyping.HasType env [] [] true (.eq word word) .prop := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨.prop, source⟩] [family] = some env := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound installed
  have original := (history.global_typing (index := 0) (declaration := ⟨.prop, source⟩) rfl).choose_spec.2
  have sourceRep : Represents snapshot.arena 10 source := decode_sound (fuel := 12) rfl
  have computed : run env snapshot.families 4 12 ⟨snapshot.arena, 0⟩ 10 =
      ⟨⟨resultArena, 4⟩, .ok 12⟩ := rfl
  obtain ⟨_, _, residual, represented, change⟩ := run_refines history sourceRep (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents resultArena 12 (.eq word word) := decode_sound (fuel := 4) rfl
  have kept := change.raw.typed original
  rw [represented.unique expected] at kept
  exact ⟨admitted, computed, rfl, kept⟩

end DropExample

namespace ExplicitExample

private def length : Term := .natural 2
private def value : Term := .natural 7
private def owner : Term := .alloc length (.integer 0)
private def reference : Term := .ref (.buffer length)
private def reader : Term := .lam false reference value
private def continuation : Term := .lam false .u64 (.lam false (.buffer length) (.var 1))
private def source : Term := .lend owner reader continuation
private def arena : Arena := #[.node (.natural 2) [], .node (.integer 0) [], .node .alloc [0, 1],
  .node .buffer [0], .node .ref [3], .node (.natural 7) [], .node (.lam false) [4, 5], .var 1,
  .node (.lam false) [3, 7], .node .u64 [], .node (.lam false) [9, 8], .node .lend [2, 6, 10]]
private def observed := reenterLend (run .empty [] 128 32) ⟨arena, 1⟩ 2 6 10

/-- The explicit source rule supplies the typed result independently of
the raw App intermediates. The native four-row spine actually reaches
that same result through its recursive visitor. -/
theorem checked_explicit_lend_reaches_typed_result :
    observed.result = .ok 5 ∧
    Represents observed.state.arena 5 value ∧ RawLend.Forward .empty source value ∧
    LoanTyping.HasType .empty [] [] true value .u64 := by
  have checked : LoanTyping.HasType .empty [] [] true source .u64 :=
    LoanTyping.Checker.check_sound (fuel := 64) (by cbv)
  have history : LoanTyping.MixedProgram.History [] [] Environment.empty := .empty
  have computed : observed.result = .ok 5 := by cbv
  obtain ⟨kept, _, residual, residualRep, forward⟩ :=
    reenterLend_forward (fun represented result => run_refines history represented result)
      (decode_sound (fuel := 6) rfl : Represents arena 2 owner)
      (decode_sound (fuel := 6) rfl : Represents arena 6 reader)
      (decode_sound (fuel := 6) rfl : Represents arena 10 continuation) computed
  have base : Represents arena 5 value := decode_sound (fuel := 3) rfl
  have expected := base.frame kept
  rw [residualRep.unique expected] at forward
  have result := checked.explicitLendFinish history.wellFormed owner reference value .u64 (.buffer length) (.var 1) rfl
  have reduced : Lending.finish owner (.var 1) (Lending.read owner value) = value := by cbv
  rw [reduced] at result
  exact ⟨computed, expected, forward, result⟩

end ExplicitExample

end Jihoo.NativeKernel.NativeCoreEarlyNormal
