import Jihoo.NativeLoanPureTyping
import Jihoo.NativeFamilyIotaNormalizer
import Jihoo.NativeEnvironmentDeltaBounded
import Jihoo.NativeLoanMixedAdmission

/-! A bounded ghost checker for the formed RawValue conversion rule. Native
Loan64 separately infers the source and checks formation of the requested
annotation. The composed value projection and the existing family/delta/ACU
normalizer supply a computable conversion witness. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureTyping.Checker

open NativeKernel.Conversion (treeSize)
open Semantics.ValueErasure.Loan (project)

private def rebuiltSize (op : Op) (sizes : List Nat) : Nat :=
  if op = .lend then
    match sizes with
    | [owner, reader, continuation] => 4 + owner + reader + continuation + owner
    | _ => 1 + sizes.sum
  else 1 + sizes.sum

private def unlendSize : Term → Nat
  | .var _ => 1
  | .node op children => rebuiltSize op (children.map unlendSize)

set_option linter.unusedSimpArgs false in
private theorem rebuiltSize_correct (op : Op) (children : List Term) :
    rebuiltSize op (children.map treeSize) = treeSize (RawLend.rebuild op children) := by
  by_cases lending : op = .lend
  · subst op
    rcases children with _ | ⟨owner, _ | ⟨reader, _ | ⟨continuation, _ | ⟨extra, rest⟩⟩⟩⟩
    all_goals simp [rebuiltSize, RawLend.rebuild, RawLend.desugar, Term.app, Term.borrow, treeSize] <;> omega
  · simp [rebuiltSize, lending, RawLend.rebuild_other lending, treeSize]

private theorem unlendSize_correct (term : Term) :
    unlendSize term = treeSize (RawLend.unlend term) := by
  induction term using Term.rec
    (motive_2 := fun children => children.map unlendSize = (RawLend.unlendArgs children).map treeSize) with
  | var => simp [unlendSize, RawLend.unlend, treeSize]
  | node op children ih => simp only [unlendSize, RawLend.unlend, ih, rebuiltSize_correct]
  | nil => simp [RawLend.unlendArgs]
  | cons child children childIH childrenIH => simp [RawLend.unlendArgs, childIH, childrenIH]

/-- Charge both global-expansion passes and the exact macro-expanded Lend
tree before constructing it. Erasing value-only wrappers cannot duplicate
any of the remaining syntax. -/
def project? (env : Environment) (fuel budget : Nat) (term : Term) : Option Term := do
  let expanded ← GlobalEnvironment.expandWork fuel env.globals budget term
  if unlendSize expanded.1 ≤ budget then
    (GlobalEnvironment.expandWork fuel env.globals budget (RawLend.unlend expanded.1)).map
      (fun unfolded => Semantics.ValueErasure.erase unfolded.1)
  else none

theorem project?_sound (accepted : project? env fuel budget term = some result) :
    result = project env term := by
  unfold project? at accepted
  obtain ⟨first, firstRun, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨expanded, remaining⟩ := first
  split at accepted
  · obtain ⟨second, secondRun, output⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨unfolded, remaining'⟩ := second
    cases output
    have firstEq := EnvironmentDelta.expansion_eq_expand (env := env)
      (GlobalEnvironment.expandWork_sound firstRun)
    have secondEq := EnvironmentDelta.expansion_eq_expand (env := env)
      (GlobalEnvironment.expandWork_sound secondRun)
    simp only [Semantics.ValueErasure.Loan.project, RawLend.project,
      Semantics.ValueErasure.project, firstEq, secondEq]
  · contradiction

theorem project?_unlend_bound (accepted : project? env fuel budget term = some result) :
    treeSize (RawLend.project env term) ≤ budget := by
  unfold project? at accepted
  obtain ⟨first, firstRun, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨expanded, remaining⟩ := first
  split at accepted
  · rename_i within
    have firstEq := EnvironmentDelta.expansion_eq_expand (env := env)
      (GlobalEnvironment.expandWork_sound firstRun)
    simpa only [RawLend.project, firstEq, ← unlendSize_correct] using within
  · contradiction

def equal (env : Environment) (fuel budget : Nat) (first second : Term) : Bool :=
  match project? env fuel budget first, project? env fuel budget second with
  | some left, some right => FamilyIota.Extended.equal env budget fuel left right
  | _, _ => false

theorem equal_sound (accepted : equal env fuel budget first second = true) :
    RawValue.Conv env first second := by
  unfold equal at accepted
  split at accepted
  · rename_i left right leftRun rightRun
    apply RawValue.Conv.ofProjected
    rw [← project?_sound leftRun, ← project?_sound rightRun]
    exact FamilyIota.Extended.equal_sound accepted
  · contradiction

/-- Return the sort actually checked for the exact requested annotation. -/
def check? (env : Environment) (typingFuel conversionFuel budget : Nat) (ctx : Context)
    (term requested : Term) : Option SortTag := do
  let sort ← LoanTyping.Checker.sort typingFuel env [] ctx requested
  let original ← LoanTyping.Checker.infer typingFuel env [] ctx true term
  if equal env conversionFuel budget original requested then some sort else none

theorem check?_sound
    (accepted : check? env typingFuel conversionFuel budget ctx term requested = some sort) :
    LoanTyping.HasType env [] ctx true requested sort.term ∧ PureTyping.HasType env ctx term requested := by
  unfold check? at accepted
  obtain ⟨formedSort, formed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨original, inferred, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i converted
    cases accepted
    have requestedFormed := LoanTyping.Checker.sort_sound formed
    exact ⟨requestedFormed,
      convert_native (LoanTyping.Checker.infer_sound inferred) requestedFormed (equal_sound converted)⟩
  · contradiction

/-- Check a single closed ghost declaration from a native version-6 graph.
The source is still decoded independently, with the native graph and scope
checks preceding ghost typing. -/
def checkClosedBytes (typingFuel conversionFuel budget : Nat) (bytes : ByteArray) : Bool :=
  match (NativeFamilyWire.decodeSnapshot bytes).bind NativeFamilyWire.decodeProgram with
  | some ([source], []) =>
      scopeCheck 0 source.type && scopeCheck 0 source.value &&
        match check? empty typingFuel conversionFuel budget [] source.value source.type with
        | some sort => Definitions.bodyMode sort
        | none => false
  | _ => false

theorem checkClosedBytes_sound (accepted : checkClosedBytes typingFuel conversionFuel budget bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (source : GlobalDeclaration) (sort : SortTag),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      NativeFamilyWire.decodeProgram snapshot = some ([source], []) ∧
      source.type.Scoped 0 ∧ source.value.Scoped 0 ∧ Definitions.bodyMode sort = true ∧
      LoanTyping.HasType empty [] [] true source.type sort.term ∧ PureTyping.HasType empty [] source.value source.type := by
  unfold checkClosedBytes at accepted
  cases decoded : NativeFamilyWire.decodeSnapshot bytes with
  | none => simp [decoded] at accepted
  | some snapshot =>
    simp only [decoded, Option.bind_some] at accepted
    split at accepted
    · rename_i source sourceDecoded
      have parts := Bool.and_eq_true_iff.mp accepted
      have bothScoped := Bool.and_eq_true_iff.mp parts.1
      cases checked : check? empty typingFuel conversionFuel budget [] source.value source.type with
      | none => simp [checked] at parts
      | some sort =>
        have mode : Definitions.bodyMode sort = true := by simpa only [checked] using parts.2
        obtain ⟨formed, typed⟩ := check?_sound checked
        exact ⟨snapshot, source, sort, NativeFamilyWire.decodeSnapshot_exact decoded, sourceDecoded,
          scopeCheck_sound bothScoped.1, scopeCheck_sound bothScoped.2, mode, formed, typed⟩
    · contradiction

/-- The version-6 bytes emitted by Core for the pure Free equality fixture. -/
private def freeEqualityBytes : ByteArray :=
  ("011;1;0001;0011;;00111;001;;;111101;1;1;;000011;01;;;;00111;;01;1;01;;1;;;11111;;01;11" ++
   ";001;;1;;;0001;;01;101;011;001101;1;;01;;111;001;;;;1;;;1001;;1;0101;101101;1;;01;1001" ++
   ";1101;01;1;;;001;;;001;;;001;;;101;;;101;;;11011;;1;1;11;;;11;;;01;1;;;001;;;0001;;01;" ++
   "0101;0101;001101;1;;01;1001;00011;0001;;01;001;011;001101;1;;01;;01011;").toUTF8

private def freeEqualitySnapshot : NativeFamilyWire.Snapshot :=
  ⟨[⟨8, 12⟩], [], #[
    .node .u64 [], .node (.natural 1) [], .node (.integer 0) [], .node .alloc [1, 2],
    .var 0, .node .free [3, 4], .var 0, .node .eq [5, 6], .node (.pi false) [0, 7],
    .node .u64 [], .var 0, .node .refl [10], .node (.lam false) [9, 11],
    .node (.universe 0) [], .node .u64 [], .node .u64 [], .node .u64 [],
    .node .i64 [], .node .i64 [], .node .buffer [1], .node .prop [], .node .prop [],
    .node (.universe 0) [], .node .u64 [], .node .eq [10, 10], .node (.pi false) [9, 24],
    .node .eq [4, 6], .node (.pi false) [0, 26]]⟩

private theorem freeEqualitySnapshot_exact :
    NativeFamilyWire.encodeSnapshot freeEqualitySnapshot = freeEqualityBytes := by decide +kernel

theorem free_equality_bytes_decode :
    (NativeFamilyWire.decodeSnapshot freeEqualityBytes).bind NativeFamilyWire.decodeProgram =
      some ([⟨PureFreeBoundary.annotation, PureFreeBoundary.body⟩], []) := by
  rw [← freeEqualitySnapshot_exact, NativeFamilyWire.decodeSnapshot_encode, Option.bind_some]
  cbv

theorem checks_free_equality_bytes : checkClosedBytes 32 32 8192 freeEqualityBytes = true := by
  unfold checkClosedBytes
  rw [free_equality_bytes_decode]
  cbv

end Jihoo.NativeKernel.Environment.LoanTyping.PureTyping.Checker
