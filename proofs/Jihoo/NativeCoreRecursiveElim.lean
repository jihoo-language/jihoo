import Jihoo.NativeCoreElimNormal
import Jihoo.NativeCoreCaseEvaluation

/-! Elim visits its original operands in native order and uses the same
recursive visitor for the emitted application spine and every induction
hypothesis. Elim can also be exposed by substitution or occur below a
supported structural, computational or conditional node. -/
namespace Jihoo.NativeKernel.NativeCoreRecursiveElim

open NativeArena Environment NativeProgramWire
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress PostExtension GhostNormalization emptyPrefix
  runWithExtension runWithExtension_refines runWithExtension_progress)
open NativeCoreCaseEvaluation (represented_branches)
open NativeCoreElimNormal (prepare reenter reenter_graph_refinesFrom reenter_progress FamilyRules)
open Environment.FamilyIota (elimTerm)

private def finish (env : Environment) (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) :
    Op → List Nat → Outcome Nat
  | .elim family count, motive :: arms =>
      match arms[count]? with
      | some scrutinee => reenter visit (prepare env state family motive (arms.take count) scrutinee)
      | none => ⟨state, .error (.outsideFragment root)⟩
  | _, _ => ⟨state, .error (.outsideFragment root)⟩

def extension (env : Environment) : PostExtension where
  accepts
    | .elim .. => true
    | _ => false
  finish visit _ _ root state op _ refs := finish env visit root state op refs

def run (env : Environment) (limit depth : Nat) (state : State) (root : Nat) : Outcome Nat :=
  runWithExtension (extension env) limit depth state root

theorem extension_metered (env : Environment) : (extension env).Metered := by
  intro visit limit depth root state op before after accepted visitor
  cases op <;> try contradiction
  case elim family count =>
    cases after with
    | nil => exact Progress.atState _ _
    | cons motive arms =>
        change Progress limit state (finish env visit root state (.elim family count) (motive :: arms))
        cases chosen : arms[count]? with
        | none => simpa only [finish, chosen] using
            (Progress.atState (limit := limit) (α := Nat) state (.error (.outsideFragment root)))
        | some scrutinee => simpa only [finish, chosen] using
            (reenter_progress (env := env) (state := state) (family := family) (motive := motive)
              (cases := arms.take count) (scrutinee := scrutinee) visitor)

theorem extension_soundFrom (rules : FamilyRules env relation) :
    (extension env).SoundFrom base relation := by
  constructor
  · intro op accepted
    cases op <;> try contradiction
    refine ⟨?_, rfl⟩
    intro equal
    cases equal
  · intro visit limit depth root state op before after terms selected accepted onBase read represented size visitor success
    cases op <;> try contradiction
    case elim family count =>
      cases represented with
      | nil => cases size
      | @cons motiveRef motive _ _ motiveRep rest =>
          obtain ⟨caseRefs, scrutRef, arms, value, rfl, rfl, width, caseRep, valueRep⟩ :=
            represented_branches rest (Nat.succ.inj size)
          subst count
          have count := NativeCoreIdentical.represented_length caseRep
          have lookup : (caseRefs ++ [scrutRef])[caseRefs.length]? = some scrutRef := by simp
          simp only [extension, finish, lookup, List.take_left] at success ⊢
          simpa only [elimTerm, ← count] using
            reenter_graph_refinesFrom rules onBase visitor motiveRep caseRep valueRep success

theorem extension_sound (history : ScopedProgram.History definitions declarations env) :
    (extension env).Sound env := by
  have proof : (extension env).SoundFrom #[] (GhostNormalization env) := extension_soundFrom (FamilyRules.ghost history)
  refine ⟨proof.1, ?_⟩
  intro visit limit depth root state op before after terms selected accepted read represented size visitor success
  exact proof.2 accepted (emptyPrefix _) read represented size (fun _ rep done => visitor rep done) success

/-- The clock is shared by original operands, appended induction hypotheses,
substitution and reentry. Rejecting visits keep the emitted prefix. -/
theorem run_progress (env : Environment) (limit depth : Nat) (state : State) (root : Nat) :
    Progress limit state (run env limit depth state root) :=
  runWithExtension_progress (extension_metered env) limit depth state root

/-- The same forward derivation controls the literal graph and its transparent
expansion, including nested induction hypotheses exposed during reentry. -/
theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (run env limit depth state root).result = .ok selected) :
    NativeCorePureComputationNormal.Refines env state term (run env limit depth state root) selected :=
  runWithExtension_refines history.wellFormed (extension_sound (ScopedProgram.History.ofLoanMixed history)) source success

/-- Every successful run on a checked definition from the original bytes
retains the stored annotation under transparent interpretation. -/
theorem run_admitted_preserves {index : Nat} {familyTerms : List NativeFamilyWire.FamilyTerms}
    (decoded : NativeFamilyWire.decodeProgram snapshot = some (definitions, familyTerms))
    (checked : LoanTyping.MixedProgram.checkProgram fuel quantityFuel definitions
      (familyTerms.map NativeLoanMixedAdmission.declaration) = some env)
    (row : snapshot.definitions[index]? = some definition)
    (success : (run env limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot).result = .ok selected) :
    let output := run env limit depth ⟨snapshot.arena, initial⟩ definition.valueRoot
    NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    ∃ entry residual, env.globals[index]? = some entry ∧
      Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
      Represents output.state.arena selected residual ∧
      LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨_, backward, defined, _⟩ := NativeFamilyWire.decodeProgram_sound decoded
  have history := LoanTyping.MixedProgram.checkProgram_sound checked
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at defined history row
  obtain ⟨kept, preserves, residual, selectedRep, change⟩ := run_refines history represented.2 success
  exact ⟨by simp [NativeLoanMixedAdmission.checkBytes_encode, NativeLoanMixedAdmission.checkSnapshot, decoded, checked],
    entry, residual, found, kept, preserves backward, selectedRep, change.expanded.typed typed⟩

namespace Examples

private def proposition : Term := .node (.ind 0 0) []
private def family : NativeFamilyWire.FamilyTerms :=
  ⟨false, 0, 0, 0, [proposition, .pi true proposition proposition]⟩
private def signature : Signature :=
  ⟨[⟨true, proposition, some []⟩], []⟩
private def entry : CheckedFamily :=
  ⟨NativeLoanMixedAdmission.declaration family, [⟨[], []⟩, signature], false⟩
private def motive : Term := .eq (.natural 0) (.natural 0)
private def evidence : Term := .refl (.natural 0)
private def branch : Term := .lam true proposition (.lam true motive (.var 0))
private def leaf : Term := .node (.con 0 0 0) []
private def successor (child : Term) : Term := .node (.con 0 1 1) [child]
private def source : Term := elimTerm 0 motive [evidence, branch] (successor (successor leaf))
private def requested : Term := .eq (.uadd (.natural 0) (.natural 0)) (.natural 0)
private def definition : GlobalDeclaration := ⟨requested, source⟩
private def env : Environment := ⟨#[definition], #[entry]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨13, 10⟩]
  families := [⟨false, 0, 0, 0, [3, 11]⟩]
  arena := #[.node (.natural 0) [], .node .eq [0, 0], .node .refl [0],
    .node (.ind 0 0) [], .var 0, .node (.lam true) [1, 4], .node (.lam true) [3, 5],
    .node (.con 0 0 0) [], .node (.con 0 1 1) [7], .node (.con 0 1 1) [8],
    .node (.elim 0 2) [1, 2, 6, 9], .node (.pi true) [3, 3], .node .uadd [0, 0], .node .eq [12, 0]]

private def outerSpine : Arena :=
  ((snapshot.arena.push (.node .app [6, 8])).push (.node (.elim 0 2) [1, 2, 6, 8])).push (.node .app [14, 15])
private def finishedArena : Arena :=
  ((outerSpine.push (.node .app [6, 7])).push (.node (.elim 0 2) [1, 2, 6, 7])).push (.node .app [17, 18])

/-- Both recursive calls are generated from the admitted graph. Reentry
reaches the original base evidence and keeps the declared converted type. -/
theorem admitted_recursive_elim_reaches_base :
    let output := run env 180 32 ⟨snapshot.arena, 0⟩ 10
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    output.result = .ok 2 ∧ output.state.arena = finishedArena ∧
    LoanTyping.HasType env [] [] true evidence requested := by
  have decoded : NativeFamilyWire.decodeProgram snapshot = some ([definition], [family]) := by cbv
  have checked : LoanTyping.MixedProgram.checkProgram 64 128 [definition]
      ([family].map NativeLoanMixedAdmission.declaration) = some env := by cbv
  have computed : (run env 180 32 ⟨snapshot.arena, 0⟩ 10).result = .ok 2 := rfl
  have exactArena : (run env 180 32 ⟨snapshot.arena, 0⟩ 10).state.arena = finishedArena := rfl
  have row : snapshot.definitions[0]? = some ⟨13, 10⟩ := rfl
  obtain ⟨admitted, found, residual, read, _, _, represented, retained⟩ :=
    run_admitted_preserves decoded checked row computed
  have entryEq : found = definition := by exact Option.some.inj read.symm
  subst found
  rw [exactArena] at represented
  have expected : Represents finishedArena 2 evidence := decode_sound (fuel := 4) rfl
  rw [represented.unique expected] at retained
  have noGlobals : EnvironmentDelta.expand env evidence = evidence := by
    simp [evidence, Term.refl, Term.natural, EnvironmentDelta.expand, EnvironmentDelta.expandArgs]
  rw [noGlobals] at retained
  exact ⟨admitted, computed, exactArena, retained⟩

/-- Rejecting the first spine visit still keeps all three emitted rows. -/
theorem first_reentry_limit_keeps_outer_spine :
    run env 16 32 ⟨snapshot.arena, 0⟩ 10 =
      ⟨⟨outerSpine, 17⟩, .error (.tick (.stepLimit 16))⟩ := rfl

end Examples

end Jihoo.NativeKernel.NativeCoreRecursiveElim
