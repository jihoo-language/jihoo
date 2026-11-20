import Jihoo.NativeLoanUniverseEqualityTransport
import Jihoo.NativeLoanOpenProofNormalization

/-! Equality elimination in an open dependent scalar and proof telescope.
The actual valuation supplies native replacements for the telescope. Erased
beta exposes a reflexive equality without a second check of its operand. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.OpenDependentTransport

open AffineSum (Expr)
open PureHypothesisObservation (Entry ScalarExpr context)
open WideHypothesisObservation (Satisfies closing)
open NativeKernel.Conversion (treeSize)
open Semantics.PureArithmetic (Formula UniversalTruth)

/-- Read a reflexive witness through erased beta and literal Strict. Each
recursive descent uses one step of the finite source spine. -/
def expose? : Nat → Term → Option Term
  | 0, _ => none
  | _ + 1, .refl value => some value
  | fuel + 1, .strict (.natural _) rest => expose? fuel rest
  | fuel + 1, .app (.lam true _ body) argument => expose? fuel (body.subst (single argument))
  | _ + 1, _ => none

/-- The original native application derivation already validates its erased
operand. Computation preserves the original Eq type without rechecking it. -/
theorem expose?_preserves (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] ctx true term type) (observed : expose? fuel term = some witness) :
    HasType env [] ctx true (.refl witness) type := by
  fun_induction expose? fuel term generalizing witness type
  · contradiction
  · cases observed
    exact typed
  · rename_i ih
    exact ih (value_root_ghost_preservation (.strict _ _) typed) observed
  · rename_i ih
    exact ih (compute_ghost_preservation wf (.beta _ _ _ _) typed) observed
  · contradiction

/-- The source certificate records only the finite syntax of the equality
spine. In particular it contains no conversion, argument typing or witness
for the expected result. -/
inductive EqualitySpine (entries : List Entry) : Nat → Term → Prop where
  | reflexive : OpenProofNormalization.Reflexive entries term → EqualitySpine entries 1 term
  | strict : EqualitySpine entries fuel term → EqualitySpine entries (fuel + 1) (.strict (.natural n) term)
  | erased : EqualitySpine entries fuel (body.subst (single argument)) →
      EqualitySpine entries (fuel + 1) (.app (.lam true domain body) argument)

theorem EqualitySpine.closes (tree : EqualitySpine entries fuel term) (words : Nat → Nat) :
    ∃ witness, expose? fuel (term.subst (closing entries words)) = some witness := by
  induction tree with
  | reflexive terminal =>
      obtain ⟨expr,shape⟩ := terminal.closed words
      exact ⟨expr.toTerm,by rw [shape,expose?]⟩
  | strict _ ih =>
      obtain ⟨witness,found⟩ := ih
      exact ⟨witness,by simpa only [Term.strict,Term.natural,Term.subst,substArgs,Op.binders,liftSub,expose?] using found⟩
  | erased _ ih =>
      obtain ⟨witness,found⟩ := ih
      refine ⟨witness,?_⟩
      simp only [Term.app,Term.lam,Term.subst,substArgs,Op.binders,liftSub,expose?]
      rw [← Term.subst_instantiate]
      exact found

/-- Invert the actual Transport rule and replay its equality operand at
that same type. The resulting Refl proof yields a kernel equation between
the original endpoints, even when the displayed endpoints differ. -/
theorem exposed_payload (wf : UnifiedProgram.EnvWellFormed env)
    (typed : PureTyping.HasType env ctx (.transport motive equation payload) requested)
    (seen : expose? fuel equation = some witness) :
    ∃ original, PureTyping.HasType env ctx payload original ∧ RawValue.Conv env original requested := by
  obtain ⟨left,right,_,checkedEquation,checkedPayload,result⟩ := typed_transport_inputs typed rfl
  have retained := expose?_preserves wf checkedEquation seen
  have equationConv : RawLend.Conv env (.eq witness witness) (.eq left right) := retained.principalView
  have endpoints := equationConv.eq_injective wf.admissible
  have between := endpoints.1.symm.trans endpoints.2
  have motiveConv : RawValue.Conv env (.app motive left) (.app motive right) :=
    .node .app (.cons (.refl _) (.cons (.old between) .nil))
  exact ⟨_,.native checkedPayload,motiveConv.trans result⟩

/-- Close the actual source rule using the valuation's checked simultaneous
substitution. The opened source syntax determines finite equality replay.
There is no expected equality formula or successful reduction premise. -/
theorem typed_open_payload (wf : UnifiedProgram.EnvWellFormed env) (valuation : Satisfies entries words)
    (tree : EqualitySpine entries fuel equation)
    (typed : PureTyping.HasType env (context entries) (.transport motive equation payload) requested) :
    ∃ original, PureTyping.HasType env [] (payload.subst (closing entries words)) original ∧
      RawValue.Conv env original (requested.subst (closing entries words)) := by
  have closed := typed.ghostSubstitution wf valuation.realizes
  obtain ⟨_,seen⟩ := tree.closes words
  simp only [Term.transport,Term.subst,substArgs,Op.binders,liftSub] at closed
  exact exposed_payload wf closed seen

def normalize? (env : Environment) (equalityFuel payloadFuel : Nat) : Term → Option Term
  | .transport _ equation payload => do
      let _ ← expose? equalityFuel equation
      OpenProofNormalization.normalize? env payloadFuel payload
  | _ => none

/-- Computed fuel from the two source certificates suffices for normalization.
The residual retains a genuine native-derived type that converts to the
closed original annotation. -/
theorem typed_open_normalization (wf : UnifiedProgram.EnvWellFormed env) (valuation : Satisfies entries words)
    (equation : EqualitySpine entries fuel evidence) (continuation : OpenProofNormalization.Tree entries payload)
    (typed : PureTyping.HasType env (context entries) (.transport motive evidence payload) requested) :
    let closedPayload := payload.subst (closing entries words)
    ∃ residual original,
      normalize? env fuel (treeSize closedPayload + 1) ((Term.transport motive evidence payload).subst (closing entries words)) = some residual ∧
      PureTyping.HasType env [] residual original ∧ RawValue.Conv env original (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨_,seen⟩ := equation.closes words
  obtain ⟨original,payloadTyped,converted⟩ := typed_open_payload wf valuation equation typed
  obtain ⟨residual,ran⟩ := continuation.normalization_total (env := env) words
    (Nat.lt_succ_self (treeSize (payload.subst (closing entries words))))
  obtain ⟨residualTyped,recognized⟩ := OpenProofNormalization.normalize?_sound wf payloadTyped ran
  refine ⟨residual,original,?_,residualTyped,converted, (Semantics.PureArithmetic.recognized_fundamental wf residualTyped recognized).convert converted⟩
  simp only [Term.transport,Term.subst,substArgs,Op.binders,liftSub,normalize?,seen]
  exact ran

/-- Checking the original requested annotation also supplies its formation,
so the exposed residual can be assigned the exact instantiated annotation. -/
theorem checked_open_normalization {limits : PureProofObservation.Limits} (wf : UnifiedProgram.EnvWellFormed env)
    (valuation : Satisfies entries words) (equation : EqualitySpine entries fuel evidence)
    (continuation : OpenProofNormalization.Tree entries payload)
    (checked : PureTyping.Checker.check? env limits.typingFuel limits.conversionFuel limits.budget (context entries)
      (.transport motive evidence payload) requested = some sort) :
    let closedPayload := payload.subst (closing entries words)
    ∃ residual,
      normalize? env fuel (treeSize closedPayload + 1) ((Term.transport motive evidence payload).subst (closing entries words)) = some residual ∧
      PureTyping.HasType env [] residual (requested.subst (closing entries words)) ∧
      UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨formed,typed⟩ := PureTyping.Checker.check?_sound checked
  obtain ⟨residual,_,ran,retained,converted,truth⟩ := typed_open_normalization wf valuation equation continuation typed
  have closed := formed.ghostSubstitution wf valuation.realizes
  rw [SortTag.subst_term] at closed
  exact ⟨residual,ran,.convert retained closed converted,truth⟩

/-- Telescope entries are in de Bruijn order, with each annotation written
in its own earlier context. -/
def telescopeLambdas : List Entry → Term → Term
  | [], body => body
  | entry :: earlier, body => telescopeLambdas earlier (.lam entry.binding.erased entry.binding.ty body)

def telescopeProducts : List Entry → Term → Term
  | [], body => body
  | entry :: earlier, body => telescopeProducts earlier (.pi entry.binding.erased entry.binding.ty body)

/-- Opening the written telescope retains each actual binder type and
the conversion to the original result annotation. -/
theorem telescope_body_typed (wf : UnifiedProgram.EnvWellFormed env) {entries outer : List Entry}
    (typed : PureTyping.HasType env (context outer) (telescopeLambdas entries body) requested)
    (written : RawValue.Conv env requested (telescopeProducts entries annotation)) :
    ∃ original, PureTyping.HasType env (context (entries ++ outer)) body original ∧ RawValue.Conv env original annotation := by
  induction entries generalizing body annotation requested with
  | nil => exact ⟨requested,typed,written⟩
  | cons entry entries ih =>
      obtain ⟨_,opened,converted⟩ := ih (body := .lam entry.binding.erased entry.binding.ty body)
        (annotation := .pi entry.binding.erased entry.binding.ty annotation) typed written
      obtain ⟨_,bodyTyped,principal⟩ := PureTyping.lambda_replay opened entry.binding.erased entry.binding.ty body rfl
      exact ⟨_,bodyTyped,((principal.trans converted).pi_injective wf.admissible).2.2⟩

/-- A byte-admitted dependent proof supplies its real open body derivation.
Its normalized proof and interpreted result require no caller-proposed
output type or successfully executed observation. -/
theorem checked_global_open_transport_truth {declaration : GlobalDeclaration} {index : Nat}
    (admitted : PureMixedAdmission.checkBytes limits bytes = some env) (found : env.globals[index]? = some declaration)
    (source : declaration.value = telescopeLambdas entries (.transport motive evidence payload))
    (annotation : declaration.type = telescopeProducts entries requested)
    (valuation : Satisfies entries words) (equation : EqualitySpine entries fuel evidence)
    (continuation : OpenProofNormalization.Tree entries payload) :
    UniversalTruth env (requested.subst (closing entries words)) := by
  obtain ⟨_,_,_,_,_,history,wf,_⟩ := PureMixedAdmission.checkBytes_sound admitted
  have original := (history.global_value_and_reference found).1
  rw [source,annotation] at original
  obtain ⟨_,opened,converted⟩ := telescope_body_typed (outer := []) wf original (.refl _)
  rw [List.append_nil] at opened
  obtain ⟨_,_,_,_,_,truth⟩ := typed_open_normalization wf valuation equation continuation opened
  exact truth.convert (converted.substitution (closing entries words) wf.admissible)

theorem open_inequality_truth (wf : UnifiedProgram.EnvWellFormed env)
    (left : ScalarExpr entries first) (right : ScalarExpr entries second)
    (grounded : UniversalTruth env ((Term.lt first.toTerm second.toTerm).subst (closing entries words))) :
    first.eval words < second.eval words := by
  obtain ⟨a,leftEq,leftValue⟩ := OpenProofNormalization.closed_affine left words
  obtain ⟨b,rightEq,rightValue⟩ := OpenProofNormalization.closed_affine right words
  have formula : UniversalTruth env (Formula.less a b).syntax := by
    simp only [Formula.syntax,Term.lt,leftEq,rightEq]
    simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using grounded
  have ordered := (UniversalTruth.formula_iff wf (.less a b)).mp formula (fun _ => 0)
  simpa only [Formula.truth,leftValue,rightValue] using ordered

section Example

private def entries : List Entry := [
  .equal (.var 2) (.var 1),
  .less (.var 1) (.add (.var 1) (.literal 1)),
  .scalar false,
  .scalar false]
private def x : Expr := .var 3
private def y : Expr := .var 2
private def xNext : Expr := .add x (.literal 1)
private def yNext : Expr := .add y (.literal 1)
private def yAfter : Expr := .add y (.literal 2)
private def eqType : Term := .eq x.toTerm y.toTerm
private def equation : Term := .app (.lam true eqType (.var 0)) (.var 0)
private def payload : Term := .ltAdd x.toTerm xNext.toTerm (.natural 1) (.var 1)
private def motive : Term :=
  .lam false .u64 (.lt (.uadd (.var 0) (.natural 1)) (.uadd (.var 0) (.natural 2)))
private def source : Term := .transport motive equation payload
private def requested : Term := .lt yNext.toTerm yAfter.toTerm
private def declaration : GlobalDeclaration := ⟨telescopeProducts entries requested,telescopeLambdas entries source⟩
private def world : Environment := ⟨#[declaration],#[]⟩
private def limits : PureMixedAdmission.Limits := ⟨48,48,48,16000⟩

private def snapshot : NativeFamilyWire.Snapshot :=
  ⟨[⟨14,30⟩],[],#[
    .node .u64 [], .var 1, .node (.natural 1) [], .node .uadd [1,2],
    .node .lt [1,3], .var 2, .node .eq [5,1], .node .uadd [5,2],
    .node (.natural 2) [], .node .uadd [5,8], .node .lt [7,9],
    .node (.pi true) [6,10], .node (.pi true) [4,11],
    .node (.pi false) [0,12], .node (.pi false) [0,13],
    .var 0, .node .uadd [15,2], .node .uadd [15,8], .node .lt [16,17],
    .node (.lam false) [0,18], .var 3, .node .eq [20,5],
    .node (.lam true) [21,15], .node .app [22,15],
    .node .uadd [20,2], .node .ltAdd [20,24,2,1], .node .transport [19,23,25],
    .node (.lam true) [6,26], .node (.lam true) [4,27],
    .node (.lam false) [0,28], .node (.lam false) [0,29]]⟩

private def fixtureBytes : ByteArray := NativeFamilyWire.encodeSnapshot snapshot

private def words : Nat → Nat
  | 2 | 3 => 2^64 - 1
  | _ => 0

private theorem populated : Satisfies entries words :=
  .equal (.var (.there (.there .here))) (.var (.there .here)) (by decide)
    (.less (.var (.there .here)) (.add (.var (.there .here)) (.literal (by decide)))
      (by decide) (.scalar (by decide) (.scalar (by decide) .empty)))

private theorem eqSpine : EqualitySpine entries 2 equation := by
  refine .erased ?_
  simp only [Term.subst,single]
  exact .reflexive (.assume .here)

private theorem continuation : OpenProofNormalization.Tree entries payload :=
  .arithmetic (.ltAdd (left := x) (right := xNext) (delta := .literal 1)
    (.var (.there (.there (.there .here)))) (.add (.var (.there (.there (.there .here)))) (.literal (by decide)))
    (.literal (by decide)) (.assume (.there .here)))

/-- The exact native bytes admit two scalar binders followed by Lt and Eq
hypotheses. Transport uses the checked, beta-hidden equation between the two
different bound variables. The exact closed run works even at the upper U64
endpoint, where the interpreted result indices are both wider than a word. -/
theorem checked_open_beta_transport_bytes :
    PureMixedAdmission.checkBytes limits fixtureBytes = some world ∧
    normalize? world 2 (treeSize (payload.subst (closing entries words)) + 1) (source.subst (closing entries words)) =
      some (payload.subst (closing entries words)) ∧
    Satisfies entries words ∧ 2^64 ≤ yNext.eval words ∧
    ∀ words, Satisfies entries words → yNext.eval words < yAfter.eval words := by
  have decoded : NativeFamilyWire.decodeProgram snapshot = some ([declaration],[]) := by cbv
  have accepted : PureMixedAdmission.checkProgram limits [declaration] [] = some world := by cbv
  have admitted : PureMixedAdmission.checkBytes limits fixtureBytes = some world := by
    simp [PureMixedAdmission.checkBytes,fixtureBytes,NativeFamilyWire.decodeSnapshot_encode,decoded,accepted]
  have ran : normalize? world 2 (treeSize (payload.subst (closing entries words)) + 1) (source.subst (closing entries words)) =
      some (payload.subst (closing entries words)) := by cbv
  obtain ⟨_,_,_,_,_,_,wf,_⟩ := PureMixedAdmission.checkBytes_sound admitted
  refine ⟨admitted,ran,populated,(by decide),?_⟩
  intro words valuation
  have truth := checked_global_open_transport_truth (declaration := declaration) (index := 0)
    (requested := requested) admitted rfl rfl rfl valuation eqSpine continuation
  exact open_inequality_truth (first := yNext) (second := yAfter) wf
    (.add (.var (.there (.there .here))) (.literal (by decide)))
    (.add (.var (.there (.there .here))) (.literal (by decide))) truth

end Example

end Jihoo.NativeKernel.Environment.LoanTyping.OpenDependentTransport
