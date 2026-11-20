import Jihoo.NativeLoanIndexedPropositionElimination
import Jihoo.NativeLoanProofTreeObservation

/-! Replay checked family induction inside the evidence positions of the
native arithmetic rules. Each position uses its own original type, including
when the surrounding proposition uses expanded pure conversion. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureFamilyArithmeticReplay

open NativeKernel.Conversion (treeSize)
open PureFamilyProofs (replay step?_sound)
open ProofTreeObservation (mapEvidence? mapEvidence_preserves)

private theorem replay_native_preserves (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true term type) (typingFuel depth fuel : Nat) :
    HasType env [] ctx true (replay env ctx typingFuel depth fuel term) type := by
  induction fuel generalizing term with
  | zero => exact typed
  | succ fuel ih =>
      rw [replay]
      split
      · exact typed
      · exact ih ((step?_sound (by assumption)).native_preserves history typed)

private theorem mapEvidence_pure_preserves (visit : Context → Term → Option Term)
    (preserved : ∀ {ctx input type result}, HasType env [] ctx true input type →
      visit ctx input = some result → HasType env [] ctx true result type)
    (typed : PureTyping.HasType env ctx input type) (mapped : mapEvidence? (visit ctx) input = some result) :
    PureTyping.HasType env ctx result type := by
  induction typed with
  | native native => exact .native (mapEvidence_preserves visit preserved native mapped)
  | convert _ formed converted ih => exact .convert (ih mapped) formed converted
  | pi | lam | app => simp [mapEvidence?] at mapped

/-- Run the existing checked family and beta replay at each visited term,
then descend into arithmetic evidence when the retained term needs it. -/
def observe? (env : Environment) (ctx : Context) (typingFuel depth replayFuel budget : Nat) :
    Nat → Term → Option Term
  | 0, _ => none
  | fuel+1, term => do
      let head := replay env ctx typingFuel depth replayFuel term
      let result ← (if ProofObservation.supported head then some head
        else mapEvidence? (observe? env ctx typingFuel depth replayFuel budget fuel) head)
      if treeSize result ≤ budget ∧ ProofObservation.supported result = true then some result else none

/-- The original native and pure typing derivations both survive contextual
replay. No operand or replacement type is supplied by the observer. -/
theorem observe?_preserves (history : ScopedProgram.History definitions declarations env) :
    (∀ {ctx term type result}, HasType env [] ctx true term type →
      observe? env ctx typingFuel depth replayFuel budget fuel term = some result → HasType env [] ctx true result type) ∧
    (∀ {ctx term type result}, PureTyping.HasType env ctx term type →
      observe? env ctx typingFuel depth replayFuel budget fuel term = some result → PureTyping.HasType env ctx result type) := by
  induction fuel with
  | zero => constructor <;> intro ctx term type result typed observed <;> simp [observe?] at observed
  | succ fuel ih =>
      have expose : ∀ {ctx term result}, observe? env ctx typingFuel depth replayFuel budget (fuel+1) term = some result →
          result = replay env ctx typingFuel depth replayFuel term ∨
          mapEvidence? (observe? env ctx typingFuel depth replayFuel budget fuel)
            (replay env ctx typingFuel depth replayFuel term) = some result := by
        intro ctx term result observed
        rw [observe?] at observed
        obtain ⟨found,replayed,observed⟩ := Option.bind_eq_some_iff.mp observed
        split at observed
        · cases observed
          split at replayed
          · exact .inl (Option.some.inj replayed).symm
          · exact .inr replayed
        · contradiction
      constructor
      · intro ctx term type result typed observed
        have head := replay_native_preserves history typed typingFuel depth replayFuel
        rcases expose observed with same | mapped
        · exact same ▸ head
        · exact mapEvidence_preserves (fun localContext => observe? env localContext typingFuel depth replayFuel budget fuel)
            (fun original ran => ih.1 original ran) head mapped
      · intro ctx term type result typed observed
        have head := PureFamilyProofs.replay_preserves history typed typingFuel depth replayFuel
        rcases expose observed with same | mapped
        · exact same ▸ head
        · exact mapEvidence_pure_preserves (fun localContext => observe? env localContext typingFuel depth replayFuel budget fuel)
            (fun original ran => ih.1 original ran) head mapped

theorem observe?_supported (observed : observe? env ctx typingFuel depth replayFuel budget fuel term = some result) :
    Semantics.LoanArithmetic.Supported result ∧ treeSize result ≤ budget := by
  cases fuel with
  | zero => simp [observe?] at observed
  | succ fuel =>
      rw [observe?] at observed
      obtain ⟨found,_,observed⟩ := Option.bind_eq_some_iff.mp observed
      split at observed
      · rename_i within
        cases observed
        exact ⟨(ProofObservation.supported_iff _).mp within.2,within.1⟩
      · contradiction

/-- Retain the original requested annotation while deriving mathematical
arithmetic truth from the actual replay. -/
theorem observed_fundamental (history : PureMixedAdmission.History definitions declarations env)
    (typed : PureTyping.HasType env ctx term type)
    (observed : observe? env ctx typingFuel depth replayFuel budget fuel term = some result) :
    Semantics.PureArithmetic.UniversalTruth env type := by
  have retained := (observe?_preserves (ScopedProgram.History.ofPureMixed history)).2 typed observed
  exact Semantics.PureArithmetic.recognized_fundamental history.wellFormed retained
    (.arithmetic (observe?_supported observed).1)

theorem observed_global_truth {declaration : GlobalDeclaration} {index : Nat}
    (admitted : PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (observed : observe? env [] typingFuel depth replayFuel budget fuel declaration.value = some result) :
    Semantics.PureArithmetic.UniversalTruth env declaration.type := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := PureMixedAdmission.checkBytes_sound admitted
  exact observed_fundamental history (history.global_value_and_reference found).1 observed

end Jihoo.NativeKernel.Environment.LoanTyping.PureFamilyArithmeticReplay

namespace Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Elimination

open AffineSum (Expr)
open Environment.FamilyIota (elimTerm)
open LoanTyping.PureFamilyArithmeticReplay (observe? observe?_preserves observe?_supported)
open MultiUniverse (Assignment)
open MultiUniverse.DependentCodes

variable {id : Nat}

/-- Replay observes only the original term's proof positions. At an affine
index the interpretation follows from the same dependent branch typing that
justified reconstruction of the recursive evidence. -/
theorem Realization.observed_affine {family : Family env id} (input : Realization family index)
    (history : LoanTyping.PureMixedAdmission.History definitions declarations env)
    (motive : AffineMotive) (motiveTyped : LoanTyping.HasType env [] [] true motive.syntax (propMotiveType 1))
    (branches : LoanTyping.Cases env [] [] motive.syntax family.entry.signatures cases)
    (observed : observe? env [] typingFuel depth replayFuel budget fuel (elimTerm id motive.syntax cases input.term) = some residual) :
    motive.Holds index := by
  let assignment := Assignment.empty (List.get ([] : List (Fin 32)))
  have retained := (observe?_preserves (ScopedProgram.History.ofPureMixed history)).2
    (.native (input.elimination_typed motiveTyped branches)) observed
  have interpreted : Finite.decodeProp ((motive.instantiate input.closed).meaning assignment) := by
    have aligned := motive.instantiate_conversion (env := env) input.closed
    have supported := (observe?_supported observed).1
    cases motive with
    | less => exact (Proofs.Tree.less (levels := []) _ _ (.arithmetic supported)).truth history retained aligned assignment
    | equal => exact (Proofs.Tree.equal (levels := []) _ _ (.arithmetic supported)).truth history retained aligned assignment
  have result := (motive.instantiate_truth input.closed assignment).mp interpreted
  rwa [input.evaluated] at result

theorem checked_global_observes_affine {declaration : GlobalDeclaration} {index : Nat} {family : Family env id}
    (admitted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (input : Realization family n) (motive : AffineMotive)
    (source : declaration.value = elimTerm id motive.syntax cases input.term)
    (observed : observe? env [] typingFuel depth replayFuel budget fuel declaration.value = some residual) :
    motive.Holds n := by
  obtain ⟨_,_,_,_,_,history,_,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound admitted
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := family) (history.global_value_and_reference found).1 source
  rw [source] at observed
  exact input.observed_affine history motive motiveTyped branches observed

section Example

private def start : Expr := .literal 0
private def predecessor : Expr := .var 0
private def advance : Expr := .add predecessor (.literal 2)
private def evenSource : FamilyDeclaration :=
  ⟨false,0,1,[propositionAt 0 (.natural 0),.pi false .u64
    (.pi true (propositionAt 0 (.var 0)) (propositionAt 0 (.uadd (.var 1) (.natural 2))))],0⟩
private def evenTable : CheckedFamily :=
  ⟨evenSource,[nullarySignature start,recursiveSignature 0 predecessor advance],false⟩
private def next (index : Term) : Term := .uadd index (.natural 1)
private def motive : AffineMotive := .less (left := .var 0) (right := .add (.var 0) (.literal 1))
  (.var .here) (.add (.var .here) (.literal (by decide)))
private def base : Term := .zeroLe (.natural 0)
private def branch : Term := .lam false .u64 (.lam true (propositionAt 0 (.var 0))
  (.lam true (.lt (.var 1) (next (.var 1))) (.ltAdd (.var 2) (next (.var 2)) (.natural 2) (.var 0))))
private def arms : List Term := [base,branch]
private def constructorProof : Term := .node (.con 0 1 2)
  [.natural 2,.node (.con 0 1 2) [.natural 0,.node (.con 0 0 0) []]]
private def source : GlobalDeclaration :=
  ⟨.lt (.natural 4) (next (.natural 4)),elimTerm 0 motive.syntax arms constructorProof⟩
private def world : Environment := ⟨#[source],#[evenTable]⟩
private def evenFamily : Family world 0 := ⟨evenTable,rfl,rfl,rfl⟩
private def limits : LoanTyping.PureMixedAdmission.Limits := ⟨48,48,48,16000⟩
private def evidence : Term := .ltAdd (.natural 2) (next (.natural 2)) (.natural 2)
  (.ltAdd (.natural 0) (next (.natural 0)) (.natural 2) base)

/-- Two checked recursive constructor layers actually consume the generated
induction hypothesis as the fourth operand of LtAdd. The observed proof
contains both shifted recursive steps and ends at the checked base. -/
theorem checked_recursive_arithmetic_elimination :
    LoanTyping.PureMixedAdmission.checkProgram limits [source] [evenSource] = some world ∧
    observe? world [] 48 16 16 4096 8 source.value = some evidence ∧ motive.Holds 4 := by
  have admitted : LoanTyping.PureMixedAdmission.checkProgram limits [source] [evenSource] = some world := by cbv
  have observed : observe? world [] 48 16 16 4096 8 source.value = some evidence := by cbv
  let history := LoanTyping.PureMixedAdmission.checkProgram_sound admitted
  let typed := (history.global_value_and_reference (index := 0) (declaration := source) rfl).1
  obtain ⟨motiveTyped,branches⟩ := checked_cases (family := evenFamily) typed rfl
  let input : Realization evenFamily 4 :=
    ⟨.literal 4,.literal (by decide),rfl,constructorProof,
      .recursive (.var .here) (.add (.var .here) (.literal (by decide))) rfl
        (.recursive (.var .here) (.add (.var .here) (.literal (by decide))) rfl (.nullary (.literal (by decide)) rfl)),
      LoanTyping.Checker.check_sound (fuel := 48) (by cbv)⟩
  exact ⟨admitted,observed,input.observed_affine history motive motiveTyped branches observed⟩

end Example

end Jihoo.NativeKernel.Environment.Semantics.IndexedProposition.Elimination
