import Jihoo.NativeLoanNumericalEvidence
import Jihoo.NativeCoreGhostLiteralAddition

/-! Numerical observations read the actual normalizer result from its
live arena. The recognized tree may contain ghost sums above one word. -/
namespace Jihoo.NativeKernel.NativeCoreNumericalObservation

open NativeArena NativeProgramWire Environment
open EnvironmentDelta (expand)
open EnvironmentDelta.NumeralForward renaming Represents → NumeralTree
open Semantics.LoanArithmetic (Numeric)

def evaluate : (term : Term) → Option {value : Nat // NumeralTree term value}
  | .natural value => some ⟨value,.natural value⟩
  | .uadd left right => do
    let a ← evaluate left
    let b ← evaluate right
    pure ⟨a.val + b.val,.add a.property b.property⟩
  | _ => none
termination_by term => sizeOf term

def read (arena : Arena) (fuel root : Nat) : Option Nat :=
  (decode fuel arena root).bind fun term => (evaluate term).map Subtype.val

/-- The actual decoder and numerical tree checker construct the value
observation at the representation returned by the graph. -/
theorem read_refines (observed : read arena fuel root = some value) :
    ∃ term, NativeArena.Represents arena root term ∧ NumeralTree term value := by
  unfold read at observed
  obtain ⟨term,decoded,evaluated⟩ := Option.bind_eq_some_iff.mp observed
  cases answer : evaluate term with
  | none => simp only [answer,Option.map_none,reduceCtorEq] at evaluated
  | some witnessed =>
    simp only [answer,Option.map_some,Option.some.injEq] at evaluated
    subst value
    exact ⟨term,decode_sound decoded,witnessed.property⟩

private theorem unfold_globals (env : Environment) (term : Term) :
    RawLend.Conv env term (expand env term) :=
  (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward env term))).toConv

/-- A successful native-style visit and inspection of its returned root
supply a numerical value of the original represented expression. -/
theorem literal_visit_numeric
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : NativeArena.Represents state.arena root term)
    (success : (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).result = .ok selected)
    (observed : read (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).state.arena
      decodeFuel selected = some value) : Numeric env term value := by
  obtain ⟨_,_,residual,held,reduced⟩ := NativeCoreGhostLiteralAddition.run_refines history aligned onBase source success
  obtain ⟨result,returned,numeric⟩ := read_refines observed
  have same := held.unique returned
  subst result
  exact ⟨residual,(unfold_globals env term).trans
    (reduced.converted.trans (unfold_globals env residual).symm),numeric⟩

private def wide : Arena := #[.node (.natural (2^64-1)) [],.node (.natural 1) [],.node .uadd [0,1]]

/-- The live output has two half-word summands. The observation recovers
their full mathematical sum from the returned root. -/
theorem wide_normalized_sum_has_exact_observation :
    let finished := NativeCoreGhostLiteralAddition.run [] 0 5 8 ⟨wide,0⟩ 2
    finished.result = .ok 4 ∧ read finished.state.arena 5 4 = some (2^64) := by
  cbv

end Jihoo.NativeKernel.NativeCoreNumericalObservation
