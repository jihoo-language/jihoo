import Jihoo.NativeCoreExpandedFamilies
import Jihoo.NativeDependentRelationalContexts

set_option maxUniverseOffset 40

/-! Exact graph normalization in an authentic mixed history preserves every
related semantic value in the original caller's fiber. The result refers to
the residual graph row, including recursively expanded globals and families. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

open NativeArena NativeProgramWire
open NativeCoreTransformExact (State)
open EnvironmentDelta (expand)

/-- Every successful raw normalization retains the original typing and has
exactly the same realization at an arbitrary semantic type and valuation. -/
theorem raw_normalization_preserves_realization {familyRows : List NativeFamilyWire.FamilyRoots}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (represented : Represents state.arena root written)
    (typed : LoanTyping.HasType env loans ctx mode (expand env written) type)
    (success : (NativeCoreExpandedFamilies.raw env familyRows roots visible limit depth state root).result = .ok selected)
    (Γ : Ctx env) (A : Ty env Γ.meaning sort) (meaning : Contextual.Tm A.code) :
    let arena := (NativeCoreExpandedFamilies.raw env familyRows roots visible limit depth state root).state.arena
    Prefix state.arena arena ∧ (Backward state.arena → Backward arena) ∧
      ∃ residual, Represents arena selected residual ∧ LoanTyping.HasType env [] ctx true (expand env residual) type ∧
        (Realizes Γ A (expand env written) meaning ↔ Realizes Γ A (expand env residual) meaning) := by
  obtain ⟨kept,backward,residual,selectedRep,change⟩ := NativeCoreExpandedFamilies.raw_refines history aligned onBase represented success
  have available : RawLend.Conv env (expand env written) (expand env residual) := change.converted
  exact ⟨kept,backward,residual,selectedRep,change.typed typed,
    conversion_realizes Γ A history.wellFormed.closed available,
    conversion_realizes Γ A history.wellFormed.closed available.symm⟩

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
