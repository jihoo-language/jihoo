import Jihoo.NativeMultiUniverseComputedFundamental
set_option maxUniverseOffset 40

/-! Native HasType checks a computed type annotation before the syntax-only
fundamental reconstructs its concrete dependent-universe interpretation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed.Examples
open Jihoo.NativeKernel.Environment.Conversion

def identityAlias : Code 1 :=
  .beta ⟨0,by decide⟩ (.parameter ⟨0,by decide⟩) (.parameter ⟨0,by decide⟩)

def identity : Term := .lam false (.univ 0) (.lam false (identityAlias.syntax 0) (.var 0))

def identityType : Term := .pi false (.univ 0)
  (.pi false (identityAlias.syntax 0) ((identityAlias.syntax 0).rename Nat.succ))

theorem identityAlias_typed :
    HasType env [⟨.univ 0,false⟩] true (identityAlias.syntax 0) (.univ 0) := by
  have typedFunction : HasType env [⟨.univ 0,false⟩] true
      (.lam false (.univ 0) (.var 0)) (.pi false (.univ 0) (.univ 0)) :=
    .lam (.intro (s := .type 1) (.univ (by decide))
      (Or.inl (by change SortTag.type 1 ≠ SortTag.prop; intro h; cases h)))
      (.var (b := ⟨.univ 0,false⟩) (by simp only [NativeKernel.lookup,Term.univ,Term.rename,renameArgs]) (Or.inl rfl))
  have typedArgument : HasType env [⟨.univ 0,false⟩] true (.var 0) (.univ 0) :=
    .var (b := ⟨.univ 0,false⟩) (by simp only [NativeKernel.lookup,Term.univ,Term.rename,renameArgs]) (Or.inl rfl)
  have applied := HasType.app typedFunction typedArgument (Or.inl rfl)
  simpa [identityAlias,Code.syntax,Code.instantiate,extendParameters,Fin.cases,
    Term.univ,Term.subst,substArgs] using applied

theorem identity_typed : HasType env [] true identity identityType :=
  .lam (.intro (s := .type 1) (.univ (by decide))
    (Or.inl (by change SortTag.type 1 ≠ SortTag.prop; intro h; cases h)))
    (.lam (.intro (s := .type 0) identityAlias_typed
      (Or.inl (by change SortTag.type 0 ≠ SortTag.prop; intro h; cases h)))
      (.var (b := ⟨(identityAlias.syntax 0).rename Nat.succ,false⟩) rfl (Or.inl rfl)))

theorem identity_recognized : UniverseRecognized [] identity :=
  .abstract ⟨0,by decide⟩ (.body (.lam identityAlias (.var (by decide))))

theorem identity_fundamental (wf : UnifiedProgram.EnvWellFormed env) :
    ∃ scheme : Scheme [], Conv env scheme.syntax identity ∧ Conv env scheme.type identityType ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))),
        Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental wf identity_typed identity_recognized

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Computed.Examples
