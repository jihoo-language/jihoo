import Jihoo.NativeLendReduction

/-! Executable checking of the two specialized ghost bodies used by the
dependent Lend path. This computes their result, including the actual partial
scope removal. Owner/loan lifetime and runtime quantity admission are separate;
this is not an executable admission rule for unrestricted native Lend. -/
namespace Jihoo.NativeKernel.Environment.Lending

def inferResult? (fuel : Nat) (env : Environment) (ctx : Context) (expansion : Expansion) : Option Term :=
  match Checker.infer fuel env ctx true expansion.read,
      Checker.expose fuel env (Checker.infer fuel env ctx true expansion.continuation) with
  | some valueType, some (.pi false domain result) =>
      if Conversion.equal env fuel valueType domain then
        (Conversion.normalize? env fuel result).bind fun normal => PartialRenaming.shift (-1) 0 normal
      else none
  | _,_ => none

def inferDependentGhost? (fuel : Nat) (env : Environment) (ctx : Context)
    (owner reader continuation : Term) : Option Term :=
  (dependent? owner reader continuation).bind (inferResult? fuel env ctx)

theorem inferResult?_sound
    (accepted : inferResult? fuel env ctx expansion = some outside) :
    ∃ domain result normal,
      HasType env ctx true expansion.read domain ∧
      HasType env ctx true expansion.continuation (.pi false domain result) ∧
      Conversion.Conv env result normal ∧
      PartialRenaming.shift (-1) 0 normal = some outside := by
  unfold inferResult? at accepted
  split at accepted
  · rename_i valueType domain result valueFound continuationFound
    split at accepted
    · rename_i same
      cases normalized : Conversion.normalize? env fuel result with
      | none => simp [normalized] at accepted
      | some normal =>
        simp only [normalized,Option.bind_some] at accepted
        obtain ⟨inferred,found,converted⟩ := Checker.expose_elim continuationFound
        exact ⟨domain,result,normal,
          (Checker.infer_sound valueFound).convert (Conversion.equal_sound same),
          (Checker.infer_sound found).convert converted,
          Conversion.normalize?_sound normalized,accepted⟩
    · contradiction
  · contradiction

/-- The result is constructed from successful executable body checks, not an
assumed typing of either the final result or the original callbacks. -/
theorem inferDependentGhost?_sound
    (wf : UnifiedProgram.EnvWellFormed env)
    (accepted : inferDependentGhost? fuel env ctx owner reader continuation = some outside) :
    ∃ output, EnvironmentDelta.Forward env (desugar owner reader continuation) output ∧
      HasType env ctx true output outside := by
  unfold inferDependentGhost? at accepted
  cases expanded : dependent? owner reader continuation with
  | none => simp [expanded] at accepted
  | some expansion =>
    simp only [expanded,Option.bind_some] at accepted
    obtain ⟨domain,result,normal,readTyped,continuationTyped,converted,removed⟩ :=
      inferResult?_sound accepted
    exact dependent_original_type wf expanded readTyped continuationTyped converted removed

end Jihoo.NativeKernel.Environment.Lending
