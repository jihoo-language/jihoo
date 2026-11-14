import Jihoo.NativeLendGhostChecking

/-! The two native ghost Lend rule shapes and their pure-model soundness.
The generic rule uses actual callback typing. The dependent rule instead uses
the specialized bodies checked by the kernel. Runtime loans are not claimed. -/
namespace Jihoo.NativeKernel.Environment.Lending

def outlivedHead (env : Environment) : Term → Bool
  | .u64 | .i64 | .refine _ | .array _ | .buffer _ | .back _ _ _ => true
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.declaration.data
  | _ => false

def Outlived (env : Environment) (type : Term) : Prop :=
  ∃ normal, Conversion.Conv env type normal ∧ outlivedHead env normal = true

private theorem app_constant
    (function : HasType env ctx true f (.pi false A (B.rename Nat.succ)))
    (argument : HasType env ctx true a A) : HasType env ctx true (.app f a) B := by
  have applied := HasType.app function argument (Or.inl rfl)
  change HasType env ctx true (.app f a) ((B.rename Nat.succ).subst (single a)) at applied
  simpa only [Term.shift_subst_single] using applied

theorem generic_pure_typed
    (ownerTyped : HasType env ctx true owner ownerType) (owned : Owned env ownerType)
    (readerTyped : HasType env ctx true reader (.pi false (.ref ownerType) (valueType.rename Nat.succ)))
    (continuationTyped : HasType env ctx true continuation
      (.pi false valueType ((Term.pi false ownerType (result.rename Nat.succ)).rename Nat.succ))) :
    HasType env ctx true (desugar owner reader continuation) result := by
  have borrowed : HasType env ctx true (.borrow owner) (.ref ownerType) :=
    .ghostBorrowOwned ownerTyped owned
  have readTyped : HasType env ctx true (.app reader (.borrow owner)) valueType := by
    exact app_constant readerTyped borrowed
  have continued : HasType env ctx true (.app continuation (.app reader (.borrow owner)))
      (.pi false ownerType (result.rename Nat.succ)) := by
    exact app_constant continuationTyped readTyped
  exact app_constant continued ownerTyped

/-- Source-facing ghost rule premises. These are kernel subchecks, never a
typing or normalization premise about the final expanded result. -/
inductive GhostDerivation (env : Environment) (ctx : Context) : Term → Term → Prop where
  | generic : HasType env ctx true owner ownerType → Owned env ownerType → Outlived env valueType →
      HasType env ctx true reader (.pi false (.ref ownerType) (valueType.rename Nat.succ)) →
      HasType env ctx true continuation
        (.pi false valueType ((Term.pi false ownerType (result.rename Nat.succ)).rename Nat.succ)) →
      GhostDerivation env ctx (.lend owner reader continuation) result
  | dependent : HasType env ctx true owner ownerType → Owned env ownerType →
      dependent? owner reader continuation = some expansion →
      Binder env ctx false expansion.domain domainSort →
      Conversion.Conv env expansion.domain (.ref ownerType) → Outlived env valueType →
      (∃ first again body, continuation = .lam false first (.lam false again body) ∧
        Conversion.Conv env again (ownerType.rename Nat.succ)) →
      HasType env ctx true expansion.read valueType →
      HasType env ctx true expansion.continuation (.pi false valueType bodyType) →
      Conversion.Conv env bodyType normal → PartialRenaming.shift (-1) 0 normal = some outside →
      GhostDerivation env ctx (.lend owner reader continuation) outside

/-- Every ghost rule constructs a typed pure-model result by actual finite
forward computation. No arbitrary reverse-typing or code reduction is used. -/
theorem GhostDerivation.sound
    (wf : UnifiedProgram.EnvWellFormed env)
    (derived : GhostDerivation env ctx (.lend owner reader continuation) type) :
    ∃ output, EnvironmentDelta.Forward env (desugar owner reader continuation) output ∧
      HasType env ctx true output type := by
  cases derived with
  | generic ownerTyped owned outlived readerTyped continuationTyped =>
    exact ⟨_,.refl,generic_pure_typed ownerTyped owned readerTyped continuationTyped⟩
  | dependent ownerTyped owned expanded binder domain outlived returned readTyped continuationTyped converted removed =>
    exact dependent_original_type wf expanded readTyped continuationTyped converted removed

end Jihoo.NativeKernel.Environment.Lending
