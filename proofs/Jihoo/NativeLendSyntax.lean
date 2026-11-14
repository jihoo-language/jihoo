import Jihoo.NativeLoanScope
import Jihoo.NativeTyping

/-! Exact tree elaboration of Core.dependent_lend. The owner must be a source
variable and both callbacks retain their explicit ordinary lambdas. The reader
is specialized to Borrow(owner); the continuation is specialized to the same
owner given back. This does not assume either callback is typable at arbitrary
arguments, and it supplies no active-loan typing or lifetime oracle. -/
namespace Jihoo.NativeKernel
namespace Term
@[match_pattern] abbrev lend (owner reader continuation : Term) : Term :=
  .node .lend [owner,reader,continuation]
end Term

namespace Environment.Lending
structure Expansion where
  domain : Term
  read : Term
  continuation : Term
  deriving DecidableEq, Repr

def Expansion.rename (expansion : Expansion) (ρ : Nat → Nat) : Expansion :=
  ⟨expansion.domain.rename ρ,expansion.read.rename ρ,expansion.continuation.rename ρ⟩

def Expansion.subst (expansion : Expansion) (σ : Nat → Term) : Expansion :=
  ⟨expansion.domain.subst σ,expansion.read.subst σ,expansion.continuation.subst σ⟩

/-- The reader's bound reference is exactly the borrow of this owner. -/
def read (owner body : Term) : Term := body.subst (single (.borrow owner))

/-- Remove the returned-owner binder while retaining the result binder. -/
def restore (owner first body : Term) : Term :=
  .lam false first (body.subst (single (owner.rename Nat.succ)))

def dependent? : Term → Term → Term → Option Expansion
  | owner@(.var _), .lam false domain body, .lam false first (.lam false _ rest) =>
      some ⟨domain,read owner body,restore owner first rest⟩
  | _,_,_ => none

theorem dependent_exact : dependent? (.var owner) (.lam false domain body)
    (.lam false first (.lam false again rest)) =
      some ⟨domain,read (.var owner) body,restore (.var owner) first rest⟩ := rfl

theorem read_rename (owner body : Term) (ρ : Nat → Nat) :
    (read owner body).rename ρ = read (owner.rename ρ) (body.rename (Indexed.liftRenaming ρ)) := by
  simpa only [read,rename_borrow] using Term.rename_instantiate body (.borrow owner) ρ

theorem read_subst (owner body : Term) (σ : Nat → Term) :
    (read owner body).subst σ = read (owner.subst σ) (body.subst (liftSubOne σ)) := by
  simpa only [read,subst_borrow] using Term.subst_instantiate body (.borrow owner) σ

private theorem raise_rename (owner : Term) (ρ : Nat → Nat) :
    (owner.rename Nat.succ).rename (Indexed.liftRenaming ρ) = (owner.rename ρ).rename Nat.succ := by
  simp only [Term.rename_comp]
  rfl

private theorem raise_subst (owner : Term) (σ : Nat → Term) :
    (owner.rename Nat.succ).subst (liftSubOne σ) = (owner.subst σ).rename Nat.succ := by
  rw [Term.subst_rename,Term.rename_subst]
  rfl

theorem restore_rename (owner first body : Term) (ρ : Nat → Nat) :
    (restore owner first body).rename ρ =
      restore (owner.rename ρ) (first.rename ρ) (body.rename (liftRenaming 2 ρ)) := by
  simp only [restore,Term.lam,Term.rename,renameArgs,Op.binders,liftRenaming]
  rw [Term.rename_instantiate,raise_rename]

theorem restore_subst (owner first body : Term) (σ : Nat → Term) :
    (restore owner first body).subst σ =
      restore (owner.subst σ) (first.subst σ) (body.subst (liftSub 2 σ)) := by
  simp only [restore,Term.lam,Term.subst,substArgs,Op.binders,liftSub]
  rw [Term.subst_instantiate,raise_subst]

theorem dependent_rename (accepted : dependent? owner reader continuation = some expansion) (ρ : Nat → Nat) :
    dependent? (owner.rename ρ) (reader.rename ρ) (continuation.rename ρ) = some (expansion.rename ρ) := by
  fun_cases dependent? owner reader continuation <;> simp only [dependent?] at accepted
  · cases accepted
    simp only [Term.rename,renameArgs,Op.binders,liftRenaming,dependent?,Expansion.rename,
      read_rename,restore_rename]
  · contradiction

/-- Code substitution must preserve the named owner as a variable. Arbitrary
substitution is not claimed to preserve the native dependent-lend syntax gate. -/
theorem dependent_subst (accepted : dependent? owner reader continuation = some expansion)
    (named : owner.subst σ = .var nextOwner) :
    dependent? (owner.subst σ) (reader.subst σ) (continuation.subst σ) = some (expansion.subst σ) := by
  fun_cases dependent? owner reader continuation <;> simp only [dependent?] at accepted
  · cases accepted
    simp only [Term.subst] at named
    simp only [Term.subst,substArgs,Op.binders,liftSub,named,dependent?,Expansion.subst,
      read_subst,restore_subst]
  · contradiction

@[simp] theorem rename_lend (owner reader continuation : Term) (ρ : Nat → Nat) :
    (Term.lend owner reader continuation).rename ρ =
      .lend (owner.rename ρ) (reader.rename ρ) (continuation.rename ρ) := by
  simp only [Term.lend,Term.rename,renameArgs,Op.binders,liftRenaming]

@[simp] theorem subst_lend (owner reader continuation : Term) (σ : Nat → Term) :
    (Term.lend owner reader continuation).subst σ =
      .lend (owner.subst σ) (reader.subst σ) (continuation.subst σ) := by
  simp only [Term.lend,Term.subst,substArgs,Op.binders,liftSub]

end Environment.Lending
end Jihoo.NativeKernel
