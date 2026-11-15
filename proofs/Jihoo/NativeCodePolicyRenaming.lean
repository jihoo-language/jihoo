import Jihoo.NativeEnvironmentGhostMetatheory
import Jihoo.NativeInferredKindArguments

/-! Runtime admission policies are stable under capture-free variable
renaming. This module does not substitute computations for variables. In
particular it retains the actual code/ghost mode and environment metadata. -/
namespace Jihoo.NativeKernel.Environment

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

@[simp] theorem kindOf_rename (term : Term) (ρ : Nat → Nat) :
    kindOf (term.rename ρ) = kindOf term := by
  fun_induction kindOf term generalizing ρ <;>
    simp_all [kindOf, Term.rename, renameArgs, Op.binders, liftRenaming]
  case case3 term _ _ =>
    cases term with
    | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
    | node op args =>
        cases op <;> cases args with
        | nil => simp_all [kindOf, Term.rename, renameArgs]
        | cons a args =>
            cases args with
            | nil => simp_all [kindOf, Term.rename, renameArgs]
            | cons b args => cases args <;> simp_all [kindOf, Term.rename, renameArgs]

@[simp] theorem firstOrderKind_rename (term : Term) (ρ : Nat → Nat) :
    firstOrderKind (term.rename ρ) = firstOrderKind term := by
  fun_induction firstOrderKind term generalizing ρ <;>
    simp_all [firstOrderKind, Term.rename, renameArgs, Op.binders, liftRenaming]
  case case3 term _ _ =>
    cases term with
    | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
    | node op args =>
        cases op <;> cases args with
        | nil => simp_all [firstOrderKind, Term.rename, renameArgs]
        | cons a args =>
            cases args with
            | nil => simp_all [firstOrderKind, Term.rename, renameArgs]
            | cons b args =>
                cases args <;> try simp_all [firstOrderKind, Term.rename, renameArgs]
                all_goals cases a with
                | var => simp_all [firstOrderKind, Term.rename, renameArgs]
                | node aop achildren =>
                    cases aop <;> cases achildren <;>
                      simp_all [firstOrderKind, Term.rename, renameArgs]

@[simp] theorem scalarLoopMotive_rename (term : Term) (ρ : Nat → Nat) :
    scalarLoopMotive (term.rename ρ) = scalarLoopMotive term := by
  cases term with
  | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
  | node op args =>
      cases op <;> cases args with
      | nil => simp [scalarLoopMotive, Term.rename, renameArgs]
      | cons a args =>
          cases args with
          | nil => simp [scalarLoopMotive, Term.rename, renameArgs]
          | cons b args =>
              cases args <;> try simp [scalarLoopMotive, Term.rename, renameArgs]
              all_goals cases b with
              | var => simp [scalarLoopMotive, Term.rename, renameArgs]
              | node bop bchildren =>
                  cases bop <;> cases bchildren with
                  | nil => simp [scalarLoopMotive, Term.rename, renameArgs]
                  | cons c rest => cases rest <;> simp [scalarLoopMotive, Term.rename, renameArgs]

@[simp] theorem hasLeadingLambdas_rename (count : Nat) (term : Term) (ρ : Nat → Nat) :
    hasLeadingLambdas count (term.rename ρ) = hasLeadingLambdas count term := by
  fun_induction hasLeadingLambdas count term generalizing ρ <;>
    simp_all [hasLeadingLambdas, Term.rename, renameArgs, Op.binders, liftRenaming]
  case case3 count term _ =>
    cases term with
    | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
    | node op args =>
        cases op <;> cases args with
        | nil => simp_all [hasLeadingLambdas, Term.rename, renameArgs]
        | cons a args =>
            cases args with
            | nil => simp_all [hasLeadingLambdas, Term.rename, renameArgs]
            | cons b args => cases args <;> simp_all [hasLeadingLambdas, Term.rename, renameArgs]

@[simp] theorem globalFree_rename (term : Term) (ρ : Nat → Nat) :
    globalFree (term.rename ρ) = globalFree term := by
  induction term using Term.rec
    (motive_2 := fun args => ∀ op offset ρ,
      globalFreeArgs (renameArgs op ρ offset args) = globalFreeArgs args) generalizing ρ with
  | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
  | node op args ih => cases op <;> simp only [Term.rename, globalFree, ih]
  | nil => simp [renameArgs, globalFreeArgs]
  | cons term rest head tail =>
      rename_i op offset ρ
      simp [renameArgs, globalFreeArgs, head, tail]

@[simp] theorem purePlain_rename (term : Term) (ρ : Nat → Nat) :
    NativeKernel.plain (term.rename ρ) = NativeKernel.plain term := by
  induction term using Term.rec
    (motive_2 := fun args =>
      (∀ term ∈ args, ∀ ρ, NativeKernel.plain (term.rename ρ) = NativeKernel.plain term) ∧
      (∀ op offset ρ, plainArgs (renameArgs op ρ offset args) = plainArgs args)) generalizing ρ with
  | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
  | node op args ih =>
      cases op <;> try simp only [Term.rename, NativeKernel.plain, ih.2]
      all_goals cases args with
      | nil => simp [Term.rename, renameArgs, NativeKernel.plain]
      | cons a args =>
          cases args with
          | nil => simp [Term.rename, renameArgs, NativeKernel.plain]
          | cons b rest =>
              cases rest <;> simp [Term.rename, renameArgs, NativeKernel.plain, ih.1 b (by simp)]
  | nil => exact ⟨by simp, by intros; simp only [renameArgs, plainArgs, familyPlainArgs]⟩
  | cons term rest head tail =>
      constructor
      · intro child member ρ
        rcases List.mem_cons.mp member with rfl | member
        · exact head ρ
        · exact tail.1 child member ρ
      · intro op offset ρ
        simp [renameArgs, plainArgs, head, tail.2]

@[simp] theorem plain_rename (term : Term) (ρ : Nat → Nat) :
    plain env (term.rename ρ) = plain env term := by
  simp only [plain, globalFree_rename, purePlain_rename, familyPlain_rename]

@[simp] theorem iterationMemoryFree_rename (term : Term) (ρ : Nat → Nat) :
    iterationMemoryFree env (term.rename ρ) = iterationMemoryFree env term := by
  induction term using Term.rec
    (motive_2 := fun args => ∀ op offset renameOp renameOffset ρ,
      iterationMemoryFreeArgs env op offset (renameArgs renameOp ρ renameOffset args) =
        iterationMemoryFreeArgs env op offset args) generalizing ρ with
  | var => simp [Term.rename, kindOf, firstOrderKind, scalarLoopMotive, hasLeadingLambdas, globalFree, NativeKernel.plain, familyPlain, iterationMemoryFree]
  | node op args ih => cases op <;> simp only [Term.rename, iterationMemoryFree, ih]
  | nil => simp [renameArgs, iterationMemoryFreeArgs]
  | cons term rest head tail =>
      rename_i op offset renameOp renameOffset ρ
      simp [renameArgs, iterationMemoryFreeArgs, head, tail]

private theorem liftRenaming_above (binders : Nat) (ρ : Nat → Nat) (x : Nat) :
    liftRenaming binders ρ (x + binders) = ρ x + binders := by
  induction binders with
  | zero => rfl
  | succ n ih =>
      simp only [Nat.add_succ, liftRenaming, Indexed.liftRenaming, Nat.add_eq, Nat.add_zero]
      exact congrArg Nat.succ ih

private theorem rename_under_scope (term : Term) (binders : Nat) (ρ : Nat → Nat) :
    (term.rename (fun x => x + binders)).rename (liftRenaming binders ρ) =
      (term.rename ρ).rename (fun x => x + binders) := by
  rw [Term.rename_comp, Term.rename_comp]
  congr 1
  funext x
  exact liftRenaming_above binders ρ x

/-- Removing a fixed binder prefix after a renaming gives the renamed
original result. No dependency on the removed slots can be introduced. -/
theorem lower_rename_scope (success : PartialRenaming.lower 0 binders term = some result)
    (ρ : Nat → Nat) :
    PartialRenaming.lower 0 binders (term.rename (liftRenaming binders ρ)) =
      some (result.rename ρ) := by
  have restored := PartialRenaming.lower_reweakens success
  have restoreEq : PartialRenaming.raiseIndex 0 binders = (fun x => x + binders) := by
    funext x
    simp [PartialRenaming.raiseIndex]
  rw [restoreEq] at restored
  rw [← restored, rename_under_scope]
  exact lower_raised (result.rename ρ) binders

theorem drop_shift_rename_scope {binders : Nat}
    (success : PartialRenaming.shift (-(binders : Int)) 0 term = some result)
    (ρ : Nat → Nat) :
    PartialRenaming.shift (-(binders : Int)) 0 (term.rename (liftRenaming binders ρ)) =
      some (result.rename ρ) := by
  cases binders with
  | zero =>
      have raiseEq : PartialRenaming.raiseIndex 0 0 = id := by
        funext x
        simp [PartialRenaming.raiseIndex]
      have shiftZero (t : Term) : PartialRenaming.shift 0 0 t = some t := by
        rw [PartialRenaming.shift_nonnegative (by decide)]
        change some (t.rename (PartialRenaming.raiseIndex 0 0)) = some t
        rw [raiseEq, Term.rename_id]
      change PartialRenaming.shift 0 0 term = some result at success
      rw [shiftZero] at success
      cases Option.some.inj success
      change PartialRenaming.shift 0 0 (term.rename ρ) = some (term.rename ρ)
      exact shiftZero _
  | succ n =>
      rw [PartialRenaming.shift_negative (Int.neg_lt_zero_iff.mpr (Int.ofNat_succ_pos n))] at success ⊢
      simp only [Int.neg_neg, Int.toNat_natCast] at success ⊢
      exact lower_rename_scope success ρ

/-- The motive binder remains protected even when array sizes refer to
arbitrary outer variables. Success of the actual partial scope removal is
transported rather than replaced by a closed-size assumption. -/
theorem viewRepresentation_rename (representation : viewRepresentation fuel binders term = true)
    (ρ : Nat → Nat) :
    viewRepresentation fuel binders (term.rename (liftRenaming binders ρ)) = true := by
  induction fuel generalizing binders term with
  | zero => simp [viewRepresentation] at representation
  | succ fuel ih =>
      cases term with
      | var => simp [viewRepresentation] at representation
      | node op args =>
          cases op <;> cases args with
          | nil => simp_all [viewRepresentation, Term.rename, renameArgs]
          | cons a args =>
              cases args with
              | nil =>
                  try simp_all [viewRepresentation, Term.rename, renameArgs]
                  all_goals
                    cases observed : PartialRenaming.shift (-(binders : Int)) 0 a with
                    | none => simp_all only [viewRepresentation, observed, Option.isSome_none, Bool.false_eq_true]
                    | some result =>
                        have shifted := drop_shift_rename_scope observed ρ
                        simpa only [viewRepresentation, Term.rename, renameArgs,
                          Op.binders, liftRenaming, shifted, Option.isSome_some]
              | cons b rest =>
                  cases rest <;> try simp_all [viewRepresentation, Term.rename, renameArgs]
                  all_goals
                    simpa only [Term.rename, renameArgs, Op.binders, liftRenaming,
                      viewRepresentation] using ih representation

 theorem applicationAllowed.renaming (allowed : applicationAllowed env mode domain argument)
    (ρ : Nat → Nat) (closed : Conversion.Closed env) :
    applicationAllowed env mode (domain.rename ρ) (argument.rename ρ) := by
  rcases allowed with ghost | ⟨normal, converted, globals, simple | ⟨kind, value, convertedValue, plainValue⟩⟩
  · exact Or.inl ghost
  · exact Or.inr ⟨normal.rename ρ, converted.renaming ρ closed,
      by simpa using globals, Or.inl (by simpa using simple)⟩
  · exact Or.inr ⟨normal.rename ρ, converted.renaming ρ closed,
      by simpa using globals, Or.inr ⟨by simpa using kind,
        value.rename ρ, convertedValue.renaming ρ closed, by simpa using plainValue⟩⟩

 theorem nonFunction_renaming (allowed : nonFunction env term) (ρ : Nat → Nat)
    (closed : Conversion.Closed env) : nonFunction env (term.rename ρ) := by
  obtain ⟨normal, converted, head⟩ := allowed
  refine ⟨normal.rename ρ, converted.renaming ρ closed, ?_⟩
  cases normal <;> simpa only [Term.rename,
    FamilyIota.Extended.nonFunctionHead] using head

 theorem absurdAllowed.renaming (allowed : absurdAllowed env mode term) (ρ : Nat → Nat)
    (closed : Conversion.Closed env) : absurdAllowed env mode (term.rename ρ) := by
  rcases allowed with ghost | allowed
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_renaming allowed ρ closed)

 theorem continuationAllowed.renaming (allowed : continuationAllowed env mode term) (ρ : Nat → Nat)
    (closed : Conversion.Closed env) : continuationAllowed env mode (term.rename ρ) := by
  rcases allowed with ghost | allowed
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_renaming allowed ρ closed)

 theorem IterationBodyAllowed.renaming (allowed : IterationBodyAllowed env mode body)
    (ρ : Nat → Nat) : IterationBodyAllowed env mode (body.rename ρ) := by
  rcases allowed with ghost | leading | free
  · exact Or.inl ghost
  · exact Or.inr (Or.inl (by simpa using leading))
  · exact Or.inr (Or.inr (by simpa using free))

 theorem IterationMotiveAllowed.renaming (allowed : IterationMotiveAllowed env mode proof motive)
    (ρ : Nat → Nat) (closed : Conversion.Closed env) :
    IterationMotiveAllowed env mode proof (motive.rename ρ) := by
  rcases allowed with ghost | proof | ⟨normal, converted, scalar⟩ | ⟨flag, domain, body, converted, owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl ⟨normal.rename ρ, converted.renaming ρ closed, by simpa using scalar⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨flag, domain.rename ρ, body.rename (liftRenaming 1 ρ),
      by simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ closed,
      owned.renaming _ closed⟩))

 theorem ViewMotiveAllowed.renaming (allowed : ViewMotiveAllowed env mode dependent motive)
    (ρ : Nat → Nat) (closed : Conversion.Closed env) :
    ViewMotiveAllowed env mode dependent (motive.rename ρ) := by
  rcases allowed with ghost | nondependent | ⟨flag, domain, body, converted, represented⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl nondependent)
  · exact Or.inr (Or.inr ⟨flag, domain.rename ρ, body.rename (liftRenaming 1 ρ),
      by simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ closed,
      viewRepresentation_rename represented ρ⟩)

end Jihoo.NativeKernel.Environment
