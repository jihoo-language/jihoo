import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanLendPreservation

/-! A hereditary induction interface for loan typing functionality. Non-lambda
substitution images cannot expose a new explicit Lend callback. Owned owners
and outlived reader results supply this head condition from actual typing. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

/-- Functionality is compared at the same context, with arbitrary permission
stacks and modes. The context itself is unrestricted. -/
def Unique (env : Environment) (term : Term) : Prop :=
  ∀ {ctx loans loans' mode mode' first second},
    HasType env loans ctx mode term first → HasType env loans' ctx mode' term second → Conv env first second

def RenamedUnique (env : Environment) (term : Term) : Prop :=
  ∀ ρ : Nat → Nat,Unique env (term.rename ρ)

def NoLambdaHead : Term → Prop
  | .node (.lam _) _ => False
  | _ => True

theorem RenamedUnique.renaming (unique : RenamedUnique env term) (ρ : Nat → Nat) :
    RenamedUnique env (term.rename ρ) := by
  intro τ ctx loans loans' mode mode' first second left right
  exact unique (fun x => τ (ρ x))
    (by simpa only [Term.rename_comp] using left)
    (by simpa only [Term.rename_comp] using right)

theorem NoLambdaHead.renaming (head : NoLambdaHead term) (ρ : Nat → Nat) :
    NoLambdaHead (term.rename ρ) := by
  cases term with
  | var => simp only [Term.rename,NoLambdaHead]
  | node op children => cases op <;> simp_all only [Term.rename,NoLambdaHead]

theorem variable_renamed_unique (index : Nat) : RenamedUnique env (.var index) := by
  intro ρ ctx loans loans' mode mode' first second left right
  simp only [Term.rename] at left right
  obtain ⟨binding,found,converted⟩ := left.principalView
  obtain ⟨binding',found',converted'⟩ := right.principalView
  have same := Option.some.inj (found.symm.trans found')
  subst binding'
  exact converted.symm.trans converted'

theorem borrow_renamed_unique (unique : RenamedUnique env owner) : RenamedUnique env (.borrow owner) := by
  intro ρ ctx loans loans' mode mode' first second left right
  simp only [Term.borrow,Term.rename,renameArgs,Op.binders,liftRenaming] at left right
  obtain ⟨ownerType,ownerTyped,converted⟩ := left.principalView
  obtain ⟨ownerType',ownerTyped',converted'⟩ := right.principalView
  have owners := unique ρ ownerTyped ownerTyped'
  exact converted.symm.trans ((RawLend.Conv.node .ref (.cons owners .nil)).trans converted')

structure UniqueSubstitution (env : Environment) (σ : Nat → Term) : Prop where
  unique : ∀ index,RenamedUnique env (σ index)
  noLambda : ∀ index,NoLambdaHead (σ index)

theorem UniqueSubstitution.identity : UniqueSubstitution env Term.var :=
  ⟨variable_renamed_unique,fun _ => True.intro⟩

theorem UniqueSubstitution.renaming (certified : UniqueSubstitution env σ) (ρ : Nat → Nat) :
    UniqueSubstitution env (fun index => (σ index).rename ρ) :=
  ⟨fun index => (certified.unique index).renaming ρ,
    fun index => (certified.noLambda index).renaming ρ⟩

theorem UniqueSubstitution.liftOne (certified : UniqueSubstitution env σ) :
    UniqueSubstitution env (liftSubOne σ) := by
  constructor
  · intro index
    cases index with
    | zero => exact variable_renamed_unique 0
    | succ index => exact (certified.unique index).renaming Nat.succ
  · intro index
    cases index with
    | zero => trivial
    | succ index => exact (certified.noLambda index).renaming Nat.succ

theorem UniqueSubstitution.lift (certified : UniqueSubstitution env σ) (depth : Nat) :
    UniqueSubstitution env (liftSub depth σ) := by
  induction depth with
  | zero => exact certified
  | succ depth ih => exact ih.liftOne

def prependSub (value : Term) (σ : Nat → Term) : Nat → Term
  | 0 => value
  | index+1 => σ index

theorem UniqueSubstitution.prepend (certified : UniqueSubstitution env σ)
    (unique : RenamedUnique env value) (head : NoLambdaHead value) :
    UniqueSubstitution env (prependSub value σ) := by
  constructor
  · intro index;cases index with
    | zero => exact unique
    | succ index => exact certified.unique index
  · intro index;cases index with
    | zero => exact head
    | succ index => exact certified.noLambda index

theorem read_substitution (body owner : Term) (σ : Nat → Term) :
    Lending.read owner (body.subst (liftSubOne σ)) = body.subst (prependSub (.borrow owner) σ) := by
  rw [Lending.read,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp only [prependSub,liftSubOne,single,Term.subst]
  | succ index => simp only [prependSub,liftSubOne,single,Term.shift_subst_single]

theorem finish_substitution (body owner value : Term) (σ : Nat → Term) :
    Lending.finish owner (body.subst (liftSub 2 σ)) value =
      body.subst (prependSub owner (prependSub value σ)) := by
  rw [Lending.finish,Term.subst_comp,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp only [prependSub,liftSub,liftSubOne,single,Term.subst,Term.rename,Term.subst_rename,Term.subst_id,Term.shift_subst_single]
  | succ index => cases index with
    | zero => simp only [prependSub,liftSub,liftSubOne,single,Term.subst,Term.rename,Term.subst_rename,Term.subst_id,Term.shift_subst_single]
    | succ index => simp only [prependSub,liftSub,liftSubOne,single,Term.rename,Term.subst,Term.subst_rename,Term.subst_id,Term.shift_subst_single]

private theorem owned_nonFunction (owned : Owned env type) : RawLend.NonFunction env type := by
  cases owned with
  | buffer converted => exact RawLend.NonFunction.of_conversion converted (.ofHead rfl)
  | family found boxed converted => exact RawLend.NonFunction.of_conversion converted (.ofHead rfl)

private theorem outlived_nonFunction (outlived : Outlived env type) : RawLend.NonFunction env type := by
  obtain ⟨normal,converted,head⟩ := outlived
  apply RawLend.NonFunction.of_conversion converted
  apply RawLend.NonFunction.ofHead
  cases normal with
  | var => simp [Lending.outlivedHead] at head
  | node op children =>
      cases op <;> simp_all [Lending.outlivedHead,RawLend.nonFunctionHead,RawLend.nonFunctionOp]

theorem HasType.noLambdaHead (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) (nonFunction : RawLend.NonFunction env type) : NoLambdaHead term := by
  cases term with
  | var => trivial
  | node op children =>
      cases op <;> try trivial
      case lam erased =>
        have view := typed.principalView
        cases children with
        | nil => exact view
        | cons domain children => cases children with
          | nil => exact view
          | cons body children => cases children with
            | cons extra rest => exact view
            | nil =>
                obtain ⟨result,bodyTyped,converted⟩ := view
                exact nonFunction.not_pi converted.symm wf.admissible

theorem HasType.owned_noLambdaHead (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) (owned : Owned env type) : NoLambdaHead term :=
  typed.noLambdaHead wf (owned_nonFunction owned)

theorem HasType.outlived_noLambdaHead (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) (outlived : Outlived env type) : NoLambdaHead term :=
  typed.noLambdaHead wf (outlived_nonFunction outlived)

 theorem RenamedUnique.original (unique : RenamedUnique env term) : Unique env term := by
  intro ctx loans loans' mode mode' first second left right
  exact unique id (by simpa only [Term.rename_id] using left) (by simpa only [Term.rename_id] using right)

end Jihoo.NativeKernel.Environment.LoanTyping
