import Jihoo.NativeMultiUniverseClosure
set_option maxUniverseOffset 40

/-! Computed type annotations with arbitrarily nested first-order type-level
lambda applications. Normal forms and conversion coherence are constructed by
structural recursion on source code; normalization is not a theorem premise.
Open code variables here denote types, not higher-kinded functions. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
open Jihoo.NativeKernel.Environment.Conversion

def Mono.substitute (A : Mono count) (substitution : Fin count → Mono target) : Mono target :=
  match A with
  | .parameter index => substitution index
  | .natural => .natural
  | .arrow A B => .arrow (A.substitute substitution) (B.substitute substitution)

theorem Mono.substitute_instantiate (A : Mono count) (substitution : Fin count → Mono target)
    (parameters : Fin target → Term) :
    (A.substitute substitution).instantiate parameters =
      A.instantiate (fun index => (substitution index).instantiate parameters) := by
  induction A generalizing parameters with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb =>
    simp only [Mono.substitute,Mono.instantiate,ha,hb]
    congr 1
    congr 1
    funext index
    exact ((substitution index).instantiate_rename parameters Nat.succ).symm

def extendParameters (parameters : Fin count → Term) : Fin (count+1) → Term :=
  Fin.cases (.var 0) (fun index => (parameters index).rename Nat.succ)

theorem extended_parameters_instantiation (A : Mono (count+1)) (parameters : Fin count → Term) (argument : Term) :
    (A.instantiate (extendParameters parameters)).subst (single argument) =
      A.instantiate (Fin.cases argument parameters) := by
  rw [Mono.instantiate_subst]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => simp only [extendParameters,Fin.cases_zero,Term.subst,NativeKernel.single]
  | succ index => simpa only [extendParameters,Fin.cases_succ] using Term.shift_subst_single (parameters index) argument

inductive Code : Nat → Type where
  | parameter (index : Fin count) : Code count
  | natural : Code count
  | arrow (domain codomain : Code count) : Code count
  | beta (level : Fin 32) (body : Code (count+1)) (argument : Code count) : Code count

def Code.normal : Code count → Mono count
  | .parameter index => .parameter index
  | .natural => .natural
  | .arrow A B => .arrow A.normal B.normal
  | .beta _ expression argument => expression.normal.substitute (Fin.cases argument.normal Mono.parameter)

def Code.instantiate (parameters : Fin count → Term) : Code count → Term
  | .parameter index => parameters index
  | .natural => .u64
  | .arrow A B => .pi false (A.instantiate parameters)
      (B.instantiate (fun index => (parameters index).rename Nat.succ))
  | .beta level expression argument =>
    .app (.lam false (.univ level.val) (expression.instantiate (extendParameters parameters)))
      (argument.instantiate parameters)

def Code.syntax (offset : Nat) (code : Code count) : Term :=
  code.instantiate (fun index => .var (offset+index.val))

/-- Source normalization is a constructive structural theorem. Its conversion
steps are actual environment-indexed beta/congruence, including arbitrary
nesting under type arrows and type-level abstractions. -/
theorem Code.normalizes (code : Code count) (parameters : Fin count → Term) :
    Conv env (code.instantiate parameters) (code.normal.instantiate parameters) := by
  induction code with
  | parameter => exact .refl _
  | natural => exact .refl _
  | arrow A B ha hb =>
    exact .node (.pi false) (.cons (ha parameters) (.cons (hb _) .nil))
  | @beta width level expression argument he ha =>
    refine .trans (.node .app (.cons
      (.node (.lam false) (.cons (.refl _) (.cons (he _) .nil))) (.cons (ha parameters) .nil))) ?_
    refine .trans (.legacy (.beta false (.univ level.val) _ _)) ?_
    rw [extended_parameters_instantiation,Code.normal,Mono.substitute_instantiate]
    have same : (fun index : Fin (width+1) => ((Fin.cases argument.normal Mono.parameter : Fin (width+1) → Mono width) index).instantiate parameters) =
        Fin.cases (argument.normal.instantiate parameters) parameters := by
      funext index
      cases index using Fin.cases <;> simp only [Fin.cases_zero,Fin.cases_succ,Mono.instantiate]
    rw [same]
    exact .refl _

def Code.code (code : Code count) (assignment : Assignment levels) : Finite.Universe (code.normal.semanticSort levels) :=
  code.normal.code assignment

theorem Code.normal_coherent (wf : UnifiedProgram.EnvWellFormed env) {first second : Code count}
    (converted : Conv env (first.syntax offset) (second.syntax offset)) : first.normal = second.normal :=
  Mono.syntax_injective wf (.trans (first.normalizes _).symm (.trans converted (second.normalizes _)))

theorem Code.model_coherent (wf : UnifiedProgram.EnvWellFormed env) {first second : Code count}
    (converted : Conv env (first.syntax offset) (second.syntax offset)) (assignment : Assignment levels) :
    HEq (first.code assignment) (second.code assignment) := by
  exact Mono.code_coherent wf
    (.trans (first.normalizes _).symm (.trans converted (second.normalizes _))) assignment

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
