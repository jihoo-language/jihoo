import Jihoo.NativeNeutralSpines
import Jihoo.NativeMultiUniverseModel
set_option maxUniverseOffset 40

/-! Concrete higher-kinded family assignments at independently chosen finite
native universe levels. Source code validity is a decidable level condition;
model values and coherence are constructed and are not fields of validity. -/
namespace Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
open Jihoo.NativeKernel.Environment.Conversion

structure Signature where
  input : Fin 32
  result : Fin 32

def Signature.term (signature : Signature) : Term :=
  .pi false (.univ signature.input.val) (.univ signature.result.val)

def Signature.kindCode (signature : Signature) :=
  Finite.pi (Finite.Values.codeUniverse signature.input)
    (.type ⟨signature.result.val+1,by omega⟩)
    (fun _ => Finite.Values.codeUniverse signature.result)

def Signature.applyCode (signature : Signature)
    (family : Finite.Carrier signature.kindCode)
    (argument : Finite.Universe (.type ⟨signature.input.val,by omega⟩)) :
    Finite.Universe (.type ⟨signature.result.val,by omega⟩) :=
  Finite.Values.decode signature.result
    ((Finite.piMeaning (Finite.Values.codeUniverse signature.input)
      (.type ⟨signature.result.val+1,by omega⟩)
      (fun _ => Finite.Values.codeUniverse signature.result)).app family
        (Finite.Values.encode signature.input argument))

variable {parameters families : Nat} {levels : Fin parameters → Fin 32} {signatures : Fin families → Signature}

def Signature.emptyFamily (signature : Signature) : Finite.Carrier signature.kindCode :=
  (Finite.piMeaning (Finite.Values.codeUniverse signature.input)
    (.type ⟨signature.result.val+1,by omega⟩)
    (fun _ => Finite.Values.codeUniverse signature.result)).lam
      (fun _ => Finite.Values.encode signature.result (Finite.Values.empty signature.result))

theorem Signature.apply_emptyFamily (signature : Signature)
    (argument : Finite.Universe (.type ⟨signature.input.val,by omega⟩)) :
    signature.applyCode signature.emptyFamily argument = Finite.Values.empty signature.result := by
  unfold Signature.applyCode Signature.emptyFamily
  rw [(Finite.piMeaning _ _ _).beta,Finite.Values.decode_encode]

structure Assignment (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) where
  parameters : ∀ index, Finite.Universe (.type ⟨(levels index).val,by omega⟩)
  families : ∀ index, Finite.Carrier (signatures index).kindCode

def Assignment.empty (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    Assignment levels signatures where
  parameters index := Finite.Values.empty (levels index)
  families index := (signatures index).emptyFamily

inductive TypeCode (parameters families : Nat) where
  | parameter (index : Fin parameters)
  | natural
  | arrow (domain codomain : TypeCode parameters families)
  | application (family : Fin families) (argument : TypeCode parameters families)
  deriving DecidableEq

def TypeCode.level (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    TypeCode parameters families → Nat
  | .parameter index => (levels index).val
  | .natural => 0
  | .arrow A B => max (A.level levels signatures) (B.level levels signatures)
  | .application family _ => (signatures family).result.val

def TypeCode.Valid (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    TypeCode parameters families → Prop
  | .parameter _ => True
  | .natural => True
  | .arrow A B => A.Valid levels signatures ∧ B.Valid levels signatures
  | .application family argument => argument.Valid levels signatures ∧
      argument.level levels signatures = (signatures family).input.val

theorem TypeCode.level_bound (A : TypeCode parameters families) : A.level levels signatures < 32 := by
  induction A with
  | parameter index => exact (levels index).isLt
  | natural => change 0 < 32; decide
  | arrow A B ha hb => exact Nat.max_lt.mpr ⟨ha,hb⟩
  | application family argument ih => exact (signatures family).result.isLt

def TypeCode.sort (A : TypeCode parameters families) (levels : Fin parameters → Fin 32)
    (signatures : Fin families → Signature) : Finite.LevelSort := .type ⟨A.level levels signatures,by have := A.level_bound (levels := levels) (signatures := signatures); omega⟩

def TypeCode.meaning (assignment : Assignment levels signatures) :
    (A : TypeCode parameters families) → A.Valid levels signatures → Finite.Universe (A.sort levels signatures)
  | .parameter index, _ => assignment.parameters index
  | .natural, _ => Finite.natural
  | .arrow A B, valid =>
    Finite.pi (A.meaning assignment valid.1) (B.sort levels signatures)
      (fun _ => B.meaning assignment valid.2)
  | .application family argument, valid =>
    (signatures family).applyCode (assignment.families family)
      (cast (congrArg Finite.Universe (congrArg Finite.LevelSort.type (Fin.ext valid.2)))
        (argument.meaning assignment valid.1))

def TypeCode.instantiate (parameters : Fin count → Term) (families : Fin familyCount → Term) :
    TypeCode count familyCount → Term
  | .parameter index => parameters index
  | .natural => .u64
  | .arrow A B => .pi false (A.instantiate parameters families)
      (B.instantiate (fun index => (parameters index).rename Nat.succ)
        (fun index => (families index).rename Nat.succ))
  | .application family argument => .app (families family) (argument.instantiate parameters families)

def TypeCode.syntax (offset : Nat) (A : TypeCode parameters families) : Term :=
  A.instantiate (fun index => .var (offset+index.val))
    (fun index => .var (offset+parameters+index.val))

theorem TypeCode.instantiate_rename (A : TypeCode count familyCount) (parameters : Fin count → Term)
    (families : Fin familyCount → Term) (ρ : Nat → Nat) :
    (A.instantiate parameters families).rename ρ =
      A.instantiate (fun index => (parameters index).rename ρ) (fun index => (families index).rename ρ) := by
  induction A generalizing parameters families ρ with
  | parameter => rfl
  | natural => simp only [TypeCode.instantiate,Term.u64,Term.rename,renameArgs]
  | arrow A B ha hb =>
    simp only [TypeCode.instantiate,Term.pi,Term.rename,renameArgs,Op.binders]
    rw [ha,hb]
    have shiftedP : (fun index => ((parameters index).rename Nat.succ).rename (liftRenaming 1 ρ)) =
        (fun index => ((parameters index).rename ρ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_rename _ _)
    have shiftedF : (fun index => ((families index).rename Nat.succ).rename (liftRenaming 1 ρ)) =
        (fun index => ((families index).rename ρ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_rename _ _)
    rw [shiftedP,shiftedF]
    rfl
  | application family argument ih =>
    simp only [TypeCode.instantiate,Term.app,Term.rename,renameArgs,Op.binders,liftRenaming]
    rw [ih]

theorem TypeCode.instantiate_subst (A : TypeCode count familyCount) (parameters : Fin count → Term)
    (families : Fin familyCount → Term) (σ : Nat → Term) :
    (A.instantiate parameters families).subst σ =
      A.instantiate (fun index => (parameters index).subst σ) (fun index => (families index).subst σ) := by
  induction A generalizing parameters families σ with
  | parameter => rfl
  | natural => simp only [TypeCode.instantiate,Term.u64,Term.subst,substArgs]
  | arrow A B ha hb =>
    simp only [TypeCode.instantiate,Term.pi,Term.subst,substArgs,Op.binders]
    rw [ha,hb]
    have shiftedP : (fun index => ((parameters index).rename Nat.succ).subst (liftSub 1 σ)) =
        (fun index => ((parameters index).subst σ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_subst _ _)
    have shiftedF : (fun index => ((families index).rename Nat.succ).subst (liftSub 1 σ)) =
        (fun index => ((families index).subst σ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_subst _ _)
    rw [shiftedP,shiftedF]
    rfl
  | application family argument ih =>
    simp only [TypeCode.instantiate,Term.app,Term.subst,substArgs,Op.binders,liftSub]
    rw [ih]

theorem TypeCode.syntax_shift (A : TypeCode parameters families) (offset : Nat) :
    (A.syntax offset).rename Nat.succ = A.syntax (offset+1) := by
  rw [TypeCode.syntax,TypeCode.instantiate_rename,TypeCode.syntax]
  have shiftedP : (fun index : Fin parameters => (Term.var (offset+index.val)).rename Nat.succ) =
      (fun index => Term.var (offset+1+index.val)) := by
    funext index; simp only [Term.rename]; congr 1; omega
  have shiftedF : (fun index : Fin families => (Term.var (offset+parameters+index.val)).rename Nat.succ) =
      (fun index => Term.var (offset+1+parameters+index.val)) := by
    funext index; simp only [Term.rename]; congr 1; omega
  rw [shiftedP,shiftedF]

theorem TypeCode.syntax_instantiate (A : TypeCode parameters families) (offset : Nat) (argument : Term) :
    (A.syntax (offset+1)).subst (single argument) = A.syntax offset := by
  rw [TypeCode.syntax,TypeCode.instantiate_subst,TypeCode.syntax]
  have shiftedP : (fun index : Fin parameters => (Term.var (offset+1+index.val)).subst (single argument)) =
      (fun index => Term.var (offset+index.val)) := by
    funext index; simp only [Term.subst]; have h : offset+1+index.val = (offset+index.val)+1 := by omega
    rw [h]; rfl
  have shiftedF : (fun index : Fin families => (Term.var (offset+1+parameters+index.val)).subst (single argument)) =
      (fun index => Term.var (offset+parameters+index.val)) := by
    funext index; simp only [Term.subst]; have h : offset+1+parameters+index.val = (offset+parameters+index.val)+1 := by omega
    rw [h]; rfl
  rw [shiftedP,shiftedF]

theorem TypeCode.syntax_arrow (A B : TypeCode parameters families) (offset : Nat) :
    (TypeCode.arrow A B).syntax offset = .pi false (A.syntax offset) (B.syntax (offset+1)) := by
  rw [TypeCode.syntax,TypeCode.instantiate]
  rw [← B.instantiate_rename _ _ Nat.succ]
  change Term.pi false (A.syntax offset) ((B.syntax offset).rename Nat.succ) = _
  rw [TypeCode.syntax_shift]

private theorem variable_injective (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env (.var x) (.var y)) : x = y :=
  (EnvironmentDelta.Basis.Conv.neutralSpine_injective (arguments := []) (replacements := []) wf.admissible converted).1

/-- Coherence reconstructs the entire open code tree, including every nested
higher-kinded family application. No equality of model assignments is assumed. -/
theorem TypeCode.syntax_injective (wf : UnifiedProgram.EnvWellFormed env) {A B : TypeCode parameters families}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) : A = B := by
  induction A generalizing B offset with
  | parameter index =>
    cases B with
    | parameter other =>
      have same := variable_injective wf converted
      have indexes : index = other := Fin.ext (by omega)
      cases indexes; rfl
    | natural => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted wf.admissible)
    | arrow B C => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted wf.admissible)
    | application family argument =>
      have impossible := (EnvironmentDelta.Basis.Conv.neutralSpine_injective
        (arguments := []) (replacements := [argument.syntax offset]) wf.admissible converted).2
      cases impossible
  | natural =>
    cases B with
    | parameter index => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => rfl
    | arrow B C => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
    | application family argument => exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [argument.syntax offset]) wf.admissible rfl (by intro h; cases h) rfl converted.symm)
  | arrow A C ha hc =>
    cases B with
    | parameter index => exact False.elim (EnvironmentDelta.Basis.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .u64) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow B D =>
      rw [TypeCode.syntax_arrow,TypeCode.syntax_arrow] at converted
      have components := converted.pi_injective wf.admissible
      cases ha components.2.1
      cases hc components.2.2
      rfl
    | application family argument => exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [argument.syntax offset]) wf.admissible rfl (by intro h; cases h) rfl converted.symm)
  | application family argument ih =>
    cases B with
    | parameter index =>
      have impossible := (EnvironmentDelta.Basis.Conv.neutralSpine_injective
        (arguments := [argument.syntax offset]) (replacements := []) wf.admissible converted).2
      cases impossible
    | natural => exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [argument.syntax offset]) wf.admissible rfl (by intro h; cases h) rfl converted)
    | arrow B C => exact False.elim (EnvironmentDelta.Basis.Conv.neutralSpine_node_separate
        (arguments := [argument.syntax offset]) wf.admissible rfl (by intro h; cases h) rfl converted)
    | application other replacement =>
      obtain ⟨heads,arguments⟩ := converted.family_application_injective wf.admissible
      have same : family = other := Fin.ext (by omega)
      cases same
      cases ih arguments
      rfl

theorem TypeCode.model_coherent (wf : UnifiedProgram.EnvWellFormed env) {A B : TypeCode parameters families}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) (assignment : Assignment levels signatures)
    (first : A.Valid levels signatures) (second : B.Valid levels signatures) :
    HEq (A.meaning assignment first) (B.meaning assignment second) := by
  cases TypeCode.syntax_injective wf converted
  rfl

end Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
