import Jihoo.NativeNeutralSpines
import Jihoo.NativeMultiUniverseModel
set_option maxUniverseOffset 40

/-! Dependent families over arbitrary abstract carriers, including function
carriers and mixed native universe levels. Family assignments are concrete
finite-model Pi values. Observation variables range over actual elements of
their domains, so the interpreted fibers genuinely depend on source values. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)

structure Signature (parameters : Nat) where
  input : Mono parameters
  result : Fin 32

def Signature.code {levels : Fin parameters → Fin 32} (signature : Signature parameters) (bases : MultiUniverse.Assignment levels) :=
  Finite.pi (signature.input.code bases) (.type ⟨signature.result.val+1,by omega⟩)
    (fun _ => Finite.Values.codeUniverse signature.result)

def Signature.fiber {levels : Fin parameters → Fin 32} (signature : Signature parameters) (bases : MultiUniverse.Assignment levels)
    (family : Finite.Carrier (signature.code bases)) (argument : Finite.Carrier (signature.input.code bases)) :
    Finite.Universe (.type ⟨signature.result.val,by omega⟩) :=
  Finite.Values.decode signature.result
    ((Finite.piMeaning (signature.input.code bases) (.type ⟨signature.result.val+1,by omega⟩)
      (fun _ => Finite.Values.codeUniverse signature.result)).app family argument)

variable {parameters familyCount observationCount : Nat} {levels : Fin parameters → Fin 32}
variable {signatures : Fin familyCount → Signature parameters} {observed : Fin observationCount → Mono parameters}

structure Assignment (levels : Fin parameters → Fin 32) (signatures : Fin familyCount → Signature parameters)
    (observed : Fin observationCount → Mono parameters) where
  bases : MultiUniverse.Assignment levels
  families : ∀ index, Finite.Carrier ((signatures index).code bases)
  observations : ∀ index, Finite.Carrier ((observed index).code bases)

inductive TypeCode (parameters familyCount observationCount : Nat) where
  | parameter (index : Fin parameters)
  | natural
  | arrow (domain codomain : TypeCode parameters familyCount observationCount)
  | fiber (family : Fin familyCount) (observation : Fin observationCount)
  deriving DecidableEq

def TypeCode.level (levels : Fin parameters → Fin 32) (signatures : Fin familyCount → Signature parameters) :
    TypeCode parameters familyCount observationCount → Nat
  | .parameter index => (levels index).val
  | .natural => 0
  | .arrow A B => max (A.level levels signatures) (B.level levels signatures)
  | .fiber family _ => (signatures family).result.val

def TypeCode.Valid (signatures : Fin familyCount → Signature parameters) (observed : Fin observationCount → Mono parameters) :
    TypeCode parameters familyCount observationCount → Prop
  | .parameter _ => True
  | .natural => True
  | .arrow A B => A.Valid signatures observed ∧ B.Valid signatures observed
  | .fiber family observation => observed observation = (signatures family).input

theorem TypeCode.level_bound (A : TypeCode parameters familyCount observationCount) : A.level levels signatures < 32 := by
  induction A with
  | parameter index => exact (levels index).isLt
  | natural => change 0 < 32; decide
  | arrow A B ha hb => exact Nat.max_lt.mpr ⟨ha,hb⟩
  | fiber family observation => exact (signatures family).result.isLt

def TypeCode.sort (A : TypeCode parameters familyCount observationCount) (levels : Fin parameters → Fin 32)
    (signatures : Fin familyCount → Signature parameters) : Finite.LevelSort :=
  .type ⟨A.level levels signatures,by have := A.level_bound (levels := levels) (signatures := signatures); omega⟩

def TypeCode.meaning (assignment : Assignment levels signatures observed) :
    (A : TypeCode parameters familyCount observationCount) → A.Valid signatures observed → Finite.Universe (A.sort levels signatures)
  | .parameter index,_ => assignment.bases.codes index
  | .natural,_ => Finite.natural
  | .arrow A B,valid => Finite.pi (A.meaning assignment valid.1) (B.sort levels signatures)
      (fun _ => B.meaning assignment valid.2)
  | .fiber family observation,valid =>
    (signatures family).fiber assignment.bases (assignment.families family)
      (cast (congrArg (fun domain : Mono parameters => Finite.Carrier (domain.code assignment.bases)) valid)
        (assignment.observations observation))

def TypeCode.instantiate (replacement : Nat → Term) : TypeCode parameters familyCount observationCount → Term
  | .parameter index => replacement (observationCount+familyCount+index.val)
  | .natural => .u64
  | .arrow A B => .pi false (A.instantiate replacement)
      (B.instantiate (fun index => (replacement index).rename Nat.succ))
  | .fiber family observation => .app (replacement (observationCount+family.val)) (replacement observation.val)

def TypeCode.syntax (offset : Nat) (A : TypeCode parameters familyCount observationCount) : Term :=
  A.instantiate (fun index => .var (offset+index))

theorem TypeCode.instantiate_rename (A : TypeCode parameters familyCount observationCount) (replacement : Nat → Term)
    (ρ : Nat → Nat) : (A.instantiate replacement).rename ρ =
      A.instantiate (fun index => (replacement index).rename ρ) := by
  induction A generalizing replacement ρ with
  | parameter => rfl
  | natural => simp only [TypeCode.instantiate,Term.u64,Term.rename,renameArgs]
  | arrow A B ha hb =>
    simp only [TypeCode.instantiate,Term.pi,Term.rename,renameArgs,Op.binders]
    rw [ha,hb]
    have shifted : (fun index => ((replacement index).rename Nat.succ).rename (liftRenaming 1 ρ)) =
        (fun index => ((replacement index).rename ρ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_rename _ _)
    rw [shifted]
    rfl
  | fiber family observation =>
    simp only [TypeCode.instantiate,Term.app,Term.rename,renameArgs,Op.binders,liftRenaming]

theorem TypeCode.instantiate_subst (A : TypeCode parameters familyCount observationCount) (replacement : Nat → Term)
    (σ : Nat → Term) : (A.instantiate replacement).subst σ =
      A.instantiate (fun index => (replacement index).subst σ) := by
  induction A generalizing replacement σ with
  | parameter => rfl
  | natural => simp only [TypeCode.instantiate,Term.u64,Term.subst,substArgs]
  | arrow A B ha hb =>
    simp only [TypeCode.instantiate,Term.pi,Term.subst,substArgs,Op.binders]
    rw [ha,hb]
    have shifted : (fun index => ((replacement index).rename Nat.succ).subst (liftSub 1 σ)) =
        (fun index => ((replacement index).subst σ).rename Nat.succ) := funext (fun _ => UniverseContext.shift_subst _ _)
    rw [shifted]
    rfl
  | fiber family observation =>
    simp only [TypeCode.instantiate,Term.app,Term.subst,substArgs,Op.binders,liftSub]

theorem TypeCode.syntax_shift (A : TypeCode parameters familyCount observationCount) (offset : Nat) :
    (A.syntax offset).rename Nat.succ = A.syntax (offset+1) := by
  rw [TypeCode.syntax,TypeCode.instantiate_rename,TypeCode.syntax]
  congr 1
  funext index
  simp only [Term.rename]
  congr 1
  omega

theorem TypeCode.syntax_instantiate (A : TypeCode parameters familyCount observationCount) (offset : Nat) (argument : Term) :
    (A.syntax (offset+1)).subst (single argument) = A.syntax offset := by
  rw [TypeCode.syntax,TypeCode.instantiate_subst,TypeCode.syntax]
  congr 1
  funext index
  simp only [Term.subst]
  have same : offset+1+index = (offset+index)+1 := by omega
  rw [same]
  rfl

theorem TypeCode.syntax_arrow (A B : TypeCode parameters familyCount observationCount) (offset : Nat) :
    (TypeCode.arrow A B).syntax offset = .pi false (A.syntax offset) (B.syntax (offset+1)) := by
  rw [TypeCode.syntax,TypeCode.instantiate,←B.instantiate_rename _ Nat.succ]
  change Term.pi false (A.syntax offset) ((B.syntax offset).rename Nat.succ) = _
  rw [TypeCode.syntax_shift]

private theorem variable_injective (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env (.var x) (.var y)) : x = y :=
  (Environment.FamilyIota.Extended.Conv.neutralSpine_injective (arguments := []) (replacements := []) wf.admissible converted).1

/-- This injectivity theorem allows arbitrary actual native computations in
conversion paths; observations and family heads are reconstructed, not assumed. -/
theorem TypeCode.syntax_injective (wf : UnifiedProgram.EnvWellFormed env)
    {A B : TypeCode parameters familyCount observationCount}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) : A = B := by
  induction A generalizing B offset with
  | parameter index =>
    cases B with
    | parameter other =>
      have same := variable_injective wf converted
      have indexes : index = other := Fin.ext (by omega)
      cases indexes; rfl
    | natural => exact False.elim (Environment.FamilyIota.Extended.Conv.full_variable_node_separate rfl converted wf.admissible)
    | arrow B C => exact False.elim (Environment.FamilyIota.Extended.Conv.full_variable_node_separate rfl converted wf.admissible)
    | fiber family observation =>
      have impossible := (Environment.FamilyIota.Extended.Conv.neutralSpine_injective
        (arguments := []) (replacements := [.var (offset+observation.val)]) wf.admissible converted).2
      cases impossible
  | natural =>
    cases B with
    | parameter index => exact False.elim (Environment.FamilyIota.Extended.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => rfl
    | arrow B C => exact False.elim (Environment.FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
    | fiber family observation => exact False.elim (Environment.FamilyIota.Extended.Conv.neutralSpine_node_separate
        (arguments := [.var (offset+observation.val)]) wf.admissible rfl (by intro h; cases h) rfl converted.symm)
  | arrow A C ha hc =>
    cases B with
    | parameter index => exact False.elim (Environment.FamilyIota.Extended.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => exact False.elim (Environment.FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .u64) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow B D =>
      rw [TypeCode.syntax_arrow,TypeCode.syntax_arrow] at converted
      have components := converted.pi_injective wf.admissible
      cases ha components.2.1
      cases hc components.2.2
      rfl
    | fiber family observation => exact False.elim (Environment.FamilyIota.Extended.Conv.neutralSpine_node_separate
        (arguments := [.var (offset+observation.val)]) wf.admissible rfl (by intro h; cases h) rfl converted.symm)
  | fiber family observation =>
    cases B with
    | parameter index =>
      have impossible := (Environment.FamilyIota.Extended.Conv.neutralSpine_injective
        (arguments := [.var (offset+observation.val)]) (replacements := []) wf.admissible converted).2
      cases impossible
    | natural => exact False.elim (Environment.FamilyIota.Extended.Conv.neutralSpine_node_separate
        (arguments := [.var (offset+observation.val)]) wf.admissible rfl (by intro h; cases h) rfl converted)
    | arrow B C => exact False.elim (Environment.FamilyIota.Extended.Conv.neutralSpine_node_separate
        (arguments := [.var (offset+observation.val)]) wf.admissible rfl (by intro h; cases h) rfl converted)
    | fiber other replacement =>
      obtain ⟨heads,arguments⟩ := converted.family_application_injective wf.admissible
      have same : family = other := Fin.ext (by omega)
      have values := variable_injective wf arguments
      have indexes : observation = replacement := Fin.ext (by omega)
      cases same
      cases indexes
      rfl

theorem TypeCode.model_coherent (wf : UnifiedProgram.EnvWellFormed env)
    {A B : TypeCode parameters familyCount observationCount}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) (assignment : Assignment levels signatures observed)
    (first : A.Valid signatures observed) (second : B.Valid signatures observed) :
    HEq (A.meaning assignment first) (B.meaning assignment second) := by
  cases TypeCode.syntax_injective wf converted
  rfl

abbrev PackedCode := (sort : Finite.LevelSort) × Finite.Universe sort

def PackedCode.carrier (code : PackedCode) : Type 34 := Finite.Carrier code.2

def packedArrow (domain result : PackedCode) : PackedCode :=
  ⟨domain.1.pi result.1,Finite.pi domain.2 result.1 (fun _ => result.2)⟩

def TypeCode.ofMono : Mono parameters → TypeCode parameters familyCount observationCount
  | .parameter index => .parameter index
  | .natural => .natural
  | .arrow A B => .arrow (TypeCode.ofMono A) (TypeCode.ofMono B)

theorem TypeCode.ofMono_valid (A : Mono parameters) : (TypeCode.ofMono A).Valid signatures observed := by
  induction A with
  | parameter => trivial
  | natural => trivial
  | arrow A B ha hb => exact ⟨ha,hb⟩

def TypeCode.packed (assignment : Assignment levels signatures observed)
    (A : TypeCode parameters familyCount observationCount) (valid : A.Valid signatures observed) : PackedCode :=
  ⟨A.sort levels signatures,A.meaning assignment valid⟩

def monoPacked (bases : MultiUniverse.Assignment levels) (A : Mono parameters) : PackedCode :=
  ⟨A.semanticSort levels,A.code bases⟩

theorem TypeCode.ofMono_packed (assignment : Assignment levels signatures observed) (A : Mono parameters) :
    TypeCode.packed assignment (TypeCode.ofMono A) (TypeCode.ofMono_valid A) = monoPacked assignment.bases A := by
  induction A with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb =>
    change packedArrow (TypeCode.packed assignment (TypeCode.ofMono A) _) (TypeCode.packed assignment (TypeCode.ofMono B) _) =
      packedArrow (monoPacked assignment.bases A) (monoPacked assignment.bases B)
    rw [ha,hb]

theorem TypeCode.ofMono_carrier (assignment : Assignment levels signatures observed) (A : Mono parameters) :
    Finite.Carrier ((TypeCode.ofMono A).meaning assignment (TypeCode.ofMono_valid A)) =
      Finite.Carrier (A.code assignment.bases) :=
  congrArg PackedCode.carrier (TypeCode.ofMono_packed assignment A)

theorem TypeCode.ofMono_syntax (A : Mono parameters) (offset : Nat) :
    (TypeCode.ofMono A : TypeCode parameters familyCount observationCount).syntax offset =
      A.syntax (offset+observationCount+familyCount) := by
  induction A generalizing offset with
  | parameter => simp only [TypeCode.ofMono,TypeCode.syntax,TypeCode.instantiate,MultiUniverse.Mono.syntax,
      MultiUniverse.Mono.instantiate,Nat.add_assoc]
  | natural => rfl
  | arrow A B ha hb =>
    rw [TypeCode.ofMono,TypeCode.syntax_arrow,MultiUniverse.Mono.syntax_arrow,ha,hb]
    have same : offset+1+observationCount+familyCount = (offset+observationCount+familyCount)+1 := by omega
    rw [same]

def Assignment.observationValue (assignment : Assignment levels signatures observed) (index : Fin observationCount) :
    Finite.Carrier ((TypeCode.ofMono (observed index)).meaning assignment (TypeCode.ofMono_valid _)) :=
  cast (TypeCode.ofMono_carrier assignment (observed index)).symm (assignment.observations index)

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
