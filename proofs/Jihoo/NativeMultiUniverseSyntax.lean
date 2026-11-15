import Jihoo.NativeUniverseLevelRealization

/-! Monotypes with any finite number of independently leveled universe
parameters. Native contexts and all lookup/formation facts are constructed;
no context-typing or representation oracle is a constructor of the source
recognition developed above this layer. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
open Jihoo.NativeKernel.Environment.Conversion

inductive Mono (parameters : Nat) where
  | parameter (index : Fin parameters)
  | natural
  | arrow (domain codomain : Mono parameters)
  deriving DecidableEq, Repr

def Mono.instantiate (parameters : Fin count → Term) : Mono count → Term
  | .parameter index => parameters index
  | .natural => .u64
  | .arrow A B => .pi false (A.instantiate parameters)
      (B.instantiate (fun index => (parameters index).rename Nat.succ))

def Mono.syntax (offset : Nat) (A : Mono count) : Term :=
  A.instantiate (fun index => .var (offset + index.val))

theorem Mono.instantiate_rename (A : Mono count) (parameters : Fin count → Term) (ρ : Nat → Nat) :
    (A.instantiate parameters).rename ρ = A.instantiate (fun index => (parameters index).rename ρ) := by
  induction A generalizing parameters ρ with
  | parameter => rfl
  | natural => simp only [Mono.instantiate,Term.u64,Term.rename,renameArgs]
  | arrow A B ha hb =>
    simp only [Mono.instantiate,Term.pi,Term.rename,renameArgs,Op.binders]
    rw [ha,hb]
    have shifted : (fun index => ((parameters index).rename Nat.succ).rename (liftRenaming 1 ρ)) =
        (fun index => ((parameters index).rename ρ).rename Nat.succ) :=
      funext (fun _ => UniverseContext.shift_rename _ _)
    rw [shifted]
    rfl

theorem Mono.instantiate_subst (A : Mono count) (parameters : Fin count → Term) (σ : Nat → Term) :
    (A.instantiate parameters).subst σ = A.instantiate (fun index => (parameters index).subst σ) := by
  induction A generalizing parameters σ with
  | parameter => rfl
  | natural => simp only [Mono.instantiate,Term.u64,Term.subst,substArgs]
  | arrow A B ha hb =>
    simp only [Mono.instantiate,Term.pi,Term.subst,substArgs,Op.binders]
    rw [ha,hb]
    have shifted : (fun index => ((parameters index).rename Nat.succ).subst (liftSub 1 σ)) =
        (fun index => ((parameters index).subst σ).rename Nat.succ) :=
      funext (fun _ => UniverseContext.shift_subst _ _)
    rw [shifted]
    rfl

theorem Mono.syntax_shift (A : Mono count) (offset : Nat) :
    (A.syntax offset).rename Nat.succ = A.syntax (offset+1) := by
  rw [Mono.syntax,Mono.instantiate_rename,Mono.syntax]
  congr 1
  funext index
  simp only [Term.rename]
  congr 1
  omega

theorem Mono.syntax_instantiate (A : Mono count) (offset : Nat) (argument : Term) :
    (A.syntax (offset+1)).subst (single argument) = A.syntax offset := by
  rw [Mono.syntax,Mono.instantiate_subst,Mono.syntax]
  congr 1
  funext index
  simp only [Term.subst]
  have index_eq : offset + 1 + index.val = (offset + index.val) + 1 := by omega
  rw [index_eq]
  rfl

theorem Mono.syntax_arrow (A B : Mono count) (offset : Nat) :
    (Mono.arrow A B).syntax offset = .pi false (A.syntax offset) (B.syntax (offset+1)) := by
  change Term.pi false (A.instantiate (fun index => .var (offset+index.val)))
      (B.instantiate (fun index => (Term.var (offset+index.val)).rename Nat.succ)) =
    Term.pi false (A.instantiate (fun index => .var (offset+index.val)))
      (B.instantiate (fun index => .var (offset+1+index.val)))
  have shifted : (fun index : Fin count => (Term.var (offset+index.val)).rename Nat.succ) =
      (fun index => Term.var (offset+1+index.val)) := by
    funext index
    simp only [Term.rename]
    congr 1
    omega
  rw [shifted]

private theorem variable_injective (wf : UnifiedProgram.EnvWellFormed env)
    (converted : Conv env (.var x) (.var y)) : x = y := by
  exact converted.full_variable_injective wf.admissible


/-- Distinct abstract parameters cannot be identified by raw delta/ACU
conversion in an authenticated world, even before assigning their model values. -/
theorem Mono.syntax_injective (wf : UnifiedProgram.EnvWellFormed env) {A B : Mono count}
    (converted : Conv env (A.syntax offset) (B.syntax offset)) : A = B := by
  induction A generalizing B offset with
  | parameter index =>
    cases B with
    | parameter other =>
      have same := variable_injective wf converted
      have indexes : index = other := Fin.ext (by omega)
      cases indexes
      rfl
    | natural => exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl converted wf.admissible)
    | arrow B C => exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl converted wf.admissible)
  | natural =>
    cases B with
    | parameter index => exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => rfl
    | arrow B C => exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .u64) (op' := .pi false) rfl rfl (by intro h; cases h) converted wf.admissible)
  | arrow A C ha hc =>
    cases B with
    | parameter index => exact False.elim (FamilyIota.Extended.Conv.full_variable_node_separate rfl converted.symm wf.admissible)
    | natural => exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint
        (op := .pi false) (op' := .u64) rfl rfl (by intro h; cases h) converted wf.admissible)
    | arrow B D =>
      rw [Mono.syntax_arrow,Mono.syntax_arrow] at converted
      have parts := converted.pi_injective wf.admissible
      cases ha parts.2.1
      cases hc parts.2.2
      rfl

private def universeList (levels : List (Fin 32)) : Context :=
  levels.map fun level => ⟨.univ level.val,false⟩

private theorem lookup_universeList (levels : List (Fin 32)) (index : Nat) :
    NativeKernel.lookup (universeList levels) index =
      (levels[index]?).map (fun level => ⟨.univ level.val,false⟩) := by
  induction levels generalizing index with
  | nil => rfl
  | cons level levels ih =>
    cases index with
    | zero => simp only [universeList,List.map,NativeKernel.lookup,Term.univ,Term.rename,renameArgs,List.getElem?_cons_zero,Option.map]
    | succ index =>
      change (NativeKernel.lookup (universeList levels) index).map _ = _
      rw [ih]
      simp only [List.getElem?_cons_succ]
      cases levels[index]? <;> simp only [Option.map,Term.univ,Term.rename,renameArgs]

def universeContext (levels : Fin count → Fin 32) : Context := universeList (List.ofFn levels)

theorem universeContext_list (levels : List (Fin 32)) :
    universeContext levels.get = levels.map (fun level => ⟨.univ level.val,false⟩) := by
  unfold universeContext
  change universeList (List.ofFn (fun i => levels[i.val])) = universeList levels
  rw [List.ofFn_getElem]

def context (levels : Fin count → Fin 32) : List (Mono count) → Context
  | [] => universeContext levels
  | A :: Γ => ⟨A.syntax Γ.length,false⟩ :: context levels Γ

theorem universe_lookup (levels : Fin count → Fin 32) (index : Fin count) :
    NativeKernel.lookup (universeContext levels) index.val = some ⟨.univ (levels index).val,false⟩ := by
  rw [universeContext,lookup_universeList]
  simp

theorem parameter_lookup (levels : Fin count → Fin 32) (Γ : List (Mono count)) (index : Fin count) :
    NativeKernel.lookup (context levels Γ) (Γ.length + index.val) = some ⟨.univ (levels index).val,false⟩ := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using universe_lookup levels index
  | cons A Γ ih =>
    simp only [context,List.length_cons,Nat.succ_add,NativeKernel.lookup,ih,
      Option.map,Term.univ,Term.rename,renameArgs]

def Mono.nativeLevel (levels : Fin count → Fin 32) : Mono count → Nat
  | .parameter index => (levels index).val
  | .natural => 0
  | .arrow A B => max (A.nativeLevel levels) (B.nativeLevel levels)

theorem Mono.nativeLevel_bound (A : Mono count) (levels : Fin count → Fin 32) : A.nativeLevel levels < 32 := by
  induction A with
  | parameter index => exact (levels index).isLt
  | natural => change 0 < 32; decide
  | arrow A B ha hb => exact Nat.max_lt.mpr ⟨ha,hb⟩

theorem Mono.formed (A : Mono count) (levels : Fin count → Fin 32) :
    HasType env (context levels Γ) mode (A.syntax Γ.length) (.univ (A.nativeLevel levels)) := by
  induction A generalizing Γ mode with
  | parameter index => exact .var (parameter_lookup levels Γ index) (Or.inr rfl)
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [Mono.syntax_arrow]
    exact .pi (s := .type (A.nativeLevel levels)) (r := .type (B.nativeLevel levels))
      (.intro (ha (mode := true)) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (hb (Γ := A :: Γ) (mode := true))

inductive Member {count : Nat} : Mono count → List (Mono count) → Nat → Type where
  | here : Member A (A :: Γ) 0
  | there : Member A Γ i → Member A (B :: Γ) (i+1)

theorem Member.lookup {A : Mono count} {Γ : List (Mono count)}
    (member : Member A Γ index) (levels : Fin count → Fin 32) :
    NativeKernel.lookup (context levels Γ) index = some ⟨A.syntax Γ.length,false⟩ := by
  induction member with
  | here => simp only [context,NativeKernel.lookup,Mono.syntax_shift,List.length_cons]
  | there previous ih =>
    change (NativeKernel.lookup (context levels _) _).map _ = _
    rw [ih]
    simp only [Option.map,Mono.syntax_shift,List.length_cons]

def Member.at (Γ : List (Mono count)) (index : Nat) (bound : index < Γ.length) :
    (A : Mono count) × Member A Γ index :=
  match Γ,index with
  | [],_ => by simp at bound
  | A :: _,0 => ⟨A,.here⟩
  | _ :: Γ,index+1 =>
    let ⟨A,member⟩ := Member.at Γ index (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound)
    ⟨A,.there member⟩

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
