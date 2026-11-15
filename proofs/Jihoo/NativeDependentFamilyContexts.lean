import Jihoo.NativeDependentFamilyModel

/-! General dependent native contexts: universe parameters, families over any
monotype carrier, and arbitrary observations in those carriers. The lookup and
formation evidence is derived from these source binders themselves. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)
variable {parameters : Nat} {levels : Fin parameters → Fin 32}

def ParametersIn (levels : Fin parameters → Fin 32) (offset : Nat) (ctx : Context) : Prop :=
  ∀ index, NativeKernel.lookup ctx (offset+index.val) = some ⟨.univ (levels index).val,false⟩

theorem ParametersIn.extend (found : ParametersIn levels offset ctx) (binding : Binding) :
    ParametersIn levels (offset+1) (binding :: ctx) := by
  intro index
  have same : offset+1+index.val = (offset+index.val)+1 := by omega
  rw [same]
  change (NativeKernel.lookup ctx (offset+index.val)).map _ = _
  rw [found index]
  simp only [Option.map,Term.univ,Term.rename,renameArgs]

theorem mono_formed_in (A : Mono parameters) (found : ParametersIn levels offset ctx) :
    HasType env ctx true (A.syntax offset) (.univ (A.nativeLevel levels)) := by
  induction A generalizing offset ctx with
  | parameter index => exact .var (found index) (Or.inl rfl)
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [MultiUniverse.Mono.syntax_arrow]
    exact .pi (s := .type (A.nativeLevel levels)) (r := .type (B.nativeLevel levels))
      (.intro (ha found) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (hb (found.extend ⟨A.syntax offset,false⟩))

def Signature.term (signature : Signature parameters) (offset : Nat) : Term :=
  .pi false (signature.input.syntax offset) (.univ signature.result.val)

theorem Signature.term_shift (signature : Signature parameters) (offset : Nat) :
    (signature.term offset).rename Nat.succ = signature.term (offset+1) := by
  simp only [Signature.term,Term.pi,Term.rename,renameArgs,Op.binders,liftRenaming,
    MultiUniverse.Mono.syntax_shift,Term.univ]

theorem Signature.formed (signature : Signature parameters) (found : ParametersIn levels offset ctx) :
    HasType env ctx true (signature.term offset)
      (.univ (max (signature.input.nativeLevel levels) (signature.result.val+1))) :=
  .pi (s := .type (signature.input.nativeLevel levels)) (r := .type (signature.result.val+1))
    (.intro (mono_formed_in signature.input found)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
    (.univ signature.result.isLt)

def familyContext (levels : Fin parameters → Fin 32) : List (Signature parameters) → Context
  | [] => MultiUniverse.universeContext levels
  | signature :: rest => ⟨signature.term rest.length,false⟩ :: familyContext levels rest

theorem familyContext_parameters (familyList : List (Signature parameters)) :
    ParametersIn levels familyList.length (familyContext levels familyList) := by
  induction familyList with
  | nil =>
    intro index
    simpa only [familyContext,List.length_nil,Nat.zero_add] using MultiUniverse.universe_lookup levels index
  | cons signature rest ih => exact ih.extend _

inductive Slot {α : Type u} : α → List α → Nat → Type u where
  | here : Slot value (value :: rest) 0
  | there : Slot value rest index → Slot value (other :: rest) (index+1)

noncomputable def Slot.ofFin (entries : List α) (index : Fin entries.length) : Slot (entries.get index) entries index.val := by
  induction entries with
  | nil => exact Fin.elim0 index
  | cons entry rest ih =>
    cases index using Fin.cases with
    | zero => exact .here
    | succ index => exact .there (ih index)

theorem Slot.family_lookup {signature : Signature parameters} {familyList : List (Signature parameters)}
    (slot : Slot signature familyList index) :
    NativeKernel.lookup (familyContext levels familyList) index = some ⟨signature.term familyList.length,false⟩ := by
  induction slot with
  | here => simp only [familyContext,NativeKernel.lookup,Signature.term_shift,List.length_cons]
  | there previous ih =>
    change (NativeKernel.lookup (familyContext levels _) _).map _ = _
    rw [ih]
    simp only [Option.map,Signature.term_shift,List.length_cons]

def observationContext (levels : Fin parameters → Fin 32) (familyList : List (Signature parameters)) :
    List (Mono parameters) → Context
  | [] => familyContext levels familyList
  | domain :: rest => ⟨domain.syntax (rest.length+familyList.length),false⟩ :: observationContext levels familyList rest

theorem observationContext_parameters (familyList : List (Signature parameters)) (observations : List (Mono parameters)) :
    ParametersIn levels (observations.length+familyList.length) (observationContext levels familyList observations) := by
  induction observations with
  | nil => simpa only [observationContext,List.length_nil,Nat.zero_add] using familyContext_parameters (levels := levels) familyList
  | cons domain rest ih =>
    have extended := ih.extend ⟨domain.syntax (rest.length+familyList.length),false⟩
    simpa only [observationContext,List.length_cons,Nat.add_comm,Nat.add_left_comm] using extended

theorem Slot.observation_family_lookup {signature : Signature parameters} {familyList : List (Signature parameters)}
    (slot : Slot signature familyList index) (observations : List (Mono parameters)) :
    NativeKernel.lookup (observationContext levels familyList observations) (observations.length+index) =
      some ⟨signature.term (observations.length+familyList.length),false⟩ := by
  induction observations with
  | nil => simpa only [observationContext,List.length_nil,Nat.zero_add] using slot.family_lookup (levels := levels)
  | cons domain rest ih =>
    simp only [observationContext,List.length_cons,Nat.succ_add,NativeKernel.lookup,ih,
      Option.map,Signature.term_shift]

theorem Slot.observation_lookup {domain : Mono parameters} {observations : List (Mono parameters)}
    (slot : Slot domain observations index) (familyList : List (Signature parameters)) :
    NativeKernel.lookup (observationContext levels familyList observations) index =
      some ⟨domain.syntax (observations.length+familyList.length),false⟩ := by
  induction slot with
  | here =>
    simp only [observationContext,NativeKernel.lookup,MultiUniverse.Mono.syntax_shift,List.length_cons,
      Nat.add_comm,Nat.add_left_comm]
  | there previous ih =>
    change (NativeKernel.lookup (observationContext levels familyList _) _).map _ = _
    rw [ih]
    simp only [Option.map,MultiUniverse.Mono.syntax_shift,List.length_cons,Nat.add_comm,Nat.add_left_comm]

def context (levels : Fin parameters → Fin 32) (familyList : List (Signature parameters))
    (observations : List (Mono parameters)) :
    List (TypeCode parameters familyList.length observations.length) → Context
  | [] => observationContext levels familyList observations
  | A :: Γ => ⟨A.syntax Γ.length,false⟩ :: context levels familyList observations Γ

theorem context_parameters (familyList : List (Signature parameters)) (observations : List (Mono parameters))
    (Γ : List (TypeCode parameters familyList.length observations.length)) :
    ParametersIn levels (Γ.length+observations.length+familyList.length) (context levels familyList observations Γ) := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using observationContext_parameters (levels := levels) familyList observations
  | cons domain rest ih =>
    have extended := ih.extend ⟨domain.syntax rest.length,false⟩
    simpa only [context,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using extended

theorem Slot.context_family_lookup {signature : Signature parameters} {familyList : List (Signature parameters)}
    (slot : Slot signature familyList index) (observations : List (Mono parameters))
    (Γ : List (TypeCode parameters familyList.length observations.length)) :
    NativeKernel.lookup (context levels familyList observations Γ) (Γ.length+observations.length+index) =
      some ⟨signature.term (Γ.length+observations.length+familyList.length),false⟩ := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using slot.observation_family_lookup (levels := levels) observations
  | cons domain rest ih =>
    simp only [context,List.length_cons,Nat.succ_add,NativeKernel.lookup,ih,Option.map,Signature.term_shift]

theorem Slot.context_observation_lookup {domain : Mono parameters} {observations : List (Mono parameters)}
    (slot : Slot domain observations index) (familyList : List (Signature parameters))
    (Γ : List (TypeCode parameters familyList.length observations.length)) :
    NativeKernel.lookup (context levels familyList observations Γ) (Γ.length+index) =
      some ⟨domain.syntax (Γ.length+observations.length+familyList.length),false⟩ := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using slot.observation_lookup (levels := levels) familyList
  | cons A rest ih =>
    simp only [context,List.length_cons,Nat.succ_add,NativeKernel.lookup,ih,Option.map,MultiUniverse.Mono.syntax_shift]

/-- Actual native formation is reconstructed for types depending on ordinary
carrier values, not merely on variables whose values are themselves types. -/
theorem TypeCode.formed (A : TypeCode parameters familyList.length observations.length)
    (valid : A.Valid familyList.get observations.get) :
    HasType env (context levels familyList observations Γ) true (A.syntax Γ.length)
      (.univ (A.level levels familyList.get)) := by
  induction A generalizing Γ with
  | parameter index =>
    simpa only [TypeCode.syntax,TypeCode.instantiate,TypeCode.level,Nat.add_assoc] using
      (HasType.var ((context_parameters familyList observations Γ) index) (Or.inl rfl) :
        HasType env (context levels familyList observations Γ) true
          (.var (Γ.length+observations.length+familyList.length+index.val)) (.univ (levels index).val))
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [TypeCode.syntax_arrow]
    exact .pi (s := .type (A.level levels familyList.get)) (r := .type (B.level levels familyList.get))
      (.intro (ha valid.1) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (hb valid.2 (Γ := A :: Γ))
  | fiber family observation =>
    have functionTyped : HasType env (context levels familyList observations Γ) true
        (.var (Γ.length+observations.length+family.val))
        ((familyList.get family).term (Γ.length+observations.length+familyList.length)) :=
      .var ((Slot.ofFin familyList family).context_family_lookup observations Γ) (Or.inl rfl)
    have argumentTyped : HasType env (context levels familyList observations Γ) true
        (.var (Γ.length+observation.val))
        ((observations.get observation).syntax (Γ.length+observations.length+familyList.length)) :=
      .var ((Slot.ofFin observations observation).context_observation_lookup familyList Γ) (Or.inl rfl)
    rw [valid] at argumentTyped
    have applied := HasType.app functionTyped argumentTyped (Or.inl rfl)
    simpa only [TypeCode.syntax,TypeCode.instantiate,TypeCode.level,Term.univ,Term.subst,substArgs,Nat.add_assoc] using applied

/-- Structural code validity is recovered from actual native typing. Even the
family/observation domain equality is an output of Pi and variable inversion. -/
theorem TypeCode.valid_of_typed (A : TypeCode parameters familyList.length observations.length)
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (context levels familyList observations Γ) mode (A.syntax Γ.length) type) :
    A.Valid familyList.get observations.get := by
  induction A generalizing Γ mode type with
  | parameter => trivial
  | natural => trivial
  | arrow A B ha hb =>
    rw [TypeCode.syntax_arrow] at typed
    obtain ⟨domainSort,resultSort,binder,bodyTyped,converted⟩ := typed.piView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    exact ⟨ha domainTyped,hb (Γ := A :: Γ) bodyTyped⟩
  | fiber family observation =>
    change HasType env (context levels familyList observations Γ) mode
      (.app (.var (Γ.length+(observations.length+family.val))) (.var (Γ.length+observation.val))) type at typed
    obtain ⟨erased,domain,codomain,functionTyped,argumentTyped,allowed,resultConverted⟩ := typed.appView
    obtain ⟨functionBinding,functionFound,functionConverted⟩ := functionTyped.principalView
    have selected := (Slot.ofFin familyList family).context_family_lookup (levels := levels) observations Γ
    rw [Nat.add_assoc] at selected
    rw [selected] at functionFound
    cases functionFound
    have components := functionConverted.pi_injective wf.admissible
    obtain ⟨argumentBinding,argumentFound,argumentConverted⟩ := argumentTyped.principalView
    rw [(Slot.ofFin observations observation).context_observation_lookup familyList Γ] at argumentFound
    cases argumentFound
    exact MultiUniverse.Mono.syntax_injective wf (.trans argumentConverted components.2.1.symm)

theorem Slot.value_lookup {familyList : List (Signature parameters)} {observations : List (Mono parameters)}
    {A : TypeCode parameters familyList.length observations.length}
    {Γ : List (TypeCode parameters familyList.length observations.length)} (slot : Slot A Γ index) :
    NativeKernel.lookup (context levels familyList observations Γ) index = some ⟨A.syntax Γ.length,false⟩ := by
  induction slot with
  | here => simp only [context,NativeKernel.lookup,TypeCode.syntax_shift,List.length_cons]
  | there previous ih =>
    change (NativeKernel.lookup (context levels familyList observations _) _).map _ = _
    rw [ih]
    simp only [Option.map,TypeCode.syntax_shift,List.length_cons]

def ContextValid (signatures : Fin familyCount → Signature parameters) (observed : Fin observationCount → Mono parameters)
    (Γ : List (TypeCode parameters familyCount observationCount)) : Prop := ∀ A ∈ Γ, A.Valid signatures observed

theorem ContextValid.slot (valid : ContextValid signatures observed Γ) (slot : Slot A Γ index) :
    A.Valid signatures observed := by
  induction slot with
  | here => exact valid _ (by simp)
  | there previous ih => exact ih (fun A member => valid A (by simp [member]))

theorem ContextValid.cons (valid : ContextValid signatures observed Γ) (domain : A.Valid signatures observed) :
    ContextValid signatures observed (A :: Γ) := by
  intro B member
  rcases List.mem_cons.mp member with same | member
  · simpa only [same] using domain
  · exact valid B member

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
