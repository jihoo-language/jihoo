import Jihoo.NativeFamilyCodeModel

/-! Native contexts with any number of universe variables and higher-kinded
family variables. Actual lookup and formation are derived for every nested
family code; no native typing derivation is a field of code validity. -/
namespace Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
open Jihoo.NativeKernel.Environment.Conversion
variable {parameters families : Nat} {levels : Fin parameters → Fin 32} {signatures : Fin families → Signature}

theorem Signature.term_rename (signature : Signature) (ρ : Nat → Nat) :
    signature.term.rename ρ = signature.term := by
  simp only [Signature.term,Term.pi,Term.univ,Term.rename,renameArgs]

theorem Signature.formed (signature : Signature) :
    HasType env ctx true signature.term (.univ (max (signature.input.val+1) (signature.result.val+1))) :=
  .pi (s := .type (signature.input.val+1)) (r := .type (signature.result.val+1))
    (.intro (.univ signature.input.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
    (.univ signature.result.isLt)

def baseContext (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) : Context :=
  List.ofFn (fun index => ⟨.univ (levels index).val,false⟩) ++
    List.ofFn (fun index => ⟨(signatures index).term,false⟩)

private theorem lookup_closed (ctx : Context)
    (closed : ∀ binding ∈ ctx, binding.ty.rename Nat.succ = binding.ty) :
    NativeKernel.lookup ctx index = ctx[index]? := by
  induction ctx generalizing index with
  | nil => rfl
  | cons binding rest ih =>
    cases index with
    | zero => simp only [NativeKernel.lookup,List.getElem?_cons_zero,closed binding (by simp)]
    | succ index =>
      change (NativeKernel.lookup rest index).map _ = rest[index]?
      rw [ih (fun binding member => closed binding (by simp [member]))]
      cases selected : rest[index]? with
      | none => rfl
      | some found =>
        have member := List.mem_of_getElem? selected
        simp only [Option.map,closed found (by simp [member])]

theorem baseContext_lookup (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    NativeKernel.lookup (baseContext levels signatures) index = (baseContext levels signatures)[index]? := by
  apply lookup_closed
  intro binding member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨index,equality⟩ := List.mem_ofFn.mp member
    cases equality
    simp only [Term.univ,Term.rename,renameArgs]
  · obtain ⟨index,equality⟩ := List.mem_ofFn.mp member
    cases equality
    exact Signature.term_rename _ _

theorem baseContext_parameter (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature)
    (index : Fin parameters) :
    NativeKernel.lookup (baseContext levels signatures) index.val = some ⟨.univ (levels index).val,false⟩ := by
  rw [baseContext_lookup,baseContext,List.getElem?_append_left (by simp)]
  simp

theorem baseContext_family (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature)
    (index : Fin families) :
    NativeKernel.lookup (baseContext levels signatures) (parameters+index.val) = some ⟨(signatures index).term,false⟩ := by
  rw [baseContext_lookup,baseContext,List.getElem?_append_right (by simp)]
  simp

def context (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature) :
    List (TypeCode parameters families) → Context
  | [] => baseContext levels signatures
  | A :: Γ => ⟨A.syntax Γ.length,false⟩ :: context levels signatures Γ

theorem parameter_lookup (Γ : List (TypeCode parameters families)) (index : Fin parameters) :
    NativeKernel.lookup (context levels signatures Γ) (Γ.length+index.val) = some ⟨.univ (levels index).val,false⟩ := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using baseContext_parameter levels signatures index
  | cons A Γ ih =>
    simp only [context,List.length_cons,Nat.succ_add,NativeKernel.lookup,ih,
      Option.map,Term.univ,Term.rename,renameArgs]

theorem family_lookup (Γ : List (TypeCode parameters families)) (index : Fin families) :
    NativeKernel.lookup (context levels signatures Γ) (Γ.length+parameters+index.val) = some ⟨(signatures index).term,false⟩ := by
  induction Γ with
  | nil => simpa only [context,List.length_nil,Nat.zero_add] using baseContext_family levels signatures index
  | cons A Γ ih =>
    have shifted : Γ.length+1+parameters+index.val = (Γ.length+parameters+index.val)+1 := by omega
    simp only [context,List.length_cons,shifted,NativeKernel.lookup,ih,Option.map,Signature.term_rename]

/-- Every well-leveled higher-kinded type expression has its actual native
universe, respecting noncumulativity and the application gate's ghost mode. -/
theorem TypeCode.formed (A : TypeCode parameters families) (valid : A.Valid levels signatures) :
    HasType env (context levels signatures Γ) true (A.syntax Γ.length) (.univ (A.level levels signatures)) := by
  induction A generalizing Γ with
  | parameter index => exact .var (parameter_lookup Γ index) (Or.inl rfl)
  | natural => exact .u64
  | arrow A B ha hb =>
    rw [TypeCode.syntax_arrow]
    exact .pi (s := .type (A.level levels signatures)) (r := .type (B.level levels signatures))
      (.intro (ha valid.1) (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h)))
      (hb valid.2 (Γ := A :: Γ))
  | application family argument ih =>
    have functionTyped : HasType env (context levels signatures Γ) true
        (.var (Γ.length+parameters+family.val))
        (.pi false (.univ (signatures family).input.val) (.univ (signatures family).result.val)) :=
      .var (family_lookup Γ family) (Or.inl rfl)
    have argumentTyped := ih valid.1 (Γ := Γ)
    rw [valid.2] at argumentTyped
    have applied := HasType.app functionTyped argumentTyped (Or.inl rfl)
    simpa only [TypeCode.syntax,TypeCode.instantiate,TypeCode.level,Term.univ,Term.subst,substArgs] using applied

inductive Member {parameters families : Nat} : TypeCode parameters families → List (TypeCode parameters families) → Nat → Type where
  | here : Member A (A :: Γ) 0
  | there : Member A Γ index → Member A (B :: Γ) (index+1)

theorem Member.lookup {A : TypeCode parameters families} {Γ : List (TypeCode parameters families)}
    (member : Member A Γ index) :
    NativeKernel.lookup (context levels signatures Γ) index = some ⟨A.syntax Γ.length,false⟩ := by
  induction member with
  | here => simp only [context,NativeKernel.lookup,TypeCode.syntax_shift,List.length_cons]
  | there previous ih =>
    change (NativeKernel.lookup (context levels signatures _) _).map _ = _
    rw [ih]
    simp only [Option.map,TypeCode.syntax_shift,List.length_cons]

def Member.at (Γ : List (TypeCode parameters families)) (index : Nat) (bound : index < Γ.length) :
    (A : TypeCode parameters families) × Member A Γ index :=
  match Γ,index with
  | [],_ => by simp at bound
  | A :: _,0 => ⟨A,.here⟩
  | _ :: Γ,index+1 =>
    let ⟨A,member⟩ := Member.at Γ index (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound)
    ⟨A,.there member⟩

def ContextValid (levels : Fin parameters → Fin 32) (signatures : Fin families → Signature)
    (Γ : List (TypeCode parameters families)) : Prop := ∀ A ∈ Γ, A.Valid levels signatures

theorem ContextValid.member (valid : ContextValid levels signatures Γ) (member : Member A Γ index) :
    A.Valid levels signatures := by
  induction member with
  | here => exact valid _ (by simp)
  | there previous ih => exact ih (fun A member => valid A (by simp [member]))

theorem ContextValid.cons (valid : ContextValid levels signatures Γ) (domain : A.Valid levels signatures) :
    ContextValid levels signatures (A :: Γ) := by
  intro B member
  rcases List.mem_cons.mp member with same | member
  · simpa only [same] using domain
  · exact valid B member

end Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
