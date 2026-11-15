import Jihoo.NativeLoanCheckerSoundness
import Jihoo.NativeContextModes
import Jihoo.NativeScopeCheck

/-! Resource modes reconstructed with the complete loan-indexed checker.
Every context binder and U64 kind-spine argument uses that same checker and
loan stack; no executable fallback to the sixty-rule checker is used. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceModes
open Jihoo.Quantity NativeQuantity CodeKinds

inductive ContextFormed (env : Environment) (loans : Loans.Stack) : Context → Prop where
  | nil : ContextFormed env loans []
  | cons : ContextFormed env loans ctx → Binder env loans ctx erased domain sort →
      domain.Scoped ctx.length → ContextFormed env loans (⟨domain,erased⟩ :: ctx)

def contextOK : Nat → Environment → Loans.Stack → Context → Bool
  | 0,_,_,_ => false
  | _+1,_,_,[] => true
  | fuel+1,env,loans,binding :: ctx =>
      contextOK fuel env loans ctx && NativeKernel.scopeCheck ctx.length binding.ty &&
        (Checker.binder fuel env loans ctx binding.erased binding.ty).isSome

theorem contextOK_sound (checked : contextOK fuel env loans ctx = true) : ContextFormed env loans ctx := by
  induction fuel generalizing ctx with
  | zero => simp [contextOK] at checked
  | succ fuel ih =>
      cases ctx with
      | nil => exact .nil
      | cons binding ctx =>
          obtain ⟨initial,binder⟩ := Bool.and_eq_true_iff.mp checked
          obtain ⟨tail,withinScope⟩ := Bool.and_eq_true_iff.mp initial
          obtain ⟨sort,found⟩ := Option.isSome_iff_exists.mp binder
          exact .cons (ih tail) (Checker.binder_sound found) (NativeKernel.scopeCheck_sound withinScope)

def LookupKind (env : Environment) (loans : Loans.Stack) (ctx : Context) (index : Nat) (kind : Kind) : Prop :=
  ∃ binding, lookup ctx index = some binding ∧
    Conversion.Conv env binding.ty kind.term ∧ HasType env loans ctx true (.var index) kind.term

def lookupKind (fuel : Nat) (env : Environment) (_loans : Loans.Stack) (ctx : Context) (index : Nat) : Option Kind := do
  let binding ← lookup ctx index
  let normal ← Conversion.normalize? env fuel binding.ty
  CodeKinds.read fuel normal

theorem lookupKind_sound (checked : lookupKind fuel env loans ctx index = some kind) :
    LookupKind env loans ctx index kind := by
  unfold lookupKind at checked
  obtain ⟨binding,selected,checked⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨normal,normalized,found⟩ := Option.bind_eq_some_iff.mp checked
  have same := CodeKinds.read_sound found
  have converted : Conversion.Conv env binding.ty kind.term := same ▸ Conversion.normalize?_sound normalized
  exact ⟨binding,selected,converted,.convert (.var selected (Or.inl rfl)) converted⟩

inductive Spine (env : Environment) (loans : Loans.Stack) (ctx : Context) : Term → Kind → Prop where
  | var : LookupKind env loans ctx index kind → Spine env loans ctx (.var index) kind
  | app : Spine env loans ctx function (.index erased result) →
      Checker.check fuel env loans ctx true argument .u64 = true →
      Spine env loans ctx (.app function argument) result

def spine : Nat → Environment → Loans.Stack → Context → Term → Option Kind
  | 0,_,_,_,_ => none
  | fuel+1,env,loans,ctx,term => match term with
      | .var index => lookupKind fuel env loans ctx index
      | .app function argument => do
          let kind ← spine fuel env loans ctx function
          match kind with
          | .index _ result => if Checker.check fuel env loans ctx true argument .u64 then some result else none
          | _ => none
      | _ => none

theorem spine_sound (checked : spine fuel env loans ctx term = some kind) : Spine env loans ctx term kind := by
  induction fuel generalizing term kind with
  | zero => simp [spine] at checked
  | succ fuel ih =>
      simp only [spine] at checked
      split at checked
      · exact .var (lookupKind_sound checked)
      · rename_i function argument
        obtain ⟨head,headChecked,checked⟩ := Option.bind_eq_some_iff.mp checked
        cases head with
        | type => contradiction
        | index erased result =>
            simp only at checked
            split at checked
            · rename_i argumentChecked
              cases checked
              exact .app (ih headChecked) argumentChecked
            · contradiction
      · contradiction

theorem Spine.typed (source : Spine env loans ctx term kind) : HasType env loans ctx true term kind.term := by
  induction source with
  | var found => exact found.choose_spec.2.2
  | @app function erased result fuel argument head checked ih =>
      have typed := HasType.app ih (by simpa using Checker.check_sound checked) (Or.inl rfl)
      simpa only [Kind.subst] using typed

def abstractType (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context) (term : Term) : Bool :=
  match spine fuel env loans ctx term with
  | some (.type _) => true
  | _ => false

theorem abstractType_sound (checked : abstractType fuel env loans ctx term = true) :
    ∃ level, Spine env loans ctx term (.type level) ∧ HasType env loans ctx true term (.univ level) := by
  unfold abstractType at checked
  cases found : spine fuel env loans ctx term with
  | none => simp [found] at checked
  | some kind =>
      cases kind with
      | type level => exact ⟨level,spine_sound found,(spine_sound found).typed⟩
      | index => simp [found] at checked

inductive Resolved (env : Environment) (loans : Loans.Stack) (ctx : Context) : Bool → Term → BinderMode → Prop where
  | erased : Resolved env loans ctx true domain .erased
  | head : Conversion.normalize? env fuel domain = some normal →
      ContextModes.head env normal = some mode → Resolved env loans ctx false domain mode
  | abstract : Conversion.normalize? env fuel domain = some normal →
      Spine env loans ctx normal (.type level) → Resolved env loans ctx false domain .unrestricted

def resolve (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context) (erased : Bool)
    (domain : Term) : Option BinderMode :=
  if erased then some .erased else do
    let normal ← Conversion.normalize? env fuel domain
    match ContextModes.head env normal with
    | some mode => some mode
    | none => if abstractType fuel env loans ctx normal then some .unrestricted else none

theorem resolve_sound (checked : resolve fuel env loans ctx erased domain = some mode) :
    Resolved env loans ctx erased domain mode := by
  unfold resolve at checked
  split at checked
  · rename_i isErased
    cases isErased
    cases checked
    exact .erased
  · have notErased : erased = false := by cases erased <;> simp_all
    subst erased
    obtain ⟨normal,normalized,checked⟩ := Option.bind_eq_some_iff.mp checked
    cases head : ContextModes.head env normal with
    | some known =>
        simp only [head,Option.some.injEq] at checked
        subst mode
        exact .head normalized head
    | none =>
        simp only [head] at checked
        split at checked
        · rename_i abstracted
          cases checked
          exact .abstract normalized (abstractType_sound abstracted).choose_spec.1
        · contradiction

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceModes
