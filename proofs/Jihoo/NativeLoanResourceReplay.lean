import Jihoo.NativeLoanResourceModes

/-! Actual dependent application replay through the complete loan checker.
The argument records are shared data only; all executable inference, checking,
context authentication and abstract-spine queries are loan-indexed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceReplay
open ResourceModes CodeKinds

abbrev Argument := Environment.CallReplay.Argument
abbrev runtimeArguments := Environment.CallReplay.runtimeArguments

inductive Steps (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) :
    Term → List Term → List Argument → Term → Prop where
  | nil : Steps env loans ctx mode signature [] [] signature
  | cons : Conversion.normalize? env fuel signature = some (.pi erased domain body) →
      Checker.check fuel env loans ctx (mode || erased) argument domain = true →
      Checker.applicationOK fuel env mode domain argument = true →
      Conversion.substitutionSafe body argument = true →
      Steps env loans ctx mode (body.subst (single argument)) rest entries result →
      Steps env loans ctx mode signature (argument :: rest) (⟨erased,domain,argument⟩ :: entries) result

def replay : Nat → Environment → Loans.Stack → Context → Bool → Term → List Term →
    Option (List Argument × Term)
  | 0,_,_,_,_,_,_ => none
  | _+1,_,_,_,_,signature,[] => some ([],signature)
  | fuel+1,env,loans,ctx,mode,signature,argument :: rest => do
      let normal ← Conversion.normalize? env fuel signature
      match normal with
      | .pi erased domain body =>
          if Checker.check fuel env loans ctx (mode || erased) argument domain &&
              Checker.applicationOK fuel env mode domain argument && Conversion.substitutionSafe body argument then
            let (entries,result) ← replay fuel env loans ctx mode (body.subst (single argument)) rest
            pure (⟨erased,domain,argument⟩ :: entries,result)
          else none
      | _ => none

theorem replay_sound (checked : replay fuel env loans ctx mode signature arguments = some (entries,result)) :
    Steps env loans ctx mode signature arguments entries result := by
  induction fuel generalizing signature arguments entries result with
  | zero => simp [replay] at checked
  | succ fuel ih =>
      cases arguments with
      | nil =>
          simp only [replay,Option.some.injEq,Prod.mk.injEq] at checked
          obtain ⟨rfl,rfl⟩ := checked
          exact .nil
      | cons argument rest =>
          simp only [replay] at checked
          obtain ⟨normal,normalized,checked⟩ := Option.bind_eq_some_iff.mp checked
          split at checked
          · rename_i erased domain body
            split at checked
            · rename_i accepted
              have flags := Bool.and_eq_true_iff.mp accepted
              have actual := Bool.and_eq_true_iff.mp flags.1
              obtain ⟨pair,next,same⟩ := Option.bind_eq_some_iff.mp checked
              obtain ⟨tail,final⟩ := pair
              cases same
              exact .cons normalized actual.1 actual.2 flags.2 (ih next)
            · contradiction
          · contradiction

theorem Steps.apply (steps : Steps env loans ctx mode signature arguments entries result)
    (typed : HasType env loans ctx mode head signature) :
    HasType env loans ctx mode (applications head arguments) result := by
  induction steps generalizing head with
  | nil => exact typed
  | cons normalized checked allowed safe next ih =>
      exact ih (.app (.convert typed (Conversion.normalize?_sound normalized))
        (Checker.check_sound checked) (Checker.applicationOK_sound allowed))

theorem Steps.values (steps : Steps env loans ctx mode signature arguments entries result) :
    entries.map (fun entry => entry.value) = arguments := by
  induction steps with
  | nil => rfl
  | cons normalized checked allowed safe next ih => exact congrArg (List.cons _) ih

def infer (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool)
    (head : Term) (arguments : List Term) : Option (List Argument × Term) := do
  let signature ← Checker.infer fuel env loans ctx mode head
  replay fuel env loans ctx mode signature arguments

theorem infer_sound (checked : infer fuel env loans ctx mode head arguments = some (entries,result)) :
    ∃ signature, HasType env loans ctx mode head signature ∧
      Steps env loans ctx mode signature arguments entries result ∧
      HasType env loans ctx mode (applications head arguments) result := by
  unfold infer at checked
  obtain ⟨signature,inferred,replayed⟩ := Option.bind_eq_some_iff.mp checked
  have typed := Checker.infer_sound inferred
  have steps := replay_sound replayed
  exact ⟨signature,typed,steps,steps.apply typed⟩

def checked (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool)
    (head : Term) (arguments : List Term) : Option (List Argument × Term) :=
  if contextOK fuel env loans ctx && NativeKernel.scopeCheck ctx.length head &&
      arguments.all (NativeKernel.scopeCheck ctx.length)
  then infer fuel env loans ctx mode head arguments else none

theorem checked_origin (accepted : checked fuel env loans ctx mode head arguments = some (entries,result)) :
    contextOK fuel env loans ctx = true ∧ head.Scoped ctx.length ∧
      (∀ argument ∈ arguments,argument.Scoped ctx.length) ∧
      infer fuel env loans ctx mode head arguments = some (entries,result) := by
  unfold checked at accepted
  split at accepted
  · rename_i guards
    obtain ⟨initial,argumentsScoped⟩ := Bool.and_eq_true_iff.mp guards
    obtain ⟨formed,headScoped⟩ := Bool.and_eq_true_iff.mp initial
    exact ⟨formed,NativeKernel.scopeCheck_sound headScoped,
      fun argument member => NativeKernel.scopeCheck_sound (List.all_eq_true.mp argumentsScoped _ member),accepted⟩
  · contradiction

theorem checked_sound (accepted : checked fuel env loans ctx mode head arguments = some (entries,result)) :
    ContextFormed env loans ctx ∧ HasType env loans ctx mode (applications head arguments) result := by
  have original := checked_origin accepted
  exact ⟨contextOK_sound original.1,(infer_sound original.2.2.2).choose_spec.2.2⟩

def linearDomain (env : Environment) : Term → Bool
  | .back _ _ _ => true
  | domain => Checker.ownedHead env domain

def ownsArgument (env : Environment) (entry : Argument) : Bool :=
  !entry.erased && linearDomain env entry.domain

def rigidResultHead : Term → Bool
  | .var _ => false
  | term@(.node _ _) => Checker.takeNonFunctionHead term

def partialOK (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (entries : List Argument) (result : Term) : Bool :=
  !(entries.any (ownsArgument env)) ||
    (rigidResultHead (Conversion.normalize env fuel result) ||
      abstractType fuel env loans ctx (Conversion.normalize env fuel result))

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceReplay
