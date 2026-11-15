import Jihoo.NativeLoanLendQuantity

/-! Complete loan-indexed native resource projection, retaining the original
contexts and stacks through every recursive source edge. Lend adds actual
entered-reader and restored-continuation guards; ordinary calls replay the
full loan checker. No old-typing-checker fallback supplies missing cases. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity ResourceModes ResourceReplay
variable {control : Control}
abbrev ControlScoped := Environment.ContextQuantity.ControlScoped

structure Opened where
  context : Context
  modes : List BinderMode
  body : Term
  deriving Repr

/-- Consume only syntactically leading source lambdas. Later computed function
expressions remain intact and are evaluated once through their checked signature. -/
def openHead : Nat → Environment → Loans.Stack → Context → Term → List Term → Option Opened
  | 0 => fun _ _ _ _ _ => none
  | fuel + 1 => fun env loans ctx head supplied => match head, supplied with
      | .lam erased domain body, _ :: arguments => do
          if !ResourceModes.contextOK fuel env loans ctx || !(Checker.binder fuel env loans ctx erased domain).isSome then none else
          let mode ← resolve fuel env loans ctx erased domain
          let rest ← openHead fuel env loans (⟨domain,erased⟩ :: ctx) body arguments
          pure ⟨rest.context,mode :: rest.modes,rest.body⟩
      | _, _ => some ⟨ctx,[],head⟩

/-- Native runtime positions outside calls and binding-sensitive operators. -/
def runtimeFields : Op → Option (List Nat)
  | .arith _ | .strict | .uadd | .usub | .alloc | .free | .drop _ | .index => some [0,1]
  | .store => some [0,1,2]
  | .elements count => some (List.range count)
  | .pack => some [1]
  | .witness => some [0]
  | .give erased => some (if erased then [1] else [1,2])
  | _ => none

/-- Types and evidence have no runtime ownership contribution. -/
def erasedNode : Op → Bool
  | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refl |
      .transport | .ind _ _ | .ltAdd | .ltCancel | .ltLe | .zeroLe |
      .refine | .proof | .buffer | .ref | .back _ | .borrow | .deref |
      .absurd | .pi _ | .natural _ | .integer _ | .decide => true
  | _ => false

def projectRaw : Nat → Environment → Loans.Stack → Context → Term → Option Control
  | 0, _, _, _, _ => none
  | _ + 1, _, _, ctx, .var index => do
      let binding ← lookup ctx index
      if binding.erased then none else some (.use index)
  | fuel + 1, env, loans, ctx, .node op arguments => do
      if arguments.length != op.arity then none else
      match op with
      | .global _ => none
      | .lend => match arguments with
          | [owner,reader,continuation] => projectLend (projectRaw fuel env) fuel env loans ctx owner reader continuation
          | _ => none
      | .borrow | .deref =>
          if (Checker.infer fuel env loans ctx false (.node op arguments)).isSome then some .pure else none
      | .con family constructor count => do
          let entry ← env.families[family]?
          let signature ← entry.signatures[constructor]?
          if count != arguments.length then none else
          let relevant ← EnvironmentQuantity.relevantFields entry.declaration.data signature.fields arguments
          let controls ← relevant.mapM (projectRaw fuel env loans ctx)
          pure (sequence controls)
      | .elim family count | .caseOf family count => do
          let table := EnvironmentCaseQuantity.compileTable env
          let entry ← EnvironmentCaseQuantity.findFamily table family
          if !entry.declaration.data then some .pure else
          let recursion := entry.boxed && match op with | .elim _ _ => true | _ => false
          let (cases, scrutinee) ← Checker.splitCases count (arguments.drop 1)
          let first ← projectRaw fuel env loans ctx scrutinee
          let controls ← EnvironmentCaseQuantity.caseControls (projectRaw fuel env loans ctx)
            entry.declaration.params recursion entry.signatures cases
          pure (.seq first (EnvironmentCaseQuantity.alternatives controls))
      | .view recursion family count => do
          let table := EnvironmentCaseQuantity.compileTable env
          let entry ← EnvironmentCaseQuantity.findFamily table family
          if !entry.boxed then none else
          let (cases, scrutinee) ← Checker.splitCases count (arguments.drop 1)
          let first ← projectRaw fuel env loans ctx scrutinee
          let controls ← EnvironmentCaseQuantity.caseControls (projectRaw fuel env loans ctx)
            entry.declaration.params recursion entry.signatures cases
          pure (.seq first (EnvironmentCaseQuantity.alternatives controls))
      | .app => do
          let (head, supplied) ← splitSpine fuel (.node .app arguments) []
          let (entries, result) ← ResourceReplay.checked fuel env loans ctx false head supplied
          if !partialOK fuel env loans ctx entries result then none else
          let opened ← openHead fuel env loans ctx head supplied
          let runtime ← (runtimeArguments entries).mapM (projectRaw fuel env loans ctx)
          let body ← projectRaw fuel env loans opened.context opened.body
          pure (if opened.modes.isEmpty then .seq body (sequence runtime)
            else .seq (sequence runtime) (.scopes opened.modes body))
      | .lam erased =>
          match arguments with
          | [domain, bodyTerm] => do
              if !ResourceModes.contextOK fuel env loans ctx || !(Checker.binder fuel env loans ctx erased domain).isSome then none else
              let mode ← resolve fuel env loans ctx erased domain
              let body ← projectRaw fuel env loans (⟨domain,erased⟩ :: ctx) bodyTerm
              pure (.closure (.scope mode (functionTail bodyTerm body)))
          | _ => none
      | .ifLt | .ifEq =>
          match arguments with
          | [left,right,yes,no] => do
              let first ← fields (projectRaw fuel env loans ctx) arguments [0,1]
              let proof := if op = .ifLt then Term.lt left right else Term.eq left right
              let yesControl ← projectRaw fuel env loans (⟨proof,true⟩ :: ctx) yes
              let noControl ← projectRaw fuel env loans ctx no
              pure (.seq first (.branch (.scope .erased yesControl) noControl))
          | _ => none
      | .fold => do
          let first ← fields (projectRaw fuel env loans ctx) arguments [0,1]
          let body ← fetch (projectRaw fuel env loans ctx) arguments 2
          pure (.seq first (.repeat (caseBody 3 body)))
      | .loop => do
          let first ← fields (projectRaw fuel env loans ctx) arguments [0,2]
          let body ← fetch (projectRaw fuel env loans ctx) arguments 3
          pure (.seq first (.repeat (caseBody 3 body)))
      | .load => do
          let first ← fields (projectRaw fuel env loans ctx) arguments [0,1]
          let body ← fetch (projectRaw fuel env loans ctx) arguments 3
          pure (.seq first (.once (caseBody 2 body)))
      | .take => do
          let first ← fetch (projectRaw fuel env loans ctx) arguments 0
          let body ← fetch (projectRaw fuel env loans ctx) arguments 1
          pure (.seq first (.once (caseBody 2 body)))
      | _ =>
          if erasedNode op then some .pure else do
          let relevant ← runtimeFields op
          fields (projectRaw fuel env loans ctx) arguments relevant

/-- Both original source scope and projected resource scope are computed.
Typing alone is not used to infer source scope. -/
def project (fuel : Nat) (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (term : Term) : Option Control := do
  if !NativeKernel.scopeCheck ctx.length term || !ResourceModes.contextOK fuel env loans ctx then none else
  let control ← projectRaw fuel env loans ctx term
  if Environment.ContextQuantity.scopeCheck ctx.length control then some control else none

 theorem project_scope (checked : project fuel env loans ctx term = some control) :
    term.Scoped ctx.length ∧ ResourceModes.ContextFormed env loans ctx ∧ ControlScoped ctx.length control := by
  unfold project at checked
  split at checked
  · contradiction
  · rename_i guards
    have permitted : NativeKernel.scopeCheck ctx.length term = true ∧
        ResourceModes.contextOK fuel env loans ctx = true := by
      simpa using Bool.eq_false_iff.mpr guards
    obtain ⟨candidate,projected,checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · rename_i scopedControl
      cases checked
      exact ⟨NativeKernel.scopeCheck_sound permitted.1,contextOK_sound permitted.2,
        Environment.ContextQuantity.scopeCheck_correct.mp scopedControl⟩
    · contradiction

def checkResource (fuel : Nat) (env : Environment) (term : Term) : Bool :=
  (project fuel env [] [] term).any (fun control => control.demand 0 == some 0)

def ResourceSafe (env : Environment) (term : Term) : Prop :=
  term.Scoped 0 ∧ EnvironmentCaseQuantity.TableValid env (EnvironmentCaseQuantity.compileTable env) ∧
    ∃ fuel control, project fuel env [] [] term = some control ∧ control.demand 0 = some 0 ∧
      LocalScopes control ∧ ControlScoped 0 control

theorem checkResource_sound (checked : checkResource fuel env term = true) : ResourceSafe env term := by
  cases projected : project fuel env [] [] term with
  | none => simp [checkResource,projected] at checked
  | some control =>
      have demand : control.demand 0 = some 0 := by
        simpa only [checkResource,projected,Option.any_some,beq_iff_eq] using checked
      have original := project_scope projected
      exact ⟨original.1,EnvironmentCaseQuantity.compileTable_valid,fuel,control,projected,demand,
        NativeQuantity.demand_localScopes _ demand,original.2.2⟩

def checkClosed (fuel quantityFuel : Nat) (env : Environment) (term expected : Term) : Bool :=
  NativeKernel.scopeCheck 0 expected && Checker.check fuel env [] [] false term expected &&
    checkResource quantityFuel env term

def ClosedSafe (env : Environment) (term expected : Term) : Prop :=
  term.Scoped 0 ∧ expected.Scoped 0 ∧ HasType env [] [] false term expected ∧
    EnvironmentCaseQuantity.TableValid env (EnvironmentCaseQuantity.compileTable env) ∧
    ∃ fuel control, project fuel env [] [] term = some control ∧ control.demand 0 = some 0 ∧
      LocalScopes control ∧ ControlScoped 0 control

 theorem checkClosed_sound (checked : checkClosed fuel quantityFuel env term expected = true) :
    ClosedSafe env term expected := by
  obtain ⟨initial,resource⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨expectedScope,typed⟩ := Bool.and_eq_true_iff.mp initial
  cases projected : project quantityFuel env [] [] term with
  | none => simp [checkResource,projected] at resource
  | some control =>
      have demand : control.demand 0 = some 0 := by
        simpa only [checkResource,projected,Option.any_some,beq_iff_eq] using resource
      have source := project_scope projected
      exact ⟨source.1,NativeKernel.scopeCheck_sound expectedScope,Checker.check_sound typed,
        EnvironmentCaseQuantity.compileTable_valid,quantityFuel,control,projected,demand,
        NativeQuantity.demand_localScopes _ demand,source.2.2⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
