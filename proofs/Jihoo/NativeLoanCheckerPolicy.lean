import Jihoo.NativeFamilyIotaDecoder
import Jihoo.NativeLoanTyping
import Jihoo.NativePartialRenaming
import Jihoo.NativeChecker

/-! Data-input executable checking on the complete native constructor syntax.
Type comparison uses verified bounded conversion. Global/family
environments and ownership rules are not silently
assumed: operators without a rule below reject. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Checker
open Environment.Checker (splitCases)

/-- Verified conversion of an actual inferred type to an expected type. -/
def accepts (fuel : Nat) (env : Environment) (inferred : Option Term) (expected : Term) : Bool :=
  match inferred with
  | some actual => Conversion.equal env fuel actual expected
  | none => false

/-- Normalize an inferred type before inspecting its head constructor. -/
def expose (fuel : Nat) (env : Environment) (inferred : Option Term) : Option Term :=
  inferred.bind (Conversion.normalize? env fuel)

def dataBinderOK (env : Environment) : Term → Bool
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.declaration.data
  | _ => false

/-- Native erased-data policy uses metadata from the actual environment. -/
def pureBinderOK (fuel : Nat) (env : Environment) (erased : Bool) (A : Term) (s : SortTag) : Bool :=
  if erased then decide (s = .prop) || Conversion.equal env fuel A .u64 else decide (s ≠ .prop)

def binderOK (fuel : Nat) (env : Environment) (erased : Bool) (A : Term) (s : SortTag) : Bool :=
  pureBinderOK fuel env erased A s ||
    (erased && dataBinderOK env (Conversion.normalize env fuel A))

/-- Executable native first-order gate after verified normalization. -/
def applicationOK (fuel : Nat) (env : Environment) (ghost : Bool) (domain argument : Term) : Bool :=
  ghost || match Conversion.normalize? env fuel domain with
    | none => false
    | some normal => globalFree normal && (!kindOf normal ||
        (firstOrderKind normal && plain env (Conversion.normalize env fuel argument)))

/-- Read the exact native loop motive sort: Prop or Type0 only. -/
def loopSort : Term → Option Bool
  | .prop => some true
  | .univ 0 => some false
  | _ => none

def loopMotiveOK (fuel : Nat) (env : Environment) (proof : Bool) (motive : Term) : Bool :=
  proof || scalarLoopMotive (Conversion.normalize env fuel motive)

/-- Resolve an owned head against actual family storage metadata. -/
def ownedHead (env : Environment) : Term → Bool
  | .buffer _ => true
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.boxed
  | _ => false

/-- Exact native representation gate. Erased motive results are propositions;
other motives normalize to lambdas with a fixed known runtime representation. -/
def backMotiveOK (fuel : Nat) (env : Environment) (erased : Bool) (motive : Term) : Bool :=
  erased || match Conversion.normalize env fuel motive with
    | .lam _ _ body => fixedRepresentation env body
    | _ => false

/-- Additional rigid ownership heads can never be function types. -/
def resourceNonFunctionHead : Term → Bool
  | .buffer _ | .ref _ | .back _ _ _ | .node (.ind _ _) _ => true
  | _ => false

def takeNonFunctionHead (result : Term) : Bool := nonFunctionHead result || resourceNonFunctionHead result

/-- Native binders(body,3) permits memory operations beneath the callback. -/
def iterationBodyOK (env : Environment) (body : Term) : Bool :=
  hasLeadingLambdas 3 body || iterationMemoryFree env body

def ownedLoopMotiveOK (fuel : Nat) (env : Environment) (motive : Term) : Bool :=
  match Conversion.normalize env fuel motive with
  | .lam _ _ body => ownedHead env body
  | _ => false

def iterationMotiveOK (fuel : Nat) (env : Environment) (proof : Bool) (motive : Term) : Bool :=
  loopMotiveOK fuel env proof motive || ownedLoopMotiveOK fuel env motive

/-- Instantiate all constructor fields using only concrete recursive inference. -/
def instantiate (inferField : Bool → Term → Option Term) (fuel : Nat) (env : Environment) (ghost data : Bool) :
    Term → List Term → Option Term
  | telescope, [] => some (Conversion.normalize env fuel telescope)
  | telescope, argument :: arguments =>
      match Conversion.normalize env fuel telescope with
      | .pi erased domain rest =>
          if accepts fuel env (inferField (ghost || !(data && !erased)) argument) domain then
            instantiate inferField fuel env ghost data
              (rest.subst (fun | 0 => argument | n + 1 => .var n)) arguments
          else none
      | _ => none

/-- Infer each proposition branch against its derived dependent case telescope. -/
def branches (inferBranch : Term → Option Term) (fuel : Nat) (env : Environment) (motive : Term) :
    List Signature → List Term → Bool
  | [], [] => true
  | signature :: signatures, branch :: rest =>
      accepts fuel env (inferBranch branch) (propCaseType signature motive) &&
        branches inferBranch fuel env motive signatures rest
  | _, _ => false

/-- Check a list of computed branch types; no signature callback is accepted. -/
def branchesAgainst (inferBranch : Term → Option Term) (fuel : Nat) (env : Environment) :
    List Term → List Term → Bool
  | [], [] => true
  | type :: types, branch :: branches =>
      accepts fuel env (inferBranch branch) type && branchesAgainst inferBranch fuel env types branches
  | _, _ => false

def dataMotiveProof (env : Environment) (inferred : Option Term) (fuel family params arity : Nat) (ps : List Term) : Option Bool :=
  if accepts fuel env inferred (dataMotiveType family params arity ps true) then some true
  else if accepts fuel env inferred (dataMotiveType family params arity ps false) then some false
  else none

/-- Concrete data elimination. The recursive inference argument is always the
smaller-fuel call of infer; soundness discharges it from that induction. -/
def dataEliminate (inferSub : Bool → Term → Option Term) (fuel : Nat)
    (env : Environment) (ctx : Context) (ghost analysis : Bool)
    (family count : Nat) (motive : Term) (children : List Term) : Option Term := do
  let entry ← env.families[family]?
  if entry.declaration.data = true ∧ (analysis = false ∨ entry.boxed = true) then
    let (cases, scrutinee) ← splitCases count children
    let .node (.ind g arity) indices ← expose fuel env (inferSub true scrutinee) | none
    if g = family ∧ arity = entry.declaration.arity ∧ indices.length = entry.declaration.arity then
      let ps := indices.take entry.declaration.params
      let proof ← dataMotiveProof env (inferSub true motive) fuel family
        entry.declaration.params entry.declaration.arity ps
      let types ← dataCaseTypes family entry.declaration.params ctx.length entry.signatures ps motive
        (entry.boxed && !analysis) proof
      let result := Term.app (applications motive (indices.drop entry.declaration.params)) scrutinee
      if accepts fuel env (inferSub (ghost || proof) scrutinee) (.node (.ind family arity) indices) = true ∧
          branchesAgainst (inferSub (ghost || proof)) fuel env types cases = true ∧
          ((ghost || proof) || takeNonFunctionHead (Conversion.normalize env fuel result)) = true
      then some result else none
    else none
  else none

/-- A type's normal form is never a lambda; a lambda supplies a view motive. -/
def viewDependent : Term → Bool
  | .lam _ _ _ => true
  | _ => false

def viewMotiveOK : Term → Bool
  | .lam _ _ body => viewRepresentation 128 1 body
  | _ => true

/-- Native borrowed view from checked constructor signatures and actual type
inference. Unknown aliases, extra indices and budget failures reject. -/
def viewEliminate (inferSub : Bool → Term → Option Term) (fuel : Nat)
    (env : Environment) (ctx : Context) (ghost recursion : Bool)
    (family count : Nat) (motive : Term) (children : List Term) : Option Term := do
  let entry ← env.families[family]?
  if entry.declaration.data = true ∧ entry.boxed = true ∧ entry.declaration.arity = entry.declaration.params then
    let (cases,scrutinee) ← splitCases count children
    let .ref (.node (.ind g arity) indices) ← expose fuel env (inferSub ghost scrutinee) | none
    if g = family ∧ arity = entry.declaration.arity ∧ indices.length = entry.declaration.params then
      let normal ← Conversion.normalize? env fuel motive
      let dependent := viewDependent normal
      if accepts fuel env (inferSub true motive)
          (viewMotiveType dependent (.node (.ind family arity) indices)) = true ∧ viewMotiveOK normal = true then
        let types ← viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive recursion dependent
        if branchesAgainst (inferSub ghost) fuel env types cases then
          some (viewResult dependent motive scrutinee)
        else none
      else none
    else none
  else none

end Jihoo.NativeKernel.Environment.LoanTyping.Checker
