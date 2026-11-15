import Jihoo.NativeViewExtension
import Jihoo.NativeEnvironmentPrefix

/-! Syntax-only genuine family-iota roots. No environment typing or checker
module is imported, so raw computation can underlie enlarged conversion. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

def elimTerm (family : Nat) (motive : Term) (cases : List Term) (scrutinee : Term) : Term :=
  .node (.elim family cases.length) (motive :: (cases ++ [scrutinee]))

def caseTerm (family : Nat) (motive : Term) (cases : List Term) (scrutinee : Term) : Term :=
  .node (.caseOf family cases.length) (motive :: (cases ++ [scrutinee]))

def viewTerm (recursion : Bool) (family : Nat) (motive : Term) (cases : List Term) (scrutinee : Term) : Term :=
  .node (.view recursion family cases.length) (motive :: (cases ++ [scrutinee]))

/-- Recursive fields come from the independently checked signature; substituted
field expressions are never inspected to guess recursive positions. -/
def elimHypotheses (family : Nat) (motive : Term) (cases : List Term)
    (fields : List Field) (values : List Term) : List Term :=
  (fields.zip values).filterMap fun (field,value) =>
    if field.recursive.isSome then some (elimTerm family motive cases value) else none

/-- Parameters are omitted from data cases and retained in Prop elimination. -/
def elimBody (entry : CheckedFamily) (signature : Signature) (family : Nat)
    (motive branch : Term) (cases values : List Term) : Term :=
  applications (applications branch (values.drop (if entry.declaration.data then entry.declaration.params else 0)))
    (elimHypotheses family motive cases signature.fields values)

/-- Retain erased arguments; borrow exactly the nonerased heap fields. -/
def viewArguments (plans : List ViewFieldPlan) (values : List Term) : List Term :=
  (plans.zip values).map fun (plan,value) => if plan.borrowed then .borrow value else value

def viewHypotheses (recursion : Bool) (family : Nat) (motive : Term) (cases : List Term)
    (plans : List ViewFieldPlan) (values : List Term) : List Term :=
  if recursion then (plans.zip values).filterMap fun (plan,value) =>
    if plan.self then some (viewTerm true family motive cases (.borrow value)) else none
  else []

def viewBody (recursion : Bool) (family params : Nat) (motive branch : Term)
    (cases values : List Term) (plans : List ViewFieldPlan) : Term :=
  applications (applications branch (viewArguments plans (values.drop params)))
    (viewHypotheses recursion family motive cases plans (values.drop params))

/-- Actual pure constructor equations. Every family, signature and selected
case comes from concrete lookup. These roots authorize no runtime destruction
and manufacture no active loan. -/
inductive Root (env : Environment) : Term → Term → Prop where
  | elim : env.families[family]? = some entry → entry.signatures[constructor]? = some signature →
      cases[constructor]? = some branch → cases.length = entry.signatures.length →
      values.length = signature.fields.length →
      Root env (elimTerm family motive cases (.node (.con family constructor values.length) values))
        (elimBody entry signature family motive branch cases values)
  | caseOf : env.families[family]? = some entry → entry.declaration.data = true →
      entry.signatures[constructor]? = some signature → cases[constructor]? = some branch →
      cases.length = entry.signatures.length → values.length = signature.fields.length →
      Root env (caseTerm family motive cases (.node (.con family constructor values.length) values))
        (applications branch (values.drop entry.declaration.params))
  | view : env.families[family]? = some entry → entry.boxed = true →
      entry.signatures[constructor]? = some signature → cases[constructor]? = some branch →
      cases.length = entry.signatures.length → values.length = signature.fields.length →
      entry.declaration.params ≤ signature.fields.length →
      viewPlan env family (signature.fields.drop entry.declaration.params) = some plans →
      Root env (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values)))
        (viewBody recursion family entry.declaration.params motive branch cases values plans)
  | drop (family : Nat) (owner rest : Term) : Root env (.node (.drop family) [owner,rest]) rest

/-- Appending a checked prefix preserves every successful concrete lookup. -/
theorem Root.extend (step : Root before term result) (extension : Extends before after) :
    Root after term result := by
  cases step with
  | elim found signature branch count fields => exact .elim (extension.families _ _ found) signature branch count fields
  | caseOf found data signature branch count fields => exact .caseOf (extension.families _ _ found) data signature branch count fields
  | view found boxed signature branch count fields params planned =>
      exact .view (extension.families _ _ found) boxed signature branch count fields params
        (viewPlan_extend extension planned)
  | drop => exact .drop _ _ _


end Jihoo.NativeKernel.Environment.FamilyIota
