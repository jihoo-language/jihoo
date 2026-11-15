import Jihoo.NativeFamilyIotaSyntax
import Jihoo.NativeFamilyIotaDecoder

/-! Pure executable family contraction below actual checking and conversion. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

def eliminate (env : Environment) (analysis : Bool) (family count : Nat)
    (motive : Term) (children : List Term) : Option Term := do
  let entry ← env.families[family]?
  let (cases,scrutinee) ← Checker.splitCases count children
  let .node (.con actual constructor arity) values := scrutinee | none
  let signature ← entry.signatures[constructor]?
  let branch ← cases[constructor]?
  if actual = family ∧ arity = values.length ∧ cases.length = entry.signatures.length ∧
      values.length = signature.fields.length then
    if analysis then
      if entry.declaration.data then some (applications branch (values.drop entry.declaration.params)) else none
    else some (elimBody entry signature family motive branch cases values)
  else none

def view (env : Environment) (recursion : Bool) (family count : Nat)
    (motive : Term) (children : List Term) : Option Term := do
  let entry ← env.families[family]?
  let (cases,scrutinee) ← Checker.splitCases count children
  let .borrow (.node (.con actual constructor arity) values) := scrutinee | none
  let signature ← entry.signatures[constructor]?
  let branch ← cases[constructor]?
  if actual = family ∧ arity = values.length ∧ cases.length = entry.signatures.length ∧
      values.length = signature.fields.length ∧ entry.boxed = true ∧
      entry.declaration.params ≤ signature.fields.length then
    let plans ← viewPlan env family (signature.fields.drop entry.declaration.params)
    some (viewBody recursion family entry.declaration.params motive branch cases values plans)
  else none

def contract (env : Environment) : Term → Option Term
  | .node (.elim family count) (motive :: children) => eliminate env false family count motive children
  | .node (.caseOf family count) (motive :: children) => eliminate env true family count motive children
  | .node (.view recursion family count) (motive :: children) => view env recursion family count motive children
  | .node (.drop _) [_,rest] => some rest
  | _ => none

end Jihoo.NativeKernel.Environment.FamilyIota
