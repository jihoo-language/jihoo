import Jihoo.NativeLoanCheckerPolicy

/-! Executable native loan checks. Recursive inference callbacks are exactly
the smaller-fuel calls of the full checker, including the entered reader stack.
These functions do not accept typing derivations or safety certificates. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Checker

def genericLend (inferSub : Bool → Term → Option Term) (fuel : Nat)
    (env : Environment) (ghost : Bool) (ownerType reader continuation : Term) : Option Term := do
  let readerType ← inferSub ghost reader
  let .pi false _ readerResult ← Conversion.normalize? env fuel readerType | none
  let rawDomain ← PartialRenaming.shift (-1) 0 readerResult
  let domain ← Conversion.normalize? env fuel rawDomain
  if Lending.outlivedHead env domain then
    let continuationType ← inferSub ghost continuation
    let .pi false _ (.pi false _ result) ← Conversion.normalize? env fuel continuationType | none
    let normal ← Conversion.normalize? env fuel result
    let outside ← PartialRenaming.shift (-2) 0 normal
    if accepts fuel env (some readerType) (.pi false (.ref ownerType) (domain.rename Nat.succ)) = true ∧
        accepts fuel env (some continuationType)
          (.pi false domain ((Term.pi false ownerType (outside.rename Nat.succ)).rename Nat.succ)) = true ∧
        (ghost || takeNonFunctionHead (Conversion.normalize env fuel outside)) = true
    then some outside else none
  else none

def dependentLend (inferStack : Loans.Stack → Bool → Term → Option Term)
    (inferBinder : Bool → Term → Option SortTag) (fuel : Nat)
    (env : Environment) (loans : Loans.Stack) (ctx : Context) (ghost : Bool)
    (owner : Nat) (ownerType domain readerBody first again body : Term) : Option Term := do
  let _ ← inferBinder false domain
  if Conversion.equal env fuel domain (.ref ownerType) then
    let stack := if ghost then loans else Loans.enter ctx.length owner loans
    let resultType ← expose fuel env (inferStack stack ghost (Lending.read (.var owner) readerBody))
    if Lending.outlivedHead env resultType = true ∧ Conversion.equal env fuel first resultType = true ∧
        Conversion.equal env fuel again (ownerType.rename Nat.succ) = true then
      let restored ← inferStack loans ghost (Lending.restore (.var owner) first body)
      let .pi false _ result ← Conversion.normalize? env fuel restored | none
      if accepts fuel env (some restored) (.pi false first result) then
        let normal ← Conversion.normalize? env fuel result
        let outside ← PartialRenaming.shift (-1) 0 normal
        if ghost || takeNonFunctionHead (Conversion.normalize env fuel outside) then some outside else none
      else none
    else none
  else none

def borrowAllowed (loans : Loans.Stack) (depth : Nat) (ghost : Bool) (owner : Term) : Bool :=
  ghost || match owner with
    | .var index => Loans.active depth loans index
    | _ => false

end Jihoo.NativeKernel.Environment.LoanTyping.Checker
