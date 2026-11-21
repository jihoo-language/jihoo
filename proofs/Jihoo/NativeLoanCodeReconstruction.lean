import Jihoo.NativeLoanPureDependentCodes

set_option maxUniverseOffset 40

/-! Reconstruct a finite semantic code directly from the written checked
type. The result packages the source identity and authentic binder levels. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes

open Finite (LevelSort)
open AffineSum (Expr)
open LoanTyping.PureHypothesisObservation (ScalarExpr)

private structure ClosedWord (term : Term) where
  expression : Expr
  scalar : ScalarExpr [] expression
  spelling : expression.toTerm = term

private def reconstructWord : Nat → (term : Term) → Option (ClosedWord term)
  | 0,_ => none
  | _+1,.natural value =>
    if fits : value < 2^64 then some ⟨.literal value,.literal fits,rfl⟩ else none
  | fuel+1,.uadd a b => do
    let first ← reconstructWord fuel a
    let second ← reconstructWord fuel b
    pure ⟨.add first.expression second.expression,.add first.scalar second.scalar,
      by simp only [Expr.toTerm,first.spelling,second.spelling]⟩
  | _+1,_ => none

structure Reconstructed (levels : List (Fin 32)) (term : Term) where
  sort : LevelSort
  code : Code levels sort
  exactSyntax : code.syntax = term

def reconstruct : Nat → (levels : List (Fin 32)) → (term : Term) → Option (Reconstructed levels term)
  | 0,_,_ => none
  | _+1,levels,.var index =>
    if inside : index < levels.length then
      some ⟨inputSort (levels.get ⟨index,inside⟩),.parameter ⟨index,inside⟩,rfl⟩
    else none
  | _+1,_,.u64 => some ⟨smallSort,.natural,rfl⟩
  | _+1,_,.prop => some ⟨smallSort,.proposition,rfl⟩
  | _+1,_,.univ level =>
    if inside : level < 32 then some ⟨universeSort ⟨level,inside⟩,.universeCode ⟨level,inside⟩,rfl⟩ else none
  | fuel+1,_,.lt a b => do
    let first ← reconstructWord fuel a
    let second ← reconstructWord fuel b
    pure ⟨.proposition,.less first.scalar second.scalar,by simp only [Code.syntax,first.spelling,second.spelling]⟩
  | fuel+1,_,.eq a b => do
    let first ← reconstructWord fuel a
    let second ← reconstructWord fuel b
    pure ⟨.proposition,.equal first.scalar second.scalar,by simp only [Code.syntax,first.spelling,second.spelling]⟩
  | fuel+1,levels,.pi false (.univ level) rest => do
    if inside : level < 32 then
      let selected : Fin 32 := ⟨level,inside⟩
      let body ← reconstruct fuel (selected::levels) rest
      pure ⟨(universeSort selected).pi body.sort,.abstract selected body.code,by simp only [Code.syntax,body.exactSyntax,selected]⟩
    else none
  | fuel+1,levels,.pi erased domain rest => do
    let first ← reconstruct fuel levels domain
    if allowed : if erased then first.sort.native = .prop else first.sort.native ≠ .prop then
      if explicitly : (PartialRenaming.lower 0 1 rest).isSome then
        let opened := (PartialRenaming.lower 0 1 rest).get explicitly
        let body ← reconstruct fuel levels opened
        have lowered : PartialRenaming.lower 0 1 rest = some opened := by
          exact (Option.some_get explicitly).symm
        have raise : PartialRenaming.raiseIndex 0 1 = Nat.succ := by
          funext index
          simp [PartialRenaming.raiseIndex]
        have scope : opened.rename Nat.succ = rest := by
          rw [←raise]
          exact PartialRenaming.lower_reweakens lowered
        pure ⟨first.sort.pi body.sort,.arrow erased allowed first.code body.code,
          by simp only [Code.syntax,first.exactSyntax,body.exactSyntax,scope]⟩
      else none
    else none
  | fuel+1,levels,.app (.lam false (.univ level) body) argument => do
    if inside : level < 32 then
      let selected : Fin 32 := ⟨level,inside⟩
      let output ← reconstruct fuel (selected::levels) body
      let input ← reconstruct fuel levels argument
      if compatible : input.sort = inputSort selected then
        let code : Code levels (inputSort selected) := compatible ▸ input.code
        have exactInput : code.syntax = argument := by
          obtain ⟨sort,expr,printed⟩ := input
          cases compatible
          exact printed
        pure ⟨output.sort,.apply selected output.code code,
          by simp only [Code.syntax,output.exactSyntax,exactInput,selected]⟩
      else none
    else none
  | _+1,_,_ => none

/-- Successful executable reconstruction connects the actual admitted
declaration to its finite semantic code at exactly the requested type. -/
theorem reconstruct_admitted {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    {result : Reconstructed [] declaration.value}
    (computed : reconstruct fuel [] declaration.value = some result) :
    RawValue.Conv env result.sort.native.term declaration.type ∧
    ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Reflected (result.code.meaning assignment) := by
  obtain ⟨_,_,_,_,_,history,wf,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  have typed := (history.global_value_and_reference found).1
  have exactSyntax := result.exactSyntax
  rw [←exactSyntax] at typed
  have _ := computed
  exact ⟨result.code.typing_agrees wf typed,result.code.reflected⟩

theorem checked_reconstruction {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (recognized : (reconstruct fuel [] declaration.value).isSome = true) :
    ∃ sort, ∃ code : Code [] sort,
      code.syntax = declaration.value ∧ RawValue.Conv env sort.native.term declaration.type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Reflected (code.meaning assignment) := by
  cases computed : reconstruct fuel [] declaration.value with
  | none => simp only [computed,Option.isSome_none,reduceCtorEq] at recognized
  | some result =>
    obtain ⟨converted,reflected⟩ := reconstruct_admitted accepted found computed
    exact ⟨result.sort,result.code,result.exactSyntax,converted,reflected⟩

theorem reconstructed_type_application :
    (reconstruct 5 [] (.app (.lam false (.univ 0) (.var 0)) .u64)).map Reconstructed.sort =
      some smallSort := by cbv

theorem reconstructed_quantified_false :
    (reconstruct 6 [] (quantifiedFalse (outer := []) [⟨0,by decide⟩,⟨31,by decide⟩]).syntax).isSome := by cbv

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes
