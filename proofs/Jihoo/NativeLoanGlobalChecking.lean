import Jihoo.NativeLoanCheckerSoundness
import Jihoo.NativeScopeCheck
import Jihoo.NativeTermShapeCheck

/-! Sequential transparent-global type checking with the full loan judgment.
Source declarations expand against the actual earlier prefix, and every stored
annotation/body is checked for native shape, closed scope and transparent form.
This module checks typing; runtime quantity admission is a separate layer. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Program

structure ExpandedTyped (env : Environment) (declaration : GlobalDeclaration) : Prop where
  typing : ∃ sort : SortTag, HasType env [] [] true declaration.type sort.term ∧
    HasType env [] [] (Definitions.bodyMode sort) declaration.value declaration.type
  typeScoped : declaration.type.Scoped 0
  valueScoped : declaration.value.Scoped 0
  typeWellFormed : declaration.type.WellFormed
  valueWellFormed : declaration.value.WellFormed
  typeTransparent : GlobalEnvironment.GlobalFree declaration.type
  valueTransparent : GlobalEnvironment.GlobalFree declaration.value

def checkExpanded (fuel : Nat) (env : Environment) (declaration : GlobalDeclaration) : Bool :=
  if shapeCheck declaration.type = true ∧ shapeCheck declaration.value = true ∧
      scopeCheck 0 declaration.type = true ∧ scopeCheck 0 declaration.value = true ∧
      Environment.globalFree declaration.type = true ∧ Environment.globalFree declaration.value = true then
    match Checker.sort fuel env [] [] declaration.type with
    | none => false
    | some sort => Checker.check fuel env [] [] (Definitions.bodyMode sort) declaration.value declaration.type
  else false

theorem checkExpanded_sound (checked : checkExpanded fuel env declaration = true) :
    ExpandedTyped env declaration := by
  unfold checkExpanded at checked
  split at checked
  · rename_i syntaxChecked
    cases sorted : Checker.sort fuel env [] [] declaration.type with
    | none => simp [sorted] at checked
    | some sort =>
        exact ⟨⟨sort,Checker.sort_sound sorted,
          Checker.check_sound (by simpa only [sorted] using checked)⟩,
          scopeCheck_sound syntaxChecked.2.2.1,scopeCheck_sound syntaxChecked.2.2.2.1,
          shapeCheck_wellFormed syntaxChecked.1,shapeCheck_wellFormed syntaxChecked.2.1,
          (Environment.globalFree_correct _).mp syntaxChecked.2.2.2.2.1,
          (Environment.globalFree_correct _).mp syntaxChecked.2.2.2.2.2⟩
  · contradiction

structure DeclarationChecked (env : Environment) (source expanded : GlobalDeclaration) : Prop where
  typeExpansion : GlobalEnvironment.Expansion env.globals source.type expanded.type
  valueExpansion : GlobalEnvironment.Expansion env.globals source.value expanded.value
  valid : ExpandedTyped env expanded

def checkDeclaration (fuel : Nat) (env : Environment) (source : GlobalDeclaration) : Option GlobalDeclaration := do
  let type ← GlobalEnvironment.expand fuel env.globals source.type
  let value ← GlobalEnvironment.expand fuel env.globals source.value
  let expanded : GlobalDeclaration := ⟨type,value⟩
  if checkExpanded fuel env expanded then some expanded else none

theorem checkDeclaration_sound
    (checked : checkDeclaration fuel env source = some expanded) : DeclarationChecked env source expanded := by
  unfold checkDeclaration at checked
  obtain ⟨type,typeExpanded,checked⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨value,valueExpanded,checked⟩ := Option.bind_eq_some_iff.mp checked
  dsimp only at checked
  split at checked
  · rename_i accepted
    cases checked
    exact ⟨GlobalEnvironment.expand_sound typeExpanded,GlobalEnvironment.expand_sound valueExpanded,
      checkExpanded_sound accepted⟩
  · contradiction

theorem DeclarationChecked.references_before (checked : DeclarationChecked env source expanded) :
    GlobalEnvironment.Before env.globals.size source.type ∧ GlobalEnvironment.Before env.globals.size source.value :=
  ⟨checked.typeExpansion.before,checked.valueExpansion.before⟩

theorem DeclarationChecked.wellFormed (checked : DeclarationChecked env source expanded)
    (prior : UnifiedProgram.EnvWellFormed env) :
    UnifiedProgram.EnvWellFormed ⟨env.globals.push expanded,env.families⟩ :=
  prior.pushGlobal
    ⟨checked.valid.typeScoped,checked.valid.valueScoped,
      checked.valid.typeWellFormed,checked.valid.valueWellFormed⟩
    ⟨checked.valid.typeTransparent,checked.valid.valueTransparent⟩

inductive ProgramChecked : List GlobalDeclaration → Environment → Prop where
  | empty : ProgramChecked [] empty
  | append : ProgramChecked sources env → DeclarationChecked env source expanded →
      ProgramChecked (sources ++ [source]) ⟨env.globals.push expanded,env.families⟩

def checkFrom (fuel : Nat) (env : Environment) : List GlobalDeclaration → Option Environment
  | [] => some env
  | source :: rest => do
      let expanded ← checkDeclaration fuel env source
      checkFrom fuel ⟨env.globals.push expanded,env.families⟩ rest

def checkProgram (fuel : Nat) (sources : List GlobalDeclaration) : Option Environment :=
  checkFrom fuel empty sources

theorem checkFrom_sound (history : ProgramChecked prior env)
    (checked : checkFrom fuel env sources = some result) : ProgramChecked (prior ++ sources) result := by
  induction sources generalizing prior env with
  | nil =>
      simp only [checkFrom,Option.some.injEq] at checked
      subst result
      simpa only [List.append_nil] using history
  | cons source rest ih =>
      simp only [checkFrom] at checked
      obtain ⟨expanded,accepted,checked⟩ := Option.bind_eq_some_iff.mp checked
      simpa only [List.append_assoc,List.singleton_append] using
        ih (.append history (checkDeclaration_sound accepted)) checked

theorem checkProgram_sound (checked : checkProgram fuel sources = some result) : ProgramChecked sources result := by
  simpa only [List.nil_append] using checkFrom_sound ProgramChecked.empty checked

theorem ProgramChecked.wellFormed (history : ProgramChecked sources env) : UnifiedProgram.EnvWellFormed env := by
  induction history with
  | empty => exact UnifiedProgram.EnvWellFormed.empty
  | append _ checked ih => exact checked.wellFormed ih

theorem ProgramChecked.size (history : ProgramChecked sources env) : env.globals.size = sources.length := by
  induction history with
  | empty => rfl
  | append _ _ ih => simpa only [Array.size_push,List.length_append,List.length_singleton] using congrArg Nat.succ ih

theorem ProgramChecked.noFamilies (history : ProgramChecked sources env) : env.families = #[] := by
  induction history with
  | empty => rfl
  | append _ _ ih => exact ih

end Jihoo.NativeKernel.Environment.LoanTyping.Program
