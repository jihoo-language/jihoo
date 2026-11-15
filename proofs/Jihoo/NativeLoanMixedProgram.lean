import Jihoo.NativeLoanGlobalChecking
import Jihoo.NativeLoanQuantity
import Jihoo.NativeUnifiedProgram

/-! One mixed program history for Loan64 typing, actual runtime resource
projection and checked inductive signatures. Every step uses its real earlier
global/family prefix. This is not a heap execution or consistency theorem. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram
open UnifiedProgram

structure ExpandedValid (env : Environment) (declaration : GlobalDeclaration) : Prop where
  typing : ∃ sort : SortTag, HasType env [] [] true declaration.type sort.term ∧
    HasType env [] [] (Definitions.bodyMode sort) declaration.value declaration.type ∧
    (Definitions.bodyMode sort = false → ResourceQuantity.ResourceSafe env declaration.value)
  typeScoped : declaration.type.Scoped 0
  valueScoped : declaration.value.Scoped 0
  typeWellFormed : declaration.type.WellFormed
  valueWellFormed : declaration.value.WellFormed
  typeTransparent : GlobalEnvironment.GlobalFree declaration.type
  valueTransparent : GlobalEnvironment.GlobalFree declaration.value

def checkExpanded (fuel quantityFuel : Nat) (env : Environment) (declaration : GlobalDeclaration) : Bool :=
  if shapeCheck declaration.type = true ∧ shapeCheck declaration.value = true ∧
      scopeCheck 0 declaration.type = true ∧ scopeCheck 0 declaration.value = true ∧
      Environment.globalFree declaration.type = true ∧ Environment.globalFree declaration.value = true then
    match Checker.sort fuel env [] [] declaration.type with
    | none => false
    | some sort => Checker.check fuel env [] [] (Definitions.bodyMode sort) declaration.value declaration.type &&
        (Definitions.bodyMode sort || ResourceQuantity.checkResource quantityFuel env declaration.value)
  else false

theorem checkExpanded_sound (accepted : checkExpanded fuel quantityFuel env declaration = true) :
    ExpandedValid env declaration := by
  unfold checkExpanded at accepted
  split at accepted
  · rename_i syntaxChecked
    cases sorted : Checker.sort fuel env [] [] declaration.type with
    | none => simp [sorted] at accepted
    | some sort =>
        have both := Bool.and_eq_true_iff.mp (by simpa only [sorted] using accepted)
        refine ⟨⟨sort,Checker.sort_sound sorted,Checker.check_sound both.1,?_⟩,
          scopeCheck_sound syntaxChecked.2.2.1,scopeCheck_sound syntaxChecked.2.2.2.1,
          shapeCheck_wellFormed syntaxChecked.1,shapeCheck_wellFormed syntaxChecked.2.1,
          (Environment.globalFree_correct _).mp syntaxChecked.2.2.2.2.1,
          (Environment.globalFree_correct _).mp syntaxChecked.2.2.2.2.2⟩
        intro code
        rcases Bool.or_eq_true_iff.mp both.2 with erased | resources
        · rw [code] at erased
          contradiction
        · exact ResourceQuantity.checkResource_sound resources
  · contradiction

structure DeclarationChecked (env : Environment) (source expanded : GlobalDeclaration) : Prop where
  typeExpansion : GlobalEnvironment.Expansion env.globals source.type expanded.type
  valueExpansion : GlobalEnvironment.Expansion env.globals source.value expanded.value
  valid : ExpandedValid env expanded

def checkDeclaration (fuel quantityFuel : Nat) (env : Environment)
    (source : GlobalDeclaration) : Option GlobalDeclaration := do
  let type ← GlobalEnvironment.expand fuel env.globals source.type
  let value ← GlobalEnvironment.expand fuel env.globals source.value
  let expanded : GlobalDeclaration := ⟨type, value⟩
  if checkExpanded fuel quantityFuel env expanded then some expanded else none

theorem checkDeclaration_sound
    (accepted : checkDeclaration fuel quantityFuel env source = some expanded) :
    DeclarationChecked env source expanded := by
  unfold checkDeclaration at accepted
  cases typeExpanded : GlobalEnvironment.expand fuel env.globals source.type with
  | none => simp [typeExpanded] at accepted
  | some type =>
      simp only [typeExpanded, Bind.bind, Option.bind] at accepted
      cases valueExpanded : GlobalEnvironment.expand fuel env.globals source.value with
      | none => simp [valueExpanded] at accepted
      | some value =>
          simp only [valueExpanded] at accepted
          split at accepted
          · rename_i checked
            cases accepted
            exact ⟨GlobalEnvironment.expand_sound typeExpanded,
              GlobalEnvironment.expand_sound valueExpanded, checkExpanded_sound checked⟩
          · contradiction

/-- Independent mixed history: every step uses the same actual earlier table.
No legacy pure-prefix judgment or caller-supplied signature is a constructor. -/
inductive History : List GlobalDeclaration → List FamilyDeclaration → Environment → Prop where
  | empty : History [] [] Environment.empty
  | definition : History definitions familyDeclarations env → DeclarationChecked env source expanded →
      History (definitions ++ [source]) familyDeclarations ⟨env.globals.push expanded, env.families⟩
  | family : History definitions familyDeclarations env → Families.FamilyChecked env source entry →
      History definitions (familyDeclarations ++ [source]) ⟨env.globals, env.families.push entry⟩

def checkEvents (fuel quantityFuel : Nat) (env : Environment) : List FamilyEnvironment.Event → Option Environment
  | [] => some env
  | .definition source :: events => do
      let expanded ← checkDeclaration fuel quantityFuel env source
      checkEvents fuel quantityFuel ⟨env.globals.push expanded, env.families⟩ events
  | .family source :: events => do
      let entry ← Families.checkFamily fuel env source
      checkEvents fuel quantityFuel ⟨env.globals, env.families.push entry⟩ events

def checkProgram (fuel quantityFuel : Nat) (definitions : List GlobalDeclaration) (familyDeclarations : List FamilyDeclaration) :
    Option Environment := do
  let events ← FamilyEnvironment.schedule (definitions.length + familyDeclarations.length + 1) 0 definitions familyDeclarations
  checkEvents fuel quantityFuel Environment.empty events

theorem checkEvents_sound {familyDeclarations : List FamilyDeclaration} (history : History definitions familyDeclarations env)
    (accepted : checkEvents fuel quantityFuel env events = some result) :
    History (definitions ++ FamilyEnvironment.eventDefinitions events)
      (familyDeclarations ++ FamilyEnvironment.eventFamilies events) result := by
  induction events generalizing definitions familyDeclarations env with
  | nil => simp only [checkEvents, Option.some.injEq] at accepted; subst result; simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies, List.append_nil] using history
  | cons event events ih =>
      cases event with
      | definition source =>
          simp only [checkEvents] at accepted
          cases checked : checkDeclaration fuel quantityFuel env source with
          | none => simp [checked] at accepted
          | some expanded =>
              simp only [checked, Bind.bind, Option.bind] at accepted
              simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
                List.append_assoc, List.singleton_append] using
                ih (.definition history (checkDeclaration_sound checked)) accepted
      | family source =>
          simp only [checkEvents] at accepted
          cases checked : Families.checkFamily fuel env source with
          | none => simp [checked] at accepted
          | some entry =>
              simp only [checked, Bind.bind, Option.bind] at accepted
              simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
                List.append_assoc, List.singleton_append] using
                ih (.family history (Families.checkFamily_sound checked)) accepted

theorem checkProgram_sound {familyDeclarations : List FamilyDeclaration} (accepted : checkProgram fuel quantityFuel definitions familyDeclarations = some result) :
    History definitions familyDeclarations result := by
  unfold checkProgram at accepted
  cases scheduled : FamilyEnvironment.schedule (definitions.length + familyDeclarations.length + 1) 0 definitions familyDeclarations with
  | none => simp [scheduled] at accepted
  | some events =>
      simp only [scheduled, Bind.bind, Option.bind] at accepted
      obtain ⟨definitionOrder, familyOrder⟩ := FamilyEnvironment.schedule_sound scheduled
      simpa only [List.nil_append, definitionOrder, familyOrder] using
        checkEvents_sound History.empty accepted

theorem DeclarationChecked.closed (checked : DeclarationChecked env source expanded) :
    expanded.type.Scoped 0 ∧ expanded.value.Scoped 0 ∧ expanded.type.WellFormed ∧ expanded.value.WellFormed := by
  exact ⟨checked.valid.typeScoped, checked.valid.valueScoped,
    checked.valid.typeWellFormed, checked.valid.valueWellFormed⟩

theorem History.wellFormed (history : History definitions familyDeclarations env) :
    UnifiedProgram.EnvWellFormed env := by
  induction history with
  | empty => exact UnifiedProgram.EnvWellFormed.empty
  | definition history checked ih =>
      exact ih.pushGlobal checked.closed
        ⟨checked.valid.typeTransparent,checked.valid.valueTransparent⟩
  | family history checked ih => exact ih.pushFamily checked.signatures_scoped

theorem checkProgram_wellFormed
    (accepted : checkProgram fuel quantityFuel definitions familyDeclarations = some env) : UnifiedProgram.EnvWellFormed env :=
  (checkProgram_sound accepted).wellFormed

theorem History.globalLength (history : History definitions familyDeclarations env) :
    env.globals.size = definitions.length := by
  induction history <;> simp_all [Environment.empty]

theorem History.familyLength (history : History definitions familyDeclarations env) :
    env.families.size = familyDeclarations.length := by
  induction history <;> simp_all [Environment.empty]

/-- Lookup provenance retains the exact validated earlier mixed prefix. -/
theorem History.global_prefix
    (history : History definitions familyDeclarations env)
    {index : Nat} {entry : GlobalDeclaration} (found : env.globals[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      History prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.globals.size = index ∧
      DeclarationChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      have bounded : index < env.globals.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.globals.size
      · have old : env.globals[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushGlobal env added)⟩
      · have same : index = env.globals.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushGlobal env entry⟩
  | @family definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushFamily env added)⟩

theorem History.family_prefix
    (history : History definitions familyDeclarations env)
    {index : Nat} {entry : CheckedFamily} (found : env.families[index]? = some entry) :
    ∃ prefixDefinitions prefixFamilies earlierEnv source,
      History prefixDefinitions prefixFamilies earlierEnv ∧ earlierEnv.families.size = index ∧
      Families.FamilyChecked earlierEnv source entry ∧ Environment.Extends earlierEnv env := by
  induction history with
  | empty =>
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions families env source added history checked ih =>
      obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih found
      exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
        extension.trans (Environment.Extends.pushGlobal env added)⟩
  | @family definitions families env source added history checked ih =>
      have bounded : index < env.families.size + 1 := by
        obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using inside
      by_cases earlier : index < env.families.size
      · have old : env.families[index]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        obtain ⟨ds, fs, earlierEnv, raw, prior, size, valid, extension⟩ := ih old
        exact ⟨ds, fs, earlierEnv, raw, prior, size, valid,
          extension.trans (Environment.Extends.pushFamily env added)⟩
      · have same : index = env.families.size := by omega
        subst index
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env, source, history, rfl, checked,
          Environment.Extends.pushFamily env entry⟩

end Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram
