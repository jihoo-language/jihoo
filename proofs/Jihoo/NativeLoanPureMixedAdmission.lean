import Jihoo.NativeLoanPureTypingChecker
import Jihoo.NativeLoanEnvironmentExtension

/-! Ordered mixed admission using the original family, raw CODE, and quantity
checkers. The ghost fallback types the fully expanded body, using the checked
types of earlier definitions for aliases and dependent applications. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureMixedAdmission

open UnifiedProgram

structure Limits where
  typingFuel : Nat
  quantityFuel : Nat
  conversionFuel : Nat
  budget : Nat

private theorem extendConversion (extension : Extends before after)
    (converted : RawValue.Conv before first second) : RawValue.Conv after first second := by
  induction converted using RawValue.Conv.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (RawValue.Conv after) xs ys) with
  | old raw => exact .old (raw.extend extension)
  | strict first rest => exact .strict first rest
  | free owner rest => exact .free owner rest
  | refl term => exact .refl term
  | symm _ ih => exact .symm ih
  | trans _ _ left right => exact .trans left right
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ left right => exact .cons left right

private theorem extendBinder (extension : Extends before after)
    (binder : Binder before [] ctx erased domain sort) : Binder after [] ctx erased domain sort := by
  cases binder with
  | intro formed allowed =>
    refine .intro (formed.extend extension) ?_
    rcases allowed with pure | ⟨erasedTrue, family, count, indices, entry, found, data, converted⟩
    · apply Or.inl
      cases erased with
      | false => exact pure
      | true => exact pure.imp id (fun converted => converted.extend extension)
    · exact Or.inr ⟨erasedTrue, family, count, indices, entry, extension.families _ _ found,
        data, converted.extend extension⟩

theorem extendTyping (extension : Extends before after)
    (typed : PureTyping.HasType before ctx term type) : PureTyping.HasType after ctx term type := by
  induction typed with
  | native typed => exact .native (typed.extend extension)
  | convert _ formed converted ih => exact .convert ih (formed.extend extension) (extendConversion extension converted)
  | pi binder _ ih => exact .pi (extendBinder extension binder) ih
  | lam binder formed _ ih => exact .lam (extendBinder extension binder) (formed.extend extension) ih
  | app _ formed argument ih => exact .app ih (formed.extend extension) (argument.extend extension)

def SlotTyping (env : Environment) : Prop :=
  ∀ (index : Nat) (declaration : GlobalDeclaration), env.globals[index]? = some declaration →
    ∃ sort : SortTag, HasType env [] [] true declaration.type sort.term ∧
      PureTyping.HasType env [] declaration.value declaration.type

private def inferStep (fuel : Nat) (env : Environment) (recur : Term → Term → Option Term) :
    Term → Term → Option Term
  | .node (.global index) [], expanded => do
    let declaration ← env.globals[index]?
    if declaration.value == expanded then some declaration.type else none
  | .app sourceFunction _, .app function argument => do
    let .pi erased domain result ← recur sourceFunction function | none
    let _ ← Checker.sort fuel env [] [⟨domain, erased⟩] result
    if Checker.check fuel env [] [] true argument domain = true ∧
        Conversion.substitutionSafe result argument = true then
      some (result.subst (single argument))
    else none
  | _, _ => none

private theorem inferStep_sound
    (prior : SlotTyping env)
    (recursiveSound : ∀ {source expanded type}, recur source expanded = some type →
      PureTyping.HasType env [] expanded type)
    (checked : inferStep fuel env recur source expanded = some type) :
    PureTyping.HasType env [] expanded type := by
  fun_cases inferStep fuel env recur source expanded
  · simp only [inferStep] at checked
    obtain ⟨declaration, found, checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · rename_i same
      have aligned := beq_iff_eq.mp same
      cases checked
      rw [← aligned]
      obtain ⟨_, _, typed⟩ := prior _ declaration found
      exact typed
    · contradiction
  · simp only [inferStep] at checked
    obtain ⟨functionType, inferred, checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · obtain ⟨sort, formed, checked⟩ := Option.bind_eq_some_iff.mp checked
      split at checked
      · rename_i argumentChecked
        cases checked
        exact .app (recursiveSound inferred) (Checker.sort_sound formed) (Checker.check_sound argumentChecked.1)
      · contradiction
    · contradiction
  · simp [inferStep, *] at checked

/-- Read a prior ghost's exact checked type only when its stored value is
actually the expanded term. A dependent application uses that type to check
the expanded argument and independently form its result. -/
def inferExpandedGhost (fuel : Nat) (env : Environment) : Nat → Term → Term → Option Term
  | 0, _, _ => none
  | depth + 1, source, expanded =>
    (inferStep fuel env (inferExpandedGhost fuel env depth) source expanded).orElse
      (fun _ => Checker.infer fuel env [] [] true expanded)

theorem inferExpandedGhost_sound (prior : SlotTyping env)
    (checked : inferExpandedGhost fuel env depth source expanded = some type) :
    PureTyping.HasType env [] expanded type := by
  induction depth generalizing source expanded type with
  | zero => simp [inferExpandedGhost] at checked
  | succ depth ih =>
    simp only [inferExpandedGhost] at checked
    cases step : inferStep fuel env (inferExpandedGhost fuel env depth) source expanded with
    | none => exact .native (Checker.infer_sound (by simpa only [step, Option.orElse_none] using checked))
    | some result =>
      simp only [step, Option.orElse_some, Option.some.injEq] at checked
      subst result
      exact inferStep_sound prior (fun ran => ih ran) step

structure ExpandedValid (env : Environment) (declaration : GlobalDeclaration) : Prop where
  typing : ∃ sort : SortTag, HasType env [] [] true declaration.type sort.term ∧
    PureTyping.HasType env [] declaration.value declaration.type ∧
    (Definitions.bodyMode sort = false →
      HasType env [] [] false declaration.value declaration.type ∧
      ResourceQuantity.ResourceSafe env declaration.value)
  closed : declaration.type.Scoped 0 ∧ declaration.value.Scoped 0 ∧
    declaration.type.WellFormed ∧ declaration.value.WellFormed
  transparent : GlobalEnvironment.GlobalFree declaration.type ∧ GlobalEnvironment.GlobalFree declaration.value

private theorem ExpandedValid.ofRaw (raw : MixedProgram.ExpandedValid env declaration) :
    ExpandedValid env declaration := by
  obtain ⟨sort, formed, typed, safe⟩ := raw.typing
  refine ⟨⟨sort, formed, .native (typed.ghost []), ?_⟩,
    ⟨raw.typeScoped, raw.valueScoped, raw.typeWellFormed, raw.valueWellFormed⟩,
    ⟨raw.typeTransparent, raw.valueTransparent⟩⟩
  intro code
  simpa only [code] using And.intro typed (safe code)

private def checkGhost (limits : Limits) (env : Environment)
    (source expanded : GlobalDeclaration) : Bool :=
  if shapeCheck expanded.type = true ∧ shapeCheck expanded.value = true ∧
      scopeCheck 0 expanded.type = true ∧ scopeCheck 0 expanded.value = true ∧
      Environment.globalFree expanded.type = true ∧ Environment.globalFree expanded.value = true then
    ((do
      let sort ← Checker.sort limits.typingFuel env [] [] expanded.type
      if !Definitions.bodyMode sort then none else
        let original ← inferExpandedGhost limits.typingFuel env limits.typingFuel source.value expanded.value
        if PureTyping.Checker.equal env limits.conversionFuel limits.budget original expanded.type
        then some () else none) : Option Unit).isSome
  else false

private theorem checkGhost_sound (prior : SlotTyping env)
    (accepted : checkGhost limits env source expanded = true) : ExpandedValid env expanded := by
  unfold checkGhost at accepted
  split at accepted
  · rename_i checkedSyntax
    obtain ⟨_, ran⟩ := Option.isSome_iff_exists.mp accepted
    obtain ⟨sort, formed, ran⟩ := Option.bind_eq_some_iff.mp ran
    split at ran
    · contradiction
    · rename_i mode
      obtain ⟨original, inferred, ran⟩ := Option.bind_eq_some_iff.mp ran
      split at ran
      · rename_i converted
        have ghost : Definitions.bodyMode sort = true := by simpa using mode
        refine ⟨⟨sort, Checker.sort_sound formed,
          .convert (inferExpandedGhost_sound prior inferred) (Checker.sort_sound formed)
            (PureTyping.Checker.equal_sound converted), ?_⟩, ?_, ?_⟩
        · intro code
          rw [ghost] at code
          contradiction
        · exact ⟨scopeCheck_sound checkedSyntax.2.2.1, scopeCheck_sound checkedSyntax.2.2.2.1,
            shapeCheck_wellFormed checkedSyntax.1, shapeCheck_wellFormed checkedSyntax.2.1⟩
        · exact ⟨(Environment.globalFree_correct _).mp checkedSyntax.2.2.2.2.1,
            (Environment.globalFree_correct _).mp checkedSyntax.2.2.2.2.2⟩
      · contradiction
  · contradiction

structure DeclarationChecked (env : Environment) (source expanded : GlobalDeclaration) : Prop where
  typeExpansion : GlobalEnvironment.Expansion env.globals source.type expanded.type
  valueExpansion : GlobalEnvironment.Expansion env.globals source.value expanded.value
  valid : ExpandedValid env expanded

def checkDeclaration (limits : Limits) (env : Environment) (source : GlobalDeclaration) : Option GlobalDeclaration := do
  let type ← GlobalEnvironment.expand limits.typingFuel env.globals source.type
  let value ← GlobalEnvironment.expand limits.typingFuel env.globals source.value
  let expanded : GlobalDeclaration := ⟨type, value⟩
  if MixedProgram.checkExpanded limits.typingFuel limits.quantityFuel env expanded ||
     checkGhost limits env source expanded then some expanded else none

theorem checkDeclaration_sound (prior : SlotTyping env)
    (accepted : checkDeclaration limits env source = some expanded) : DeclarationChecked env source expanded := by
  unfold checkDeclaration at accepted
  obtain ⟨type, typeExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨value, valueExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · rename_i checked
    cases accepted
    refine ⟨GlobalEnvironment.expand_sound typeExpanded, GlobalEnvironment.expand_sound valueExpanded, ?_⟩
    rcases Bool.or_eq_true_iff.mp checked with raw | pure
    · exact .ofRaw (MixedProgram.checkExpanded_sound raw)
    · exact checkGhost_sound prior pure
  · contradiction

theorem checkDeclaration_accepts_raw
    (accepted : MixedProgram.checkDeclaration limits.typingFuel limits.quantityFuel env source = some expanded) :
    checkDeclaration limits env source = some expanded := by
  unfold MixedProgram.checkDeclaration at accepted
  obtain ⟨type, typeExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨value, valueExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · rename_i acceptedRaw
    cases accepted
    simp [checkDeclaration, typeExpanded, valueExpanded, acceptedRaw]
  · contradiction

/-- In CODE mode the new admission has exactly the original acceptance
criteria, including the resource projection of the expanded body. -/
theorem checkDeclaration_code_is_raw
    (accepted : checkDeclaration limits env source = some expanded)
    (sorted : Checker.sort limits.typingFuel env [] [] expanded.type = some sort)
    (code : Definitions.bodyMode sort = false) :
    MixedProgram.checkDeclaration limits.typingFuel limits.quantityFuel env source = some expanded := by
  unfold checkDeclaration at accepted
  obtain ⟨type, typeExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨value, valueExpanded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · rename_i checked
    cases accepted
    rcases Bool.or_eq_true_iff.mp checked with raw | ghost
    · simp [MixedProgram.checkDeclaration, typeExpanded, valueExpanded, raw]
    · unfold checkGhost at ghost
      split at ghost
      · simp [sorted, code] at ghost
      · contradiction
  · contradiction

inductive History : List GlobalDeclaration → List FamilyDeclaration → Environment → Prop where
  | empty : History [] [] Environment.empty
  | definition : History definitions familyDeclarations env → DeclarationChecked env source expanded →
      History (definitions ++ [source]) familyDeclarations ⟨env.globals.push expanded, env.families⟩
  | family : History definitions familyDeclarations env → Families.FamilyChecked env source entry →
      History definitions (familyDeclarations ++ [source]) ⟨env.globals, env.families.push entry⟩

theorem History.wellFormed (history : History definitions familyDeclarations env) : EnvWellFormed env := by
  induction history with
  | empty => exact .empty
  | definition _ checked ih => exact ih.pushGlobal checked.valid.closed checked.valid.transparent
  | family _ checked ih => exact ih.pushFamily checked.signatures_scoped

/-- A stored value retains the particular prefix that independently checked
its original annotation, body, and any CODE resource obligations. -/
theorem History.global_prefix (history : History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration) :
    ∃ prefixDefinitions prefixFamilies earlier source,
      History prefixDefinitions prefixFamilies earlier ∧ earlier.globals.size = index ∧
        DeclarationChecked earlier source declaration ∧ Extends earlier env := by
  induction history with
  | empty =>
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact False.elim (Nat.not_lt_zero index inside)
  | @definition definitions familyDeclarations env source added history checked ih =>
    have extension := Extends.pushGlobal env added
    by_cases earlier : index < env.globals.size
    · have old : env.globals[index]? = some declaration := by
        rw [Array.getElem?_eq_getElem earlier]
        simpa only [Array.getElem?_push_lt earlier] using found
      obtain ⟨ds, fs, priorEnv, raw, history, size, valid, retained⟩ := ih old
      exact ⟨ds, fs, priorEnv, raw, history, size, valid, retained.trans extension⟩
    · have inside := (Array.getElem?_eq_some_iff.mp found).1
      have same : index = env.globals.size := by simp only [Array.size_push] at inside; omega
      subst index
      rw [Array.getElem?_push_size] at found
      cases found
      exact ⟨definitions, familyDeclarations, env, source, history, rfl, checked, extension⟩
  | @family definitions familyDeclarations env source entry history checked ih =>
    obtain ⟨ds, fs, priorEnv, raw, history, size, valid, retained⟩ := ih found
    exact ⟨ds, fs, priorEnv, raw, history, size, valid, retained.trans (Extends.pushFamily env entry)⟩

theorem History.slotTyping (history : History definitions familyDeclarations env) : SlotTyping env := by
  intro index declaration found
  obtain ⟨_, _, _, _, _, _, checked, retained⟩ := history.global_prefix found
  obtain ⟨sort, formed, typed, _⟩ := checked.valid.typing
  exact ⟨sort, formed.extend retained, extendTyping retained typed⟩

theorem History.global_value_and_reference (history : History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration) :
    PureTyping.HasType env [] declaration.value declaration.type ∧
      PureTyping.HasType env [] (.node (.global index) []) declaration.type := by
  obtain ⟨_, _, typed⟩ := history.slotTyping index declaration found
  have referenced : HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) := .global found
  rw [Term.rename_id] at referenced
  exact ⟨typed, .native referenced⟩

def checkEvents (limits : Limits) (env : Environment) : List FamilyEnvironment.Event → Option Environment
  | [] => some env
  | .definition source :: events => do
    let expanded ← checkDeclaration limits env source
    checkEvents limits ⟨env.globals.push expanded, env.families⟩ events
  | .family source :: events => do
    let entry ← Families.checkFamily limits.typingFuel env source
    checkEvents limits ⟨env.globals, env.families.push entry⟩ events

theorem checkEvents_sound (history : History definitions familyDeclarations env)
    (accepted : checkEvents limits env events = some result) :
    History (definitions ++ FamilyEnvironment.eventDefinitions events)
      (familyDeclarations ++ FamilyEnvironment.eventFamilies events) result := by
  induction events generalizing definitions familyDeclarations env with
  | nil =>
    cases accepted
    simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies, List.append_nil] using history
  | cons event events ih =>
    cases event with
    | definition source =>
      obtain ⟨expanded, checked, rest⟩ := Option.bind_eq_some_iff.mp accepted
      simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
        List.append_assoc, List.singleton_append] using
        ih (.definition history (checkDeclaration_sound history.slotTyping checked)) rest
    | family source =>
      obtain ⟨entry, checked, rest⟩ := Option.bind_eq_some_iff.mp accepted
      simpa only [FamilyEnvironment.eventDefinitions, FamilyEnvironment.eventFamilies,
        List.append_assoc, List.singleton_append] using
        ih (.family history (Families.checkFamily_sound checked)) rest

def checkProgram (limits : Limits) (definitions : List GlobalDeclaration) (familyDeclarations : List FamilyDeclaration) :
    Option Environment := do
  let events ← FamilyEnvironment.schedule (definitions.length + familyDeclarations.length + 1) 0 definitions familyDeclarations
  checkEvents limits empty events

theorem checkProgram_sound (accepted : checkProgram limits definitions familyDeclarations = some env) :
    History definitions familyDeclarations env := by
  obtain ⟨events, scheduled, checked⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨orderedDefs, orderedFamilies⟩ := FamilyEnvironment.schedule_sound scheduled
  simpa only [List.nil_append, orderedDefs, orderedFamilies] using checkEvents_sound History.empty checked

def checkBytes (limits : Limits) (bytes : ByteArray) : Option Environment := do
  let snapshot ← NativeFamilyWire.decodeSnapshot bytes
  let (definitions, familyDeclarations) ← NativeFamilyWire.decodeProgram snapshot
  checkProgram limits definitions (familyDeclarations.map NativeLoanMixedAdmission.declaration)

theorem checkBytes_sound (accepted : checkBytes limits bytes = some env) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List GlobalDeclaration)
      (familyDeclarations : List NativeFamilyWire.FamilyTerms),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      NativeFamilyWire.decodeProgram snapshot = some (definitions, familyDeclarations) ∧
      History definitions (familyDeclarations.map NativeLoanMixedAdmission.declaration) env ∧
      EnvWellFormed env ∧ SlotTyping env := by
  obtain ⟨snapshot, decoded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨program, source, checked⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨definitions, familyDeclarations⟩ := program
  have history := checkProgram_sound checked
  exact ⟨snapshot, definitions, familyDeclarations, NativeFamilyWire.decodeSnapshot_exact decoded, source,
    history, history.wellFormed, history.slotTyping⟩

private def fixtureLimits : Limits := ⟨32, 32, 32, 8192⟩

private def freeDefinition : GlobalDeclaration := ⟨PureFreeBoundary.annotation, PureFreeBoundary.body⟩

private def inheritedDefinition : GlobalDeclaration :=
  ⟨PureFreeBoundary.annotation, .node (.global 0) []⟩

private def appliedDefinition : GlobalDeclaration :=
  ⟨.eq (.free PureFreeBoundary.owner (.natural 0)) (.natural 0),
    .app (.node (.global 1) []) (.natural 0)⟩

private def scalarDefinition : GlobalDeclaration := ⟨.i64, .integer 7⟩

private def bit : Term := .node (.ind 0 0) []

private def bitFamily : FamilyDeclaration :=
  ⟨true, 0, 0, [bit, .pi false .u64 bit], 2⟩

/-- The original Free equality admits a later alias. The family is checked
after those two ghosts and before their dependent application and the raw
scalar declaration. -/
theorem checks_mixed_prior_ghosts :
    (checkProgram fixtureLimits
      [freeDefinition, inheritedDefinition, appliedDefinition, scalarDefinition] [bitFamily]).isSome = true := by
  cbv

/-- Replay uses the earlier slot type, so the dependent result keeps the
original Free annotation even though the expanded lambda infers a different
principal type in the raw checker. -/
theorem dependent_alias_keeps_stored_type :
    inferExpandedGhost 32 ⟨#[freeDefinition, freeDefinition], #[]⟩ 32 appliedDefinition.value
      (.app PureFreeBoundary.body (.natural 0)) = some appliedDefinition.type := by
  cbv

end Jihoo.NativeKernel.Environment.LoanTyping.PureMixedAdmission
