import Jihoo.NativeCoreViewShape

/-! The live View telescope and the independently checked signature meet
at rigid domain trees. Authentic field checking supplies conversion from the
written domain to the stored field. Successful graph visits supply a second
conversion, and rigidity forces the two results to be the same tree. -/
namespace Jihoo.NativeKernel.NativeCoreViewShapeAlignment

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome runThroughAliases runWithConditionals)
open NativeCoreViewShape (CheckedVisits piAt skipParameters)
open NativeCoreViewNormal (checkedShape ShapeAgrees)
open NativeCoreCaseNormal (Refines)
open FamilyIota (viewTerm)
open NativeProgramWire (Roots RepresentsDefinitions)
open UnifiedProgram.Families
open NativeKernel.Conversion (ListRel)

inductive RigidTree : Term → Prop where
  | var : RigidTree (.var index)
  | node : RawLend.rigid op = true → (∀ child ∈ children, RigidTree child) →
      RigidTree (.node op children)

private theorem fixed_children (related : ListRel (RawLend.Forward env) sources targets)
    (fixed : ∀ source ∈ sources, ∀ target, RawLend.Forward env source target → target = source) :
    targets = sources := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      rw [fixed _ (by simp) _ head, ih (fun source member => fixed source (by simp [member]))]

theorem RigidTree.forward_fixed (rigid : RigidTree term) (forward : RawLend.Forward env term residual) :
    residual = term := by
  induction rigid generalizing residual with
  | var => exact forward.variable_shape _ rfl
  | node head _ ih =>
      obtain ⟨children, rfl, related⟩ := forward.rigid_shape head rfl
      rw [fixed_children related ih]

theorem RigidTree.converted_equal (first : RigidTree left) (second : RigidTree right)
    (converted : RawLend.Conv env left right) (valid : EnvironmentDelta.Admissible env) : left = right := by
  obtain ⟨common, firstStep, secondStep⟩ := converted.church_rosser valid
  exact (first.forward_fixed firstStep).symm.trans (second.forward_fixed secondStep)

private theorem expand_converts (env : Environment) (term : Term) :
    RawLend.Conv env term (EnvironmentDelta.expand env term) :=
  (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward env term))).toConv

private theorem expansion_converts (expanded : GlobalEnvironment.Expansion env.globals raw result) :
    RawLend.Conv env raw result := by
  rw [← EnvironmentDelta.expansion_eq_expand expanded]
  exact expand_converts env raw

private theorem indices_convert (verified : IndicesChecked env self ctx written normalized) :
    ListRel (RawLend.Conv env) written normalized := by
  induction verified with
  | nil => exact .nil
  | cons index _ ih =>
      obtain ⟨_, _, expanded, _, converted, _⟩ := index
      exact .cons ((expansion_converts expanded).trans (.old converted)) ih

private theorem field_converts (checked : FieldChecked env self declaration ctx erased written field) :
    field.erased = erased ∧ RawLend.Conv env written field.domain := by
  cases checked with
  | ordinary _ expanded _ converted _ _ =>
      exact ⟨rfl, (expansion_converts expanded).trans (.old converted)⟩
  | recursive _ _ verified _ _ =>
      exact ⟨rfl, .node _ (indices_convert verified)⟩

/-- Each callback really runs on the raw domain at its live clock. Its
represented result is rigid and has an independently proved conversion from
its input. This certificate contains no checked signature or expected terms. -/
inductive RigidVisits (env : Environment) (visit : State → Nat → Outcome Nat) : State → Nat → State → Prop
  | done : piAt state.arena cursor = none → RigidVisits env visit state cursor state
  | step : piAt state.arena cursor = some (erased, raw, rest) → rest < cursor →
      (visit state raw).result = .ok selected →
      Prefix state.arena (visit state raw).state.arena →
      (Backward state.arena → Backward (visit state raw).state.arena) →
      Represents (visit state raw).state.arena selected observed → RigidTree observed →
      (∀ term, Represents state.arena raw term → RawLend.Conv env term observed) →
      RigidVisits env visit (visit state raw).state rest after →
      RigidVisits env visit state cursor after

theorem RigidVisits.frame (visits : RigidVisits env visit state cursor after) :
    Prefix state.arena after.arena ∧ (Backward state.arena → Backward after.arena) := by
  induction visits with
  | done => exact ⟨.refl _, id⟩
  | step _ _ _ kept backward _ _ _ _ ih =>
      exact ⟨kept.trans ih.1, fun checked => ih.2 (backward checked)⟩

/-- The existing graph proof supplies a visit's conversion even when a
visible global leads into beta reduction. The certificate asks only for
the actual accepted result, its representation and its rigidity. -/
theorem RigidVisits.alias_step
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions state.arena roots definitions)
    (read : piAt state.arena cursor = some (erased, raw, rest)) (older : rest < cursor)
    (source : Represents state.arena raw written)
    (success : (runThroughAliases roots visible limit depth state raw).result = .ok selected)
    (output : Represents (runThroughAliases roots visible limit depth state raw).state.arena selected observed)
    (rigid : RigidTree observed)
    (more : RigidVisits env (runThroughAliases roots visible limit depth)
      (runThroughAliases roots visible limit depth state raw).state rest after) :
    RigidVisits env (runThroughAliases roots visible limit depth) state cursor after := by
  obtain ⟨kept, backward, residual, represented, changed⟩ :=
    NativeCorePureComputationNormal.runThroughAliases_refines aligned history source success
  have same := represented.unique output
  subst residual
  refine .step read older success kept backward output rigid ?_ more
  intro term held
  rw [held.unique source]
  exact (expand_converts env written).trans (changed.converted.trans (expand_converts env observed).symm)

private theorem RigidVisits.finish (visits : RigidVisits env visit state cursor after)
    (endOfTelescope : piAt state.arena cursor = none) : after = state := by
  cases visits with
  | done => rfl
  | step found => rw [endOfTelescope] at found; cases found

private theorem RigidVisits.advance (visits : RigidVisits env visit state cursor after)
    (read : piAt state.arena cursor = some (erased, raw, rest)) :
    ∃ selected observed, rest < cursor ∧ (visit state raw).result = .ok selected ∧
      Prefix state.arena (visit state raw).state.arena ∧
      Represents (visit state raw).state.arena selected observed ∧ RigidTree observed ∧
      (∀ term, Represents state.arena raw term → RawLend.Conv env term observed) ∧
      RigidVisits env visit (visit state raw).state rest after := by
  cases visits with
  | done stopped => rw [read] at stopped; cases stopped
  | step found older returned kept _ represented rigid converts more =>
      obtain ⟨flag, refs⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans read))
      obtain ⟨rawRef, tailRef⟩ := Prod.mk.inj refs
      subst_vars
      exact ⟨_, _, older, returned, kept, represented, rigid, converts, more⟩

private theorem fields_prefix (checked : TelescopeChecked env self declaration prior source signature) :
    ∃ fields, signature.fields = prior ++ fields := by
  induction checked with
  | result => exact ⟨[], List.append_nil _ |>.symm⟩
  | field _ _ ih =>
      obtain ⟨fields, extended⟩ := ih
      exact ⟨_, extended.trans (List.append_assoc _ _ _)⟩

private theorem advance_fields
    (checked : TelescopeChecked env self declaration (prior ++ [field]) source signature) :
    signature.fields.drop prior.length = field :: signature.fields.drop (prior ++ [field]).length := by
  obtain ⟨fields, stored⟩ := fields_prefix checked
  calc
    _ = field :: fields := by rw [stored, List.append_assoc, List.singleton_append, List.drop_left]
    _ = _ := by rw [stored, List.drop_left]

private theorem read_pi {cursor raw rest : Nat}
    (read : arena[cursor]? = some (.node (.pi erased) [raw, rest])) :
    piAt arena cursor = some (erased, raw, rest) := by
  simp only [piAt, read]

private theorem telescope_visits (checked : TelescopeChecked before self declaration prior source signature)
    (extension : Extends before env) (valid : EnvironmentDelta.Admissible env)
    (represented : Represents state.arena cursor source)
    (visits : RigidVisits env visit state (skipParameters state.arena skip cursor) after)
    (canonical : ∀ field ∈ (signature.fields.drop prior.length).drop skip, RigidTree field.domain) :
    CheckedVisits visit state (skipParameters state.arena skip cursor)
      ((signature.fields.drop prior.length).drop skip) after := by
  induction checked generalizing state cursor skip with
  | result count _ _ _ =>
      cases represented with
      | node read _ _ =>
          have terminal : piAt state.arena cursor = none := by simp only [piAt, read]
          have skipped : skipParameters state.arena skip cursor = cursor := by
            cases skip <;> simp only [skipParameters, terminal]
          rw [skipped] at visits ⊢
          rw [visits.finish terminal, List.drop_length, List.drop_nil]
          exact .done terminal
  | field formed tail ih =>
      have fields := advance_fields tail
      cases represented with
      | @node _ _ refs _ read _ representedChildren =>
          cases representedChildren with
          | cons rawDomain representedTail =>
              cases representedTail with
              | cons rawRest empty =>
                  cases empty
                  have pi := read_pi read
                  cases skip with
                  | succ skip =>
                      simp only [skipParameters, pi, fields, List.drop_succ_cons] at visits canonical ⊢
                      exact ih rawRest visits canonical
                  | zero =>
                      simp only [skipParameters, fields, List.drop_zero] at visits canonical ⊢
                      obtain ⟨selected, observed, older, returned, kept, result, rigid, converted, later⟩ :=
                        visits.advance pi
                      obtain ⟨erasure, independent⟩ := field_converts formed
                      have agree := rigid.converted_equal (canonical _ (by simp))
                        ((converted _ rawDomain).symm.trans (independent.extend extension)) valid
                      rw [agree] at result
                      exact .step (by simpa only [erasure] using pi) older returned result
                        (ih (skip := 0) (rawRest.frame kept) later
                          (fun child member => canonical child (List.mem_cons_of_mem _ member)))

/-- Recover the actual canonical fields, erasure flags, and parameter skip
from the genuine checked family prefix and its represented raw constructor.
Only the graph visits' rigidity and conversion certificates are supplied. -/
theorem checked_visits_from_history
    {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (raw : entry.declaration.constructors[constructor]? = some source)
    (represented : Represents state.arena typeRoot source)
    (visits : RigidVisits env visit state (skipParameters state.arena entry.declaration.params typeRoot) after)
    (canonical : ∀ field ∈ signature.fields.drop entry.declaration.params, RigidTree field.domain) :
    CheckedVisits visit state (skipParameters state.arena entry.declaration.params typeRoot)
      (signature.fields.drop entry.declaration.params) after := by
  obtain ⟨_, _, _, declaration, _, _, familyChecked, extension⟩ := history.family_prefix found
  obtain ⟨written, selected, telescope⟩ := familyChecked.signatures.right sig
  have rawLookup : declaration.constructors[constructor]? = some source := by
    simpa only [familyChecked.declaration] using raw
  have same : written = source := Option.some.inj (selected.symm.trans rawLookup)
  subst written
  exact telescope_visits telescope extension history.wellFormed.admissible represented visits canonical

/-- The genuine declaration and matched rigid visits determine the exact
shape flags and the shared arena and clock produced by the traversal. -/
theorem run_from_history
    {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (raw : entry.declaration.constructors[constructor]? = some source)
    (represented : Represents state.arena typeRoot source)
    (visits : RigidVisits env visit state (skipParameters state.arena entry.declaration.params typeRoot) after)
    (canonical : ∀ field ∈ signature.fields.drop entry.declaration.params, RigidTree field.domain)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans) :
    NativeCoreViewShape.run env family visit state entry.declaration.params typeRoot =
        ⟨after, .ok (checkedShape plans)⟩ ∧ ShapeAgrees env family constructor (checkedShape plans) :=
  NativeCoreViewShape.run_checked found sig
    (checked_visits_from_history history found sig raw represented visits canonical) planned

/-- From the known-owner stage, a rigid live telescope run and a checked
reentry visitor together retain the original View type and arena prefix. -/
theorem run_preserves_from_history
    {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (sig : entry.signatures[constructor]? = some signature)
    (raw : entry.declaration.constructors[constructor]? = some source)
    (represented : Represents state.arena typeRoot source)
    (visits : RigidVisits env visit state (skipParameters state.arena entry.declaration.params typeRoot) after)
    (canonical : ∀ field ∈ signature.fields.drop entry.declaration.params, RigidTree field.domain)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (motiveRep : Represents state.arena motiveRef motive)
    (casesRep : RepresentsList state.arena caseRefs cases)
    (scrutineeRep : Represents state.arena scrutinee (.borrow (.node (.con family constructor values.length) values)))
    (typed : LoanTyping.HasType env loans ctx mode
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type)
    (visitSound : ∀ {next root term output}, Represents next.arena root term →
      LoanTyping.HasType env [] ctx true term type → (visit next root).result = .ok output →
      Refines env next.arena (visit next root).state.arena output ctx term type)
    (success : (NativeCoreViewShape.runWithShape env visit state recursion family motiveRef entry.declaration.params
      typeRoot caseRefs scrutinee).result = .ok (some selected)) :
    Refines env state.arena
      (NativeCoreViewShape.runWithShape env visit state recursion family motiveRef entry.declaration.params
        typeRoot caseRefs scrutinee).state.arena selected ctx
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor values.length) values))) type :=
  NativeCoreViewShape.runWithShape_preserves history found sig planned
    (checked_visits_from_history history found sig raw represented visits canonical)
    motiveRep casesRep scrutineeRep typed visits.frame.1 visits.frame.2 visitSound success

namespace Examples

private def box : Term := .node (.ind 0 0) []
private def betaDomain : Term := .app (.lam false .u64 .u64) (.natural 1)
private def alias : Term := .node (.global 0) []
private def definition : GlobalDeclaration := ⟨.univ 0, betaDomain⟩
private def rawConstructor : Term := .pi false alias box
private def declaration : FamilyDeclaration := ⟨true, 0, 0, [rawConstructor, .pi false box box], 1⟩
private def scalar : Field := ⟨false, .u64, none⟩
private def signature : Signature := ⟨[scalar], []⟩
private def entry : CheckedFamily :=
  ⟨declaration, [signature, ⟨[⟨false, box, some []⟩], []⟩], true⟩
private def env : Environment := ⟨#[definition], #[entry]⟩
private def owner : Term := .node (.con 0 0 1) [.natural 7]
private def branches : List Term := [.lam false .u64 (.var 0), .lam false (.ref box) (.natural 0)]
private def source : Term := FamilyIota.viewTerm false 0 .u64 branches (.borrow owner)
private def arena : Arena := #[.node (.universe 0) [], .node .u64 [], .node (.lam false) [1, 1],
  .node (.natural 1) [], .node .app [2, 3], .node (.global 0) [], .node (.ind 0 0) [],
  .node (.pi false) [5, 6], .node (.natural 7) [], .node (.con 0 0 1) [8], .node .borrow [9],
  .var 0, .node (.lam false) [1, 11], .node .ref [6], .node (.natural 0) [], .node (.lam false) [13, 14]]
private def start : State := ⟨arena, 2⟩
private def roots : List Roots := [⟨0, 4⟩]
private def visit := runThroughAliases roots 1 64 16

/-- A constructor actually admitted by the mixed checker has a written
global domain. The live graph follows the alias, contracts its beta redex,
and obtains its checked U64 field without a supplied canonical-domain match. -/
theorem checked_alias_beta_view :
    let shape := NativeCoreViewShape.run env 0 visit start 0 7
    let output := NativeCoreViewShape.runWithShape env visit start false 0 1 0 7 [12, 15] 10
    entry.declaration.constructors[0]? = some rawConstructor ∧ Represents arena 7 rawConstructor ∧
      shape = ⟨⟨arena, 10⟩, .ok [(false, false)]⟩ ∧
      output = ⟨⟨arena.push (.node .app [12, 8]), 18⟩, .ok (some 8)⟩ ∧
      NativeCoreCaseNormal.Refines env arena output.state.arena 8 [] source .u64 := by
  have history : LoanTyping.MixedProgram.History [definition] [declaration] env :=
    LoanTyping.MixedProgram.checkProgram_sound
      (by cbv : LoanTyping.MixedProgram.checkProgram 48 96 [definition] [declaration] = some env)
  have constructorRep : Represents arena 7 rawConstructor := decode_sound (fuel := 8) (by cbv)
  have aliasRep : Represents arena 5 alias := decode_sound (fuel := 8) (by cbv)
  have aligned : RepresentsDefinitions arena roots [definition] :=
    .cons (NativeProgramWire.decodeRoot_sound (by cbv)) .nil
  have fieldReduced : visit start 5 = ⟨⟨arena, 10⟩, .ok 1⟩ := by cbv
  have scalarRep : Represents (visit start 5).state.arena 1 .u64 := by
    rw [fieldReduced]
    exact decode_sound (fuel := 8) (by cbv)
  have scalarRigid : RigidTree .u64 := .node rfl (by simp)
  have more : RigidVisits env visit (visit start 5).state 6 ⟨arena, 10⟩ := by
    rw [fieldReduced]
    exact .done rfl
  have visited : RigidVisits env visit start 7 ⟨arena, 10⟩ :=
    RigidVisits.alias_step history aligned rfl (by decide) aliasRep (congrArg Outcome.result fieldReduced)
      scalarRep scalarRigid more
  have found : env.families[0]? = some entry := rfl
  have sig : entry.signatures[0]? = some signature := rfl
  have planned : viewPlan env 0 signature.fields = some [⟨scalar, false, false⟩] := rfl
  have rigidFields : ∀ field ∈ signature.fields.drop entry.declaration.params, RigidTree field.domain := by
    intro field member
    have eq : field = scalar := List.mem_singleton.mp member
    cases eq
    exact scalarRigid
  have alignedShape := run_from_history (typeRoot := 7) history found sig rfl constructorRep visited rigidFields planned
  have exactShape : NativeCoreViewShape.run env 0 visit start 0 7 = ⟨⟨arena, 10⟩, .ok [(false, false)]⟩ :=
    alignedShape.1
  have result :
      NativeCoreViewShape.runWithShape env visit start false 0 1 0 7 [12, 15] 10 =
        ⟨⟨arena.push (.node .app [12, 8]), 18⟩, .ok (some 8)⟩ := by
    simp only [NativeCoreViewShape.runWithShape, exactShape]
    cbv
  have appResult :
      NativeCoreViewNormal.run env 64 16 ⟨arena, 10⟩ false 0 1 [12, 15] 10 [(false, false)] =
        ⟨⟨arena.push (.node .app [12, 8]), 18⟩, .ok (some 8)⟩ := by cbv
  have accepted : LoanTyping.Checker.check 48 env [] [] true source .u64 = true := by cbv
  have motiveRep : Represents arena 1 .u64 := decode_sound (fuel := 8) (by cbv)
  have casesRep : RepresentsList arena [12, 15] branches :=
    .cons (decode_sound (fuel := 8) (by cbv)) (.cons (decode_sound (fuel := 8) (by cbv)) .nil)
  have ownerRep : Represents arena 10 (.borrow owner) := decode_sound (fuel := 8) (by cbv)
  have flagsAgree : ShapeAgrees env 0 0 [(false, false)] := alignedShape.2
  have preserved := NativeCoreViewNormal.run_preserves (constructor := 0) (values := [.natural 7])
    history motiveRep casesRep ownerRep (LoanTyping.Checker.check_sound accepted) flagsAgree
    (congrArg Outcome.result appResult)
  rw [appResult] at preserved
  refine ⟨rfl, constructorRep, exactShape, result, ?_⟩
  rw [result]
  exact preserved

end Examples
end Jihoo.NativeKernel.NativeCoreViewShapeAlignment
