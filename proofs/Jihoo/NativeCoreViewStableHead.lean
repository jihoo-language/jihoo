import Jihoo.NativeCoreGhostLiteralAddition
import Jihoo.NativeCoreViewShape

/-! A represented stable View head is retained by the concrete ghost
normalizer, including when it is exposed by transparent definitions.
Dependent subterms can still compute during the visit. -/
namespace Jihoo.NativeKernel.NativeCoreViewStableHead

open Environment NativeArena NativeProgramWire
open NativeCorePureComputationNormal (Outcome Rules)
open NativeCoreTransformExact (State)
open EnvironmentDelta (expand expandArgs)

inductive Stable : Op → Prop where
  | function : Stable (.lam erased)
  | product : Stable (.pi erased)
  | natural : Stable .u64
  | integer : Stable .i64
  | array : Stable .array
  | buffer : Stable .buffer
  | refine : Stable .refine
  | family : Stable (.ind family arity)

/-- A transparent expansion may reveal a stable head even when the
original graph reference is a global. -/
def Keeps (env : Environment) (source output : Term) : Prop :=
  ∀ {op args}, Stable op → expand env source = .node op args → ∃ fields,expand env output = .node op fields

private theorem absent (ordinary : GlobalEnvironment.ordinary op = true) (unsupported : ¬ Stable op) :
    Keeps env (.node op args) output := by
  intro observed _ head expanded
  rw [EnvironmentDelta.expand_ordinary ordinary] at expanded
  have same := (Term.node.inj expanded).1
  subst observed
  exact False.elim (unsupported head)

private theorem rules (env : Environment) : Rules (Keeps env) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro term op args head expanded
    exact ⟨args,expanded⟩
  · intro first middle last initial after op args head expanded
    obtain ⟨fields,shape⟩ := initial head expanded
    exact after head shape
  · intro source output reduced
    cases reduced <;> apply absent rfl <;> intro impossible <;> cases impossible
  · intro op inputs outputs _ ordinary _
    intro actual args head expanded
    rw [EnvironmentDelta.expand_ordinary ordinary] at expanded
    have same := (Term.node.inj expanded).1
    subst actual
    exact ⟨expandArgs env outputs,EnvironmentDelta.expand_ordinary ordinary⟩

private theorem literal_keeps
    (history : LoanTyping.MixedProgram.History definitions declarations env) :
    NativeCoreGhostLiteralAddition.extension.SoundFrom base (Keeps env) := by
  let sound := NativeCoreGhostLiteralAddition.extension_sound (base := base) history
  refine ⟨sound.1,?_⟩
  intro visit limit depth root state op before after terms selected accepted onBase read children arity visitor success
  have actual : op = .uadd := by
    simpa only [NativeCoreGhostLiteralAddition.extension,beq_iff_eq] using accepted
  subst op
  let unused : State → Nat → Outcome Nat := fun state root => ⟨state,.error (.outsideFragment root)⟩
  let evidence := sound.2 (visit := unused) (limit := limit) (depth := depth) accepted onBase read children arity
    (fun _ _ impossible => by cases impossible) success
  obtain ⟨kept,safe,residual,output,_⟩ := evidence
  exact ⟨kept,safe,residual,output,absent rfl (by intro impossible; cases impossible)⟩

/-- Any successful normal visit retains a stable represented head. Both the
input definition history and the result row come from the actual visits. -/
theorem run_keeps_head
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root term) (stable : Stable op)
    (expanded : expand env term = .node op args)
    (success : (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).result = .ok selected) :
    ∃ children, Represents (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).state.arena
      selected (.node op children) := by
  have early : (NativeCoreNestedAliases.extension roots visible).SoundFrom base (Keeps env) := by
    apply NativeCoreNestedAliases.extension_soundFor history aligned
    intro source middle result same proof selected arguments known expandedSource
    exact proof known (same.symm.trans expandedSource)
  obtain ⟨_,_,residual,held,head⟩ := NativeCorePureComputationNormal.runWithExtensions_refinesFrom
    (rules env) (literal_keeps history) early onBase source success
  obtain ⟨children,result⟩ := head stable expanded
  have free := NativeCoreGhostLiteralAddition.run_resolves history aligned onBase source success held
  rw [EnvironmentDelta.expand_globalFree ((globalFree_correct _).mp free)] at result
  exact ⟨children,result ▸ held⟩


private theorem relevant_plan_head
    (planned : viewFieldPlan env family ⟨false,domain,recursive⟩ = some plan) :
    ∃ op args, domain = .node op args ∧ Stable op := by
  cases domain with
  | var index => simp [viewFieldPlan] at planned
  | node op args =>
    cases op <;> simp [viewFieldPlan] at planned
    case ind observed arity => exact ⟨_,_,rfl,.family⟩
    case u64 => exact ⟨_,_,rfl,.natural⟩
    case i64 => exact ⟨_,_,rfl,.integer⟩
    case refine => exact ⟨_,_,rfl,.refine⟩
    case buffer => exact ⟨_,_,rfl,.buffer⟩

private theorem classify_relevant
    (stable : Stable op)
    (planned : viewFieldPlan env family ⟨false,.node op written,recursive⟩ = some plan) :
    NativeCoreViewShape.classify env family false (.node op observed) = (plan.borrowed,plan.self) := by
  cases stable
  case family actual arity =>
    by_cases recursiveFamily : actual = family
    · simp only [viewFieldPlan,Bool.false_eq_true,ite_false,recursiveFamily,ite_true,Option.some.injEq] at planned
      subst plan
      simp [NativeCoreViewShape.classify,recursiveFamily]
    · cases visible : env.families[actual]? with
      | none => simp [viewFieldPlan,recursiveFamily,visible] at planned
      | some entry =>
        simp only [viewFieldPlan,Bool.false_eq_true,ite_false,recursiveFamily,visible,Option.map_some,Option.some.injEq] at planned
        subst plan
        simp [NativeCoreViewShape.classify,recursiveFamily,visible]
  all_goals
    rcases written with _ | ⟨_,_ | ⟨_,_⟩⟩
    all_goals simp [viewFieldPlan] at planned
    all_goals subst plan; rfl

/-- The live domain normalization agrees with the checked field's plan
when transparency has exposed the corresponding outer constructor. Its
children may change during substitution and normalization. -/
theorem normal_matches_view_plan
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (aligned : RepresentsDefinitions base roots definitions) (onBase : Prefix base state.arena)
    (source : Represents state.arena root term)
    (planned : viewFieldPlan env family field = some plan)
    (head : field.erased = false → ∀ {op fields}, field.domain = .node op fields →
      ∃ opened, expand env term = .node op opened)
    (success : (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).result = .ok selected) :
    let after := (NativeCoreGhostLiteralAddition.run roots visible limit depth state root).state.arena
    ∃ row, after[selected]? = some row ∧
      NativeCoreViewShape.classify env family field.erased row = (plan.borrowed,plan.self) := by
  cases field with
  | mk erased domain recursive =>
    cases erased
    · obtain ⟨op,written,rfl,stable⟩ := relevant_plan_head planned
      obtain ⟨_,expanded⟩ := head rfl rfl
      obtain ⟨_,out⟩ := run_keeps_head history aligned onBase source stable expanded success
      cases out with
      | node found _ _ => exact ⟨_,found,classify_relevant stable planned⟩
    · change some (⟨⟨true,domain,recursive⟩,false,false⟩ : ViewFieldPlan) = some plan at planned
      have same := Option.some.inj planned
      subst plan
      obtain ⟨_,_,_,out,_⟩ := NativeCoreGhostLiteralAddition.run_refines history aligned onBase source success
      cases out with
      | var found | node found => exact ⟨_,found,rfl⟩

private theorem Stable.rigid (known : Stable op) : RawLend.rigid op = true := by
  cases known <;> rfl

private theorem rigid_ordinary (known : RawLend.rigid op = true) : GlobalEnvironment.ordinary op = true := by
  cases op <;> first | rfl | cases known

/-- Reading a dependent field under earlier borrows can change all its
arguments. A rigid normalized head still has the same ownership flags as
the checked field, by conversion of the opened domains. -/
theorem converted_head_matches_view_plan
    (admissible : EnvironmentDelta.Admissible env)
    (represented : Represents arena selected shape) (read : arena[selected]? = some row)
    (planned : viewFieldPlan env family field = some plan)
    (related : RawLend.Conv env (expand env shape) (viewRead previous (field.domain.subst values)))
    (rigid : field.erased = false → ∃ op args, shape = .node op args ∧ RawLend.rigid op = true) :
    NativeCoreViewShape.classify env family field.erased row = (plan.borrowed,plan.self) := by
  cases field with
  | mk erased domain recursive =>
    cases erased
    · obtain ⟨expected,written,rfl,stable⟩ := relevant_plan_head planned
      obtain ⟨observed,args,rfl,head⟩ := rigid rfl
      have opening : ∃ terms, viewRead previous ((Term.node expected written).subst values) =
          .node expected terms := by
        simp only [viewRead,Term.subst]
        exact ⟨_,rfl⟩
      obtain ⟨terms,opened⟩ := opening
      rw [EnvironmentDelta.expand_ordinary (rigid_ordinary head),opened] at related
      have agrees := (related.full_rigid_node_injective head stable.rigid admissible).1
      subst observed
      cases represented with
      | node found arity children =>
        rw [read] at found
        cases found
        exact classify_relevant stable planned
    · change some (⟨⟨true,domain,recursive⟩,false,false⟩ : ViewFieldPlan) = some plan at planned
      cases planned
      rfl

end Jihoo.NativeKernel.NativeCoreViewStableHead
