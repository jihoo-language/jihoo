import Jihoo.NativeCoreCodeArgumentPolicy
import Jihoo.NativeCoreCodeHeadInference

/-! A runtime application passes the head flag to its callee, selects
the argument mode from the product erasure, and checks the argument
representation before substituting it into the codomain. -/
namespace Jihoo.NativeKernel.NativeCoreCodeApplication

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred next_progress requireTypes requireTypes_progress
  requireTypes_refines RetainedComparisons)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def instantiated (limit depth : Nat) (state : State) (type argument : Nat) : Outcome Nat :=
  let changed := NativeCoreTransformExact.substitute limit depth state type argument
  ⟨changed.state,changed.result.mapError .substitution⟩

private def finishSaturated (normal : Visit) (state : State) (candidate root : Nat) (head : Bool) : Outcome Nat :=
  if head then ⟨state,.ok candidate⟩
  else
    (normal state candidate).next fun after normalized =>
      match after.arena[normalized]? with
      | some (.node (.pi _) _) => reject after root
      | _ => ⟨after,.ok candidate⟩

/-- This entry covers nested spine segments and runtime applications whose
top-level result has a nonfunction representation. Unsaturated function
values enter the separate native owned-argument query. -/
def run (functionInfer : Infer) (argumentInfer : Bool → Infer) (normal : Nat → Visit)
    (env : Environment) (limit depth : Nat) (state : State) (root function argument : Nat) (head : Bool) : Outcome Inferred :=
  (functionInfer state function).next fun called functionType =>
    (normal depth called functionType.typeRoot).next fun exposed product =>
      match exposed.arena[product]? with
      | some (.node (.pi erased) [domain,result]) =>
        (argumentInfer erased exposed argument).next fun inferred argumentType =>
          (requireTypes (normal depth) limit depth inferred argumentType.typeRoot domain argument).next fun checked compared =>
            (NativeCoreCodeArgumentPolicy.run normal env limit depth checked domain argument).next fun accepted _ =>
              (instantiated limit depth accepted result argument).next fun substituted candidate =>
                (finishSaturated (normal depth) substituted candidate root head).next fun after selected =>
                  ⟨after,.ok ⟨selected,functionType.compared ++ argumentType.compared ++ [compared]⟩⟩
      | _ => reject exposed function

private theorem instantiated_success (accepted : (instantiated limit depth state type argument).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state type argument).result = .ok selected := by
  unfold instantiated at accepted
  cases computed : (NativeCoreTransformExact.substitute limit depth state type argument).result <;>
    simp only [computed,Except.mapError,reduceCtorEq,Except.ok.injEq] at accepted ⊢
  exact accepted

private theorem instantiated_progress : Progress limit state (instantiated limit depth state type argument) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state type (.replace .substitute argument) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ result =>
    progress.accepted room _ (instantiated_success result)⟩

private theorem finishSaturated_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (finishSaturated normal state candidate root head) := by
  unfold finishSaturated
  split
  · exact Progress.atState _ _
  · exact (normalProgress _ _).next (fun _ => by split <;> exact Progress.atState _ _)

theorem run_progress
    (functionProgress : ∀ state root, state.steps ≤ limit → Progress limit state (functionInfer state root))
    (argumentProgress : ∀ mode state root, state.steps ≤ limit → Progress limit state (argumentInfer mode state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run functionInfer argumentInfer normal env limit depth state root function argument head) := by
  unfold run
  apply next_progress (functionProgress _ _ room) room
  intro _ _ functionRoom
  apply next_progress (normalProgress depth _ _) functionRoom
  intro _ _ exposedRoom
  split
  · apply next_progress (argumentProgress _ _ _ exposedRoom) exposedRoom
    intro _ _ argumentRoom
    apply next_progress (requireTypes_progress (fun state root _ => normalProgress depth state root) argumentRoom) argumentRoom
    intro _ _ comparedRoom
    apply next_progress (NativeCoreCodeArgumentPolicy.run_progress normalProgress) comparedRoom
    intro _ _ _
    exact instantiated_progress.next (fun _ =>
      (finishSaturated_progress (normalProgress depth)).next (fun _ => Progress.atState _ _))
  · exact Progress.atState _ _

/-- The callee and argument visitors may use different native entry
policies. They retain their mode and loan stack in the source judgment. -/
def Sound (env : Environment) (loans : Loans.Stack) (base : Arena) (ctx : Context) (limit : Nat)
    (mode : Bool) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final → RetainedComparisons final answer →
      let after := (visit state root).state.arena
      Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
        ∃ type, Represents after answer.typeRoot type ∧ LoanTyping.HasType env loans ctx mode (expand env term) (expand env type)

private theorem product_rep
    (represented : Represents arena root term) (read : arena[root]? = some (.node (.pi erased) [domain,result])) :
    ∃ D R, Represents arena domain D ∧ Represents arena result R ∧ term = .pi erased D R := by
  cases represented with
  | var found => rw [read] at found; cases found
  | node found _ children =>
    rw [read] at found
    cases found
    cases children with
    | cons first rest =>
      cases rest with
      | cons next tail =>
        cases tail
        exact ⟨_,_,first,next,rfl⟩

private theorem finishSaturated_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (source : Represents state.arena candidate written)
    (success : (finishSaturated normal state candidate root head).result = .ok selected) :
    let after := (finishSaturated normal state candidate root head).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected written := by
  cases head with
  | true =>
    cases success
    exact ⟨.refl _,id,source⟩
  | false =>
    unfold finishSaturated at success ⊢
    simp only [Bool.false_eq_true,ite_false] at success ⊢
    obtain ⟨normalized,normalizes,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨kept,backward,_,_,_⟩ := normalSound onBase source normalizes
    split at success
    · cases success
    · cases success
      exact ⟨kept,backward,source.frame kept⟩

private theorem expand_instantiation (wf : UnifiedProgram.EnvWellFormed env) (type value : Term) :
    expand env (type.subst (single value)) = (expand env type).subst (single (expand env value)) := by
  rw [EnvironmentDelta.expand_substitution wf.admissible]
  congr 1
  funext index
  cases index <;> simp only [single,expand]

/-- The checked code callee and mode-selected argument produce source
application typing at the original dependent codomain instantiation. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (free : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs normal)
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (functionSound : Sound env loans base ctx limit false functionInfer)
    (argumentSound : ∀ mode, Sound env loans base ctx limit mode (argumentInfer mode))
    (functionProgress : ∀ state root, state.steps ≤ limit → Progress limit state (functionInfer state root))
    (argumentProgress : ∀ mode state root, state.steps ≤ limit → Progress limit state (argumentInfer mode state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fn : Represents state.arena function f) (arg : Represents state.arena argument a)
    (success : (run functionInfer argumentInfer normal env limit depth state root function argument head).result = .ok answer)
    (ambient : Prefix (run functionInfer argumentInfer normal env limit depth state root function argument head).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (run functionInfer argumentInfer normal env limit depth state root function argument head).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧ LoanTyping.HasType env loans ctx false
        (.app (expand env f) (expand env a)) (expand env type) := by
  unfold run at success ambient ⊢
  obtain ⟨functionResult,functionOk,functionNext⟩ := Outcome.next_success success
  rw [functionNext] at success ambient ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ambient ⊢
  split at success
  · rename_i erased domain result read
    simp only [read] at ambient ⊢
    obtain ⟨argumentResult,argumentOk,argumentNext⟩ := Outcome.next_success success
    rw [argumentNext] at success ambient ⊢
    obtain ⟨comparison,comparisonOk,comparisonNext⟩ := Outcome.next_success success
    rw [comparisonNext] at success ambient ⊢
    obtain ⟨⟨⟩,policyOk,policyNext⟩ := Outcome.next_success success
    rw [policyNext] at success ambient ⊢
    obtain ⟨substituted,substitutedOk,substitutedNext⟩ := Outcome.next_success success
    rw [substitutedNext] at success ambient ⊢
    obtain ⟨selected,selectedOk,selectedNext⟩ := Outcome.next_success success
    rw [selectedNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let functionRun := functionInfer state function
    let productRun := normal depth functionRun.state functionResult.typeRoot
    let argumentRun := argumentInfer erased productRun.state argument
    let comparisonRun := requireTypes (normal depth) limit depth argumentRun.state argumentResult.typeRoot domain argument
    let policyRun := NativeCoreCodeArgumentPolicy.run normal env limit depth comparisonRun.state domain argument
    let instantiatedRun := instantiated limit depth policyRun.state result argument
    have functionCost := functionProgress state function room
    have functionRoom := functionCost.accepted room functionResult functionOk
    have productCost := normalProgress depth functionRun.state functionResult.typeRoot
    have productRoom := productCost.accepted functionRoom product productOk
    have argumentCost := argumentProgress erased productRun.state argument productRoom
    have argumentRoom := argumentCost.accepted productRoom argumentResult argumentOk
    have compareCost := requireTypes_progress (state := argumentRun.state) (depth := depth)
      (actual := argumentResult.typeRoot) (expected := domain) (argument := argument)
      (fun state root _ => normalProgress depth state root) argumentRoom
    have policyCost := NativeCoreCodeArgumentPolicy.run_progress (env := env) (depth := depth) (state := comparisonRun.state)
      (domain := domain) (argument := argument) normalProgress
    have instantiationCost := instantiated_progress (limit := limit) (depth := depth) (state := policyRun.state)
      (type := result) (argument := argument)
    have finishCost := finishSaturated_progress (limit := limit) (state := instantiatedRun.state)
      (candidate := substituted) (root := root) (head := head) (normalProgress depth)
    have afterInstantiation := finishCost.kept.trans ambient
    have afterPolicy := instantiationCost.kept.trans afterInstantiation
    have afterComparison := policyCost.kept.trans afterPolicy
    have afterArgument := compareCost.kept.trans afterComparison
    have afterProduct := argumentCost.kept.trans afterArgument
    have afterFunction := productCost.kept.trans afterProduct
    obtain ⟨functionKept,functionBack,rawFunctionType,functionTypeRep,typedFunction⟩ := functionSound onBase room fn functionOk
      afterFunction (fun pair member => retained pair (List.mem_append_left _ (List.mem_append_left _ member)))
    obtain ⟨productKept,productBack,_,productRep,converted⟩ := normalSound depth
      (onBase.trans functionKept) functionTypeRep productOk
    obtain ⟨D,R,domainRep,resultRep,shape⟩ := product_rep productRep read
    have called := functionKept.trans productKept
    obtain ⟨argumentKept,argumentBack,_,argumentTypeRep,typedArgument⟩ := argumentSound erased (onBase.trans called)
      productRoom (arg.frame called) argumentOk afterArgument
      (fun pair member => retained pair (List.mem_append_left _ (List.mem_append_right _ member)))
    have throughArgument := called.trans argumentKept
    obtain ⟨comparedKept,comparedBack,equalDomain⟩ := requireTypes_refines (normalSound depth) (onBase.trans throughArgument)
      argumentTypeRep (domainRep.frame argumentKept) comparisonOk afterComparison (retained comparison (by simp))
    have sinceProduct := argumentKept.trans comparedKept
    have throughComparison := throughArgument.trans comparedKept
    have domainBeforePolicy := domainRep.frame sinceProduct
    have argumentBeforePolicy := arg.frame throughComparison
    have allowed := NativeCoreCodeArgumentPolicy.run_refines normalSound normalProgress free (onBase.trans throughComparison)
      domainBeforePolicy argumentBeforePolicy policyOk
    have policyBack (backward : Backward state.arena) := NativeCoreCodeArgumentPolicy.run_backward normalSound
      (onBase.trans throughComparison) (comparedBack (argumentBack (productBack (functionBack backward))))
      domainBeforePolicy argumentBeforePolicy policyOk
    have throughPolicy := throughComparison.trans policyCost.kept
    obtain ⟨instantiationKept,instantiationBack,instantiationRep⟩ := NativeCoreTransformExact.substitute_refines
      (resultRep.frame (sinceProduct.trans policyCost.kept)) (arg.frame throughPolicy) (instantiated_success substitutedOk)
    have throughInstantiation := throughPolicy.trans instantiationKept
    obtain ⟨finishKept,finishBack,finishedRep⟩ := finishSaturated_refines (normalSound depth)
      (onBase.trans throughInstantiation) instantiationRep selectedOk
    have selectedType : RawLend.Conv env (expand env rawFunctionType) (.pi erased (expand env D) (expand env R)) := by
      simpa only [shape,Term.pi,expand,expandArgs] using converted.converted
    have typed := LoanTyping.HasType.app (typedFunction.convert selectedType) (typedArgument.convert equalDomain) allowed
    refine ⟨throughInstantiation.trans finishKept,finishBack ∘ instantiationBack ∘ policyBack,_,finishedRep,?_⟩
    rw [expand_instantiation wf]
    exact typed
  · cases success

private def run_fixture (rows : List NativeCoreGhostSpineInference.GraphBinding) (input : Arena) :
    Outcome Inferred :=
  let limit := 16
  let depth := 31
  let normal := NativeCoreGhostLiteralAddition.run [] 0 limit
  let code := NativeCoreCodeHeadInference.run limit depth rows
  let argument := fun erased => if erased then NativeCoreGhostSpineInference.runWith normal [] 0 limit depth rows else code
  run code argument normal empty limit depth ⟨input,1⟩ 5 3 4 false

/-- Code applications inspect the result representation without replacing
the original result root. The function's erasure flag determines whether
a local erased argument is visited successfully. -/
theorem saturated_code_application_selects_argument_mode :
    let ordinary : Arena := #[.node .u64 [],.node .i64 [],.node (.pi false) [0,1],.var 0,
      .node (.natural 7) [],.node .app [3,4]]
    let erased : Arena := #[.node .u64 [],.node .i64 [],.node (.pi true) [0,1],.var 1,.var 0,.node .app [3,4]]
    let relevant := erased.set! 2 (.node (.pi false) [0,1])
    let call := run_fixture [⟨2,false⟩] ordinary
    let ghostArg := run_fixture [⟨0,true⟩,⟨2,false⟩] erased
    let wrong := run_fixture [⟨0,true⟩,⟨2,false⟩] relevant
    call.state.steps = 15 ∧ call.state.arena.size = 7 ∧ call.result.map Inferred.typeRoot = .ok 1 ∧
      ghostArg.state.steps = 16 ∧ ghostArg.state.arena = erased ∧ ghostArg.result.map Inferred.typeRoot = .ok 1 ∧
      wrong.state.steps = 9 ∧ wrong.state.arena = relevant ∧ wrong.result = .error (.outsideFragment 4) := by cbv

end Jihoo.NativeKernel.NativeCoreCodeApplication
