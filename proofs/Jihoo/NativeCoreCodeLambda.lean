import Jihoo.NativeCoreCodeApplication
import Jihoo.NativeCoreCodeLinearity
import Jihoo.NativeCoreCodeUses
import Jihoo.NativeCoreExpandedFamilies

/-! Runtime lambda checking visits the ghost annotation and the code
body under the new graph binding. It classifies and checks a relevant
binder's owner demand only after its body has been inferred. -/
namespace Jihoo.NativeKernel.NativeCoreCodeLambda

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (GraphBinding Infer InferSound Visit Inferred RetainedComparisons next_progress)
open NativeCoreGhostBinderCheck (inferBinder inferBinder_progress inferBinder_refines)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

def checkDemand (normal : Visit) (boxed : Nat → Bool) (limit depth : Nat)
    (state : State) (root domain body : Nat) (erased : Bool) : Outcome Unit :=
  if erased then ⟨state,.ok ()⟩
  else
    (NativeCoreCodeLinearity.run normal boxed state domain).next fun exposed linear =>
      if linear then
        (NativeCoreCodeUses.function limit depth exposed body 0).next fun after count =>
          if count = 1 then ⟨after,.ok ()⟩ else ⟨after,.error (.outsideFragment root)⟩
      else ⟨exposed,.ok ()⟩

theorem checkDemand_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (checkDemand normal boxed limit depth state root domain body erased) := by
  unfold checkDemand
  split
  · exact Progress.atState _ _
  · apply (NativeCoreCodeLinearity.run_progress normalizes).next
    intro linear
    split
    · exact NativeCoreCodeUses.function_progress.next fun _ => by split <;> exact Progress.atState _ _
    · exact Progress.atState _ _

private theorem checkDemand_backward
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (metadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (onBase : Prefix base state.arena) (back : Backward state.arena)
    (domainRep : Represents state.arena domain D) (bodyRep : Represents state.arena body b)
    (success : (checkDemand normal boxed limit depth state root domain body erased).result = .ok ()) :
    Backward (checkDemand normal boxed limit depth state root domain body erased).state.arena := by
  unfold checkDemand at success ⊢
  split at success
  · rename_i erasedBinder
    simp only [ite_eq_left erasedBinder]
    exact back
  · rename_i relevant
    simp only [ite_eq_right relevant]
    obtain ⟨linear,exposed,entered⟩ := Outcome.next_success success
    rw [entered] at success ⊢
    obtain ⟨kept,backward,_⟩ := NativeCoreCodeLinearity.run_refines metadata normalSound onBase domainRep exposed
    split at success
    · rename_i linearDomain
      simp only [ite_eq_left linearDomain]
      obtain ⟨count,counted,countedNext⟩ := Outcome.next_success success
      rw [countedNext] at success ⊢
      split at success
      · rename_i once
        simp only [ite_eq_left once]
        obtain ⟨same,_⟩ := NativeCoreCodeUses.function_refines (backward back) (bodyRep.frame kept) counted
        exact same.symm ▸ backward back
      · cases success
    · rename_i ordinary
      simp only [ite_eq_right ordinary]
      exact backward back

theorem linear_body_demand
    (notErased : erased = false) (back : Backward exposed.arena)
    (represented : Represents exposed.arena body term)
    (exposedState : exposed = (NativeCoreCodeLinearity.run normal boxed state domain).state)
    (owned : (NativeCoreCodeLinearity.run normal boxed state domain).result = .ok true)
    (success : (checkDemand normal boxed limit depth state root domain body erased).result = .ok ()) :
    ∃ binders inner control, NativeCoreCodeUses.BodyOf term binders inner ∧
      NativeCoreCodeUses.Projects inner control ∧ control.demand binders = some 1 := by
  subst erased exposed
  simp only [checkDemand,Bool.false_eq_true,ite_false,Outcome.next,owned,ite_true] at success
  cases counted : (NativeCoreCodeUses.function limit depth
      (NativeCoreCodeLinearity.run normal boxed state domain).state body 0).result with
  | error reason => simp only [counted,reduceCtorEq] at success
  | ok count =>
    simp only [counted] at success
    split at success
    · rename_i once
      subst count
      obtain ⟨_,binders,inner,control,opened,projected,demand⟩ :=
        NativeCoreCodeUses.function_refines back represented counted
      exact ⟨_,_,_,opened,projected,by simpa only [Nat.zero_add] using demand⟩
    · cases success

def run (visitBinder : Infer) (visitBody : GraphBinding → Infer) (normal : Visit) (isData boxed : Nat → Bool)
    (limit depth : Nat) (state : State) (root domain body : Nat) (erased : Bool) : Outcome Inferred :=
  (inferBinder visitBinder normal isData state domain erased).next fun formed binder =>
    (visitBody ⟨domain,erased⟩ formed body).next fun inferred result =>
      (checkDemand normal boxed limit depth inferred root domain body erased).next fun used _ =>
        (append used (.pi erased) [domain,result.typeRoot]).next fun after selected =>
          ⟨after,.ok ⟨selected,binder.compared ++ result.compared⟩⟩

theorem run_progress
    (binderProgress : ∀ state root, state.steps ≤ limit → Progress limit state (visitBinder state root))
    (bodyProgress : ∀ state ref, state.steps ≤ limit → Progress limit state (visitBody ⟨domain,erased⟩ state ref))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run visitBinder visitBody normal isData boxed limit depth state root domain body erased) := by
  unfold run
  apply next_progress (inferBinder_progress binderProgress normalProgress room) room
  intro _ _ binderRoom
  apply next_progress (bodyProgress _ _ binderRoom) binderRoom
  intro _ _ _
  exact (checkDemand_progress normalProgress).next fun _ =>
    (append_progress _ _ _).next fun _ => Progress.atState _ _

/-- The result retains the written annotation and the inferred body
type in their original scopes. The body is checked with the same loan stack. -/
theorem run_refines (metadata : NativeCoreGhostSort.DataFamilies env isData)
    (boxedMetadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (binderSound : InferSound env base ctx limit visitBinder)
    (bodySound : NativeCoreCodeApplication.Sound env loans base (⟨expand env D,erased⟩ :: ctx)
      limit false (visitBody ⟨domain,erased⟩))
    (binderProgress : ∀ state root, state.steps ≤ limit → Progress limit state (visitBinder state root))
    (bodyProgress : ∀ state ref, state.steps ≤ limit → Progress limit state (visitBody ⟨domain,erased⟩ state ref))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit) (back : Backward state.arena)
    (domainRep : Represents state.arena domain D) (bodyRep : Represents state.arena body b)
    (success : (run visitBinder visitBody normal isData boxed limit depth state root domain body erased).result = .ok answer)
    (ambient : Prefix (run visitBinder visitBody normal isData boxed limit depth state root domain body erased).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (run visitBinder visitBody normal isData boxed limit depth state root domain body erased).state.arena
    Prefix state.arena after ∧ Backward after ∧
      ∃ type, Represents after answer.typeRoot (.pi erased D type) ∧
        LoanTyping.HasType env loans ctx false (.lam erased (expand env D) (expand env b))
          (.pi erased (expand env D) (expand env type)) := by
  unfold run at success ambient ⊢
  obtain ⟨binder,binderOk,binderNext⟩ := Outcome.next_success success
  rw [binderNext] at success ambient ⊢
  obtain ⟨result,bodyOk,bodyNext⟩ := Outcome.next_success success
  rw [bodyNext] at success ambient ⊢
  obtain ⟨⟨⟩,used,useNext⟩ := Outcome.next_success success
  rw [useNext] at success ambient ⊢
  obtain ⟨output,added,outputNext⟩ := Outcome.next_success success
  rw [outputNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let formed := inferBinder visitBinder normal isData state domain erased
  let inferred := visitBody ⟨domain,erased⟩ formed.state body
  let checked := checkDemand normal boxed limit depth inferred.state root domain body erased
  have binderCost := inferBinder_progress (state := state) (domain := domain) (erased := erased)
    (isData := isData) binderProgress normalProgress room
  have binderRoom := binderCost.accepted room binder binderOk
  have bodyCost := bodyProgress formed.state body binderRoom
  have useCost := checkDemand_progress (state := inferred.state) (root := root)
    (domain := domain) (body := body) (boxed := boxed) (erased := erased) (depth := depth) normalProgress
  have appendCost := append_progress (limit := limit) checked.state (.pi erased) [domain,result.typeRoot]
  have retainedAfterBody := useCost.kept.trans (appendCost.kept.trans ambient)
  obtain ⟨domainKept,domainBack,binderType⟩ := inferBinder_refines metadata normalSound normalProgress
    binderSound binderProgress onBase room domainRep binderOk (bodyCost.kept.trans retainedAfterBody)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨bodyKept,bodyBack,type,resultRep,typed⟩ :=
    bodySound (onBase.trans domainKept) binderRoom (bodyRep.frame domainKept) bodyOk retainedAfterBody
      (fun pair member => retained pair (List.mem_append_right _ member))
  have beforeDemand := domainKept.trans bodyKept
  have afterDemand := beforeDemand.trans useCost.kept
  have demandBack := checkDemand_backward normalSound boxedMetadata (onBase.trans beforeDemand)
    (bodyBack (domainBack back)) (domainRep.frame beforeDemand) (bodyRep.frame beforeDemand) used
  obtain ⟨appendKept,appendBack,represented⟩ := append_refines
    (.cons (domainRep.frame afterDemand) (.cons (resultRep.frame useCost.kept) .nil)) rfl added
  have actualBinder : LoanTyping.Binder env loans ctx erased (expand env D) binder.sort := by
    cases binderType with | intro existsSort allowed => exact .intro (existsSort.ghost loans) allowed
  exact ⟨afterDemand.trans appendKept,appendBack demandBack,_,represented,.lam actualBinder typed⟩

private def fixture : Arena :=
  #[.node (.natural 2) [],.node .u64 [],.node .buffer [0],.node (.lam false) [2,1],
    .node (.back false) [2,3],.node (.integer 0) [],.var 0,.node .free [6,5],.node .strict [7,7],
    .node (.lam false) [1,5],.node (.lam false) [2,5],.node (.lam false) [4,5],.node (.lam false) [2,7],
    .node (.lam false) [2,8],.node (.lam false) [4,6]]

private def runFixture (limit root domain body : Nat) : Outcome Inferred :=
  let depth := 31
  let normal := NativeCoreExpandedFamilies.raw empty [] [] 0 limit
  let ghost := NativeCoreGhostSpineInference.runWith normal [] 0 limit depth []
  let code := fun binding => NativeCoreCodeHeadInference.run limit depth [binding]
  run ghost code (normal depth) (fun _ => false) (fun _ => false) limit depth ⟨fixture,1⟩ root domain body false

/-- The original annotation survives the successful code lambda. Zero
uses of an owned annotation reject without appending its product. -/
theorem checked_scalar_and_owner_lambdas_match_native :
    (let word := runFixture 6 9 1 5
     word.state.steps = 6 ∧ word.state.arena.size = 18 ∧ word.result.map Inferred.typeRoot = .ok 17 ∧
       word.state.arena[17]? = some (.node (.pi false) [1,16])) ∧
    (let buffer := runFixture 13 10 2 5
     buffer.state.steps = 13 ∧ buffer.state.arena.size = 19 ∧ buffer.result = .error (.outsideFragment 10)) ∧
    (let unused := runFixture 43 11 4 5
     unused.state.steps = 43 ∧ unused.state.arena.size = 25 ∧ unused.result = .error (.outsideFragment 11)) ∧
    (let returned := runFixture 50 14 4 6
     returned.state.steps = 50 ∧ returned.state.arena.size = 25 ∧ returned.result.map Inferred.typeRoot = .ok 24 ∧
       returned.state.arena[24]? = some (.node (.pi false) [4,4])) := by
  exact ⟨by cbv,by cbv,by cbv,by cbv⟩

end Jihoo.NativeKernel.NativeCoreCodeLambda
