import Jihoo.NativeCoreBufferRelease
import Jihoo.NativeCoreGhostTypeRequirement

/-! A native ghost constructor field walk starts with the live shifted
signature. Each field is checked in the caller's context and the original
argument root is substituted into the next dependent domain. -/
namespace Jihoo.NativeKernel.NativeCoreGhostConstructorFields

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Visit Infer Inferred InferSound requireTypes requireTypes_progress requireTypes_refines RetainedComparisons next_progress)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def instantiate (limit depth : Nat) (state : State) (result argument : Nat) : Outcome Nat :=
  let step := NativeCoreTransformExact.substitute limit depth state result argument
  ⟨step.state,step.result.mapError .substitution⟩

private theorem instantiate_success
    (success : (instantiate limit depth state result argument).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state result argument).result = .ok selected := by
  unfold instantiate at success
  cases observed : (NativeCoreTransformExact.substitute limit depth state result argument).result <;>
    simp only [observed,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

private theorem instantiate_progress (limit depth : Nat) (state : State) (result argument : Nat) :
    Progress limit state (instantiate limit depth state result argument) := by
  have progress := NativeCoreTransformExact.substitute_progress limit depth state result argument
  exact ⟨progress.kept,progress.monotone,progress.bounded,
    fun room value success => progress.accepted room value (instantiate_success success)⟩

/-- The last normalized type must be inductive. In a successful field
step, require compares the two live normalized domains before substitution. -/
def runByErasure (inferField : Bool → Infer) (normal : Visit) (limit depth root : Nat) : List Nat → State → Nat → Outcome Inferred
  | [], state, telescope =>
    (normal state telescope).next fun after result =>
      match after.arena[result]? with
      | some (.node (.ind _ _) _) => ⟨after,.ok ⟨result,[]⟩⟩
      | _ => reject after root
  | argument :: rest, state, telescope =>
    (normal state telescope).next fun exposed piType =>
      match exposed.arena[piType]? with
      | some (.node (.pi erased) [domain,result]) =>
        (inferField erased exposed argument).next fun afterArg inferred =>
          (requireTypes normal limit depth afterArg inferred.typeRoot domain argument).next fun checked comparison =>
            (instantiate limit depth checked result argument).next fun instantiated tail =>
              (runByErasure inferField normal limit depth root rest instantiated tail).next fun after output =>
                ⟨after,.ok ⟨output.typeRoot,inferred.compared ++ (comparison :: output.compared)⟩⟩
      | _ => reject exposed argument

abbrev run (infer : Infer) :=
  runByErasure (fun _ => infer)

theorem runByErasure_progress
    (infers : ∀ erased state root, state.steps ≤ limit → Progress limit state (inferField erased state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runByErasure inferField normal limit depth root fields state telescope) := by
  induction fields generalizing state telescope with
  | nil =>
    apply (normalizes _ _).next
    intro selected
    split <;> exact Progress.atState _ _
  | cons arg rest ih =>
    unfold runByErasure
    apply next_progress (normalizes _ _) room
    intro selected _ exposedRoom
    split
    · rename_i erased domain result read
      apply next_progress (infers erased _ _ exposedRoom) exposedRoom
      intro inferred _ inferredRoom
      apply next_progress (requireTypes_progress (fun state root _ => normalizes state root) inferredRoom) inferredRoom
      intro comparison _ comparedRoom
      apply next_progress (instantiate_progress _ _ _ _ _) comparedRoom
      intro tail _ tailRoom
      exact (ih tailRoom).next (fun _ => Progress.atState _ _)
    · exact Progress.atState _ _

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal limit depth root fields state telescope) :=
  runByErasure_progress (fun _ => infers) normalizes room

private theorem graph_node (held : Represents arena root term) (read : arena[root]? = some (.node op refs)) :
    ∃ args, term = .node op args ∧ RepresentsList arena refs args := by
  cases held with
  | var found => rw [read] at found; cases found
  | node found _ args => rw [read] at found; cases found; exact ⟨_,rfl,args⟩

private theorem graph_pi (held : Represents arena root term) (read : arena[root]? = some (.node (.pi erased) [a,b])) :
    ∃ domain body, term = .pi erased domain body ∧ Represents arena a domain ∧ Represents arena b body := by
  obtain ⟨terms,shape,children⟩ := graph_node held read
  cases children with
  | cons first tail =>
    cases tail with
    | cons second empty =>
      cases empty
      exact ⟨_,_,shape,first,second⟩

structure ModeRefines (env : Environment) (loans : Loans.Stack) (start : Arena)
    (ctx : Context) (mode data : Bool) (source : Term)
    (inputs : List Term) (output : Outcome Inferred) (answer : Inferred) : Prop where
  kept : Prefix start output.state.arena
  backward : Backward start → Backward output.state.arena
  result : ∃ family count indices,
    Represents output.state.arena answer.typeRoot (.node (.ind family count) indices) ∧
    LoanTyping.Arguments env loans ctx mode data (expand env source) (expandArgs env inputs)
      (.node (.ind family count) (expandArgs env indices))

abbrev Refines (env : Environment) (start : Arena) (ctx : Context) (data : Bool) :=
  ModeRefines env [] start ctx true data

/-- The checked graph walk produces the full Loan64 Arguments derivation
at the original source telescope, including all dependent substitutions. -/
theorem runByErasure_refines_formed
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : ∀ erased, NativeCoreBufferRelease.ModeSound env loans base ctx limit
      (mode || !(data && !erased)) (inferField erased))
    (inferProgress : ∀ erased state root, state.steps ≤ limit → Progress limit state (inferField erased state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena telescope type) (fieldsRep : RepresentsList state.arena fields args)
    (success : (runByErasure inferField normal limit depth root fields state telescope).result = .ok answer)
    (ambient : Prefix (runByErasure inferField normal limit depth root fields state telescope).state.arena final)
    (retained : RetainedComparisons final answer) :
    ModeRefines env loans state.arena ctx mode data type args (runByErasure inferField normal limit depth root fields state telescope) answer ∧
    (∀ {sort : SortTag} {output : Term},
      Represents (runByErasure inferField normal limit depth root fields state telescope).state.arena answer.typeRoot output →
      LoanTyping.HasType env [] ctx true (expand env type) sort.term →
      ∃ resultSort : SortTag, LoanTyping.HasType env [] ctx true (expand env output) resultSort.term) := by
  induction fields generalizing state telescope type args answer with
  | nil =>
    cases fieldsRep
    unfold runByErasure at success ambient ⊢
    obtain ⟨selected,normalized,next⟩ := Outcome.next_success success
    rw [next] at success ambient ⊢
    obtain ⟨kept,backward,residual,held,changed⟩ := normalSound onBase written normalized
    split at success
    · rename_i family count refs read
      simp only [Except.ok.injEq] at success
      subst answer
      obtain ⟨indices,shape,children⟩ := graph_node held read
      subst residual
      refine ⟨⟨kept,backward,family,count,indices,held,?_⟩,?_⟩
      · simp only [expandArgs]
        exact .nil (by simpa only [expand] using changed.converted)
      · intro sort output represented formed
        have agrees := held.unique represented
        cases agrees
        exact ⟨sort,changed.preserves formed⟩
    · simp [reject] at success
  | cons arg rest ih =>
    cases fieldsRep with
    | @cons _ source _ more argRep restRep =>
      unfold runByErasure at success ambient ⊢
      obtain ⟨piRoot,exposedOk,exposedNext⟩ := Outcome.next_success success
      rw [exposedNext] at success ambient ⊢
      split at success
      · rename_i erased domain result read
        simp only [read] at ambient
        obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
        rw [inferredNext] at success ambient ⊢
        obtain ⟨pair,compareOk,compareNext⟩ := Outcome.next_success success
        rw [compareNext] at success ambient ⊢
        obtain ⟨remaining,substituteOk,substituteNext⟩ := Outcome.next_success success
        rw [substituteNext] at success ambient ⊢
        obtain ⟨output,tailOk,tailNext⟩ := Outcome.next_success success
        rw [tailNext] at success ambient ⊢
        simp only [Except.ok.injEq] at success
        subst answer
        let exposed := normal state telescope
        let inferredType := inferField erased exposed.state arg
        let checked := requireTypes normal limit depth inferredType.state inferred.typeRoot domain arg
        let substituted := instantiate limit depth checked.state result arg
        have normalWithin := (normalProgress state telescope).accepted room piRoot exposedOk
        have inferredProgress := inferProgress erased exposed.state arg normalWithin
        have inferredWithin := inferredProgress.accepted normalWithin inferred inferredOk
        have comparedProgress := requireTypes_progress (state := inferredType.state) (depth := depth)
          (actual := inferred.typeRoot) (expected := domain) (argument := arg)
          (fun after root _ => normalProgress after root) inferredWithin
        have comparedWithin := comparedProgress.accepted inferredWithin pair compareOk
        have substProgress := instantiate_progress limit depth checked.state result arg
        have substWithin := substProgress.accepted comparedWithin remaining substituteOk
        have restProgress := runByErasure_progress (root := root) (fields := rest) (state := substituted.state)
          (telescope := remaining) (depth := depth) inferProgress normalProgress substWithin
        have comparedFinal := substProgress.kept.trans (restProgress.kept.trans ambient)
        obtain ⟨normalKept,normalBack,exposedType,exposedRep,changed⟩ := normalSound onBase written exposedOk
        obtain ⟨argumentType,bodyType,samePi,domainRep,bodyRep⟩ := graph_pi exposedRep read
        obtain ⟨argKept,argBack,_,actualRep,actualTyped⟩ := inferSound erased (onBase.trans normalKept) normalWithin
          (argRep.frame normalKept) inferredOk (comparedProgress.kept.trans comparedFinal)
          (fun entry member => retained entry (List.mem_append_left _ member))
        have throughArg := normalKept.trans argKept
        obtain ⟨compareKept,compareBack,compatible⟩ := requireTypes_refines normalSound (onBase.trans throughArg)
          actualRep (domainRep.frame argKept) compareOk comparedFinal (retained pair (by simp))
        have throughCompare := throughArg.trans compareKept
        obtain ⟨substKept,substBack,remainingRep⟩ := NativeCoreTransformExact.substitute_refines
          (bodyRep.frame (argKept.trans compareKept)) (argRep.frame throughCompare) (instantiate_success substituteOk)
        have throughSubst := throughCompare.trans substKept
        obtain ⟨⟨tailKept,tailBack,family,count,indices,resultRep,typedTail⟩,tailFormed⟩ :=
          ih (onBase.trans throughSubst) substWithin remainingRep (restRep.frame throughSubst) tailOk ambient
            (fun entry member => retained entry (List.mem_append_right _ (List.mem_cons_of_mem _ member)))
        have substitution : expand env (bodyType.subst (single source)) =
            (expand env bodyType).subst (single (expand env source)) := by
          rw [EnvironmentDelta.expand_substitution wf.admissible]
          congr 1
          funext index
          cases index <;> simp only [single,expand]
        have piConversion : LoanTyping.Conversion.Conv env (expand env type)
            (.pi erased (expand env argumentType) (expand env bodyType)) := by
          simpa only [samePi,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs] using changed.converted
        rw [substitution] at typedTail
        have argumentTyped := actualTyped.convert compatible
        refine ⟨⟨throughSubst.trans tailKept,tailBack ∘ substBack ∘ compareBack ∘ argBack ∘ normalBack,
          family,count,indices,resultRep,?_⟩,?_⟩
        · simp only [expandArgs]
          exact .cons piConversion argumentTyped typedTail
        · intro sort output represented formed
          have exposedFormed : LoanTyping.HasType env [] ctx true
              (.pi erased (expand env argumentType) (expand env bodyType)) sort.term := by
            simpa only [samePi,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs] using changed.preserves formed
          obtain ⟨_,bodySort,_,bodyFormed,_⟩ := exposedFormed.principalView
          have tailTyped := bodyFormed.ghostInstantiate wf (argumentTyped.ghost [])
          rw [← substitution,SortTag.subst_term] at tailTyped
          exact tailFormed represented tailTyped
      · simp [reject] at success

theorem runByErasure_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : ∀ erased, NativeCoreBufferRelease.ModeSound env loans base ctx limit
      (mode || !(data && !erased)) (inferField erased))
    (inferProgress : ∀ erased state root, state.steps ≤ limit → Progress limit state (inferField erased state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena telescope type) (fieldsRep : RepresentsList state.arena fields args)
    (success : (runByErasure inferField normal limit depth root fields state telescope).result = .ok answer)
    (ambient : Prefix (runByErasure inferField normal limit depth root fields state telescope).state.arena final)
    (retained : RetainedComparisons final answer) :
    ModeRefines env loans state.arena ctx mode data type args (runByErasure inferField normal limit depth root fields state telescope) answer :=
  (runByErasure_refines_formed wf normalSound normalProgress inferSound inferProgress onBase room
    written fieldsRep success ambient retained).1

theorem run_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (written : Represents state.arena telescope type) (fieldsRep : RepresentsList state.arena fields args)
    (success : (run infer normal limit depth root fields state telescope).result = .ok answer)
    (ambient : Prefix (run infer normal limit depth root fields state telescope).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx data type args (run infer normal limit depth root fields state telescope) answer := by
  apply runByErasure_refines wf normalSound normalProgress _ (fun _ => inferProgress)
    onBase room written fieldsRep success ambient retained
  intro erased _ _ _ _ _ later cost represented accepted after tape
  obtain ⟨kept,backward,typed⟩ := inferSound later cost represented accepted after tape
  exact ⟨kept,backward,typed⟩

end Jihoo.NativeKernel.NativeCoreGhostConstructorFields
