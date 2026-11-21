import Jihoo.NativeCoreGhostTypeRequirement

/-! Buffer length recovery and Free use the same schedule in ghost and
code checking. The buffer and tail keep their original checking mode. -/
namespace Jihoo.NativeKernel.NativeCoreBufferRelease

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreGhostSpineInference (Infer Visit Inferred PairRetained RetainedComparisons next_progress)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand expandArgs)

def ModeSound (env : Environment) (loans : Loans.Stack) (base : Arena) (ctx : Context) (limit : Nat)
    (mode : Bool) (visit : Infer) : Prop :=
  ∀ {state root term answer final}, Prefix base state.arena → state.steps ≤ limit → Represents state.arena root term →
    (visit state root).result = .ok answer → Prefix (visit state root).state.arena final → RetainedComparisons final answer →
      let after := (visit state root).state.arena
      Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
        ∃ type, Represents after answer.typeRoot type ∧ LoanTyping.HasType env loans ctx mode (expand env term) (expand env type)

private def discard (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

def bufferLength (infer : Infer) (normal : Visit) (state : State) (buffer : Nat) :
    Outcome (Nat × List (Nat × Nat)) :=
  (infer state buffer).next fun inferred found =>
    (normal inferred found.typeRoot).next fun exposed root =>
      match exposed.arena[root]? with
      | some (.node .buffer [length]) => ⟨exposed,.ok (length,found.compared)⟩
      | _ => discard exposed buffer

def inferFree (infer : Infer) (normal : Visit) (state : State) (buffer tail : Nat) : Outcome Inferred :=
  (bufferLength infer normal state buffer).next fun afterBuffer checked =>
    (infer afterBuffer tail).next fun after result =>
      ⟨after,.ok ⟨result.typeRoot,checked.2 ++ result.compared⟩⟩

theorem bufferLength_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (bufferLength infer normal state buffer) := by
  apply next_progress (infers _ _ room) room
  intro _ _ _
  apply (normalizes _ _).next
  intro root
  split <;> exact Progress.atState _ _

theorem inferFree_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (inferFree infer normal state buffer tail) := by
  apply next_progress (bufferLength_progress infers normalizes room) room
  intro _ _ bufferRoom
  exact (infers _ _ bufferRoom).next (fun _ => Progress.atState _ _)

theorem unary_read (represented : Represents arena root term)
    (read : arena[root]? = some (.node op [ref])) :
    ∃ child, term = .node op [child] ∧ Represents arena ref child := by
  cases represented with
  | var other => rw [read] at other; cases other
  | node other arity args =>
    rw [read] at other
    cases other
    cases args with
    | cons first tail => cases tail; exact ⟨_,rfl,first⟩

theorem bufferLength_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : ModeSound env loans base ctx limit mode infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b)
    (success : (bufferLength infer normal state buffer).result = .ok answer)
    (ambient : Prefix (bufferLength infer normal state buffer).state.arena final)
    (retained : ∀ pair ∈ answer.2, PairRetained final pair) :
    let after := (bufferLength infer normal state buffer).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ length, Represents after answer.1 length ∧
        LoanTyping.HasType env loans ctx mode (expand env b) (.buffer (expand env length)) := by
  unfold bufferLength at success ambient ⊢
  obtain ⟨found,foundOk,foundNext⟩ := Outcome.next_success success
  rw [foundNext] at success ambient ⊢
  obtain ⟨root,exposedOk,exposedNext⟩ := Outcome.next_success success
  rw [exposedNext] at success ambient ⊢
  split at success
  · rename_i length read
    simp only [read] at ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    have inferred := childProgress state buffer room
    have normalized := normalProgress (infer state buffer).state found.typeRoot
    obtain ⟨_,inferredBack,_,foundRep,typed⟩ := childSound onBase room bufferRep foundOk
      (normalized.kept.trans ambient) retained
    obtain ⟨kept,backward,residual,held,converted⟩ := normalSound (onBase.trans inferred.kept) foundRep exposedOk
    obtain ⟨count,shape,countRep⟩ := unary_read held read
    refine ⟨inferred.kept.trans kept,backward ∘ inferredBack,count,countRep,?_⟩
    simpa only [shape,Term.buffer,expand,expandArgs] using typed.convert converted.converted
  · simp [discard] at success

theorem inferFree_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (childSound : ModeSound env loans base ctx limit mode infer)
    (childProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (bufferRep : Represents state.arena buffer b) (tailRep : Represents state.arena tail t)
    (success : (inferFree infer normal state buffer tail).result = .ok answer)
    (ambient : Prefix (inferFree infer normal state buffer tail).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (inferFree infer normal state buffer tail).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env loans ctx mode (expand env (.free b t)) (expand env type) := by
  unfold inferFree at success ambient ⊢
  obtain ⟨checked,bufferOk,bufferNext⟩ := Outcome.next_success success
  rw [bufferNext] at success ambient ⊢
  obtain ⟨result,tailOk,tailNext⟩ := Outcome.next_success success
  rw [tailNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let checkedBuffer := bufferLength infer normal state buffer
  have bufferProgress := bufferLength_progress (state := state) (buffer := buffer) childProgress normalProgress room
  have bufferRoom := bufferProgress.accepted room checked bufferOk
  have tailProgress := childProgress checkedBuffer.state tail bufferRoom
  obtain ⟨bufferKept,bufferBack,_,_,typedBuffer⟩ := bufferLength_refines normalSound normalProgress childSound
    childProgress onBase room bufferRep bufferOk (tailProgress.kept.trans ambient)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨tailKept,tailBack,_,resultRep,typedTail⟩ := childSound (onBase.trans bufferKept) bufferRoom
    (tailRep.frame bufferKept) tailOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
  refine ⟨bufferKept.trans tailKept,tailBack ∘ bufferBack,_,resultRep,?_⟩
  simp only [Term.free,expand,expandArgs]
  exact .free typedBuffer typedTail

end Jihoo.NativeKernel.NativeCoreBufferRelease
