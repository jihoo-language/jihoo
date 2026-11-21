import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeCoreFamilyHeadFormation

/-! View retains the normalized outer reference type for its motive
comparison and separately normalizes the referenced family to recover
the original parameter roots. -/
namespace Jihoo.NativeKernel.NativeCoreViewSubject

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred RetainedComparisons next_progress)
open EnvironmentDelta (expand expandArgs)

structure Exposure where
  inferred : Inferred
  referenceType : Nat
  arity : Nat
  parameters : List Nat

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def exposeFamily (normal : Visit) (state : State) (family subject outer inner : Nat)
    (inferred : Inferred) : Outcome Exposure :=
  (normal state inner).next fun after selected =>
    match after.arena[selected]? with
    | some (.node (.ind actual arity) parameters) =>
      if actual = family then ⟨after,.ok ⟨inferred,outer,arity,parameters⟩⟩ else reject after subject
    | _ => reject after subject

private def expose (normal : Visit) (state : State) (family subject : Nat) (inferred : Inferred) : Outcome Exposure :=
  (normal state inferred.typeRoot).next fun exposed outer =>
    match exposed.arena[outer]? with
    | some (.node .ref [inner]) => exposeFamily normal exposed family subject outer inner inferred
    | _ => reject exposed subject

def run (infer : Infer) (normal : Visit) (state : State) (family subject : Nat) : Outcome Exposure :=
  (infer state subject).next fun inferred answer => expose normal inferred family subject answer

private theorem exposeFamily_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (exposeFamily normal state family subject outer inner inferred) :=
  (normalProgress _ _).next (fun _ => by split; split <;> exact Progress.atState _ _; exact Progress.atState _ _)

private theorem expose_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (expose normal state family subject inferred) :=
  (normalProgress _ _).next (fun _ => by
    split
    · exact exposeFamily_progress normalProgress
    · exact Progress.atState _ _)

theorem run_progress
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run infer normal state family subject) :=
  (inferProgress _ _ room).next (fun _ => expose_progress normalProgress)

private theorem reference_child (held : Represents arena outer reflected)
    (read : arena[outer]? = some (.node .ref [inner])) :
    ∃ T, reflected = .ref T ∧ Represents arena inner T := by
  cases held with
  | var found => rw [read] at found; cases found
  | node found width refs =>
    rw [read] at found
    cases found
    cases refs with
    | cons child tail =>
      cases tail
      exact ⟨_,rfl,child⟩

private theorem family_children (held : Represents arena selected residual)
    (read : arena[selected]? = some (.node (.ind family arity) parameters)) :
    ∃ values, residual = .node (.ind family arity) values ∧
      RepresentsList arena parameters values ∧ parameters.length = arity := by
  cases held with
  | var found => rw [read] at found; cases found
  | node found width refs =>
    rw [read] at found
    cases found
    exact ⟨_,rfl,refs,width⟩

/-- The two distinct normalization visits justify the reference used by the
motive and the selected family's parameter roots used by the cases. -/
private theorem run_trace
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena subject X)
    (success : (run infer normal state family subject).result = .ok answer)
    (ambient : Prefix (run infer normal state family subject).state.arena final)
    (retained : RetainedComparisons final answer.inferred) :
    let after := (run infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ original inner values, (infer state subject).result = .ok answer.inferred ∧
        Represents (infer state subject).state.arena answer.inferred.typeRoot original ∧
        ExpandedNormalization env original (.ref inner) ∧
        ExpandedNormalization env inner (.node (.ind family answer.arity) values) ∧
        Represents after answer.referenceType (.ref inner) ∧
        RepresentsList after answer.parameters values ∧ answer.parameters.length = answer.arity ∧
        RawLend.Conv env (expand env inner) (.node (.ind family answer.arity) (expandArgs env values)) ∧
        LoanTyping.HasType env [] ctx true (expand env X)
          (.ref (.node (.ind family answer.arity) (expandArgs env values))) := by
  unfold run at success ambient ⊢
  obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  let checked := (infer state subject).state
  have exposeCost := expose_progress (state := checked) (family := family) (subject := subject) (inferred := inferred) normalProgress
  unfold expose at success ambient ⊢
  obtain ⟨outer,outerOk,outerNext⟩ := Outcome.next_success success
  rw [outerNext] at success ambient ⊢
  split at success
  · rename_i inner found
    simp only [found] at ambient ⊢
    unfold exposeFamily at success ambient ⊢
    obtain ⟨selected,selectedOk,selectedNext⟩ := Outcome.next_success success
    rw [selectedNext] at success ambient ⊢
    split at success
    · rename_i actual arity parameters read
      simp only [read] at ambient ⊢
      split at success
      · rename_i same
        subst actual
        simp only [ite_true,Except.ok.injEq] at success ambient ⊢
        subst answer
        have exposed : Prefix (expose normal checked family subject inferred).state.arena final := by
          unfold expose
          rw [outerNext,found]
          change Prefix (exposeFamily normal (normal checked inferred.typeRoot).state family subject outer inner inferred).state.arena final
          unfold exposeFamily
          rw [selectedNext,read]
          simpa only [ite_true] using ambient
        obtain ⟨inferKept,inferBack,inferredType,inferredRep,typed⟩ := inferSound onBase room source inferredOk
          (exposeCost.kept.trans exposed) retained
        obtain ⟨outerKept,outerBack,_,outerRep,outerChanged⟩ := normalSound (onBase.trans inferKept) inferredRep outerOk
        obtain ⟨T,shape,innerRep⟩ := reference_child outerRep found
        have beforeInner := inferKept.trans outerKept
        obtain ⟨innerKept,innerBack,_,selectedRep,innerChanged⟩ :=
          normalSound (onBase.trans beforeInner) innerRep selectedOk
        obtain ⟨values,familyShape,valuesRep,width⟩ := family_children selectedRep read
        have innerConversion : RawLend.Conv env (expand env T) (.node (.ind family arity) (expandArgs env values)) := by
          simpa only [familyShape,expand] using innerChanged.converted
        have outerConversion : RawLend.Conv env (expand env inferredType) (.ref (expand env T)) := by
          simpa only [shape,Term.ref,expand,expandArgs] using outerChanged.converted
        exact ⟨beforeInner.trans innerKept,innerBack ∘ outerBack ∘ inferBack,inferredType,T,values,inferredOk,inferredRep,
          shape ▸ outerChanged,familyShape ▸ innerChanged,shape ▸ outerRep.frame innerKept,valuesRep,width,innerConversion,
          typed.convert (outerConversion.trans (.node .ref (.cons innerConversion .nil)))⟩
      · cases success
    · cases success
  · cases success

theorem run_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena subject X)
    (success : (run infer normal state family subject).result = .ok answer)
    (ambient : Prefix (run infer normal state family subject).state.arena final)
    (retained : RetainedComparisons final answer.inferred) :
    let after := (run infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ inner values, Represents after answer.referenceType (.ref inner) ∧
        RepresentsList after answer.parameters values ∧ answer.parameters.length = answer.arity ∧
        RawLend.Conv env (expand env inner) (.node (.ind family answer.arity) (expandArgs env values)) ∧
        LoanTyping.HasType env [] ctx true (expand env X)
          (.ref (.node (.ind family answer.arity) (expandArgs env values))) := by
  obtain ⟨kept,safe,_,inner,values,_,_,_,_,reference,parameters,width,relation,typed⟩ :=
    run_trace normalSound normalProgress inferSound onBase room source success ambient retained
  exact ⟨kept,safe,inner,values,reference,parameters,width,relation,typed⟩


private def ReferenceFormation (env : Environment) (ctx : Context) : Term → Prop
  | .ref inner => LoanTyping.HasType env [] ctx true inner (.univ 0)
  | _ => True

private theorem reference_formation (typed : LoanTyping.HasType env [] ctx true (.ref subject) type) :
    LoanTyping.HasType env [] ctx true subject (.univ 0) := by
  have recover {loans ctx mode term type} (actual : LoanTyping.HasType env loans ctx mode term type) :
      ReferenceFormation env ctx term := by
    apply LoanTyping.HasType.rec (t := actual)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ ctx _ term _ _ => ReferenceFormation env ctx term)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | exact True.intro | assumption | skip
    case refBuffer length _ => exact .buffer (length.ghost [])
    case refOwned owner _ _ => exact owner.ghost []
    case dataElim => split <;> trivial
  exact recover typed

/-- If the original inferred annotation has independent formation, the
actual normalized borrow determines the declared arity and checks every
recovered parameter as a word. This uses both original visits. -/
theorem run_refines_formed
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (source : Represents state.arena subject X)
    (formation : ∀ {input original}, (infer state subject).result = .ok input →
      Represents (infer state subject).state.arena input.typeRoot original →
      ∃ sort : SortTag, LoanTyping.HasType env [] ctx true (expand env original) sort.term)
    (success : (run infer normal state family subject).result = .ok answer)
    (ambient : Prefix (run infer normal state family subject).state.arena final)
    (retained : RetainedComparisons final answer.inferred) :
    let after := (run infer normal state family subject).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ entry inner values, env.families[family]? = some entry ∧ answer.arity = entry.declaration.arity ∧
        Represents after answer.referenceType (.ref inner) ∧ RepresentsList after answer.parameters values ∧
        values.length = answer.arity ∧
        (∀ value ∈ values,LoanTyping.HasType env [] ctx true (expand env value) .u64) ∧
        RawLend.Conv env (expand env inner) (.node (.ind family answer.arity) (expandArgs env values)) ∧
        LoanTyping.HasType env [] ctx true (expand env X)
          (.ref (.node (.ind family answer.arity) (expandArgs env values))) := by
  obtain ⟨kept,safe,original,inner,values,inferredOk,originalRep,outerChange,innerChange,referenceRep,
    parameterRep,_,innerConv,typed⟩ := run_trace normalSound normalProgress inferSound onBase room
      source success ambient retained
  obtain ⟨sort,formed⟩ := formation inferredOk originalRep
  have reference : LoanTyping.HasType env [] ctx true (.ref (expand env inner)) sort.term := by
    simpa only [Term.ref,EnvironmentDelta.expand_node_cons,expandArgs] using outerChange.preserves formed
  obtain ⟨entry,found,arity,width,parametersTyped⟩ := NativeCoreFamilyHeadFormation.normalized_family_head
    (reference_formation reference) innerChange
  exact ⟨kept,safe,entry,inner,values,found,arity,referenceRep,parameterRep,width,parametersTyped,innerConv,typed⟩

end Jihoo.NativeKernel.NativeCoreViewSubject
