import Jihoo.NativeCoreGhostSort

/-! Reference inference uses the same single normalization visit for the
owned-head gate and for exposing a Ref result. The boxed-family gate reads
the checked family metadata and leaves the original type reference intact. -/
namespace Jihoo.NativeKernel.NativeCoreGhostReferenceTypes

open NativeArena Environment
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSort (Visit)
open EnvironmentDelta (expand expandArgs)

def BoxedFamilies (env : Environment) (isBoxed : Nat → Bool) : Prop :=
  ∀ family, isBoxed family = true → ∃ entry, env.families[family]? = some entry ∧ entry.boxed = true

def isBoxedAt (env : Environment) (family : Nat) : Bool :=
  (env.families[family]?.map fun entry => entry.boxed).getD false

theorem isBoxedAt_sound (env : Environment) : BoxedFamilies env (isBoxedAt env) := by
  intro family boxed
  cases found : env.families[family]? with
  | none => simp [isBoxedAt,found] at boxed
  | some entry => exact ⟨entry,rfl,by simpa [isBoxedAt,found] using boxed⟩

def requireOwned (normal : Visit) (isBoxed : Nat → Bool) (state : NativeCoreTransformExact.State)
    (root rejected : Nat) : Outcome Unit :=
  (normal state root).next fun after selected =>
    match after.arena[selected]? with
    | some (.node .buffer [_]) => ⟨after,.ok ()⟩
    | some (.node (.ind family _) _) =>
        if isBoxed family then ⟨after,.ok ()⟩ else ⟨after,.error (.outsideFragment rejected)⟩
    | _ => ⟨after,.error (.outsideFragment rejected)⟩

def referenceTarget (normal : Visit) (state : NativeCoreTransformExact.State) (root rejected : Nat) : Outcome Nat :=
  (normal state root).next fun after selected =>
    match after.arena[selected]? with
    | some (.node .ref [target]) => ⟨after,.ok target⟩
    | _ => ⟨after,.error (.outsideFragment rejected)⟩

theorem requireOwned_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (requireOwned normal isBoxed state root rejected) := by
  unfold requireOwned
  apply (normalProgress _ _).next
  intro _
  split
  · exact Progress.atState _ _
  · split <;> exact Progress.atState _ _
  · exact Progress.atState _ _

theorem referenceTarget_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (referenceTarget normal state root rejected) := by
  unfold referenceTarget
  apply (normalProgress _ _).next
  intro _
  split <;> exact Progress.atState _ _

private theorem represented_node (written : Represents arena ref term)
    (read : arena[ref]? = some (.node op refs)) :
    ∃ children, term = .node op children ∧ RepresentsList arena refs children := by
  cases written with
  | var found => rw [read] at found; cases found
  | node found _ children => rw [read] at found; cases found; exact ⟨_,rfl,children⟩

theorem requireOwned_refines (metadata : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (source : Represents state.arena root term)
    (success : (requireOwned normal isBoxed state root rejected).result = .ok ()) :
    let after := (requireOwned normal isBoxed state root rejected).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ LoanTyping.Owned env (expand env term) := by
  unfold requireOwned at success ⊢
  obtain ⟨selected,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,residual,held,converted⟩ := normalSound onBase source normalized
  split at success
  · rename_i length read
    obtain ⟨args,shape,children⟩ := represented_node held read
    cases children with
    | cons countRep tail =>
      cases tail
      exact ⟨kept,backward,.buffer (by simpa only [shape,Term.buffer,expand,expandArgs] using converted.converted)⟩
  · rename_i family count refs read
    split at success
    · rename_i boxed
      obtain ⟨entry,found,flag⟩ := metadata family boxed
      obtain ⟨args,shape,_⟩ := represented_node held read
      simp only [ite_eq_left boxed]
      exact ⟨kept,backward,.family found flag (by simpa only [shape,expand] using converted.converted)⟩
    · contradiction
  · contradiction

theorem referenceTarget_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena root term)
    (success : (referenceTarget normal state root rejected).result = .ok target) :
    let after := (referenceTarget normal state root rejected).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ referred, Represents after target referred ∧ LoanTyping.Conversion.Conv env (expand env term)
        (.ref (expand env referred)) := by
  unfold referenceTarget at success ⊢
  obtain ⟨selected,normalized,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,residual,held,converted⟩ := normalSound onBase source normalized
  split at success
  · rename_i child read
    have same : child = target := Except.ok.inj success
    subst target
    obtain ⟨args,shape,children⟩ := represented_node held read
    cases children with
    | cons written tail =>
      cases tail
      exact ⟨kept,backward,_,written,by simpa only [shape,Term.ref,expand,expandArgs] using converted.converted⟩
  · contradiction

end Jihoo.NativeKernel.NativeCoreGhostReferenceTypes
