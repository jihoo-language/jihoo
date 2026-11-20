import Jihoo.NativeCoreTypedEqual

/-! Sort exposure and binder admissibility in the live ghost inference arena.
The binder policy consults the data-family table only after an erased domain's
sort is known to be a universe and the domain has been normalized. -/
namespace Jihoo.NativeKernel.NativeCoreGhostSort

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand expandArgs)

abbrev Visit := State → Nat → Outcome Nat

private def reject (state : State) (root : Nat) : Outcome α :=
  ⟨state, .error (.outsideFragment root)⟩

/-- The native sort query normalizes its input once at the given depth. -/
def sort (normal : Visit) (state : State) (typeRoot : Nat) : Outcome SortTag :=
  (normal state typeRoot).next fun after exposed =>
    match after.arena[exposed]? with
    | some (.node .prop []) => ⟨after, .ok .prop⟩
    | some (.node (.universe level) []) => ⟨after, .ok (.type level)⟩
    | _ => reject after typeRoot

theorem sort_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (sort normal state typeRoot) :=
  (normalProgress _ _).next (fun _ => by split <;> exact Progress.atState _ _)

theorem sort_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (represented : Represents state.arena typeRoot type)
    (success : (sort normal state typeRoot).result = .ok selected) :
    let after := (sort normal state typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.Conversion.Conv env (expand env type) selected.term := by
  unfold sort at success ⊢
  obtain ⟨exposed, normalized, continued⟩ := Outcome.next_success success
  rw [continued] at success ⊢
  obtain ⟨kept, backward, residual, residualRep, related⟩ := normalSound onBase represented normalized
  split at success
  · rename_i read
    have shape := residualRep.unique (Represents.node read rfl .nil)
    cases success
    exact ⟨kept, backward, by simpa only [shape, SortTag.term, Term.prop, expand, expandArgs] using related.converted⟩
  · rename_i read
    have shape := residualRep.unique (Represents.node read rfl .nil)
    cases success
    exact ⟨kept, backward, by simpa only [shape, SortTag.term, Term.univ, expand, expandArgs] using related.converted⟩
  · simp [reject] at success

def DataFamilies (env : Environment) (isData : Nat → Bool) : Prop :=
  ∀ family, isData family = true → ∃ entry, env.families[family]? = some entry ∧ entry.declaration.data = true

def isDataAt (env : Environment) (family : Nat) : Bool :=
  (env.families[family]?.map fun entry => entry.declaration.data).getD false

theorem isDataAt_sound (env : Environment) : DataFamilies env (isDataAt env) := by
  intro family data
  cases found : env.families[family]? with
  | none => simp [isDataAt, found] at data
  | some entry => exact ⟨entry, rfl, by simpa [isDataAt, found] using data⟩

def testDomain (normal : Visit) (isData : Nat → Bool) (state : State) (domain : Nat) : Outcome Unit :=
  (normal state domain).next fun after exposed =>
    match after.arena[exposed]? with
    | some (.node .u64 []) => ⟨after, .ok ()⟩
    | some (.node (.ind family _) _) =>
        if isData family then ⟨after, .ok ()⟩ else reject after domain
    | _ => reject after domain

/-- A relevant binder needs a type. An erased binder accepts a proposition,
or checks that a type domain exposes a word or a declared data family. -/
def policy (normal : Visit) (isData : Nat → Bool) (state : State) (domain : Nat)
    (erased : Bool) (selected : SortTag) : Outcome Unit :=
  match erased, selected with
  | false, .prop => reject state domain
  | true, .type _ => testDomain normal isData state domain
  | _, _ => ⟨state, .ok ()⟩

theorem policy_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (policy normal isData state domain erased selected) := by
  cases erased <;> cases selected <;> try exact Progress.atState _ _
  change Progress limit state (testDomain normal isData state domain)
  unfold testDomain
  exact (normalProgress _ _).next (fun _ => by
    split
    · exact Progress.atState _ _
    · split <;> exact Progress.atState _ _
    · exact Progress.atState _ _)

private theorem testDomain_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (metadata : DataFamilies env isData) (onBase : Prefix base state.arena)
    (represented : Represents state.arena domain type)
    (success : (testDomain normal isData state domain).result = .ok ()) :
    let after := (testDomain normal isData state domain).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      (LoanTyping.Conversion.Conv env (expand env type) .u64 ∨ LoanTyping.dataBinderAllowed env (expand env type)) := by
  unfold testDomain at success ⊢
  obtain ⟨exposed, normalized, continued⟩ := Outcome.next_success success
  rw [continued] at success ⊢
  obtain ⟨kept, backward, residual, residualRep, related⟩ := normalSound onBase represented normalized
  split at success
  · rename_i read
    have shape := residualRep.unique (Represents.node read rfl .nil)
    exact ⟨kept, backward, .inl (by simpa only [shape, Term.u64, expand, expandArgs] using related.converted)⟩
  · rename_i family count refs read
    split at success
    · rename_i isKnownData
      simp only [ite_eq_left isKnownData]
      obtain ⟨entry, found, data⟩ := metadata family isKnownData
      have shape : ∃ indices, residual = .node (.ind family count) indices := by
        cases residualRep with
        | var other => rw [read] at other; cases other
        | node other => rw [read] at other; cases other; exact ⟨_, rfl⟩
      obtain ⟨indices, shape⟩ := shape
      exact ⟨kept, backward, .inr ⟨family, count, expandArgs env indices, entry, found, data,
        by simpa only [shape, expand] using related.converted⟩⟩
    · simp [reject] at success
  · simp [reject] at success

theorem policy_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (metadata : DataFamilies env isData) (onBase : Prefix base state.arena)
    (represented : Represents state.arena domain type)
    (success : (policy normal isData state domain erased selected).result = .ok ()) :
    let after := (policy normal isData state domain erased selected).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      LoanTyping.binderAllowed env erased (expand env type) selected := by
  cases erased <;> cases selected
  · simp [policy, reject] at success
  · exact ⟨.refl _, id, .inl (fun impossible => by cases impossible)⟩
  · exact ⟨.refl _, id, .inl (.inl rfl)⟩
  · obtain ⟨kept, backward, domainAllowed⟩ := testDomain_refines normalSound metadata onBase represented success
    refine ⟨kept, backward, ?_⟩
    exact domainAllowed.elim (fun word => .inl (.inr word)) (fun data => .inr ⟨rfl, data⟩)

end Jihoo.NativeKernel.NativeCoreGhostSort
