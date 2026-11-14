import Jihoo.NativeResourceSyntax

/-! Loan snapshots used by Core.lending: a stored owner is a source variable
at the context depth where a dependent reader was entered. Lookup raises that
variable to the current depth and never activates a snapshot from a future
context. This is a concrete permission algebra, not yet a Lend typing rule or
a native heap/lifetime theorem. -/
namespace Jihoo.NativeKernel.Environment.Loans

structure Frame where
  depth : Nat
  owner : Nat
  deriving DecidableEq, Repr

abbrev Stack := List Frame

def Frame.indexAt (frame : Frame) (current : Nat) : Option Nat :=
  if frame.depth ≤ current then some (frame.owner + (current - frame.depth)) else none

def active (current : Nat) (frames : Stack) (owner : Nat) : Bool :=
  frames.any fun frame => frame.indexAt current == some owner

def Scoped (frames : Stack) : Prop := ∀ frame ∈ frames, frame.owner < frame.depth

def Entered (current : Nat) (frames : Stack) : Prop := ∀ frame ∈ frames, frame.depth ≤ current

def enter (current owner : Nat) (frames : Stack) : Stack := ⟨current,owner⟩ :: frames

def exit : Stack → Stack := List.tail

theorem Frame.indexAt_some {frame : Frame} {current owner : Nat} : frame.indexAt current = some owner ↔
    frame.depth ≤ current ∧ owner = frame.owner + (current - frame.depth) := by
  by_cases before : frame.depth ≤ current
  all_goals simp [Frame.indexAt,before,eq_comm]

theorem active_iff : active current frames owner = true ↔
    ∃ frame ∈ frames, frame.depth ≤ current ∧ owner = frame.owner + (current - frame.depth) := by
  simp only [active,List.any_eq_true,beq_iff_eq,Frame.indexAt_some]

theorem active_empty : active current [] owner = false := rfl

theorem active_enter : active current (enter current owner frames) queried =
    ((owner == queried) || active current frames queried) := by
  simp [active,enter,Frame.indexAt]

theorem exit_enter : exit (enter current owner frames) = frames := rfl

theorem scoped_enter (scope : Scoped frames) (inside : owner < current) :
    Scoped (enter current owner frames) := by
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact inside
  · exact scope frame member

theorem entered_enter (entered : Entered current frames) :
    Entered current (enter current owner frames) := by
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_refl _
  · exact entered frame member

theorem active_bound (scope : Scoped frames) (allowed : active current frames owner = true) : owner < current := by
  obtain ⟨frame,member,before,same⟩ := active_iff.mp allowed
  have bound := scope frame member
  omega

/-- Scope exit preserves all earlier permissions exactly; it removes only the
latest reader's snapshot, even when nested readers lend the same owner. -/
theorem exit_preserves_outer (allowed : active current frames owner = true) :
    active current (exit (enter enteredDepth borrowed frames)) owner = true := allowed

/-- Existing snapshots remain active below a newly entered ordinary binder.
The Entered premise rules out stale future-depth entries becoming new loans. -/
theorem active_weaken (entered : Entered current frames) :
    active (current+1) frames (owner+1) = active current frames owner := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro allowed
    obtain ⟨frame,member,before,same⟩ := active_iff.mp allowed
    have oldBefore := entered frame member
    exact active_iff.mpr ⟨frame,member,oldBefore,by omega⟩
  · intro allowed
    obtain ⟨frame,member,before,same⟩ := active_iff.mp allowed
    exact active_iff.mpr ⟨frame,member,by omega,by omega⟩

/-- Materialize only currently eligible snapshots at a new context depth.
This handles arbitrary variable renaming without guessing a scalar mode. -/
def rebase (current target : Nat) (ρ : Nat → Nat) (frames : Stack) : Stack :=
  frames.filterMap fun frame => (frame.indexAt current).map fun owner => ⟨target,ρ owner⟩

theorem active_rebase (allowed : active current frames owner = true) :
    active target (rebase current target ρ frames) (ρ owner) = true := by
  obtain ⟨frame,member,before,same⟩ := active_iff.mp allowed
  apply active_iff.mpr
  refine ⟨⟨target,ρ owner⟩,?_,Nat.le_refl _,by simp⟩
  apply List.mem_filterMap.mpr
  refine ⟨frame,member,?_⟩
  rw [(Frame.indexAt_some).mpr ⟨before,same⟩]
  rfl

theorem scoped_rebase (scope : Scoped frames)
    (maps : ∀ owner, owner < current → ρ owner < target) :
    Scoped (rebase current target ρ frames) := by
  intro selected selectedMember
  unfold rebase at selectedMember
  obtain ⟨frame,frameMember,mapped⟩ := List.mem_filterMap.mp selectedMember
  obtain ⟨owner,found,equality⟩ := Option.map_eq_some_iff.mp mapped
  cases equality
  have activeOwner : active current frames owner = true :=
    active_iff.mpr ⟨frame,frameMember,(Frame.indexAt_some.mp found)⟩
  exact maps owner (active_bound scope activeOwner)

/-- Ghost borrowing ignores the runtime loan stack; code borrowing only reads
an actual active source variable. The later typing rule must also check Owned. -/
def borrowAllowed (ghost : Bool) (current : Nat) (frames : Stack) : Term → Bool
  | .var owner => ghost || active current frames owner
  | .node _ _ => ghost

theorem ghost_borrow_allowed : borrowAllowed true current frames term = true := by
  cases term <;> rfl

theorem code_borrow_allowed : borrowAllowed false current frames term = true ↔
    ∃ owner, term = .var owner ∧ active current frames owner = true := by
  cases term <;> simp [borrowAllowed]

theorem code_borrow_rename (allowed : borrowAllowed false current frames term = true) :
    borrowAllowed false target (rebase current target ρ frames) (term.rename ρ) = true := by
  obtain ⟨owner,rfl,allowed⟩ := code_borrow_allowed.mp allowed
  simpa only [borrowAllowed,Term.rename,Bool.false_or] using
    (active_rebase (target := target) (ρ := ρ) allowed)

end Jihoo.NativeKernel.Environment.Loans
