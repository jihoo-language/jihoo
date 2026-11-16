import Jihoo.NativeBindingMachineFreshDynamicRelease
import Jihoo.NativeLoanBorrowedBudget

/-! The converse of LoanSlots: any retained owner with an actual enclosing
reader has a source loan. This is a physical/source association, independent
of operation guards. Global preservation across arbitrary calls is still open. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Unlike LoanSlots, this direction rules out unrecorded physical readers. -/
def LoanCoverage (code : Code) (loans : Loans.Stack) (stack : List Frame) : Prop :=
  ∀ index object, code.values[index]? = some (some (.owner object)) → ObjectReader object stack →
    Loans.active code.context.length loans index = true

def OwnerSlotsDistinct (code : Code) : Prop :=
  ∀ (first second object : Nat), code.values[first]? = some (some (.owner object)) →
    code.values[second]? = some (some (.owner object)) → first = second

theorem LoanCoverage.empty (code : Code) : LoanCoverage code loans [] := by
  rintro index object stored ⟨frame,member,rest⟩
  cases member

theorem LoanCoverage.child (coverage : LoanCoverage code loans stack) (term : Term) :
    LoanCoverage (code.child term) loans stack := coverage

theorem LoanCoverage.inactive (coverage : LoanCoverage code loans stack)
    (stored : code.values[index]? = some (some (.owner object)))
    (inactive : Loans.active code.context.length loans index = false) : ¬ ObjectReader object stack := by
  intro present
  have active := coverage index object stored present
  rw [inactive] at active
  cases active

/-- Ordinary non-owner bindings preserve the converse loan association. -/
theorem LoanCoverage.enter_nonowner (coverage : LoanCoverage code loans stack)
    (entered : Loans.Entered code.context.length loans)
    (erased : Bool) (domain body origin : Term) (argument : Option Value)
    (notOwner : ∀ object, argument ≠ some (.owner object)) :
    LoanCoverage (enter erased domain body code.context code.origins code.values origin argument) loans stack := by
  intro index object stored present
  cases index with
  | zero => exact False.elim (notOwner object (Option.some.inj stored))
  | succ index =>
      have active := coverage index object stored present
      simpa only [enter,List.length_cons,Loans.active_weaken entered] using active

/-- New reader names cover all owner slots when the captured physical owner
slots are distinct; no assumption about their allocation ages is needed. -/
theorem LoanCoverage.begin_reader (coverage : LoanCoverage code loans stack) (distinct : OwnerSlotsDistinct code)
    (stored : code.values[owner]? = some (some (.owner object)))
    (token : Nat) (origin readerOrigin : Term) (continuation : Code) :
    LoanCoverage code (Loans.enter code.context.length owner loans)
      (.lendReader token object (some (code.context.length-owner)) origin readerOrigin continuation :: stack) := by
  rintro index queried selected ⟨frame,member,lease,name,descriptor⟩
  rcases List.mem_cons.mp member with rfl | member
  · have sameObject : object = queried := congrArg (fun entry : Nat × Nat × Option Nat => entry.2.1) (Option.some.inj descriptor)
    rw [← sameObject] at selected
    have sameIndex := distinct index owner object selected stored
    subst index
    simp only [Loans.active_enter,beq_self_eq_true,Bool.true_or]
  · have active := coverage index queried selected ⟨frame,member,lease,name,descriptor⟩
    simp only [Loans.active_enter,Bool.or_eq_true]
    exact Or.inr active

theorem OwnerSlotsDistinct.initial (term : Term) : OwnerSlotsDistinct (.initial term) := by
  intro first second object stored
  cases stored

/-- Scalar/reference/evidence entries cannot introduce owner aliasing. -/
theorem OwnerSlotsDistinct.enter_nonowner (distinct : OwnerSlotsDistinct code)
    (erased : Bool) (domain body origin : Term) (argument : Option Value)
    (notOwner : ∀ object, argument ≠ some (.owner object)) :
    OwnerSlotsDistinct (enter erased domain body code.context code.origins code.values origin argument) := by
  intro first second object firstStored secondStored
  cases first with
  | zero => exact False.elim (notOwner object (Option.some.inj firstStored))
  | succ first =>
      cases second with
      | zero => exact False.elim (notOwner object (Option.some.inj secondStored))
      | succ second => exact congrArg Nat.succ (distinct first second object firstStored secondStored)

/-- All-prefix allocation provenance constructs owner-slot separation for an
actual fresh owner argument, without assuming old captures are still live. -/
theorem OwnerSlotsDistinct.enter_fresh (distinct : OwnerSlotsDistinct code) (bounded : CodeOwners object code)
    (domain body origin : Term) :
    OwnerSlotsDistinct (enter false domain body code.context code.origins code.values origin (some (.owner object))) := by
  intro first second queried firstStored secondStored
  cases first with
  | zero =>
      have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj firstStored))
      subst queried
      cases second with
      | zero => rfl
      | succ second =>
          have before := (ValuesOwners.valueAt bounded secondStored).ownerBound
          omega
  | succ first =>
      cases second with
      | zero =>
          have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj secondStored))
          subst queried
          have before := (ValuesOwners.valueAt bounded firstStored).ownerBound
          omega
      | succ second => exact congrArg Nat.succ (distinct first second queried firstStored secondStored)

/-- The converse loan association is constructed at fresh argument entry from
actual saved-frame provenance, then retained below the source binder. -/
theorem LoanCoverage.enter_fresh (coverage : LoanCoverage code loans stack)
    (entered : Loans.Entered code.context.length loans) (owners : StackOwners object stack)
    (domain body origin : Term) :
    LoanCoverage (enter false domain body code.context code.origins code.values origin (some (.owner object))) loans stack := by
  intro index queried stored present
  cases index with
  | zero =>
      have same : object = queried := Value.owner.inj (Option.some.inj (Option.some.inj stored))
      exact False.elim (owners.no_reader_at_limit (same ▸ present))
  | succ index =>
      have active := coverage index queried stored present
      simpa only [enter,List.length_cons,Loans.active_weaken entered] using active

/-- Reader activation and administrative frames preserve this association
whenever their actual reader projections agree. -/
theorem LoanCoverage.same_frames (coverage : LoanCoverage code loans before)
    (same : readerFrames before = readerFrames after) : LoanCoverage code loans after := by
  rintro index object stored ⟨frame,member,token,name,descriptor⟩
  have observed : (token,object,name) ∈ readerFrames after := List.mem_filterMap.mpr ⟨frame,member,descriptor⟩
  rw [← same] at observed
  obtain ⟨previous,member,descriptor⟩ := List.mem_filterMap.mp observed
  exact coverage index object stored ⟨previous,member,token,name,descriptor⟩

/-- Quantity inactivity becomes a real Free precondition using exact reachable
reader inventory. This applies to old owners, without a birth-prefix premise. -/
theorem reachable_covered_free_guard (term : Term) (fuel : Nat) (code : Code)
    (coverage : LoanCoverage code loans (run fuel (initial term)).state.stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans code.context
      (.free (.var owner) tail) = some control)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans control) :
    freeGuard (run fuel (initial term)).state.heap object = true := by
  have inactive := LoanTyping.ResourceQuantity.projectRaw_free_inactive checked budget
  have absent := coverage.inactive stored inactive
  exact (ReaderInventory.free_guard_iff (initial_run_heap_valid term fuel) (initial_reader_inventory term fuel)).mpr absent

end Jihoo.NativeKernel.Environment.BindingMachine
