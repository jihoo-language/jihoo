import Jihoo.NativeCoreGhostTypeRequirement
import Jihoo.NativeLoanErasedCaseSpines

/-! Compiled case analysis may be applied to erased arguments. The native
checker scans the product spine without additional ticks after normalizing
the returned annotation, and prevents a partial case application from escaping. -/
namespace Jihoo.NativeKernel.NativeCoreErasedCasePolicy

open Environment NativeArena
open EnvironmentDelta (expand expandArgs)
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreGhostSpineInference (Visit)
open NativeCoreBinderTraversal (VisitsFrom)

open LoanTyping.ErasedCaseSpines (ErasedProducts CaseHead)

private def scan (arena : Arena) : Nat → Nat → Bool
  | 0,_ => false
  | fuel+1,root =>
    match arena[root]? with
    | some (.node (.pi true) [_,range]) => scan arena fuel range
    | some (.node (.pi _) _) => false
    | some _ => true
    | none => false

private theorem scan_refines (represented : Represents arena root term)
    (accepted : scan arena fuel root = true) : ErasedProducts term := by
  induction fuel generalizing root term with
  | zero => contradiction
  | succ fuel ih =>
    cases represented with
    | var lookup => exact .var _
    | @node _ op ids terms lookup width children =>
      cases op <;> try solve | apply ErasedProducts.other; intro flag clash; cases clash
      case pi flag =>
        have length : ids.length = 2 := width
        rcases ids with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons domain rest =>
          cases rest with
          | cons range rest =>
            cases rest
            cases flag
            · simp [scan,lookup] at accepted
            · exact .binder (ih range (by simpa only [scan,lookup] using accepted))

private theorem scan_complete (backward : Backward arena) (inside : root < fuel)
    (represented : Represents arena root term) (erased : ErasedProducts term) :
    scan arena fuel root = true := by
  induction fuel generalizing root term with
  | zero => omega
  | succ fuel ih =>
    cases represented with
    | var lookup => simp only [scan,lookup]
    | @node root op ids terms lookup width children =>
      cases op <;> try solve | simp only [scan,lookup]
      case pi flag =>
        have length : ids.length = 2 := width
        rcases ids with _ | ⟨_,_ | ⟨rangeRoot,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons domain rest =>
          cases rest with
          | cons range rest =>
            cases rest
            have earlier : rangeRoot < root := backward _ _ lookup _ (by simp [Node.references])
            cases flag
            · cases erased with
              | other distinct => exact False.elim (distinct false rfl)
            · cases erased with
              | other distinct => exact False.elim (distinct true rfl)
              | binder shape =>
                simp only [scan,lookup]
                exact ih (by omega) range shape

/-- In a backward arena the bounded scan is exact: an erased telescope
ends at any raw non-Pi head, just as in the native head inspection. -/
theorem erased_products_iff (backward : Backward arena) (represented : Represents arena root term) :
    scan arena (root+1) root = true ↔ ErasedProducts term :=
  ⟨scan_refines represented,scan_complete backward (Nat.lt_succ_self _) represented⟩

/-- One normalization followed by the native unmetered erased-binder scan. -/
def check (normal : Visit) (state : State) (result motive : Nat) : Outcome Unit :=
  (normal state result).next fun exposed selected =>
    if scan exposed.arena (selected+1) selected then ⟨exposed,.ok ()⟩
    else ⟨exposed,.error (.outsideFragment motive)⟩

theorem check_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (check normal state result motive) := by
  unfold check
  exact (normalProgress _ _).next fun _ => by split <;> exact Progress.atState _ _

/-- The check retains the original result annotation and certifies the
actual normalized product telescope. -/
theorem check_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (original : Represents state.arena result type)
    (accepted : (check normal state result motive).result = .ok ()) :
    let after := (check normal state result motive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ observed, ExpandedNormalization env type observed ∧ ErasedProducts observed := by
  unfold check at accepted ⊢
  obtain ⟨selected, normalized, next⟩ := Outcome.next_success accepted
  rw [next] at accepted ⊢
  obtain ⟨kept,safe,term,represented,converted⟩ := normalSound onBase original normalized
  split at accepted
  · rename_i scanned
    rw [ite_eq_left scanned]
    exact ⟨kept,safe,term,converted,scan_refines represented scanned⟩
  · cases accepted

private def scanHead (arena : Arena) : Nat → Nat → Bool
  | 0,_ => false
  | fuel+1,root =>
    match arena[root]? with
    | some (.node .app [function,_]) => scanHead arena fuel function
    | some (.node (.caseOf _ _) _) => true
    | _ => false

def hasCaseHead (arena : Arena) (root : Nat) : Bool := scanHead arena (root+1) root

private theorem scanHead_iff (backward : Backward arena) (inside : root < fuel)
    (represented : Represents arena root term) : scanHead arena fuel root = true ↔ CaseHead term := by
  induction fuel generalizing root term with
  | zero => omega
  | succ fuel ih =>
    cases represented with
    | var lookup => simp [scanHead,lookup,CaseHead]
    | @node root op ids terms lookup width children =>
      cases op <;> try solve | simp [scanHead,lookup,CaseHead]
      case app =>
        have length : ids.length = 2 := width
        rcases ids with _ | ⟨functionRoot,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at length
        cases children with
        | cons function rest =>
          cases rest with
          | cons argument rest =>
            cases rest
            have earlier : functionRoot < root := backward _ _ lookup _ (by simp [Node.references])
            simp only [scanHead,lookup,CaseHead]
            exact ih (by omega) function

theorem hasCaseHead_iff (backward : Backward arena) (represented : Represents arena root term) :
    hasCaseHead arena root = true ↔ CaseHead term :=
  scanHead_iff backward (Nat.lt_succ_self _) represented

end Jihoo.NativeKernel.NativeCoreErasedCasePolicy
