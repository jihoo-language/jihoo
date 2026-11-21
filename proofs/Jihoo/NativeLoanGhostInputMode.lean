import Jihoo.NativeLoanGhostPromotion
import Jihoo.NativeEnvironmentDelta

/-! Formation and evidence constructors with an entirely erased
premise list may reuse their ghost visits in either outer mode. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.GhostInputMode

def eligible : Op → Bool
  | .array | .lt | .eq | .refl | .pi _ | .refine | .buffer | .ref | .ind _ _
  | .transport | .ltAdd | .ltCancel | .ltLe | .decide => true
  | _ => false

def Head : Term → Prop
  | .node op _ => eligible op = true
  | .var _ => False

theorem Head.expanded (eligibleHead : eligible op = true) :
    Head (EnvironmentDelta.expand env (.node op args)) := by
  cases op <;> simp_all only [EnvironmentDelta.expand,Head,eligible,Bool.false_eq_true]

private theorem ghostBinder (binder : Binder env old ctx erased type sort) :
    Binder env target ctx erased type sort := by
  cases binder with
  | intro typed allowed => exact .intro (typed.ghost target) allowed

/-- The original type is preserved when only the outer mode changes.
Each child derivation is replayed in ghost mode at the requested stack. -/
theorem recheck (typed : HasType env old ctx original term type) (head : Head term) :
    HasType env target ctx mode term type := by
  revert head
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ => Head term → HasType env target ctx mode term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (next head => simp only [Head,eligible] at head; contradiction)
  case array bound ih head => exact .array (bound.ghost target)
  case lt left right ihLeft ihRight head => exact .lt (left.ghost target) (right.ghost target)
  case eq left right ihLeft ihRight head => exact .eq (left.ghost target) (right.ghost target)
  case pi domain body ihDomain ihBody head => exact .pi (ghostBinder domain) (body.ghost target)
  case refl value ih head => exact .refl (value.ghost target)
  case decide first second ordered head => exact .decide first second ordered
  case decideConverted left right first second firstFits secondFits ordered ihLeft ihRight head =>
    exact .decideConverted (left.ghost target) (right.ghost target) first second firstFits secondFits ordered
  case ltAdd left right shift proof ihLeft ihRight ihShift ihProof head =>
    exact .ltAdd (left.ghost target) (right.ghost target) (shift.ghost target) (proof.ghost target)
  case ltCancel left right shift proof ihLeft ihRight ihShift ihProof head =>
    exact .ltCancel (left.ghost target) (right.ghost target) (shift.ghost target) (proof.ghost target)
  case ltLe left middle right first second ihLeft ihMiddle ihRight ihFirst ihSecond head =>
    exact .ltLe (left.ghost target) (middle.ghost target) (right.ghost target) (first.ghost target) (second.ghost target)
  case transport family equality payload ihFamily ihEquality ihPayload head =>
    exact .transport (family.ghost target) (equality.ghost target) (payload.ghost target)
  case «refine» predicate ih head => exact .refine (predicate.ghost target)
  case ind found arity size members ih head =>
    exact .ind found arity size (fun index member => (members index member).ghost target)
  case buffer bound ih head => exact .buffer (bound.ghost target)
  case refBuffer bound ih head => exact .refBuffer (bound.ghost target)
  case refOwned formation owned ih head => exact .refOwned (formation.ghost target) owned
  case convert original converted ih head => exact (ih head).convert converted
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found isData boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches head
    cases analysis <;> simp [Head,eligible] at head

end Jihoo.NativeKernel.Environment.LoanTyping.GhostInputMode
