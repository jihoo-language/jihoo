import Jihoo.NativeLoanPureTyping
import Jihoo.NativeCoreIdentical

/-! Core.identical ignores evidence in three constructors. Recovering the
well-formed proposition of each skipped occurrence from the source checker
provides the typing premise needed for proof irrelevance. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

open NativeArena
open NativeCoreCompare (project projectArgs Shape FullyRetained header_injective project_injective_of_fully_retained)
open ACU.Canonical (rank payload)

def HasEvidence (env : Environment) (ctx : Context) (proposition evidence : Term) : Prop :=
  HasType env [] ctx true proposition .prop ∧ HasType env [] ctx true evidence proposition

def RetainsEvidenceTyping (env : Environment) (ctx : Context) : Term → Prop
  | .usub a b proof => HasEvidence env ctx (.lt b (.uadd a (.natural 1))) proof
  | .pack predicate value proof => HasEvidence env ctx (.app predicate value) proof
  | .give true motive owner proof => HasEvidence env ctx (.app motive owner) proof
  | _ => True

private theorem formed_application
    (function : HasType env loans ctx true motive (.pi false domain .prop))
    (argument : HasType env otherLoans ctx mode value domain) :
    HasType env [] ctx true (.app motive value) .prop := by
  have application := HasType.app (function.ghost []) (argument.ghost []) (Or.inl rfl)
  simpa only [Term.subst, substArgs] using application

/-- The original typing derivation supplies the formation and evidence
judgments for every ignored root field, including through conversion. -/
theorem checked_evidence (typed : HasType env loans ctx mode term type) : RetainsEvidenceTyping env ctx term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term _ _ => RetainsEvidenceTyping env ctx term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | exact True.intro | assumption | skip
  case usub left right proof _ _ _ =>
      exact ⟨.lt (right.ghost []) (.uadd (left.ghost []) (.natural (by decide))), proof.ghost []⟩
  case pack predicate value proof _ _ _ =>
      exact ⟨formed_application predicate value, proof.ghost []⟩
  case give _ _ _ _ _ _ erased _ owner _ motive _ proof _ _ _ =>
      cases erased
      · trivial
      · exact ⟨formed_application motive owner, proof.ghost []⟩
  case dataElim => split <;> trivial

theorem expanded_checked_evidence (typed : PureTyping.HasType env ctx term type) :
    RetainsEvidenceTyping env ctx term := by
  induction typed with
  | native original => exact checked_evidence original
  | convert _ _ _ checked => exact checked
  | pi | lam | app => trivial

/-- A comparison of corresponding roots with exactly the same retained
operands, naming their ignored proofs and their dependent proposition. -/
inductive SharedOperands : Term → Term → Term → Term → Term → Prop where
  | subtract : SharedOperands (.usub a b left) (.usub a b right) (.lt b (.uadd a (.natural 1))) left right
  | pack : SharedOperands (.pack predicate value left) (.pack predicate value right)
      (.app predicate value) left right
  | give : SharedOperands (.give true motive owner left) (.give true motive owner right)
      (.app motive owner) left right

theorem SharedOperands.project_eq (operands : SharedOperands first second proposition left right) :
    project first = project second := by
  cases operands <;>
    simp only [project, projectArgs, NativeCoreCompare.syntaxView, NativeCoreCompare.conversionChildren] <;> rfl

/-- When comparison skips differing evidence at corresponding checked
roots, both proofs inhabit the same well-formed original proposition. -/
theorem SharedOperands.common_proposition
    (operands : SharedOperands first second proposition left right)
    (leftTyped : PureTyping.HasType env ctx first leftType)
    (rightTyped : PureTyping.HasType env ctx second rightType) :
    HasType env [] ctx true proposition .prop ∧
      HasType env [] ctx true left proposition ∧ HasType env [] ctx true right proposition := by
  have firstEvidence := expanded_checked_evidence leftTyped
  have secondEvidence := expanded_checked_evidence rightTyped
  cases operands <;> exact ⟨firstEvidence.1, firstEvidence.2, secondEvidence.2⟩

/-- The proposition belonging to the third, ignored child of a retained
constructor header and its first two operands. -/
inductive IgnoredProposition : Op → Term → Term → Term → Prop where
  | subtract : IgnoredProposition .usub a b (.lt b (.uadd a (.natural 1)))
  | pack : IgnoredProposition .pack predicate value (.app predicate value)
  | give : IgnoredProposition (.give true) motive owner (.app motive owner)

private theorem IgnoredProposition.arity (field : IgnoredProposition op a b proposition) : op.arity = 3 := by
  cases field <;> rfl

private theorem IgnoredProposition.project_node (field : IgnoredProposition op a b proposition) (proof : Term) :
    project (.node op [a, b, proof]) = .node (rank op, payload op) [project a, project b] := by
  cases field <;>
    simp only [project, projectArgs, NativeCoreCompare.syntaxView, NativeCoreCompare.conversionChildren] <;> rfl

/-- Live identity of checked roots with ignored evidence supplies a common
well-formed proposition, provided identity retained both operand subtrees
in full. The unmatched proof children are typed by the original derivations. -/
theorem live_identity_common_proposition
    (firstField : IgnoredProposition firstOp firstA firstB firstType)
    (secondField : IgnoredProposition secondOp secondA secondB secondType)
    (firstShape : Represents arena leftRoot (.node firstOp [firstA, firstB, firstProof]))
    (secondShape : Represents arena rightRoot (.node secondOp [secondA, secondB, secondProof]))
    (firstTyped : PureTyping.HasType env ctx (.node firstOp [firstA, firstB, firstProof]) firstResult)
    (secondTyped : PureTyping.HasType env ctx (.node secondOp [secondA, secondB, secondProof]) secondResult)
    (firstKept : FullyRetained firstA ∧ FullyRetained firstB)
    (secondKept : FullyRetained secondA ∧ FullyRetained secondB)
    (compared : NativeCoreIdentical.runArena arena limit depth initial leftRoot rightRoot = (.ok true, spent)) :
    firstType = secondType ∧ HasType env [] ctx true firstType .prop ∧
      HasType env [] ctx true firstProof firstType ∧ HasType env [] ctx true secondProof firstType := by
  have matched := (NativeCoreIdentical.runArena_refines firstShape secondShape compared).mp rfl
  rw [firstField.project_node, secondField.project_node] at matched
  obtain ⟨header, kept⟩ := Shape.node.inj matched
  have sameOp := header_injective header (firstField.arity.trans secondField.arity.symm)
  simp only [List.cons.injEq, and_true] at kept
  have sameA := project_injective_of_fully_retained firstKept.1 secondKept.1 kept.1
  have sameB := project_injective_of_fully_retained firstKept.2 secondKept.2 kept.2
  subst secondOp
  subst secondA
  subst secondB
  cases firstField <;> cases secondField
  · exact ⟨rfl, SharedOperands.subtract.common_proposition firstTyped secondTyped⟩
  · exact ⟨rfl, SharedOperands.pack.common_proposition firstTyped secondTyped⟩
  · exact ⟨rfl, SharedOperands.give.common_proposition firstTyped secondTyped⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence
