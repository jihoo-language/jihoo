import Jihoo.NativeLoanPureTyping
import Jihoo.NativeLoanCheckerSoundness
import Jihoo.NativeCoreIdentical
import Jihoo.NativeCoreComparisonOccurrences
import Jihoo.NativeFamilyIotaNeutralCoherence

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

/-- Corresponding retained operands may already be related by computation.
Congruence transports the actual proposition of the erased evidence along
both operand conversions. -/
theorem IgnoredProposition.converted (first : IgnoredProposition op a b proposition)
    (second : IgnoredProposition op a' b' other)
    (left : RawLend.Conv env a a') (right : RawLend.Conv env b b') :
    RawLend.Conv env proposition other := by
  cases first <;> cases second
  · exact .node .lt (.cons right (.cons (.node .uadd (.cons left (.cons (.refl _) .nil))) .nil))
  · exact .node .app (.cons left (.cons right .nil))
  · exact .node .app (.cons left (.cons right .nil))

/-- The source derivations place both erasure-sensitive operands in one
formed proposition, even when the retained fields are only convertible. -/
theorem converted_operands_common_proposition
    (first : IgnoredProposition op a b proposition) (second : IgnoredProposition op a' b' other)
    (firstTyped : PureTyping.HasType env ctx (.node op [a,b,leftProof]) firstType)
    (secondTyped : PureTyping.HasType env ctx (.node op [a',b',rightProof]) secondType)
    (left : RawLend.Conv env a a') (right : RawLend.Conv env b b') :
    HasEvidence env ctx proposition leftProof ∧ HasType env [] ctx true rightProof proposition := by
  have propositions := first.converted second left right
  have firstEvidence := expanded_checked_evidence firstTyped
  have secondEvidence := expanded_checked_evidence secondTyped
  cases first <;> cases second <;> exact ⟨firstEvidence,secondEvidence.2.convert propositions.symm⟩

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

/-- An accepted live identity comparison retains the original aligned
subtrees and their omitted evidence positions under arbitrary binders. -/
theorem live_identity_aligns_occurrences
    (first : Represents arena left firstTerm) (second : Represents arena right secondTerm)
    (accepted : NativeCoreIdentical.runArena arena limit depth initial left right = (.ok true,spent)) :
    NativeCoreCompare.OccurrenceAlignment firstTerm secondTerm :=
  NativeCoreCompare.project_aligns_occurrences first.wellFormed second.wellFormed
    ((NativeCoreIdentical.runArena_refines first second accepted).mp rfl)

/-- Actual checking of two dependent types exposes the ignored arguments
under the original Pi binder. Their source derivations retain the common
proposition when the two visited operands are convertible. -/
theorem pi_application_common_proposition
    (first : IgnoredProposition op a b proposition) (second : IgnoredProposition op a' b' other)
    (firstTyped : HasType env loans ctx mode (.pi erased domain (.app family (.node op [a,b,leftProof]))) leftType)
    (secondTyped : HasType env otherLoans ctx otherMode
      (.pi erased domain (.app family (.node op [a',b',rightProof]))) rightType)
    (left : RawLend.Conv env a a') (right : RawLend.Conv env b b') :
    HasEvidence env (⟨domain,erased⟩ :: ctx) proposition leftProof ∧
      HasType env [] (⟨domain,erased⟩ :: ctx) true rightProof proposition := by
  obtain ⟨_,_,_,leftBody,_⟩ := firstTyped.principalView
  obtain ⟨_,_,_,rightBody,_⟩ := secondTyped.principalView
  obtain ⟨_,_,_,_,leftArgument,_,_⟩ := leftBody.appView
  obtain ⟨_,_,_,_,rightArgument,_,_⟩ := rightBody.appView
  exact converted_operands_common_proposition first second (.native (leftArgument.ghost []))
    (.native (rightArgument.ghost [])) left right

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence.Examples

open NativeArena NativeProgramWire

private def zero : Term := .natural 0
private def one : Term := .natural 1
private def predicate : Term := .lam false .u64 (.lt (.var 0) one)
private def familyDomain : Term := .pi false (.refine predicate) (.univ 0)
private def pack (evidence : Term) : Term := .pack predicate zero evidence
private def dependentType (evidence : Term) : Term :=
  .pi false familyDomain (.app (.var 0) (pack evidence))

private def arena : Arena := #[
  .node .u64 [], .var 0, .node (.natural 0) [], .node (.natural 1) [],
  .node .lt [1, 3], .node (.lam false) [0, 4], .node .refine [5],
  .node (.universe 0) [], .node (.pi false) [6, 7],
  .node .zeroLe [2], .node .decide [2, 3], .node .pack [5, 2, 9], .node .pack [5, 2, 10],
  .node .app [1, 11], .node .app [1, 12], .node (.pi false) [8, 13], .node (.pi false) [8, 14]]

private theorem emptyWorld : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed

private theorem different_evidence :
    ¬ FamilyIota.Extended.Conv empty (.zeroLe zero) (.decide zero one) :=
  fun converted => FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
    (by intro same; cases same) converted emptyWorld.admissible

/-- Both domains are actual checked closed types. Native graph identity
equates them because it skips the packed evidence under the bound family's
application. The full raw conversion keeps that field, even for valid proofs
of the same dependent proposition. -/
theorem checked_closed_types_need_typed_evidence_irrelevance :
    HasType empty [] [] true (dependentType (.zeroLe zero)) (.univ 1) ∧
    HasType empty [] [] true (dependentType (.decide zero one)) (.univ 1) ∧
    Represents arena 15 (dependentType (.zeroLe zero)) ∧
    Represents arena 16 (dependentType (.decide zero one)) ∧
    (NativeCoreIdentical.runArena arena 128 24 0 15 16).1 = .ok true ∧
    ¬ RawValue.Conv empty (dependentType (.zeroLe zero)) (dependentType (.decide zero one)) := by
  refine ⟨Checker.infer_sound (fuel := 64) (by cbv), Checker.infer_sound (fuel := 64) (by cbv),
    decode_sound (fuel := 12) (by rfl), decode_sound (fuel := 12) (by rfl), by cbv, ?_⟩
  intro comparable
  have projected := comparable.projected emptyWorld.admissible
  have first : Semantics.ValueErasure.Loan.project empty (dependentType (.zeroLe zero)) =
      dependentType (.zeroLe zero) := by cbv
  have second : Semantics.ValueErasure.Loan.project empty (dependentType (.decide zero one)) =
      dependentType (.decide zero one) := by cbv
  rw [first, second] at projected
  have bodies := (projected.pi_injective emptyWorld.admissible).2.2
  have packs := (bodies.family_application_injective emptyWorld.admissible).2
  obtain ⟨_, arguments⟩ := packs.full_rigid_node_injective rfl rfl emptyWorld.admissible
  cases arguments with
  | cons _ rest =>
    cases rest with
    | cons _ rest =>
      cases rest with
      | cons evidence _ => exact different_evidence evidence

/-- The deployed identity path exposes the same Pack position in both
checked dependent types, even though their proof subtrees differ. -/
theorem checked_comparison_aligns_hidden_pack_proofs :
    NativeCoreCompare.OccurrenceAlignment (dependentType (.zeroLe zero)) (dependentType (.decide zero one)) := by
  obtain ⟨_,_,first,second,identity,_⟩ := checked_closed_types_need_typed_evidence_irrelevance
  rcases found : NativeCoreIdentical.runArena arena 128 24 0 15 16 with ⟨answer,spent⟩
  simp only [found] at identity
  subst answer
  exact live_identity_aligns_occurrences first second found

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence.Examples
