import Jihoo.NativeLoanComparisonEvidence
import Jihoo.NativeLoanContextConversion

/-! Exact checked occurrences under any sequence of written binders,
applications and Strict tails. A proof ignored by the native comparison
retains its original source context, including every erased binder. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence

/-- Retained source occurrences record the exact extension of their context.
Application visits add no binders. Strict only exposes its retained tail. -/
inductive Focus : Term → List Binding → Term → Prop where
  | root : Focus source [] source
  | piDomain : Focus domain entered selected → Focus (.pi erased domain body) entered selected
  | piBody : Focus body entered selected → Focus (.pi erased domain body) (entered ++ [⟨domain,erased⟩]) selected
  | lambdaDomain : Focus domain entered selected → Focus (.lam erased domain body) entered selected
  | lambdaBody : Focus body entered selected → Focus (.lam erased domain body) (entered ++ [⟨domain,erased⟩]) selected
  | function : Focus f entered selected → Focus (.app f arg) entered selected
  | argument : Focus arg entered selected → Focus (.app f arg) entered selected
  | strictTail : Focus tail entered selected → Focus (.strict effects tail) entered selected

/-- Recover the source typing of the kept occurrence from the actual
derivation. Each scope is extended at its original annotation and erasure. -/
theorem Focus.checked_occurrence (path : Focus source entered selected)
    (typed : HasType env loans ctx mode source requested) :
    ∃ type, HasType env [] (entered ++ ctx) true selected type := by
  induction path generalizing loans ctx mode requested with
  | root => exact ⟨requested,typed.ghost []⟩
  | piDomain child ih =>
    obtain ⟨_,_,domain,_,_⟩ := typed.principalView
    exact ih domain
  | piBody child ih =>
    obtain ⟨_,_,_,body,_⟩ := typed.principalView
    simpa only [List.append_assoc,List.singleton_append] using ih body
  | lambdaDomain child ih =>
    obtain ⟨_,_,binder,_,_⟩ := typed.lamView
    cases binder with
    | intro domain _ => exact ih domain
  | lambdaBody child ih =>
    obtain ⟨_,_,_,body,_⟩ := typed.lamView
    simpa only [List.append_assoc,List.singleton_append] using ih body
  | function child ih =>
    obtain ⟨_,_,_,head,_,_,_⟩ := typed.appView
    exact ih head
  | argument child ih =>
    obtain ⟨_,_,_,_,argument,_,_⟩ := typed.appView
    exact ih argument
  | strictTail child ih =>
    obtain ⟨_,tailTyped,_⟩ := typed.principalView
    exact ih tailTyped

/-- The two checked retained occurrences can have different Strict prefixes
and different outer check modes. Under their shared written binder context,
both omitted proofs inhabit the same formed dependent proposition when
the retained operands are convertible. -/
theorem focused_common_proposition
    (firstPath : Focus leftSource entered (.node op [a,b,leftProof]))
    (secondPath : Focus rightSource entered (.node op [a',b',rightProof]))
    (first : IgnoredProposition op a b proposition)
    (second : IgnoredProposition op a' b' other)
    (firstTyped : HasType env loans ctx mode leftSource leftType)
    (secondTyped : HasType env otherLoans ctx otherMode rightSource rightType)
    (left : RawLend.Conv env a a') (right : RawLend.Conv env b b') :
    HasEvidence env (entered ++ ctx) proposition leftProof ∧ HasType env [] (entered ++ ctx) true rightProof proposition := by
  obtain ⟨_,leftOccurrence⟩ := firstPath.checked_occurrence firstTyped
  obtain ⟨_,rightOccurrence⟩ := secondPath.checked_occurrence secondTyped
  exact converted_operands_common_proposition first second (.native leftOccurrence) (.native rightOccurrence) left right

/-- Checked binder annotations along the two retained paths may be written
differently. Typed context conversion aligns the actual occurrences without
changing either erased proof term. -/
theorem focused_common_proposition_converted
    (wf : UnifiedProgram.EnvWellFormed env)
    (firstPath : Focus leftSource leftEntered (.node op [a,b,leftProof]))
    (secondPath : Focus rightSource rightEntered (.node op [a',b',rightProof]))
    (contexts : Ghost.ContextConversion env (rightEntered ++ rightContext) (leftEntered ++ leftContext))
    (first : IgnoredProposition op a b proposition)
    (second : IgnoredProposition op a' b' other)
    (firstTyped : HasType env loans leftContext mode leftSource leftType)
    (secondTyped : HasType env otherLoans rightContext otherMode rightSource rightType)
    (left : RawLend.Conv env a a') (right : RawLend.Conv env b b') :
    HasEvidence env (leftEntered ++ leftContext) proposition leftProof ∧
      HasType env [] (leftEntered ++ leftContext) true rightProof proposition := by
  obtain ⟨_,leftOccurrence⟩ := firstPath.checked_occurrence firstTyped
  obtain ⟨_,rightOccurrence⟩ := secondPath.checked_occurrence secondTyped
  exact converted_operands_common_proposition first second (.native leftOccurrence)
    (.native (rightOccurrence.ghostContext wf contexts)) left right

end Jihoo.NativeKernel.Environment.LoanTyping.ComparisonEvidence
