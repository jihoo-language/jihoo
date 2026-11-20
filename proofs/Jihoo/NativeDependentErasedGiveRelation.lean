import Jihoo.NativeDependentRelationalContexts
import Jihoo.NativeLoanComparisonEvidence

set_option maxUniverseOffset 40

/-! An owner returned with erased evidence is a dependent subtype of its
original owner at Type0. The witness is retained in the source realization
and has no effect on the semantic owner value. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

open Finite (Carrier Universe decode0 decodeProp)

private def embedOwner (code : Universe (.type ⟨0,by decide⟩)) : decode0 code → Carrier code :=
  match code with
  | .type0 _ => ULift.up

private def unembedOwner (code : Universe (.type ⟨0,by decide⟩)) : Carrier code → decode0 code :=
  match code with
  | .type0 _ => ULift.down

private theorem owner_roundtrip (code : Universe (.type ⟨0,by decide⟩)) (value : Carrier code) :
    embedOwner code (unembedOwner code value) = value := by
  cases code
  rfl

private theorem decodeEvidence (code : Universe .proposition) : Carrier code → decodeProp code :=
  match code with
  | .proposition _ => fun value => value.down.down

private def encodeEvidence (code : Universe .proposition) : decodeProp code → Carrier code :=
  match code with
  | .proposition _ => fun proof => ⟨⟨proof⟩⟩

private theorem evidence_irrelevant (code : Universe .proposition) (first second : Carrier code) :
    first = second := by
  cases code
  cases first with
  | up left =>
    cases second with
    | up right =>
      cases left with
      | up firstProof =>
        cases right with
        | up secondProof =>
          exact congrArg ULift.up (congrArg PLift.up (Subsingleton.elim firstProof secondProof))

def erasedBack (A : Ty env Γ (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ A.code) .proposition) : Ty env Γ (.type ⟨0,by decide⟩) where
  code point := .type0 { owner : decode0 (A.code point) //
    decodeProp (result.code ⟨point,embedOwner _ owner⟩) }
  realizes point term value :=
    let ownerValue := embedOwner (A.code point) value.down.val
    ∃ motive owner evidence,RawLend.Conv env term (.give true motive owner evidence) ∧
      A.realizes point owner ownerValue ∧
      result.realizes ⟨point,ownerValue⟩ evidence (encodeEvidence _ value.down.property)
  conversion := by
    intro point first second value converted
    constructor
    · rintro ⟨motive,owner,evidence,shape,owned,proved⟩
      exact ⟨motive,owner,evidence,converted.symm.trans shape,owned,proved⟩
    · rintro ⟨motive,owner,evidence,shape,owned,proved⟩
      exact ⟨motive,owner,evidence,converted.trans shape,owned,proved⟩

def erasedGiven (A : Ty env Γ (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ A.code) .proposition) (point : Γ)
    (owner : Carrier (A.code point)) (proof : Carrier (result.code ⟨point,owner⟩)) :
    Carrier ((erasedBack A result).code point) :=
  ⟨⟨unembedOwner _ owner,by
    rw [owner_roundtrip]
    exact decodeEvidence _ proof⟩⟩

private theorem erased_given_realizes (A : Ty env Γ (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ A.code) .proposition) (point : Γ)
    {ownerValue : Carrier (A.code point)} {proofValue : Carrier (result.code ⟨point,ownerValue⟩)}
    (owned : A.realizes point owner ownerValue) (proved : result.realizes ⟨point,ownerValue⟩ evidence proofValue)
    (motive : Term) :
    (erasedBack A result).realizes point (.give true motive owner evidence) (erasedGiven A result point ownerValue proofValue) := by
  refine ⟨motive,owner,evidence,.refl _,?_,?_⟩
  · simpa only [erasedGiven,owner_roundtrip] using owned
  · have transported (ownerProjection : Carrier (A.code point)) (same : ownerProjection = ownerValue)
        (proofProjection : Carrier (result.code ⟨point,ownerProjection⟩)) :
        result.realizes ⟨point,ownerProjection⟩ evidence proofProjection := by
      subst ownerProjection
      rw [evidence_irrelevant _ proofProjection proofValue]
      exact proved
    exact transported _ (owner_roundtrip _ _) _

theorem erased_give_realizes (Γ : Ctx env) (A : Ty env Γ.meaning (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ.meaning A.code) .proposition)
    {ownerMeaning : Contextual.Tm A.code}
    {evidenceMeaning : Contextual.Tm (result.substitution (Contextual.pair Contextual.identity ownerMeaning)).code}
    (owned : Realizes Γ A owner ownerMeaning)
    (proved : Realizes Γ (result.substitution (Contextual.pair Contextual.identity ownerMeaning)) evidence evidenceMeaning)
    (motive : Term) :
    Realizes Γ (erasedBack A result) (.give true motive owner evidence)
      (fun point => erasedGiven A result point (ownerMeaning point) (evidenceMeaning point)) := by
  intro values point assigned
  simpa only [Term.give,Term.subst,substArgs,Op.binders,liftSub] using
    erased_given_realizes A result point (owned values point assigned) (proved values point assigned) (motive.subst values)

theorem erased_given_evidence_agrees (A : Ty env Γ (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ A.code) .proposition) (point : Γ)
    {owner : Carrier (A.code point)} (first second : Carrier (result.code ⟨point,owner⟩)) :
    erasedGiven A result point owner first = erasedGiven A result point owner second := by
  apply congrArg ULift.up
  exact Subtype.ext rfl

/-- The actual checked Give derivations recover their dependent evidence
proposition. Returning either valid proof gives the same interpreted owner
to a dependent family at any finite result sort. -/
theorem checked_erased_give_applications_agree (Γ : Ctx env) (A : Ty env Γ.meaning (.type ⟨0,by decide⟩))
    (result : Ty env (Contextual.extend Γ.meaning A.code) .proposition)
    (returns : Ty env (Contextual.extend Γ.meaning (erasedBack A result).code) sort)
    {ownerMeaning : Contextual.Tm A.code}
    {firstMeaning secondMeaning : Contextual.Tm (result.substitution (Contextual.pair Contextual.identity ownerMeaning)).code}
    {functionMeaning : Contextual.Tm (pi (erasedBack A result) returns).code}
    (left : LoanTyping.HasType env loans ctx mode (.give true motive owner first) leftType)
    (right : LoanTyping.HasType env otherLoans ctx otherMode (.give true motive owner second) rightType)
    (function : Realizes Γ (pi (erasedBack A result) returns) family functionMeaning)
    (owned : Realizes Γ A owner ownerMeaning)
    (firstProof : Realizes Γ (result.substitution (Contextual.pair Contextual.identity ownerMeaning)) first firstMeaning)
    (secondProof : Realizes Γ (result.substitution (Contextual.pair Contextual.identity ownerMeaning)) second secondMeaning) :
    LoanTyping.ComparisonEvidence.HasEvidence env ctx (.app motive owner) first ∧
    LoanTyping.HasType env [] ctx true second (.app motive owner) ∧
    ∃ argument : Contextual.Tm (erasedBack A result).code,
      let fiber := returns.substitution (Contextual.pair Contextual.identity argument)
      ∃ meaning : Contextual.Tm fiber.code,
        Realizes Γ fiber (.app family (.give true motive owner first)) meaning ∧
        Realizes Γ fiber (.app family (.give true motive owner second)) meaning := by
  have ⟨formed,proofLeft,proofRight⟩ := LoanTyping.ComparisonEvidence.SharedOperands.common_proposition
    .give (.native (left.ghost [])) (.native (right.ghost []))
  have firstValue := erased_give_realizes Γ A result owned firstProof motive
  have secondValue := erased_give_realizes Γ A result owned secondProof motive
  have agrees :
      (fun point => erasedGiven A result point (ownerMeaning point) (firstMeaning point)) =
      (fun point => erasedGiven A result point (ownerMeaning point) (secondMeaning point)) := by
    funext point
    exact erased_given_evidence_agrees A result point _ _
  rw [← agrees] at secondValue
  exact ⟨⟨formed,proofLeft⟩,proofRight,_,_,
    application_realizes Γ _ returns function firstValue,
    application_realizes Γ _ returns function secondValue⟩

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
