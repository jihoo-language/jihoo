import Jihoo.NativeDependentErasedGiveRelation
import Jihoo.NativeLoanComputationPreservation

set_option maxUniverseOffset 40

/-! The typed Take equation enters the original continuation with an
interpreted owner and evidence in its dependent fiber. The reduction result
is interpreted in the caller's original type. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

def erasedTakeContinuation (A : Ty env Γ (.type ⟨0,by decide⟩))
    (proof : Ty env (Contextual.extend Γ A.code) .proposition)
    (result : Ty env Γ sort) : Ty env Γ
      ((Finite.LevelSort.type ⟨0,by decide⟩).pi (Finite.LevelSort.proposition.pi sort)) :=
  pi A (pi proof (result.substitution fun point => point.1.1))

/-- Applying the two arguments selected by the checked Take equation gives
the actual dependent continuation result. The original result fiber is
preserved after both arguments are substituted. -/
theorem checked_erased_take_realizes_result (wf : UnifiedProgram.EnvWellFormed env)
    (Γ : Ctx env) (A : Ty env Γ.meaning (.type ⟨0,by decide⟩))
    (evidenceType : Ty env (Contextual.extend Γ.meaning A.code) .proposition)
    (result : Ty env Γ.meaning sort)
    {ownerMeaning : Contextual.Tm A.code}
    {proofMeaning : Contextual.Tm (evidenceType.substitution (Contextual.pair Contextual.identity ownerMeaning)).code}
    {continuationMeaning : Contextual.Tm (erasedTakeContinuation A evidenceType result).code}
    (typed : LoanTyping.HasType env loans ctx mode
      (.take (.give true motive source proof) (.lam false ownerDomain (.lam true proofDomain body))) requested)
    (owned : Realizes Γ A source ownerMeaning)
    (evidence : Realizes Γ (evidenceType.substitution (Contextual.pair Contextual.identity ownerMeaning)) proof proofMeaning)
    (callback : Realizes Γ (erasedTakeContinuation A evidenceType result)
      (.lam false ownerDomain (.lam true proofDomain body)) continuationMeaning) :
    let continuation := Term.lam false ownerDomain (.lam true proofDomain body)
    let applied := Term.app (.app continuation source) proof
    LoanTyping.HasType env [] ctx true applied requested ∧
      ∃ meaning : Contextual.Tm result.code, Realizes Γ result applied meaning := by
  let underBoth : Ty env (Contextual.extend (Contextual.extend Γ.meaning A.code) evidenceType.code) sort :=
    result.substitution fun point => point.1.1
  let ownerSub := Contextual.pair Contextual.identity ownerMeaning
  have first := application_realizes Γ A (pi evidenceType underBoth) callback owned
  have specialized : Realizes Γ
      (pi (evidenceType.substitution ownerSub) (underBoth.substitution (Contextual.lift ownerSub)))
      (.app (.lam false ownerDomain (.lam true proofDomain body)) source)
      (Contextual.app (A := A.code) (B := (pi evidenceType underBoth).code) continuationMeaning ownerMeaning) := by
    exact first
  have combined := application_realizes Γ (evidenceType.substitution ownerSub) (underBoth.substitution (Contextual.lift ownerSub))
    specialized evidence
  exact ⟨LoanTyping.take_give_ghost_preservation wf typed,_,combined⟩

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
