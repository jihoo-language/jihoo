import Jihoo.NativeLoanLocalUniqueness
import Jihoo.NativeLoanSubstitutionShapes
import Jihoo.NativeLoanLendInputs

/-! Functionality for the complete loan-indexed judgment. Strong induction is
on the original source skeleton, while certified non-lambda substitutions may
grow its specialized reader and continuation. Ownership and outlives gates
supply the missing callback-head invariant from actual source subchecks. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

private theorem source_finish_unique (wf : UnifiedProgram.EnvWellFormed env)
    (ih : ∀ source : Term,sizeOf source < sizeOf (Term.node op children) →
      ∀ σ,UniqueSubstitution env σ → RenamedUnique env (source.subst σ))
    (certified : UniqueSubstitution env σ) : FinishUnique env ((Term.node op children).subst σ) := by
  intro loans ctx mode type typed owner domain readerBody first again body matched
  have actual : HasType env loans ctx mode
      (.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))) type := matched ▸ typed
  obtain ⟨ownerType,valueType,ownerTyped,owned,readTyped,outlived⟩ := actual.explicitLendInputs wf
  obtain ⟨sourceOwner,sourceReader,sourceContinuation,head,layout,ownerEq,readerEq,continuationEq⟩ := subst_lend_shape matched
  obtain ⟨sourceDomain,sourceReaderBody,sourceReaderEq,domainEq,readerBodyEq⟩ :=
    subst_lambda_shape certified.noLambda readerEq.symm
  obtain ⟨sourceFirst,sourceInner,sourceContinuationEq,firstEq,innerEq⟩ :=
    subst_lambda_shape certified.noLambda continuationEq.symm
  obtain ⟨sourceAgain,sourceBody,sourceInnerEq,againEq,bodyEq⟩ :=
    subst_lambda_shape certified.liftOne.noLambda innerEq.symm
  subst op
  subst children
  subst sourceReader
  subst sourceContinuation
  subst sourceInner
  have ownerUnique : RenamedUnique env owner := by
    rw [ownerEq]
    exact ih sourceOwner (by simp;omega) σ certified
  have ownerHead : NoLambdaHead owner := ownerTyped.owned_noLambdaHead wf owned
  have referenceCertified : UniqueSubstitution env (prependSub (.borrow owner) σ) :=
    certified.prepend (borrow_renamed_unique ownerUnique) (by trivial)
  have readerUnique : RenamedUnique env (Lending.read owner readerBody) := by
    rw [readerBodyEq,read_substitution]
    exact ih sourceReaderBody (by simp;omega) _ referenceCertified
  have readerHead : NoLambdaHead (Lending.read owner readerBody) := readTyped.outlived_noLambdaHead wf outlived
  have finishCertified : UniqueSubstitution env
      (prependSub owner (prependSub (Lending.read owner readerBody) σ)) :=
    (certified.prepend readerUnique readerHead).prepend ownerUnique ownerHead
  have sourceBodyEq : body = sourceBody.subst (liftSub 2 σ) := by
    simpa only [liftSub] using bodyEq
  rw [sourceBodyEq,finish_substitution]
  intro targetCtx targetLoans targetLoans' targetMode targetMode' targetFirst targetSecond targetLeft targetRight
  exact (ih sourceBody (by simp;omega) _ finishCertified).original targetLeft targetRight

/-- All source syntax remains functional under arbitrary certified images,
including all renamings. The final public uniqueness theorem instantiates this
with variables; no callback or final-output uniqueness premise remains. -/
theorem renamed_unique_substitution (wf : UnifiedProgram.EnvWellFormed env) (term : Term) :
    ∀ σ,UniqueSubstitution env σ → RenamedUnique env (term.subst σ) := by
  have measureWF : WellFounded (fun first second : Term => sizeOf first < sizeOf second) := (measure sizeOf).wf
  induction term using measureWF.induction with
  | h term ih =>
      intro σ certified ρ ctx loans loans' mode mode' first second left right
      cases term with
      | var index =>
          simp only [Term.subst] at left right
          exact certified.unique index ρ left right
      | node op children =>
          rw [Term.rename_subst] at left right
          have renamed := certified.renaming ρ
          have smaller : ∀ source ∈ children,sizeOf source < sizeOf (Term.node op children) := by
            intro source member
            have bound := List.sizeOf_lt_of_mem member
            simp only [Term.node.sizeOf_spec]
            omega
          apply unique_of_inputs wf (term := (Term.node op children).subst (fun index => (σ index).rename ρ)) ?_
            (source_finish_unique wf ih renamed) left right
          intro value member targetCtx targetLoans targetLoans' targetMode targetMode' targetFirst targetSecond targetLeft targetRight
          simp only [Term.subst,directChildren] at member
          obtain ⟨source,found,depth,rfl⟩ := substArgs_member member
          exact (ih source (smaller source found) _ (renamed.lift depth)).original targetLeft targetRight

/-- Type uniqueness for all 64 loan-indexed rules, across CODE/GHOST and any
permission stacks at the same context, under the installed family conversion. -/
theorem HasType.unique (left : HasType env loans ctx mode term first)
    (wf : UnifiedProgram.EnvWellFormed env) (right : HasType env loans' ctx mode' term second) :
    Conv env first second := by
  have allRenamings := renamed_unique_substitution wf term Term.var UniqueSubstitution.identity
  exact allRenamings.original (by simpa only [Term.subst_id] using left)
    (by simpa only [Term.subst_id] using right)

theorem Binder.unique (left : Binder env loans ctx erased domain first)
    (wf : UnifiedProgram.EnvWellFormed env) (right : Binder env loans' ctx erased domain second) : first = second := by
  cases left with
  | intro typed allowed => cases right with
    | intro typed' allowed' => exact (typed.unique wf typed').sort_injective wf.admissible

theorem HasType.sort_unique {first second : SortTag}
    (left : HasType env loans ctx mode term first.term) (wf : UnifiedProgram.EnvWellFormed env)
    (right : HasType env loans' ctx mode' term second.term) : first = second :=
  (left.unique wf right).sort_injective wf.admissible

end Jihoo.NativeKernel.Environment.LoanTyping
