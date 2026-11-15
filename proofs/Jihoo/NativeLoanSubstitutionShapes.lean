import Jihoo.NativeLoanUniquenessSubstitutions

/-! Source skeleton inversion under the hereditary substitutions used by the
Loan64 functionality proof. Images can be arbitrary certified terms, while
ownership and outlives gates rule out newly exposed callback lambda heads. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem NoLambdaHead.substitution {term : Term} {σ : Nat → Term} (head : NoLambdaHead term)
    (images : ∀ index,NoLambdaHead (σ index)) : NoLambdaHead (term.subst σ) := by
  cases term with
  | var index => simpa only [Term.subst] using images index
  | node op children => cases op <;> simp_all only [Term.subst,NoLambdaHead]

theorem subst_lambda_shape {term domain body : Term} {erased : Bool} {σ : Nat → Term} (images : ∀ index,NoLambdaHead (σ index))
    (matched : term.subst σ = .lam erased domain body) :
    ∃ sourceDomain sourceBody,term = .lam erased sourceDomain sourceBody ∧
      domain = sourceDomain.subst σ ∧ body = sourceBody.subst (liftSubOne σ) := by
  cases term with
  | var index =>
      have head := images index
      simp only [Term.subst] at matched
      rw [matched] at head
      exact False.elim head
  | node op children =>
      simp only [Term.subst,Term.lam] at matched
      obtain ⟨sameHead,sameArguments⟩ := Term.node.inj matched
      subst op
      have length : children.length = 2 := by
        have count := congrArg List.length sameArguments
        simpa only [substArgs_length,List.length_cons,List.length_nil] using count
      cases children with
      | nil => simp at length
      | cons sourceDomain children => cases children with
        | nil => simp at length
        | cons sourceBody children => cases children with
          | cons extra rest => simp only [List.length_cons] at length;omega
          | nil =>
              simp only [substArgs,Op.binders,liftSub] at sameArguments
              obtain ⟨domainEq,rest⟩ := List.cons.inj sameArguments
              have bodyEq := (List.cons.inj rest).1
              exact ⟨sourceDomain,sourceBody,rfl,domainEq.symm,bodyEq.symm⟩

theorem substArgs_member (member : value ∈ substArgs op σ offset children) :
    ∃ source ∈ children,∃ depth,value = source.subst (liftSub depth σ) := by
  induction children generalizing offset with
  | nil => simp only [substArgs,List.not_mem_nil] at member
  | cons source children ih =>
      simp only [substArgs,List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨source,by simp,_,rfl⟩
      · obtain ⟨original,found,depth,same⟩ := ih member
        exact ⟨original,by simp [found],depth,same⟩

theorem substArgs_renamed_unique
    (childrenUnique : ∀ source ∈ children,∀ σ,UniqueSubstitution env σ → RenamedUnique env (source.subst σ))
    (certified : UniqueSubstitution env σ) :
    ∀ value ∈ substArgs op σ offset children,RenamedUnique env value := by
  intro value member
  obtain ⟨source,found,depth,rfl⟩ := substArgs_member member
  exact childrenUnique source found _ (certified.lift depth)

 theorem subst_lend_shape {op : Op} {children : List Term} {σ : Nat → Term}
    (matched : (Term.node op children).subst σ = .lend owner reader continuation) :
    ∃ sourceOwner sourceReader sourceContinuation,op = .lend ∧
      children = [sourceOwner,sourceReader,sourceContinuation] ∧
      owner = sourceOwner.subst σ ∧ reader = sourceReader.subst σ ∧ continuation = sourceContinuation.subst σ := by
  simp only [Term.subst,Term.lend] at matched
  obtain ⟨sameHead,sameArguments⟩ := Term.node.inj matched
  subst op
  have length : children.length = 3 := by
    have count := congrArg List.length sameArguments
    simpa only [substArgs_length,List.length_cons,List.length_nil] using count
  cases children with
  | nil => simp at length
  | cons sourceOwner children => cases children with
    | nil => simp at length
    | cons sourceReader children => cases children with
      | nil => simp at length
      | cons sourceContinuation children => cases children with
        | cons extra rest => simp only [List.length_cons] at length;omega
        | nil =>
            simp only [substArgs,Op.binders,liftSub] at sameArguments
            obtain ⟨ownerEq,rest⟩ := List.cons.inj sameArguments
            obtain ⟨readerEq,rest⟩ := List.cons.inj rest
            have continuationEq := (List.cons.inj rest).1
            exact ⟨sourceOwner,sourceReader,sourceContinuation,rfl,rfl,ownerEq.symm,readerEq.symm,continuationEq.symm⟩

end Jihoo.NativeKernel.Environment.LoanTyping
