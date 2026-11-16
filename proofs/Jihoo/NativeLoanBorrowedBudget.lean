import Jihoo.NativeLoanRawResourceOrigins

/-! Zero ownership demand for every active source loan. These are obligations
of the original recursive quantity receipt, not successful-execution premises.
They compose through scopes and actual dependent-Lend reader/restore checks. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity
variable {control : Control}

def LoanBudget (depth : Nat) (loans : Loans.Stack) (control : Control) : Prop :=
  ∀ index, Loans.active depth loans index = true → control.demand index = some 0

private theorem sequence_zero (zero : (Control.seq first second).demand index = some 0) :
    first.demand index = some 0 ∧ second.demand index = some 0 := by
  simp only [Control.demand] at zero
  obtain ⟨left,leftDemand,zero⟩ := Option.bind_eq_some_iff.mp zero
  obtain ⟨right,rightDemand,same⟩ := Option.bind_eq_some_iff.mp zero
  have total : left+right = 0 := Option.some.inj same
  have leftZero : left = 0 := by omega
  have rightZero : right = 0 := by omega
  exact ⟨leftZero ▸ leftDemand,rightZero ▸ rightDemand⟩

theorem LoanBudget.empty (depth : Nat) (control : Control) : LoanBudget depth [] control := by
  intro index active
  cases active

theorem LoanBudget.sequence (budget : LoanBudget depth loans (.seq first second)) :
    LoanBudget depth loans first ∧ LoanBudget depth loans second := by
  exact ⟨fun index active => (sequence_zero (budget index active)).1,
    fun index active => (sequence_zero (budget index active)).2⟩

/-- Either nondeterministic branch retains the same old-reader authority. -/
theorem LoanBudget.branch (budget : LoanBudget depth loans (.branch first second)) :
    LoanBudget depth loans first ∧ LoanBudget depth loans second := by
  have both : ∀ index, Loans.active depth loans index = true →
      first.demand index = some 0 ∧ second.demand index = some 0 := by
    intro index active
    have zero := budget index active
    simp only [Control.demand] at zero
    obtain ⟨left,leftDemand,zero⟩ := Option.bind_eq_some_iff.mp zero
    obtain ⟨right,rightDemand,zero⟩ := Option.bind_eq_some_iff.mp zero
    split at zero
    · rename_i same
      have leftZero : left = 0 := Option.some.inj zero
      have rightZero : right = 0 := by omega
      exact ⟨leftZero ▸ leftDemand,rightZero ▸ rightDemand⟩
    · contradiction
  exact ⟨fun index active => (both index active).1,fun index active => (both index active).2⟩

theorem LoanBudget.scope (budget : LoanBudget depth loans (.scope mode body))
    (entered : Loans.Entered depth loans) : LoanBudget (depth+1) loans body := by
  intro index active
  cases index with
  | zero =>
      obtain ⟨frame,member,before,same⟩ := Loans.active_iff.mp active
      have old := entered frame member
      omega
  | succ index =>
      have previous : Loans.active depth loans index = true := by
        simpa only [Loans.active_weaken entered] using active
      have shifted := Jihoo.Quantity.scopes_outer (modes := [mode]) (budget index previous)
      exact shifted

/-- Original Lend receipt fixes ownership demand independently of which
physical allocation supplied the owner. -/
theorem projectRaw_lend_owner_demand
    (checked : projectRaw (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control) :
    control.demand owner = some 1 := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,sourceTyped,readTyped,
    binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,rfl⟩ := dependent_raw_project_contract checked
  simp only [Control.demand,readZero,restOne]
  rfl

/-- A valid enclosing reader budget excludes consuming any already active
named owner at another Lend, rather than relying on a fresh allocation. -/
theorem projectRaw_lend_inactive
    (checked : projectRaw (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control)
    (budget : LoanBudget ctx.length loans control) : Loans.active ctx.length loans owner = false := by
  apply Bool.eq_false_iff.mpr
  intro active
  have zero := budget owner active
  rw [projectRaw_lend_owner_demand checked] at zero
  contradiction

/-- The authentic query constructs the new reader's zero budget and preserves
all enclosing-reader budgets in both original checked subexpressions. -/
theorem projectRaw_lend_budgets
    (checked : projectRaw (fuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) = some control)
    (budget : LoanBudget ctx.length loans control) (entered : Loans.Entered ctx.length loans) :
    ∃ reader mode rest,
      projectRaw fuel env (Loans.enter ctx.length owner loans) ctx (Lending.read (.var owner) readerBody) = some reader ∧
      projectRaw fuel env loans (⟨first,false⟩ :: ctx) (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      LoanBudget ctx.length (Loans.enter ctx.length owner loans) reader ∧
      LoanBudget (ctx.length+1) loans rest ∧ control = .seq reader (.scope mode rest) := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,sourceTyped,readTyped,
    binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,rfl⟩ := dependent_raw_project_contract checked
  have parts := budget.sequence
  refine ⟨reader,mode,rest,readProjected,restProjected,?_,parts.2.scope entered,rfl⟩
  intro index active
  rw [Loans.active_enter,Bool.or_eq_true] at active
  rcases active with same | previous
  · have sameIndex : owner = index := beq_iff_eq.mp same
    subst index
    exact readZero
  · exact parts.1 index previous

/-- Free's consuming variable is not an active source loan under the same
whole quantity receipt. Tail typing or successful Free is not an input. -/
theorem projectRaw_free_inactive
    (checked : projectRaw (fuel+2) env loans ctx (.free (.var owner) tail) = some control)
    (budget : LoanBudget ctx.length loans control) : Loans.active ctx.length loans owner = false := by
  obtain ⟨binding,rest,found,relevant,restProjected,rfl⟩ := projectRaw_free_variable checked
  apply Bool.eq_false_iff.mpr
  intro active
  have zero := (budget.sequence.1) owner active
  have impossible : (1 : Nat) = 0 := by simpa only [Control.demand,ite_true,Option.some.injEq] using zero
  omega

/-- All enclosing-reader zero budgets, as well as the consumed owner's zero
residual demand, survive the actual restored Free and its two physical aliases. -/
theorem projectRaw_lend_free_tail_budget
    (checked : projectRaw (fuel+3) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.free (.var index) tail)))) = some control)
    (budget : LoanBudget ctx.length loans control) (entered : Loans.Entered ctx.length loans)
    (selected : index = 0 ∨ index = owner+2) :
    ∃ rest,
      projectRaw (fuel+1) env loans (⟨first,false⟩ :: ctx)
        (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      LoanBudget (ctx.length+1) loans rest ∧ rest.demand (owner+1) = some 0 := by
  obtain ⟨reader,mode,rest,readProjected,restProjected,readBudget,restBudget,same⟩ :=
    projectRaw_lend_budgets checked budget entered
  have ownerMapping : (Term.var index).subst (single ((Term.var owner).rename Nat.succ)) = .var (owner+1) := by
    rcases selected with rfl | rfl
    · exact restored_returned_owner
    · exact restored_original_owner
  rw [subst_free,ownerMapping] at restProjected
  obtain ⟨binding,tailControl,found,relevant,tailProjected,rfl⟩ := projectRaw_free_variable restProjected
  have tailBudget := restBudget.sequence.2.sequence.1
  obtain ⟨original,originalProjected,zero,remaining⟩ := raw_lend_free_tail_zero selected checked
  have identity : original = tailControl := Option.some.inj (originalProjected.symm.trans tailProjected)
  rw [identity] at zero
  exact ⟨tailControl,tailProjected,tailBudget,zero⟩

/-- Literal call opening carries every enclosing-reader zero budget below the
actual argument binder, from its original full recursive query. -/
theorem projectRaw_single_lambda_call_budget
    (checked : projectRaw (fuel+3) env loans ctx (.app (.lam false domain body) argument) = some control)
    (budget : LoanBudget ctx.length loans control) (entered : Loans.Entered ctx.length loans) :
    ∃ bodyControl, projectRaw (fuel+2) env loans (⟨domain,false⟩ :: ctx) body = some bodyControl ∧
      LoanBudget (ctx.length+1) loans bodyControl := by
  simp only [projectRaw,splitSpine,Op.arity,List.length_cons,List.length_nil,Nat.reduceAdd,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  obtain ⟨⟨head,supplied⟩,splitSpineChecked,checked⟩ := Option.bind_eq_some_iff.mp checked
  cases splitSpineChecked
  obtain ⟨⟨entries,result⟩,replayed,checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · contradiction
  · obtain ⟨opened,openedProof,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨runtime,runtimeProjected,checked⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨bodyControl,bodyProjected,same⟩ := Option.bind_eq_some_iff.mp checked
    simp only [openHead] at openedProof
    split at openedProof
    · contradiction
    · obtain ⟨mode,resolved,openedProof⟩ := Option.bind_eq_some_iff.mp openedProof
      have identity : opened = ⟨⟨domain,false⟩ :: ctx,[mode],body⟩ := (Option.some.inj openedProof).symm
      subst opened
      have controlShape : control = .seq (sequence runtime) (.scope mode bodyControl) := by
        simpa only [Control.scopes,List.foldr,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] using (Option.some.inj same).symm
      rw [controlShape] at budget
      exact ⟨bodyControl,bodyProjected,budget.sequence.2.scope entered⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
