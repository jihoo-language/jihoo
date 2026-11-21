import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeLoanComputationPreservation
import Jihoo.NativeLoanPureTyping

/-! A finite numeric reduct determines a mathematical value even for an
overflowing ghost sum. The arithmetic proof rules use these observations
after a closing substitution, including arguments with computed syntax. -/
namespace Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic

open EnvironmentDelta.NumeralForward (Represents)

def Numeric (env : Environment) (term : Term) (value : Nat) : Prop :=
  ∃ tree, RawLend.Conv env term tree ∧ Represents tree value

theorem Numeric.natural (env : Environment) (value : Nat) : Numeric env (.natural value) value :=
  ⟨_,.refl _,.natural value⟩

theorem Numeric.convert (known : Numeric env term value) (same : RawLend.Conv env term other) :
    Numeric env other value := by
  obtain ⟨tree,converted,represented⟩ := known
  exact ⟨tree,same.symm.trans converted,represented⟩

theorem Numeric.unique (admissible : EnvironmentDelta.Admissible env)
    (first : Numeric env term a) (second : Numeric env term b) : a = b := by
  obtain ⟨firstTree,firstConversion,firstValue⟩ := first
  obtain ⟨secondTree,secondConversion,secondValue⟩ := second
  obtain ⟨common,left,right⟩ := (firstConversion.symm.trans secondConversion).church_rosser admissible
  have unique {term : Term} {a b : Nat} (first : Represents term a) (second : Represents term b) : a = b := by
    induction first generalizing b with
    | natural => cases second; rfl
    | add left right ihLeft ihRight =>
      cases second with
      | add otherLeft otherRight => rw [ihLeft otherLeft,ihRight otherRight]
  exact unique (left.represents firstValue) (right.represents secondValue)

theorem Numeric.add (left : Numeric env a m) (right : Numeric env b n) :
    Numeric env (.uadd a b) (m+n) := by
  obtain ⟨leftTree,leftConversion,leftValue⟩ := left
  obtain ⟨rightTree,rightConversion,rightValue⟩ := right
  exact ⟨.uadd leftTree rightTree,.node .uadd (.cons leftConversion (.cons rightConversion .nil)),.add leftValue rightValue⟩

def Order (env : Environment) (type : Term) : Prop :=
  ∃ a b m n, RawLend.Conv env type (.lt a b) ∧ Numeric env a m ∧ Numeric env b n ∧ m < n

theorem Order.convert (truth : Order env type) (same : RawLend.Conv env type other) : Order env other := by
  obtain ⟨a,b,m,n,converted,left,right,ordered⟩ := truth
  exact ⟨a,b,m,n,same.symm.trans converted,left,right,ordered⟩

theorem Order.reflect (admissible : EnvironmentDelta.Admissible env)
    (truth : Order env (.lt a b)) (left : Numeric env a m) (right : Numeric env b n) : m < n := by
  obtain ⟨_,_,_,_,converted,oldLeft,oldRight,ordered⟩ := truth
  obtain ⟨leftConversion,rightConversion⟩ := converted.lt_injective admissible
  rw [left.unique admissible (oldLeft.convert leftConversion.symm),
    right.unique admissible (oldRight.convert rightConversion.symm)]
  exact ordered

theorem Order.no_zero_upper (admissible : EnvironmentDelta.Admissible env)
    (truth : Order env (.lt left (.natural 0))) : False := by
  obtain ⟨_,_,_,value,converted,_,right,ordered⟩ := truth
  have same := (Numeric.natural env 0).unique admissible
    (right.convert (converted.lt_injective admissible).2.symm)
  rw [←same] at ordered
  exact Nat.not_lt_zero _ ordered

/-- The evidence observations depend on the arithmetic operands whose
values a proof actually uses. -/
def ObservedEvidenceUsing (hasValue : Term → Prop) : Term → Prop
  | .decide _ _ => True
  | .zeroLe a => hasValue a
  | .ltAdd a b c proof | .ltCancel a b c proof =>
    hasValue a ∧ hasValue b ∧ hasValue c ∧ ObservedEvidenceUsing hasValue proof
  | .ltLe a b c first second => hasValue a ∧ hasValue b ∧ hasValue c ∧
    ObservedEvidenceUsing hasValue first ∧ ObservedEvidenceUsing hasValue second
  | .strict _ rest | .free _ rest | .node (.drop _) [_,rest] => ObservedEvidenceUsing hasValue rest
  | .ifLt _ _ _ rest | .ifEq _ _ _ rest => ObservedEvidenceUsing hasValue rest
  | .absurd _ proof => ObservedEvidenceUsing hasValue proof
  | _ => False
termination_by term => sizeOf term

def ObservedEvidence (env : Environment) (values : Nat → Term) (term : Term) : Prop :=
  ObservedEvidenceUsing (fun operand => ∃ value, Numeric env (operand.subst values) value) term

/-- Arithmetic interpretation may observe written terms directly or
erase value-irrelevant computation before inspecting them. -/
structure ArithmeticView (env : Environment) where
  observe : Term → Term
  natural : ∀ value, observe (.natural value) = .natural value
  addition : ∀ left right, observe (.uadd left right) = .uadd (observe left) (observe right)
  inequality : ∀ left right, observe (.lt left right) = .lt (observe left) (observe right)
  converts : ∀ {input output}, RawLend.Conv env input output → RawLend.Conv env (observe input) (observe output)

def ArithmeticView.direct (env : Environment) : ArithmeticView env :=
  ⟨id,fun _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun h => h⟩

private theorem ArithmeticView.natural_subst (view : ArithmeticView env) (values : Nat → Term) (n : Nat) :
    view.observe ((Term.natural n).subst values) = .natural n := by
  simpa only [Term.natural,Term.subst,substArgs] using view.natural n

private theorem ArithmeticView.addition_subst (view : ArithmeticView env) (values : Nat → Term) (a b : Term) :
    view.observe ((a.uadd b).subst values) = .uadd (view.observe (a.subst values)) (view.observe (b.subst values)) := by
  simpa only [Term.uadd,Term.subst,substArgs,Op.binders,liftSub] using
    view.addition (a.subst values) (b.subst values)

private theorem ArithmeticView.inequality_subst (view : ArithmeticView env) (values : Nat → Term) (a b : Term) :
    view.observe ((a.lt b).subst values) = .lt (view.observe (a.subst values)) (view.observe (b.subst values)) := by
  simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using
    view.inequality (a.subst values) (b.subst values)

private theorem original_order (left : Numeric env a m) (right : Numeric env b n) (ordered : m < n) :
    Order env (.lt a b) := ⟨a,b,m,n,.refl _,left,right,ordered⟩

/-- A finite observed value of each used word operand suffices for the
original dependent proof type. No syntactic restrictions on the observed
word terms or word bounds on their mathematical sums are needed. -/
theorem observed_evidence_order_in (wf : UnifiedProgram.EnvWellFormed env) (view : ArithmeticView env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (evidence : ObservedEvidenceUsing (fun operand => ∃ value, Numeric env (view.observe (operand.subst values)) value) term) : Order env (view.observe (type.subst values)) := by
  revert evidence
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term type _ => ObservedEvidenceUsing (fun operand => ∃ value, Numeric env (view.observe (operand.subst values)) value) term → Order env (view.observe (type.subst values)))
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (simp only [ObservedEvidenceUsing] at *)
  case decide =>
    rename_i leftBound rightBound ordered evidence
    simpa only [view.inequality_subst,view.natural_subst] using
      original_order (Numeric.natural env _) (Numeric.natural env _) ordered
  case decideConverted =>
    rename_i leftTyped rightTyped leftConv rightConv leftBound rightBound ordered ihLeft ihRight evidence
    have left := view.converts (leftConv.substitution values wf.closed).symm
    have right := view.converts (rightConv.substitution values wf.closed).symm
    simp only [view.natural_subst] at left right
    simpa only [view.inequality_subst] using
      original_order ((Numeric.natural env _).convert left) ((Numeric.natural env _).convert right) ordered
  case zeroLe =>
    rename_i typed ih supported
    obtain ⟨value,actual⟩ := supported
    simpa only [view.inequality_subst,view.addition_subst,view.natural_subst] using
      original_order (Numeric.natural env 0) (actual.add (Numeric.natural env 1)) (Nat.zero_lt_succ value)
  case ltAdd =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof evidence
    obtain ⟨⟨_,left⟩,⟨_,right⟩,⟨_,step⟩,proofObserved⟩ := evidence
    have proof := ihProof proofObserved
    simp only [view.inequality_subst] at proof
    have ordered := proof.reflect wf.admissible left right
    simpa only [view.inequality_subst,view.addition_subst] using
      original_order (left.add step) (right.add step) (Nat.add_lt_add_right ordered _)
  case ltCancel =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof evidence
    obtain ⟨⟨_,left⟩,⟨_,right⟩,⟨_,step⟩,proofObserved⟩ := evidence
    have proof := ihProof proofObserved
    simp only [view.inequality_subst,view.addition_subst] at proof
    have ordered := proof.reflect wf.admissible (left.add step) (right.add step)
    simpa only [view.inequality_subst] using
      original_order left right (Nat.lt_of_add_lt_add_right ordered)
  case ltLe =>
    rename_i leftTyped middleTyped rightTyped lowerTyped upperTyped ihLeft ihMiddle ihRight ihLower ihUpper evidence
    obtain ⟨⟨_,left⟩,⟨_,middle⟩,⟨_,right⟩,lowerObserved,upperObserved⟩ := evidence
    have lowerProof := ihLower lowerObserved
    have upperProof := ihUpper upperObserved
    simp only [view.inequality_subst,view.addition_subst,view.natural_subst] at lowerProof upperProof
    have lower := lowerProof.reflect wf.admissible left middle
    have upper := upperProof.reflect wf.admissible middle (right.add (Numeric.natural env 1))
    simpa only [view.inequality_subst] using original_order left right (by omega)
  case strict => rename_i first rest ihFirst ihRest evidence; exact ihRest evidence
  case free => rename_i owner rest ihOwner ihRest evidence; exact ihRest evidence
  case drop => rename_i found boxed owner rest ihOwner ihRest evidence; exact ihRest evidence
  case ifLt => rename_i left right yes no ihLeft ihRight ihYes ihNo evidence; exact ihNo evidence
  case ifEq => rename_i left right yes no ihLeft ihRight ihYes ihNo evidence; exact ihNo evidence
  case absurd =>
    rename_i target proof allowed ihTarget ihProof evidence
    have interpreted := ihProof evidence
    simp only [view.inequality_subst,view.natural_subst] at interpreted
    exact False.elim (interpreted.no_zero_upper wf.admissible)
  case convert =>
    rename_i typed converted ih evidence
    exact (ih evidence).convert (view.converts (converted.substitution values wf.closed))
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches evidence
    cases analysis <;> simp [ObservedEvidenceUsing] at evidence

/-- Direct conversion keeps the original indices and their full
mathematical values, including wide ghost sums. -/
theorem observed_evidence_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (evidence : ObservedEvidence env values term) : Order env (type.subst values) :=
  observed_evidence_order_in wf (ArithmeticView.direct env) typed evidence

/-- A typed contextual computation can expose the evidence grammar used
by the numerical interpretation. Its source proof can contain other
computations, including actual family elimination. -/
theorem observed_residual_order
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (steps : LoanTyping.ComputationEvaluation.Steps env term residual)
    (observed : ObservedEvidence env values residual) : Order env (type.subst values) :=
  observed_evidence_order history.wellFormed (history.computation_preservation steps typed).2 observed

theorem no_observed_residual_less_zero
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanTyping.HasType env loans ctx mode term (.lt left (.natural 0)))
    (steps : LoanTyping.ComputationEvaluation.Steps env term residual)
    (observed : ObservedEvidence env values residual) : False := by
  have evaluated : Order env (.lt (left.subst values) (.natural 0)) := by
    simpa only [Term.lt,Term.natural,Term.subst,substArgs,Op.binders,liftSub] using observed_residual_order history typed steps observed
  exact evaluated.no_zero_upper history.wellFormed.admissible

private theorem project_natural (env : Environment) (value : Nat) :
    ValueErasure.Loan.project env (.natural value) = .natural value :=
  ValueErasure.Loan.project_ordinary_node (op := .natural value) rfl (by intro impossible; cases impossible) []

private theorem project_addition (env : Environment) (left right : Term) :
    ValueErasure.Loan.project env (.uadd left right) =
      .uadd (ValueErasure.Loan.project env left) (ValueErasure.Loan.project env right) := by
  simp only [Term.uadd,ValueErasure.Loan.project_ordinary_node (op := .uadd) rfl (by decide),
    List.map_cons,List.map_nil,ValueErasure.emit]

private theorem project_inequality (env : Environment) (left right : Term) :
    ValueErasure.Loan.project env (.lt left right) =
      .lt (ValueErasure.Loan.project env left) (ValueErasure.Loan.project env right) := by
  simp only [Term.lt,ValueErasure.Loan.project_ordinary_node (op := .lt) rfl (by decide),
    List.map_cons,List.map_nil,ValueErasure.emit]

/-- The source value erasure respects terminals, numeric addition,
inequality, and the original raw conversion theory. -/
def ArithmeticView.projected (wf : UnifiedProgram.EnvWellFormed env) : ArithmeticView env where
  observe := ValueErasure.Loan.project env
  natural := project_natural env
  addition := project_addition env
  inequality := project_inequality env
  converts converted := .old (ValueErasure.Loan.conversion wf.admissible converted)

def ProjectedObserved (env : Environment) (values : Nat → Term) (term : Term) : Prop :=
  ObservedEvidenceUsing
    (fun operand => ∃ value, Numeric env (ValueErasure.Loan.project env (operand.subst values)) value) term

theorem projected_evidence_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (evidence : ProjectedObserved env values term) :
    Order env (ValueErasure.Loan.project env (type.subst values)) :=
  observed_evidence_order_in wf (.projected wf) typed evidence

/-- The richer pure judgment can convert a written type through value
erasure. The original arithmetic derivation still supplies its order. -/
theorem projected_pure_evidence_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (evidence : ProjectedObserved env values term) :
    Order env (ValueErasure.Loan.project env (type.subst values)) := by
  induction typed with
  | native original => exact projected_evidence_order wf original evidence
  | convert original _ converted ih =>
    exact ih evidence |>.convert (.old ((converted.substitution values wf.admissible).projected wf.admissible))
  | pi | lam | app => simp only [ProjectedObserved,ObservedEvidenceUsing] at evidence

theorem projected_closed_evidence_excludes_zero (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env [] term (.lt left (.natural 0)))
    (evidence : ProjectedObserved env Term.var term) : False := by
  have order := projected_pure_evidence_order wf typed evidence
  have result : Order env (.lt (ValueErasure.Loan.project env left) (.natural 0)) := by
    simpa only [Term.subst_id,project_inequality,project_natural]
      using order
  exact result.no_zero_upper wf.admissible

private def wrapped : Term := .strict (.integer 3) (.natural 0)
private def written : GlobalDeclaration :=
  ⟨.lt (.natural 0) (.uadd wrapped (.natural 1)),.zeroLe wrapped⟩
private def world : Environment := ⟨#[written],#[]⟩

/-- The actual admitted arithmetic operand contains an evaluable Strict
prefix. Its source result type is interpreted at the observed pure word. -/
theorem admitted_projected_strict_order :
    Order world (.lt (.natural 0) (.uadd (.natural 0) (.natural 1))) := by
  have accepted : LoanTyping.MixedProgram.checkProgram 64 64 [written] [] = some world := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound accepted
  obtain ⟨_,_,typed⟩ := history.global_typing (index := 0) (declaration := written) rfl
  have observed : ProjectedObserved world Term.var written.value := by
    simp only [ProjectedObserved,written,ObservedEvidenceUsing,Term.subst_id,wrapped,
      ValueErasure.Loan.project_strict,project_natural]
    exact ⟨0,Numeric.natural world 0⟩
  have order := projected_evidence_order history.wellFormed typed observed
  simpa only [written,Term.subst_id,wrapped,project_inequality,
    project_addition,ValueErasure.Loan.project_strict,
    project_natural] using order

end Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
