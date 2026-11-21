import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeLoanComputationPreservation

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

private def Observed (env : Environment) (values : Nat → Term) (term : Term) : Prop :=
  ∃ value, Numeric env (term.subst values) value

/-- Only the original operands whose values the algebraic rules use
require observations. The actual Decide rule already checks that its
arguments convert to bounded literals. -/
def ObservedEvidence (env : Environment) (values : Nat → Term) : Term → Prop
  | .decide _ _ => True
  | .zeroLe a => Observed env values a
  | .ltAdd a b c proof | .ltCancel a b c proof =>
    Observed env values a ∧ Observed env values b ∧ Observed env values c ∧ ObservedEvidence env values proof
  | .ltLe a b c first second => Observed env values a ∧ Observed env values b ∧ Observed env values c ∧
    ObservedEvidence env values first ∧ ObservedEvidence env values second
  | .strict _ rest | .free _ rest | .node (.drop _) [_,rest] => ObservedEvidence env values rest
  | .ifLt _ _ _ rest | .ifEq _ _ _ rest => ObservedEvidence env values rest
  | .absurd _ proof => ObservedEvidence env values proof
  | _ => False
termination_by term => sizeOf term

private theorem original_order (left : Numeric env a m) (right : Numeric env b n) (ordered : m < n) :
    Order env (.lt a b) := ⟨a,b,m,n,.refl _,left,right,ordered⟩

/-- A finite observed value of each used word operand suffices for the
original dependent proof type. No syntactic restrictions on the observed
word terms or word bounds on their mathematical sums are needed. -/
theorem observed_evidence_order (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans ctx mode term type)
    (evidence : ObservedEvidence env values term) : Order env (type.subst values) := by
  revert evidence
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term type _ => ObservedEvidence env values term → Order env (type.subst values))
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (simp only [ObservedEvidence] at *)
  case decide =>
    rename_i leftBound rightBound ordered evidence
    simpa only [Term.lt,Term.natural,Term.subst,substArgs,Op.binders,liftSub] using
      original_order (Numeric.natural env _) (Numeric.natural env _) ordered
  case decideConverted =>
    rename_i leftTyped rightTyped leftConv rightConv leftBound rightBound ordered ihLeft ihRight evidence
    have left := (leftConv.substitution values wf.closed).symm
    have right := (rightConv.substitution values wf.closed).symm
    simp only [Term.subst,substArgs] at left right
    simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using
      original_order ((Numeric.natural env _).convert left) ((Numeric.natural env _).convert right) ordered
  case zeroLe =>
    rename_i typed ih supported
    obtain ⟨value,actual⟩ := supported
    simpa only [Term.lt,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,liftSub] using
      original_order (Numeric.natural env 0) (actual.add (Numeric.natural env 1)) (Nat.zero_lt_succ value)
  case ltAdd =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof evidence
    obtain ⟨⟨_,left⟩,⟨_,right⟩,⟨_,step⟩,proofObserved⟩ := evidence
    have proof := ihProof proofObserved
    simp only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] at proof
    have ordered := proof.reflect wf.admissible left right
    simpa only [Term.lt,Term.uadd,Term.subst,substArgs,Op.binders,liftSub] using
      original_order (left.add step) (right.add step) (Nat.add_lt_add_right ordered _)
  case ltCancel =>
    rename_i leftTyped rightTyped stepTyped proofTyped ihLeft ihRight ihStep ihProof evidence
    obtain ⟨⟨_,left⟩,⟨_,right⟩,⟨_,step⟩,proofObserved⟩ := evidence
    have proof := ihProof proofObserved
    simp only [Term.lt,Term.uadd,Term.subst,substArgs,Op.binders,liftSub] at proof
    have ordered := proof.reflect wf.admissible (left.add step) (right.add step)
    simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using
      original_order left right (Nat.lt_of_add_lt_add_right ordered)
  case ltLe =>
    rename_i leftTyped middleTyped rightTyped lowerTyped upperTyped ihLeft ihMiddle ihRight ihLower ihUpper evidence
    obtain ⟨⟨_,left⟩,⟨_,middle⟩,⟨_,right⟩,lowerObserved,upperObserved⟩ := evidence
    have lowerProof := ihLower lowerObserved
    have upperProof := ihUpper upperObserved
    simp only [Term.lt,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,liftSub] at lowerProof upperProof
    have lower := lowerProof.reflect wf.admissible left middle
    have upper := upperProof.reflect wf.admissible middle (right.add (Numeric.natural env 1))
    simpa only [Term.lt,Term.subst,substArgs,Op.binders,liftSub] using original_order left right (by omega)
  case strict => rename_i first rest ihFirst ihRest evidence; exact ihRest evidence
  case free => rename_i owner rest ihOwner ihRest evidence; exact ihRest evidence
  case drop => rename_i found boxed owner rest ihOwner ihRest evidence; exact ihRest evidence
  case ifLt => rename_i left right yes no ihLeft ihRight ihYes ihNo evidence; exact ihNo evidence
  case ifEq => rename_i left right yes no ihLeft ihRight ihYes ihNo evidence; exact ihNo evidence
  case absurd =>
    rename_i target proof allowed ihTarget ihProof evidence
    have interpreted := ihProof evidence
    simp only [Term.lt,Term.natural,Term.subst,substArgs,Op.binders,liftSub] at interpreted
    exact False.elim (interpreted.no_zero_upper wf.admissible)
  case convert =>
    rename_i typed converted ih evidence
    exact (ih evidence).convert (converted.substitution values wf.closed)
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches evidence
    cases analysis <;> simp [ObservedEvidence] at evidence

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

end Jihoo.NativeKernel.Environment.Semantics.LoanArithmetic
