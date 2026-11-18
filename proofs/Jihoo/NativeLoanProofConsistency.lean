import Jihoo.NativeDependentProofFundamental
import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanMixedProgram

/-! Closed literal consistency for a syntax-recognized fragment of Loan64.
Actual source typing yields the propositions proved by dependent proof
functions, and the numeral comparisons justified by Decide. Conversion may
use all installed raw Loan64 equations. A mixed history supplies the actual
earlier derivation of a stored global proof. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Dependent.Loan64

private def DecideView (env : Environment) : Term → Term → Prop
  | .decide _ _, type => ∃ left right : Nat,
      left < right ∧ RawLend.Conv env (.lt (.natural left) (.natural right)) type
  | _, _ => True

private theorem DecideView.convert (view : DecideView env term first)
    (converted : RawLend.Conv env first second) : DecideView env term second := by
  fun_cases DecideView env term first <;> simp only [DecideView] at view ⊢
  obtain ⟨left,right,ordered,original⟩ := view
  exact ⟨left,right,ordered,original.trans converted⟩

private theorem decide_view (typed : LoanTyping.HasType env loans ctx mode term type) :
    DecideView env term type := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term type _ => DecideView env term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case decide =>
    rename_i leftBound rightBound ordered
    exact ⟨_,_,ordered,.refl _⟩
  case decideConverted =>
    rename_i leftTyped rightTyped leftConv rightConv leftBound rightBound ordered ihLeft ihRight
    exact ⟨_,_,ordered,.node .lt (.cons leftConv.symm (.cons rightConv.symm .nil))⟩
  case dataElim =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutineeTerm indices types cases
      found data boxed size motive scrutinee generated branches allowed ihMotive ihScrutinee ihBranches
    cases analysis <;> trivial
  case convert =>
    rename_i typed converted ih
    exact ih.convert converted

/-- Recognition constrains syntax only. In particular, a Decide node carries
no premise about the values or ordering of its operands. Branches can use
arbitrary computations in the condition and the context-extended true arm. -/
inductive Recognized : Term → Prop where
  | refl (value : Index) : Recognized (.refl value.syntax)
  | decide (left right : Term) : Recognized (.decide left right)
  | lam : Recognized body → Recognized (.lam false .u64 body)
  | app (argument : Index) : Recognized function → Recognized (.app function argument.syntax)
  | strict (first : Term) : Recognized rest → Recognized (.strict first rest)
  | free (owner : Term) : Recognized rest → Recognized (.free owner rest)
  | drop (family : Nat) (owner : Term) : Recognized rest → Recognized (.node (.drop family) [owner,rest])
  | ifLt (left right yes : Term) : Recognized no → Recognized (.ifLt left right yes no)
  | ifEq (left right yes : Term) : Recognized no → Recognized (.ifEq left right yes no)

/-- A raw result type can denote a proposition through its Loan64 conversion
class. An interpretation of the proposition or of its inputs is unnecessary. -/
def UniversalTruth (env : Environment) (type : Term) : Prop :=
  ∃ formula : Formula, RawLend.Conv env formula.syntax type ∧ ∀ assignment, formula.truth assignment

private theorem UniversalTruth.convert (truth : UniversalTruth env type)
    (converted : RawLend.Conv env type result) : UniversalTruth env result := by
  obtain ⟨formula,original,truth⟩ := truth
  exact ⟨formula,original.trans converted,truth⟩

private theorem UniversalTruth.extend (truth : UniversalTruth before type)
    (extension : Environment.Extends before after) : UniversalTruth after type := by
  obtain ⟨formula,converted,truth⟩ := truth
  exact ⟨formula,converted.extend extension,truth⟩

/-- Every authentic Loan64 derivation of recognized syntax proves a concrete
proposition family under every assignment. A dependent application obtains
its quantified proof from the function and instantiates it at its source
argument; a Decide obtains strict order from the actual typing rule. -/
theorem recognized_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans (context depth) mode term type)
    (recognized : Recognized term) : UniversalTruth env type := by
  induction recognized generalizing depth mode type with
  | refl value => exact ⟨.equal value value,typed.principalView,fun _ => rfl⟩
  | decide left right =>
    obtain ⟨a,b,ordered,converted⟩ := decide_view typed
    exact ⟨.less (.natural a) (.natural b),converted,fun _ => ordered⟩
  | lam _ ih =>
    obtain ⟨_,_,_,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨formula,bodyConverted,truth⟩ := ih (depth := depth+1) bodyTyped
    exact ⟨.all formula,(RawLend.Conv.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))).trans converted,
      fun assignment value => truth (extend assignment value)⟩
  | app argument _ ih =>
    obtain ⟨erased,domain,codomain,functionTyped,_,_,resultConverted⟩ := typed.appView
    obtain ⟨formula,functionConverted,truth⟩ := ih functionTyped
    cases formula with
    | equal left right =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .eq) (op' := .pi erased)
        rfl rfl (by intro same; cases same) functionConverted wf.admissible)
    | less left right =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .lt) (op' := .pi erased)
        rfl rfl (by intro same; cases same) functionConverted wf.admissible)
    | all body =>
      have parts := functionConverted.pi_injective wf.admissible
      refine ⟨body.subst (singleIndex argument),?_,?_⟩
      · rw [Formula.instantiate_syntax]
        exact (parts.2.2.substitution (single argument.syntax) wf.closed).trans resultConverted
      · intro assignment
        rw [Formula.instantiate_truth]
        exact truth assignment (argument.meaning assignment)
  | strict first _ ih =>
    obtain ⟨_,rest,converted⟩ := typed.principalView
    exact (ih rest).convert converted
  | free owner _ ih =>
    obtain ⟨_,rest,converted⟩ := typed.principalView
    exact (ih rest).convert converted
  | drop family owner _ ih =>
    obtain ⟨_,rest,converted⟩ := typed.principalView
    exact (ih rest).convert converted
  | ifLt left right yes _ ih =>
    obtain ⟨_,no,converted⟩ := typed.principalView
    exact (ih no).convert converted
  | ifEq left right yes _ ih =>
    obtain ⟨_,no,converted⟩ := typed.principalView
    exact (ih no).convert converted

/-- A realized literal inequality is true in Nat. This uses the checked
world's genuine raw conversion injectivity, including substitution for the
observed coordinates of a proposition family. -/
theorem UniversalTruth.less_numerals (wf : UnifiedProgram.EnvWellFormed env)
    (truth : UniversalTruth env (.lt (.natural a) (.natural b))) : a < b := by
  obtain ⟨formula,converted,truth⟩ := truth
  cases formula with
  | equal left right =>
    exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .eq) (op' := .lt)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  | all body =>
    exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .pi false) (op' := .lt)
      rfl rfl (by intro same; cases same) converted wf.admissible)
  | less left right =>
    let assignment : Nat → Nat := fun _ => 0
    have parts := converted.lt_injective wf.admissible
    have leftValue := parts.1.substitution (fun i => .natural (assignment i)) wf.closed
    have rightValue := parts.2.substitution (fun i => .natural (assignment i)) wf.closed
    rw [Index.closed_value] at leftValue rightValue
    simp only [Term.natural,Term.subst,substArgs] at leftValue rightValue
    have leftEqual := leftValue.natural_injective wf.admissible
    have rightEqual := rightValue.natural_injective wf.admissible
    rw [← leftEqual,← rightEqual]
    exact truth assignment

theorem no_closed_recognized_lt_zero_zero (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans [] mode term (.lt (.natural 0) (.natural 0)))
    (recognized : Recognized term) : False :=
  Nat.lt_irrefl 0 ((recognized_fundamental (depth := 0) wf typed recognized).less_numerals wf)

theorem check_recognized_lt_zero_zero_rejected (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : Recognized term) :
    LoanTyping.Checker.check fuel env [] [] true term (.lt (.natural 0) (.natural 0)) = false := by
  cases checked : LoanTyping.Checker.check fuel env [] [] true term (.lt (.natural 0) (.natural 0)) with
  | false => rfl
  | true => exact False.elim (no_closed_recognized_lt_zero_zero wf (LoanTyping.Checker.check_sound checked) recognized)

/-- Look up the actual declaration in a mixed history to recover its checked
body and earlier environment. The body is the expanded stored body, so input
globals inside the source need no externally supplied expansion witness. -/
theorem checked_global_truth (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    {index : Nat} {declaration : GlobalDeclaration}
    (found : env.globals[index]? = some declaration) (recognized : Recognized declaration.value) :
    UniversalTruth env declaration.type := by
  obtain ⟨_,_,_,_,prior,_,checked,extension⟩ := history.global_prefix found
  obtain ⟨_,_,typed,_⟩ := checked.valid.typing
  exact (recognized_fundamental (depth := 0) prior.wellFormed typed recognized).extend extension

theorem no_checked_global_lt_zero_zero (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    {index : Nat} {declaration : GlobalDeclaration}
    (found : env.globals[index]? = some declaration) (recognized : Recognized declaration.value)
    (requested : RawLend.Conv env declaration.type (.lt (.natural 0) (.natural 0))) : False :=
  Nat.lt_irrefl 0 (((checked_global_truth history found recognized).convert requested).less_numerals history.wellFormed)

private def computedBound : Term := .app (.lam false .u64 (.var 0)) (.natural 2)

private def computedProof : GlobalDeclaration :=
  ⟨.lt (.natural 0) (.natural 2),
    .app (.lam false .u64 (.decide (.natural 0) computedBound)) (.natural 11)⟩

private def computedWorld : Environment := ⟨#[computedProof],#[]⟩

example : UniversalTruth computedWorld (.lt (.natural 0) (.natural 2)) := by
  have checked : LoanTyping.MixedProgram.checkProgram 32 32 [computedProof] [] = some computedWorld := by cbv
  exact checked_global_truth (LoanTyping.MixedProgram.checkProgram_sound checked)
    (index := 0) (declaration := computedProof) rfl
    (.app (.natural 11) (.lam (.decide (.natural 0) computedBound)))

end Jihoo.NativeKernel.Environment.Semantics.Dependent.Loan64
