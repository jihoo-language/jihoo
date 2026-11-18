import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeLoanProofObservation
import Jihoo.NativeLoanPureMixedAdmission

/-! Reflect dependent arithmetic proofs through the source ghost typing
fragment with Free/Strict conversion. Quantifiers range over mathematical
naturals. The recognized proof grammar includes all existing affine evidence,
and a dependent spine can instantiate a quantified proof with affine sums. -/
namespace Jihoo.NativeKernel.Environment.Semantics.PureArithmetic

open AffineSum (Expr)
open NativeKernel.Conversion (ListRel)
open ValueErasure.Loan (project)

private theorem project_affine (expr : Expr) : project env expr.toTerm = expr.toTerm := by
  induction expr with
  | var index => exact ValueErasure.Loan.project_variable _ _
  | literal value =>
      exact ValueErasure.Loan.project_ordinary_node (op := .natural value) rfl (by intro same; cases same) []
  | add first second left right =>
      simp only [Expr.toTerm,ValueErasure.Loan.project_ordinary_node (op := .uadd) rfl (by decide),
        List.map_cons,List.map_nil,ValueErasure.emit,left,right]

theorem affine_conversion_value (wf : UnifiedProgram.EnvWellFormed env) (left right : Expr)
    (converted : RawValue.Conv env left.toTerm right.toTerm) (assignment : Nat → Nat) :
    left.eval assignment = right.eval assignment := by
  have coherence := converted.projected wf.admissible
  rw [project_affine left,project_affine right] at coherence
  exact LoanArithmetic.affine_conversion_value wf left right (.old coherence) assignment

private def replace (values : Nat → Expr) : Expr → Expr
  | .var index => values index
  | .literal value => .literal value
  | .add left right => .add (replace values left) (replace values right)

private theorem replace_term (expr : Expr) (values : Nat → Expr) :
    (replace values expr).toTerm = expr.toTerm.subst (fun index => (values index).toTerm) := by
  induction expr with
  | var | literal => simp only [replace,Expr.toTerm,Term.subst,substArgs]
  | add _ _ first second => simp only [replace,Expr.toTerm,Term.subst,substArgs,Op.binders,liftSub,first,second]

private theorem replace_eval (expr : Expr) (values : Nat → Expr) (assignment : Nat → Nat) :
    (replace values expr).eval assignment = expr.eval (fun index => (values index).eval assignment) := by
  induction expr with
  | var | literal => rfl
  | add _ _ first second => simp only [replace,Expr.eval,first,second]

private def extend (values : Nat → α) (value : α) : Nat → α
  | 0 => value
  | index+1 => values index

private def liftExpr (values : Nat → Expr) : Nat → Expr :=
  extend (fun index => replace (fun x => .var (x+1)) (values index)) (.var 0)

private theorem lifted_term (values : Nat → Expr) :
    (fun index => (liftExpr values index).toTerm) = liftSubOne (fun index => (values index).toTerm) := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      change (replace (fun x => .var (x+1)) (values index)).toTerm = (values index).toTerm.rename Nat.succ
      generalize values index = expr
      induction expr with
      | var | literal => simp only [replace,Expr.toTerm,Term.rename,renameArgs,Nat.add_one]
      | add _ _ first second => simp only [replace,Expr.toTerm,Term.rename,renameArgs,Op.binders,
          liftRenaming,first,second]

private theorem lifted_eval (values : Nat → Expr) (assignment : Nat → Nat) (value : Nat) :
    (fun index => (liftExpr values index).eval (extend assignment value)) =
      extend (fun index => (values index).eval assignment) value := by
  funext index
  cases index with
  | zero => rfl
  | succ index => exact replace_eval _ _ _

inductive Formula where
  | equal (left right : Expr)
  | less (left right : Expr)
  | all (erased : Bool) (body : Formula)

def Formula.syntax : Formula → Term
  | .equal left right => .eq left.toTerm right.toTerm
  | .less left right => .lt left.toTerm right.toTerm
  | .all erased body => .pi erased .u64 body.syntax

def Formula.truth (assignment : Nat → Nat) : Formula → Prop
  | .equal left right => left.eval assignment = right.eval assignment
  | .less left right => left.eval assignment < right.eval assignment
  | .all _ body => ∀ value : Nat, body.truth (extend assignment value)

def Formula.subst (values : Nat → Expr) : Formula → Formula
  | .equal left right => .equal (replace values left) (replace values right)
  | .less left right => .less (replace values left) (replace values right)
  | .all erased body => .all erased (body.subst (liftExpr values))

theorem Formula.syntax_subst (formula : Formula) (values : Nat → Expr) :
    (formula.subst values).syntax = formula.syntax.subst (fun index => (values index).toTerm) := by
  induction formula generalizing values with
  | equal | less =>
      simp only [Formula.subst,Formula.syntax,Term.eq,Term.lt,Term.subst,substArgs,Op.binders,liftSub,replace_term]
  | all erased body ih =>
      simp only [Formula.subst,Formula.syntax,Term.pi,Term.u64,Term.subst,substArgs,Op.binders,liftSub,ih,lifted_term]

theorem Formula.truth_subst (formula : Formula) (values : Nat → Expr) (assignment : Nat → Nat) :
    (formula.subst values).truth assignment ↔ formula.truth (fun index => (values index).eval assignment) := by
  induction formula generalizing values assignment with
  | equal | less => simp only [Formula.subst,Formula.truth,replace_eval]
  | all erased body ih =>
      simp only [Formula.subst,Formula.truth]
      exact forall_congr' (fun value => by rw [ih, lifted_eval])

private def singleExpr (argument : Expr) : Nat → Expr := extend Expr.var argument

theorem Formula.instantiate_syntax (body : Formula) (argument : Expr) :
    (body.subst (singleExpr argument)).syntax = body.syntax.subst (single argument.toTerm) := by
  rw [Formula.syntax_subst]
  congr 1
  funext index
  cases index <;> rfl

theorem Formula.instantiate_truth (body : Formula) (argument : Expr) (assignment : Nat → Nat) :
    (body.subst (singleExpr argument)).truth assignment ↔ body.truth (extend assignment (argument.eval assignment)) := by
  rw [Formula.truth_subst]
  have aligned : (fun index => (singleExpr argument index).eval assignment) = extend assignment (argument.eval assignment) := by
    funext index
    cases index <;> rfl
  rw [aligned]

private theorem project_formula (formula : Formula) : project env formula.syntax = formula.syntax := by
  induction formula with
  | equal left right =>
      simp only [Formula.syntax,Term.eq,ValueErasure.Loan.project_ordinary_node (op := .eq) rfl (by decide),
        List.map_cons,List.map_nil,ValueErasure.emit,project_affine]
  | less left right =>
      simp only [Formula.syntax,Term.lt,ValueErasure.Loan.project_ordinary_node (op := .lt) rfl (by decide),
        List.map_cons,List.map_nil,ValueErasure.emit,project_affine]
  | all erased body ih =>
      have numeric : project env .u64 = .u64 := ValueErasure.Loan.project_ordinary_node (op := .u64) rfl (by decide) []
      simp only [Formula.syntax,ValueErasure.Loan.project_pi,numeric,ih]

theorem Formula.conversion_truth (wf : UnifiedProgram.EnvWellFormed env)
    (left right : Formula) (converted : RawValue.Conv env left.syntax right.syntax) (assignment : Nat → Nat) :
    left.truth assignment ↔ right.truth assignment := by
  induction left generalizing right assignment with
  | equal a b =>
      cases right with
      | equal c d =>
          have parts := converted.eq_injective wf.admissible
          simp only [Formula.truth,affine_conversion_value wf a c parts.1 assignment,
            affine_conversion_value wf b d parts.2 assignment]
      | less | all =>
          have projected := converted.projected wf.admissible
          rw [project_formula,project_formula] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) projected wf.admissible)
  | less a b =>
      cases right with
      | less c d =>
          have projected := converted.projected wf.admissible
          rw [project_formula,project_formula] at projected
          have parts := projected.lt_injective wf.admissible
          simp only [Formula.truth,LoanArithmetic.affine_conversion_value wf a c (.old parts.1) assignment,
            LoanArithmetic.affine_conversion_value wf b d (.old parts.2) assignment]
      | equal | all =>
          have projected := converted.projected wf.admissible
          rw [project_formula,project_formula] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) projected wf.admissible)
  | all erased body ih =>
      cases right with
      | all erased' other =>
          have parts := converted.pi_injective wf.admissible
          exact forall_congr' (fun value => ih other parts.2.2 (extend assignment value))
      | equal | less =>
          have projected := converted.projected wf.admissible
          rw [project_formula,project_formula] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) projected wf.admissible)

def UniversalTruth (env : Environment) (type : Term) : Prop :=
  ∃ formula : Formula, RawValue.Conv env formula.syntax type ∧ ∀ assignment, formula.truth assignment

theorem UniversalTruth.convert (truth : UniversalTruth env type) (converted : RawValue.Conv env type result) :
    UniversalTruth env result := by
  obtain ⟨formula,original,truth⟩ := truth
  exact ⟨formula,original.trans converted,truth⟩

theorem UniversalTruth.formula_iff (wf : UnifiedProgram.EnvWellFormed env) (formula : Formula) :
    UniversalTruth env formula.syntax ↔ ∀ assignment, formula.truth assignment := by
  constructor
  · rintro ⟨original,converted,truth⟩ assignment
    exact (original.conversion_truth wf formula converted assignment).mp (truth assignment)
  · intro truth
    exact ⟨formula,.refl _,truth⟩

inductive Recognized (env : Environment) : Term → Prop where
  | arithmetic : LoanArithmetic.Supported term → Recognized env term
  | refl (value : Expr) : Recognized env (.refl value.toTerm)
  | lam (erased : Bool) : Recognized env body → Recognized env (.lam erased .u64 body)
  | app (value : Expr) : Recognized env function → RawValue.Conv env argument value.toTerm →
      Recognized env (.app function argument)
  | strict (first : Term) : Recognized env rest → Recognized env (.strict first rest)
  | free (owner : Term) : Recognized env rest → Recognized env (.free owner rest)

private def structuralHead : Term → Bool
  | .node (.pi _) _ | .node (.lam _) _ | .node .app _ => true
  | _ => false

private theorem supported_head (supported : LoanArithmetic.Supported term) : structuralHead term = false := by
  fun_cases LoanArithmetic.Supported term
  all_goals first | rfl | simp only [LoanArithmetic.Supported] at supported

private theorem native_head (typed : LoanTyping.PureTyping.HasType env ctx term type)
    (head : structuralHead term = false) : ∃ principal,
      LoanTyping.HasType env [] ctx true term principal ∧ RawValue.Conv env principal type := by
  induction typed with
  | native original => exact ⟨_,original,.refl _⟩
  | convert _ _ converted ih =>
      obtain ⟨principal,original,prior⟩ := ih head
      exact ⟨principal,original,prior.trans converted⟩
  | pi | lam | app => simp [structuralHead] at head

/-- Actual source derivations give an affine proposition family, meaningful
in every valuation. The only application premise beyond syntax identifies an
affine argument using the same pure conversion as source ghost typing. -/
theorem recognized_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env ctx term type) (recognized : Recognized env term) :
    UniversalTruth env type := by
  induction recognized generalizing ctx type with
  | arithmetic supported =>
      obtain ⟨principal,original,outer⟩ := native_head typed (supported_head supported)
      obtain ⟨left,right,converted,ordered⟩ := LoanArithmetic.supported_truth wf original supported
      exact ⟨.less left right,(RawValue.Conv.old converted).trans outer,ordered⟩
  | refl value =>
      obtain ⟨principal,original,outer⟩ := native_head typed rfl
      exact ⟨.equal value value,(RawValue.Conv.old original.principalView).trans outer,fun _ => rfl⟩
  | lam erased _ ih =>
      obtain ⟨_,body,converted⟩ := LoanTyping.PureTyping.lambda_replay typed erased .u64 _ rfl
      obtain ⟨formula,bodyConversion,truth⟩ := ih body
      exact ⟨.all erased formula,
        (RawValue.Conv.node (.pi erased) (.cons (.refl _) (.cons bodyConversion .nil))).trans converted,
        fun assignment value => truth (extend assignment value)⟩
  | app value _ argumentConversion ih =>
      obtain ⟨erased,domain,codomain,functionTyped,_,resultConversion⟩ :=
        LoanTyping.PureTyping.application_replay typed _ _ rfl
      obtain ⟨formula,functionConversion,truth⟩ := ih functionTyped
      cases formula with
      | equal | less =>
          have projected := functionConversion.projected wf.admissible
          rw [project_formula,ValueErasure.Loan.project_pi] at projected
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) projected wf.admissible)
      | all erased' body =>
          have codomainConversion := (functionConversion.pi_injective wf.admissible).2.2
          refine ⟨body.subst (singleExpr value),?_,fun assignment => ?_⟩
          · rw [Formula.instantiate_syntax]
            exact (LoanTyping.PureTyping.instantiate_conversion wf.admissible codomainConversion
              argumentConversion.symm).trans resultConversion
          · exact (body.instantiate_truth value assignment).mpr (truth assignment (value.eval assignment))
  | strict first _ ih =>
      obtain ⟨_,original,outer⟩ := native_head typed rfl
      obtain ⟨_,body,converted⟩ := original.principalView
      exact (ih (.native body)).convert ((RawValue.Conv.old converted).trans outer)
  | free owner _ ih =>
      obtain ⟨_,original,outer⟩ := native_head typed rfl
      obtain ⟨_,body,converted⟩ := original.principalView
      exact (ih (.native body)).convert ((RawValue.Conv.old converted).trans outer)

/-- In the supported proof grammar, giving the checker the full pure
conversion equations cannot manufacture a false closed inequality. -/
theorem no_false_numeral_inequality (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env [] term (.lt (.natural left) (.natural right)))
    (recognized : Recognized env term) (unordered : ¬ left < right) : False := by
  exact unordered ((UniversalTruth.formula_iff wf (.less (.literal left) (.literal right))).mp
    (recognized_fundamental wf typed recognized) (fun _ => 0))

private def checkShape (env : Environment) (projectionFuel budget : Nat) (visit : Term → Bool) : Term → Bool
  | .refl term => (AffineSum.parse term).isSome
  | .lam _ .u64 body => visit body
  | .app function argument => visit function && ((LoanTyping.PureTyping.Checker.project? env
      projectionFuel budget argument).bind AffineSum.parse).isSome
  | .strict _ rest | .free _ rest => visit rest
  | _ => false

private theorem checkShape_sound (visit : Term → Bool) (sound : ∀ term, visit term = true → Recognized env term)
    (accepted : checkShape env projectionFuel budget visit term = true) : Recognized env term := by
  fun_cases checkShape env projectionFuel budget visit term <;> simp only [checkShape] at accepted
  · obtain ⟨expr,parsed⟩ := Option.isSome_iff_exists.mp accepted
    rw [← AffineSum.parse_sound parsed]
    exact .refl expr
  · exact .lam _ (sound _ accepted)
  · rename_i function argument
    obtain ⟨checkedFunction,checkedArgument⟩ := Bool.and_eq_true_iff.mp accepted
    obtain ⟨expr,parsed⟩ := Option.isSome_iff_exists.mp checkedArgument
    obtain ⟨projected,exposed,parsed⟩ := Option.bind_eq_some_iff.mp parsed
    have projectedEq := LoanTyping.PureTyping.Checker.project?_sound exposed
    have affineEq := AffineSum.parse_sound parsed
    have conversion : RawValue.Conv env argument expr.toTerm := by
      rw [affineEq,projectedEq]
      exact (RawValue.project_forward env _).toConv
    exact .app expr (sound function checkedFunction) conversion
  · exact .strict _ (sound _ accepted)
  · exact .free _ (sound _ accepted)
  · contradiction

/-- A bounded syntactic check uses the existing proof-operand recognizer and
obtains affine arguments from the budgeted pure projection of their source. -/
def recognizes (env : Environment) (projectionFuel budget : Nat) : Nat → Term → Bool
  | 0, _ => false
  | fuel+1, term => LoanTyping.ProofObservation.supported term ||
      checkShape env projectionFuel budget (recognizes env projectionFuel budget fuel) term

theorem recognizes_sound (accepted : recognizes env projectionFuel budget fuel term = true) : Recognized env term := by
  induction fuel generalizing term with
  | zero => cases accepted
  | succ fuel ih =>
      simp only [recognizes,Bool.or_eq_true] at accepted
      exact accepted.elim (fun supported => .arithmetic ((LoanTyping.ProofObservation.supported_iff _).mp supported))
        (checkShape_sound _ (fun _ yes => ih yes))

theorem checked_arithmetic_truth (wf : UnifiedProgram.EnvWellFormed env)
    (checked : LoanTyping.PureTyping.Checker.check? env typingFuel projectionFuel budget ctx term type = some sort)
    (recognized : recognizes env projectionFuel budget proofFuel term = true) : UniversalTruth env type :=
  recognized_fundamental wf (LoanTyping.PureTyping.Checker.check?_sound checked).2 (recognizes_sound recognized)

/-- A recognized stored proof derives its mathematical meaning from the
authentic checked v6 history and the exact original stored annotation. -/
theorem checked_global_arithmetic_truth {env : Environment} {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration)
    (recognized : recognizes env projectionFuel budget proofFuel declaration.value = true) :
    UniversalTruth env declaration.type := by
  obtain ⟨_,_,_,_,_,history,wf,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  exact recognized_fundamental wf (history.global_value_and_reference found).1 (recognizes_sound recognized)

theorem checker_rejects_false_inequality (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : recognizes env projectionFuel budget proofFuel term = true) (unordered : ¬ left < right) :
    LoanTyping.PureTyping.Checker.check? env typingFuel projectionFuel budget [] term
      (.lt (.natural left) (.natural right)) = none := by
  cases checked : LoanTyping.PureTyping.Checker.check? env typingFuel projectionFuel budget [] term
      (.lt (.natural left) (.natural right)) with
  | none => rfl
  | some sort => exact False.elim (no_false_numeral_inequality wf
      (LoanTyping.PureTyping.Checker.check?_sound checked).2 (recognizes_sound recognized) unordered)

private def arithmeticProof : Term :=
  .app (.lam true .u64 (.zeroLe (.var 0)))
    (.free (.alloc (.natural 1) (.integer 0)) (.uadd (.natural 7) (.natural 2)))

/-- Check and interpret the same dependent application with an erased Free
argument, a genuinely dependent result, and an affine sum as the value. -/
theorem checked_free_affine_application : UniversalTruth .empty (.lt (.natural 0) (.natural 10)) := by
  have checked : LoanTyping.PureTyping.Checker.check? .empty 48 32 4096 [] arithmeticProof
      (.lt (.natural 0) (.natural 10)) = some .prop := by cbv
  have recognized : recognizes .empty 32 4096 6 arithmeticProof = true := by cbv
  exact checked_arithmetic_truth UnifiedProgram.EnvWellFormed.empty checked recognized

end Jihoo.NativeKernel.Environment.Semantics.PureArithmetic
