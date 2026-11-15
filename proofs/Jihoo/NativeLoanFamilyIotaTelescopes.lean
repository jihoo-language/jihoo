import Jihoo.NativeLoanFamilyIotaMetadata
import Jihoo.NativeLoanTypeUniqueness
import Jihoo.NativeDataBindingAlgebra

/-! Actual constructor-argument derivations instantiate actual functions.
All application policies below are discharged by ghost mode, rather than
accepted as a callback or reflected typing assertion. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem arguments_change_telescope (arguments : Arguments env [] ctx mode data telescope xs result)
    (converted : Conversion.Conv env telescope' telescope) :
    Arguments env [] ctx mode data telescope' xs result := by
  cases arguments with
  | nil result => exact .nil (converted.trans result)
  | cons head value rest => exact .cons (converted.trans head) value rest

/-- Consume a real dependent Pi, cancelling the independently supplied
conversion head using the authenticated environment. -/
theorem arguments_pi_view (wf : UnifiedProgram.EnvWellFormed env)
    (arguments : Arguments env [] ctx true data (.pi erased domain body) (value :: values) result) :
    HasType env [] ctx true value domain ∧
      Arguments env [] ctx true data (body.subst (single value)) values result := by
  cases arguments with
  | cons converted typed rest =>
    have parts := converted.pi_injective wf.admissible
    refine ⟨.convert (by simpa only [Bool.true_or] using typed) parts.2.1.symm,?_⟩
    exact arguments_change_telescope rest (parts.2.2.substitution (single value) wf.closed)

/-- The existing mutual Arguments judgment itself supplies every argument's
typing and all instantiation evidence. This lemma introduces no signature axiom. -/
theorem arguments_apply (arguments : Arguments env [] ctx true data telescope values result)
    (typed : HasType env [] ctx true function telescope) :
    HasType env [] ctx true (applications function values) result := by
  induction values generalizing telescope function with
  | nil =>
    cases arguments with
    | nil converted => exact .convert typed converted
  | cons value values ih =>
    cases arguments with
    | cons converted valueTyped rest =>
      apply ih rest
      exact .app (.convert typed converted) (by simpa only [Bool.true_or] using valueTyped) (Or.inl rfl)

/-- Follow exactly one real Pi for each supplied field. A function returned
by the motive is never mistaken for another constructor field. -/
def consume : Term → List Term → Option Term
  | telescope,[] => some telescope
  | .pi _ _ body,value :: values => consume (body.subst (single value)) values
  | _,_ :: _ => none

/-- A structural certificate of equal field domains; erasure annotations may
differ because all instantiation here is in ghost mode. -/
inductive SameDomains : Nat → Term → Term → Prop where
  | zero (first second : Term) : SameDomains 0 first second
  | step (erased erased' : Bool) (domain : Term) : SameDomains n first second →
      SameDomains (n+1) (.pi erased domain first) (.pi erased' domain second)

theorem SameDomains.substitution (related : SameDomains n first second) (σ : Nat → Term) :
    SameDomains n (first.subst σ) (second.subst σ) := by
  induction related generalizing σ with
  | zero => exact .zero _ _
  | step erased erased' domain rest ih =>
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      SameDomains.step erased erased' (domain.subst σ) (ih (liftSubOne σ))

/-- Apply an actual checked branch using the actual constructor argument
proofs. The structural domain certificate is instantiated beneath each binder. -/
theorem apply_same_domains (wf : UnifiedProgram.EnvWellFormed env)
    (related : SameDomains values.length telescope branchType)
    (arguments : Arguments env [] ctx true data telescope values result)
    (branch : HasType env [] ctx true function branchType) :
    ∃ output,consume branchType values = some output ∧
      HasType env [] ctx true (applications function values) output := by
  induction values generalizing telescope branchType function with
  | nil => exact ⟨branchType,rfl,branch⟩
  | cons value values ih =>
    cases related with
    | step erased erased' domain tail =>
      obtain ⟨valueTyped,rest⟩ := arguments_pi_view wf arguments
      have applied := HasType.app branch (by simpa only [Bool.true_or] using valueTyped) (Or.inl rfl)
      exact ih (tail.substitution (single value)) rest applied

theorem signature_same_domains (family : Nat) (signature : Signature) (result : Term) :
    SameDomains signature.fields.length (signatureTerm family signature)
      (closeDataFields (signature.fields.map fun field => (field.erased,field.domain)) result) := by
  rcases signature with ⟨fields,indices⟩
  induction fields with
  | nil => exact .zero _ _
  | cons field fields ih =>
    simpa only [signatureTerm,closeDataFields,List.foldr_cons,List.map_cons,List.length_cons] using
      SameDomains.step field.erased field.erased field.domain ih

private theorem parameterAt_empty_stable {term : Term} {position depth : Nat} (scope : term.Scoped position) :
    term.subst (parameterAt depth position []) = term := by
  calc
    term.subst (parameterAt depth position []) = term.subst Term.var := by
      apply scoped_subst_congr scope
      intro x inside
      simp only [parameterAt,inside,↓reduceIte]
    _ = term := Term.subst_id term

theorem instantiatedFields_no_parameters (depth position : Nat) (fields : List Field)
    (scopes : ∀ (j : Nat) field,fields[j]? = some field → field.domain.Scoped (position + j)) :
    instantiatedFields depth [] false position fields = fields.map (fun field => (field.erased,field.domain)) := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
    simp only [instantiatedFields,Bool.false_and,Bool.false_eq_true,↓reduceIte,List.map_cons]
    rw [parameterAt_empty_stable (by simpa only [Nat.add_zero] using scopes 0 field rfl)]
    congr 1
    apply ih
    intro j selected found
    simpa only [Nat.add_assoc,Nat.add_comm 1 j] using scopes (j+1) selected found

/-- The certificate for an authentic successful nonparameter Case builder is
derived here, not accepted as a signature premise. -/
theorem data_case_domains_no_parameters (scope : UnifiedProgram.SignatureScoped signature)
    (generated : dataCaseType family constructor 0 depth signature [] motive false proof = some type) :
    SameDomains signature.fields.length (signatureTerm family signature) type := by
  unfold dataCaseType at generated
  simp only [List.length_nil,Nat.not_lt_zero,Bool.false_eq_true,List.drop_zero,↓reduceIte] at generated
  cases generated
  rw [instantiatedFields_no_parameters depth 0 signature.fields
    (by intro j field found;simpa only [Nat.zero_add] using scope.domains j field found)]
  exact signature_same_domains _ _ _

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
