import Jihoo.NativeBindingMachineMutable
import Jihoo.NativeLoanDeltaPreservation

/-! Pack and Witness share the machine's U64 representation. A local
interpretation records the checked original predicate and evidence without
expanding the runtime value or changing the legacy representation relation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def RefinementInputs
    (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .pack predicate witness evidence =>
      HasType env loans ctx true predicate (.pi false .u64 .prop) ∧
      HasType env loans ctx mode witness .u64 ∧ HasType env loans ctx true evidence (.app predicate witness)
  | .witness packed => ∃ predicate, HasType env loans ctx mode packed (.refine predicate)
  | _ => True

private theorem refinement_inputs (typed : HasType env loans ctx mode term type) :
    RefinementInputs env loans ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => RefinementInputs env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case witness => exact ⟨_,by assumption⟩
  case dataElim => split <;> trivial

theorem HasType.pack_inputs (typed : HasType env loans ctx mode (.pack predicate number evidence) type) :
    HasType env loans ctx true predicate (.pi false .u64 .prop) ∧
    HasType env loans ctx mode number .u64 ∧ HasType env loans ctx true evidence (.app predicate number) :=
  refinement_inputs typed

theorem HasType.witness_input (typed : HasType env loans ctx mode (.witness packed) type) :
    ∃ predicate, HasType env loans ctx mode packed (.refine predicate) := refinement_inputs typed

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- A retained U64 represents the original checked refinement introduction.
The predicate and its proof remain available to the source interpretation. -/
def RefinementWord (env : Environment) (source type : Term) (representation : Value) : Prop :=
  ∃ (predicate : Term) (number : Nat) (evidence : Term),
    source = .pack predicate (.natural number) evidence ∧ representation = .natural number ∧
    LoanTyping.HasType env [] [] true predicate (.pi false .u64 .prop) ∧
    LoanTyping.HasType env [] [] true (.natural number) .u64 ∧
    LoanTyping.HasType env [] [] true evidence (.app predicate (.natural number)) ∧
    LoanTyping.Conversion.Conv env (.refine predicate) type

theorem RefinementWord.ghost_type (word : RefinementWord env source type representation) :
    LoanTyping.HasType env [] [] true source type := by
  obtain ⟨_,_,_,rfl,_,predicate,number,evidence,converted⟩ := word
  exact (LoanTyping.HasType.pack predicate number evidence).convert converted

theorem RefinementWord.convert (word : RefinementWord env source type representation)
    (converted : LoanTyping.Conversion.Conv env type requested) :
    RefinementWord env source requested representation := by
  obtain ⟨predicate,number,evidence,shape,represented,predicateTyped,numberTyped,evidenceTyped,original⟩ := word
  exact ⟨predicate,number,evidence,shape,represented,predicateTyped,numberTyped,evidenceTyped,original.trans converted⟩

private theorem literal_pack_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .pack predicate (.natural number) evidence) (width : number < 2^64) :
    run 3 state = ⟨⟨state.heap,.returned (.natural number),state.stack,state.pending⟩,[],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,executeLegacy,execute,Option.map_none,
    returnAction,resumeBuffer,width,↓reduceIte]
  rfl

private theorem variable_witness_steps (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .witness (.var slot)) (stored : code.values[slot]? = some (some (.natural number))) :
    run 3 state = ⟨⟨state.heap,.returned (.natural number),state.stack,state.pending⟩,[],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,executeLegacy,execute,Option.map_none,
    returnAction,resumeBuffer,stored]
  rfl

/-- Pack evaluates only the literal witness. Full original typing builds the
word interpretation at the requested refinement type, including conversion. -/
theorem typed_literal_pack (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .pack predicate (.natural number) evidence) :
    run 3 state = ⟨⟨state.heap,.returned (.natural number),state.stack,state.pending⟩,[],3⟩ ∧
    RefinementWord env (code.term.subst meanings) type (.natural number) := by
  have closed : LoanTyping.HasType env [] [] true
      (.pack (predicate.subst meanings) (.natural number) (evidence.subst meanings)) type := by
    simpa only [shape,Term.subst,substArgs,Op.binders,liftSub] using typed.closed history
  obtain ⟨predicateTyped,numberTyped,evidenceTyped⟩ := closed.pack_inputs
  refine ⟨literal_pack_steps state evaluating shape numberTyped.natural_bound,?_⟩
  refine ⟨predicate.subst meanings,number,evidence.subst meanings,?_,rfl,
    predicateTyped,numberTyped,evidenceTyped,closed.principalView⟩
  simp only [shape,Term.subst,substArgs,Op.binders,liftSub]

/-- The actual pending refinement frame forwards the computed word, restoring
the saved continuation. Typed replay of the original closed witness supplies
the matching source refinement value and retains its dependent evidence. -/
theorem typed_computed_pack_resume (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .pack predicate witness evidence)
    (wordSteps : LoanTyping.DeltaEvaluation.Steps env (witness.subst meanings) (.natural number))
    (returned : state.control = .returned (.natural number))
    (stackShape : state.stack = [])
    (pendingShape : state.pending = (.refinement,saved) :: pending) :
    let source := Term.pack (predicate.subst meanings) (.natural number) (evidence.subst meanings)
    step state = some (⟨state.heap,.returned (.natural number),saved,pending⟩,none) ∧
    RefinementWord env source type (.natural number) ∧
    RawLend.Forward env (code.term.subst meanings) source := by
  let source := Term.pack (predicate.subst meanings) (.natural number) (evidence.subst meanings)
  have original : code.term.subst meanings =
      .pack (predicate.subst meanings) (witness.subst meanings) (evidence.subst meanings) := by
    simp only [shape,Term.subst,substArgs,Op.binders,liftSub]
  have steps : LoanTyping.DeltaEvaluation.Steps env (code.term.subst meanings) source := by
    rw [original]
    exact .node .pack (by intro impossible; cases impossible)
      (.cons (.computation (.family .refl)) (.cons wordSteps (.cons (.computation (.family .refl)) .nil)))
  obtain ⟨forward,computed⟩ := history.delta_computation_preservation steps (typed.closed history)
  obtain ⟨predicateTyped,numberTyped,evidenceTyped⟩ := computed.pack_inputs
  refine ⟨?_,⟨predicate.subst meanings,number,evidence.subst meanings,rfl,rfl,
    predicateTyped,numberTyped,evidenceTyped,computed.principalView⟩,forward⟩
  simp only [step,returned,stackShape,returnAction,pendingShape,resumeBuffer]

/-- Witness projects the existing word of a retained refinement slot.
Its original Loan64 argument fixes the refinement predicate, and the actual
result is typed at the original converted U64 result type. -/
theorem typed_variable_witness (state : State)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .witness (.var slot))
    (stored : code.values[slot]? = some (some representation))
    (word : RefinementWord env (meanings slot) storedType representation) :
    ∃ predicate number,
      LoanTyping.HasType env loans code.context false (.var slot) (.refine predicate) ∧
      RefinementWord env (meanings slot) (.refine (predicate.subst meanings)) (.natural number) ∧
      run 3 state = ⟨⟨state.heap,.returned (.natural number),state.stack,state.pending⟩,[],3⟩ ∧
      LoanTyping.HasType env [] [] false (.natural number) type := by
  obtain ⟨closing,_,original,converted⟩ := typed
  rw [shape] at original
  obtain ⟨predicate,input⟩ := original.witness_input
  have closedInput : LoanTyping.HasType env [] [] true (meanings slot) (.refine (predicate.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using input.ghostSubstitution history.wellFormed closing
  have refined := word.convert (word.ghost_type.unique history.wellFormed closedInput)
  obtain ⟨_,number,_,_,represented,_,numberTyped,_,_⟩ := word
  have sourceType : LoanTyping.Conversion.Conv env .u64 type := by
    simpa only [Term.subst,substArgs] using
      (original.principalView.substitution meanings history.wellFormed.closed).trans converted
  subst representation
  exact ⟨predicate,number,input,refined,variable_witness_steps state evaluating shape stored,
    (LoanTyping.HasType.natural numberTyped.natural_bound).convert sourceType⟩

namespace Examples

set_option maxRecDepth 4096

private def predicate : Term := .lam false .u64 (.lt (.var 0) (.natural 8))
private def packed : Term := .pack predicate (.natural 3) (.decide (.natural 3) (.natural 8))
private def project : Term := .app (.lam false (.refine predicate) (.witness (.var 0))) packed

theorem refinement_admitted : LoanTyping.MixedProgram.checkDeclaration 32 64 .empty
    ⟨.u64,project⟩ = some ⟨.u64,project⟩ := by cbv

theorem refinement_returns : observe (run 20 (initial project)) = .natural 3 := by rfl

theorem refinement_origin :
    (run 20 (initial project)).events = [.legacy (.activate false (.witness (.var 0)) packed)] := by
  have observed : (run 20 (initial project)).events =
      [.legacy (.activate false (.witness (.var 0)) (packed.subst Term.var))] := by rfl
  simpa only [Term.subst_id] using observed

theorem refinement_erases_evidence :
    let erased := Term.alloc (.natural 1) (.integer 11)
    (run 5 (initial (.witness (.pack erased (.natural 3) erased)))).events = [] := by rfl

theorem witness_wrong_representation :
    observe (run 3 (initial (.witness (.integer 3)))) = .fault .wrongValue := by rfl

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
