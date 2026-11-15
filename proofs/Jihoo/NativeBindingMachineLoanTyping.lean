import Jihoo.NativeBindingMachineReaderState
import Jihoo.NativeBindingMachineTyping
import Jihoo.NativeLoanFunctionInversion

/-! The full Loan64 judgment and its actual mixed history accompany original
code and ghost origins across real closure entry. These are source typing and
slot-permission lemmas, not semantic typing of arbitrary runtime values. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Ghost
open CodeKinds

theorem Substitution.consValues
    (closing : Substitution env ctx [] values)
    (argument : HasType env [] [] true value (domain.subst values)) :
    Substitution env (⟨domain,erased⟩ :: ctx) [] (consValues value values) := by
  intro index binding selected
  cases index with
  | zero =>
      simp only [lookup,Option.some.injEq] at selected
      subst binding
      simpa only [CodeKinds.consValues,shift_subst_consValues] using argument
  | succ index =>
      obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      simpa only [CodeKinds.consValues,shift_subst_consValues] using closing index original found

end Jihoo.NativeKernel.Environment.LoanTyping.Ghost

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- Actual source derivation with its exact closing origin store. Runtime value
interpretation and resource-stack preservation are deliberately not assumed. -/
def LoanSourceTyped (env : Environment) (loans : Loans.Stack) (mode : Bool)
    (code : Code) (type : Term) : Prop :=
  LoanTyping.Ghost.Substitution env code.context [] code.origins ∧
    ∃ localType, LoanTyping.HasType env loans code.context mode code.term localType ∧
      LoanTyping.Conversion.Conv env (localType.subst code.origins) type

theorem LoanSourceTyped.initial (typed : LoanTyping.HasType env [] [] mode term type) :
    LoanSourceTyped env [] mode (.initial term) type := by
  refine ⟨?_,type,typed,?_⟩
  · intro index binding selected
    cases selected
  · simpa only [Code.initial,Term.subst_id] using (show LoanTyping.Conversion.Conv env type type from .refl type)

theorem LoanSourceTyped.closed
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type) :
    LoanTyping.HasType env [] [] true code.origin type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  exact (source.ghostSubstitution history.wellFormed closing).convert converted

theorem enter_loan_source_typed
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (functionTyped : LoanSourceTyped env loans false
      ⟨.lam erased domain body,context,origins,captured⟩ (.pi actualErased actualDomain actualBody))
    (argumentTyped : LoanSourceTyped env argumentLoans argumentMode argumentCode actualDomain)
    (runtimeArgument : Option Value) :
    erased = actualErased ∧
      LoanSourceTyped env loans false
        (enter erased domain body context origins captured argumentCode.origin runtimeArgument)
        (actualBody.subst (single argumentCode.origin)) := by
  obtain ⟨closing,localType,functionTyped,actualType⟩ := functionTyped
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := functionTyped.lamView
  have converted := (sourceType.substitution origins history.wellFormed.closed).trans actualType
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi erased (domain.subst origins) (bodyType.subst (liftSubOne origins)))
      (.pi actualErased actualDomain actualBody) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameFlag,domainConverted,bodyConverted⟩ := convertedPi.pi_injective history.wellFormed.admissible
  have argumentOriginTyped := (argumentTyped.closed history).convert domainConverted.symm
  refine ⟨sameFlag,closing.consValues argumentOriginTyped,bodyType,bodyTyped,?_⟩
  simpa only [enter,subst_lift_consValues] using
    bodyConverted.substitution (single argumentCode.origin) history.wellFormed.closed

theorem application_loan_source_frames
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .app function argument) :
    ∃ erased domain body,
      LoanSourceTyped env loans false (code.child function) ((Term.pi erased domain body).subst code.origins) ∧
      LoanSourceTyped env loans erased (code.child argument) (domain.subst code.origins) ∧
      LoanTyping.Conversion.Conv env ((body.subst (single argument)).subst code.origins) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨erased,domain,body,functionTyped,argumentTyped,allowed,resultConverted⟩ := source.appView
  refine ⟨erased,domain,body,⟨closing,_,functionTyped,.refl _⟩,
    ⟨closing,_,by simpa only [Code.child,Bool.false_or] using argumentTyped,.refl _⟩,?_⟩
  exact (resultConverted.substitution code.origins history.wellFormed.closed).trans converted

theorem LoanSlots.child (slots : LoanSlots code loans stack) (term : Term) :
    LoanSlots (code.child term) loans stack := slots

/-- A normal binder shifts source indices and actual runtime slots together.
Existing loans keep the same lexical key and concrete owner identity. -/
theorem LoanSlots.enter (slots : LoanSlots code loans stack)
    (entered : Loans.Entered code.context.length loans)
    (erased : Bool) (domain body argumentOrigin : Term) (argument : Option Value) :
    LoanSlots (BindingMachine.enter erased domain body code.context code.origins code.values argumentOrigin argument)
      loans stack := by
  intro index active
  change Loans.active (code.context.length+1) loans index = true at active
  cases index with
  | zero =>
      obtain ⟨frame,member,before,same⟩ := Loans.active_iff.mp active
      have previous := entered frame member
      omega
  | succ index =>
      have permission : Loans.active code.context.length loans index = true := by
        simpa only [Loans.active_weaken entered] using active
      obtain ⟨object,stored,present⟩ := slots index permission
      refine ⟨object,?_,?_⟩
      · simpa only [BindingMachine.enter,List.getElem?_cons_succ] using stored
      · simpa only [BindingMachine.enter,List.length_cons,Nat.add_sub_add_right] using present

/-- Reader entry supplies the new static named-owner permission from the
actual saved owner slot and the newly installed concrete reader frame. -/
theorem LoanSlots.begin_reader (slots : LoanSlots code loans stack)
    (stored : code.values[owner]? = some (some (.owner object)))
    (token : Nat) (origin readerOrigin : Term) (continuation : Code) :
    LoanSlots code (Loans.enter code.context.length owner loans)
      (.lendReader token object (some (code.context.length-owner)) origin readerOrigin continuation :: stack) := by
  intro index active
  rw [Loans.active_enter,Bool.or_eq_true] at active
  rcases active with same | previous
  · have identity : owner = index := by simpa only [beq_iff_eq] using same
    subst index
    exact ⟨object,stored,_,List.mem_cons_self,token,rfl⟩
  · obtain ⟨object,stored,frame,member,token,descriptor⟩ := slots index previous
    exact ⟨object,stored,frame,List.mem_cons_of_mem _ member,token,descriptor⟩

/-- Admission's actual mixed declaration supplies the entry source derivation
and that same checker's resource evidence. No legacy typing history is used. -/
theorem checked_mixed_definition_entry
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source expanded) :
    ∃ sort : SortTag,
      LoanSourceTyped env [] (Definitions.bodyMode sort) (.initial expanded.value) expanded.type ∧
      (Definitions.bodyMode sort = false → LoanTyping.ResourceQuantity.ResourceSafe env expanded.value) := by
  obtain ⟨sort,formed,typed,resource⟩ := checked.valid.typing
  exact ⟨sort,LoanSourceTyped.initial typed,resource⟩

/-- The concrete activation, source type and named-owner slot alignment are
preserved together at an ordinary closure call. This does not type the
arbitrary runtime argument's heap contents. -/
theorem activate_loan_source
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (functionTyped : LoanSourceTyped env loans false
      ⟨.lam erased domain body,context,origins,captured⟩ (.pi actualErased actualDomain actualBody))
    (argumentTyped : LoanSourceTyped env argumentLoans argumentMode argumentCode actualDomain)
    (slots : LoanSlots ⟨.lam erased domain body,context,origins,captured⟩ loans stack)
    (entered : Loans.Entered context.length loans) (argument : Option Value) :
    let bodyCode := BindingMachine.enter erased domain body context origins captured argumentCode.origin argument
    execute heap (applyValue (.closure erased domain body context origins captured)
      argumentCode.origin argument stack) =
      (⟨heap,.evaluate bodyCode,stack⟩,some (.activate erased body argumentCode.origin)) ∧
    LoanSourceTyped env loans false bodyCode (actualBody.subst (single argumentCode.origin)) ∧
    LoanSlots bodyCode loans stack := by
  refine ⟨rfl,(enter_loan_source_typed history functionTyped argumentTyped argument).2,?_⟩
  exact slots.enter entered erased domain body argumentCode.origin argument

private def LoanReadable (context : Context) (mode : Bool) : Term → Prop
  | .var index => ∃ binding, lookup context index = some binding ∧ (mode = true ∨ binding.erased = false)
  | _ => True

private theorem loan_readable (typed : LoanTyping.HasType env loans context mode term type) :
    LoanReadable context mode term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx mode term _ _ => LoanReadable ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case var => exact ⟨_,by assumption,by assumption⟩

/-- The original Loan64 variable derivation excludes missing/erased slots
under ordinary captured-slot alignment. -/
theorem loan_code_variable_returns (typed : LoanSourceTyped env loans false code type)
    (ready : Ready code.context code.values) (shape : code.term = .var index) :
    ∃ value, evaluateAction code stack = .control (.returned value) stack := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨binding,selected,permission⟩ := loan_readable source
  have relevant : binding.erased = false := by simpa using permission
  obtain ⟨value,found,flag⟩ := ready index binding selected
  cases value with
  | none => simp [relevant] at flag
  | some value => exact ⟨value,by simp only [evaluateAction,shape,found]⟩

end Jihoo.NativeKernel.Environment.BindingMachine
