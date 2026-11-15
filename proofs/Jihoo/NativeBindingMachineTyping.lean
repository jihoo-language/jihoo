import Jihoo.NativeBindingMachineHeap

/-! Original source typing and exact origin stores accompany the actual CBV
binding updates. These are source-code and variable-access invariants, not an
unproved semantic typing relation for arbitrary returned runtime values. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

def SourceTyped (env : Environment) (mode : Bool) (code : Code) (type : Term) : Prop :=
  ContextFormed env code.context ∧ Ghost.Substitution env code.context [] code.origins ∧
    ∃ localType, HasType env code.context mode code.term localType ∧
      Conversion.Conv env (localType.subst code.origins) type

theorem SourceTyped.closed
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : SourceTyped env mode code type) : HasType env [] true code.origin type := by
  obtain ⟨formed,closing,localType,source,converted⟩ := typed
  exact (source.ghostSubstitution history.wellFormed closing).convert converted

/-- The actual closure carries exactly the creator's original code context,
origins and values, and creation does not execute its body. -/
theorem lambda_creation (code : Code)
    (shape : code.term = .lam erased domain body) (stack : List Frame) :
    evaluateAction code stack = .control
      (.returned (.closure erased domain body code.context code.origins code.values)) stack := by
  simp only [evaluateAction,shape]

/-- The actual binding transition retains false-mode source body typing and
extends its exact ghost origin store. Runtime arguments may be owner handles;
their computations are never substituted into the source code body. -/
theorem enter_source_typed
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (functionTyped : SourceTyped env false ⟨.lam erased domain body,context,origins,captured⟩
      (.pi actualErased actualDomain actualBody))
    (argumentTyped : SourceTyped env argumentMode argumentCode actualDomain)
    (runtimeArgument : Option Value) :
    erased = actualErased ∧
      SourceTyped env false (enter erased domain body context origins captured argumentCode.origin runtimeArgument)
        (actualBody.subst (single argumentCode.origin)) := by
  obtain ⟨formed,closing,localType,functionTyped,actualType⟩ := functionTyped
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := functionTyped.lamView
  have converted := (sourceType.substitution origins history.wellFormed.closed).trans actualType
  have convertedPi : Conversion.Conv env
      (.pi erased (domain.subst origins) (bodyType.subst (liftSubOne origins)))
      (.pi actualErased actualDomain actualBody) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameFlag,domainConverted,bodyConverted⟩ := convertedPi.pi_injective history.wellFormed.admissible
  have argumentOriginTyped := (argumentTyped.closed history).convert domainConverted.symm
  refine ⟨sameFlag,.cons formed binder,closing.consValues argumentOriginTyped,bodyType,bodyTyped,?_⟩
  simpa only [enter,subst_lift_consValues] using
    bodyConverted.substitution (single argumentCode.origin) history.wellFormed.closed

/-- Parent application typing supplies both actual evaluation frames' source
typing. Its existing code gate is retained by the original source derivation. -/
theorem application_source_frames
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : SourceTyped env false code type) (shape : code.term = .app function argument) :
    ∃ erased domain body,
      SourceTyped env false (code.child function) ((Term.pi erased domain body).subst code.origins) ∧
      SourceTyped env erased (code.child argument) (domain.subst code.origins) ∧
      Conversion.Conv env ((body.subst (single argument)).subst code.origins) type := by
  obtain ⟨formed,closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨erased,domain,body,functionTyped,argumentTyped,allowed,resultConverted⟩ := source.appView
  refine ⟨erased,domain,body,⟨formed,closing,_,functionTyped,.refl _⟩,
    ⟨formed,closing,_,by simpa only [Code.child,Bool.false_or] using argumentTyped,.refl _⟩,?_⟩
  exact (resultConverted.substitution code.origins history.wellFormed.closed).trans converted

/-- Runtime slot presence and erasure agree with original source lookups.
The values' semantic heap types are a separate, explicitly open invariant. -/
def Ready (context : Context) (values : List (Option Value)) : Prop :=
  ∀ index binding, lookup context index = some binding →
    ∃ value, values[index]? = some value ∧ value.isNone = binding.erased

theorem Ready.empty : Ready [] [] := by
  intro index binding selected
  simp [lookup] at selected

theorem Ready.cons (ready : Ready context captured)
    (flag : argument.isNone = erased) : Ready (⟨domain,erased⟩ :: context) (argument :: captured) := by
  intro index binding selected
  cases index with
  | zero =>
      simp only [lookup,Option.some.injEq] at selected
      subst binding
      exact ⟨argument,rfl,flag⟩
  | succ index =>
      obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp selected
      subst binding
      exact ready index original found

private def Readable (context : Context) (mode : Bool) : Term → Prop
  | .var index => ∃ binding, lookup context index = some binding ∧ (mode = true ∨ binding.erased = false)
  | _ => True

private theorem readable (typed : HasType env context mode term type) : Readable context mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx mode term _ _ => Readable ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case var => exact ⟨_,by assumption,by assumption⟩

/-- A code-typed source variable with aligned captured slots always returns
an actual runtime value. Missing/erased-variable faults are excluded here by
the original typing and slot flags, without assuming lookup success. -/
theorem code_variable_returns (typed : SourceTyped env false code type)
    (ready : Ready code.context code.values) (shape : code.term = .var index) :
    ∃ value, evaluateAction code stack = .control (.returned value) stack := by
  obtain ⟨formed,closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨binding,selected,permission⟩ := readable source
  have relevant : binding.erased = false := by simpa using permission
  obtain ⟨value,found,flag⟩ := ready index binding selected
  cases value with
  | none => simp [relevant] at flag
  | some value => exact ⟨value,by simp only [evaluateAction,shape,found]⟩

end Jihoo.NativeKernel.Environment.BindingMachine
