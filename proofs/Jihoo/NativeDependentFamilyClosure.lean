import Jihoo.NativeDependentFamilySource
set_option maxUniverseOffset 40

/-! Concrete dependent-Pi closure reconstructed from authentic native source:
universe variables, families B:A→Type_j, arbitrary carrier observations x:A,
and value programs whose types contain fibers B x. All finite block lengths,
mixed universe levels and monotype family domains are quantified. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)

def Signature.sort (signature : Signature parameters) (levels : Fin parameters → Fin 32) : Finite.LevelSort :=
  (signature.input.semanticSort levels).pi (.type ⟨signature.result.val+1,by omega⟩)

theorem Signature.sort_native (signature : Signature parameters) (levels : Fin parameters → Fin 32) :
    (signature.sort levels).native = .type (max (signature.input.nativeLevel levels) (signature.result.val+1)) := by
  rw [Signature.sort,Finite.LevelSort.pi_native,MultiUniverse.Mono.semanticSort_native]
  rfl

def Assignment.extendFamily {levels : Fin parameters → Fin 32} {familyList : List (Signature parameters)}
    (assignment : Assignment levels familyList.get (List.get ([] : List (Mono parameters))))
    (signature : Signature parameters) (family : Finite.Carrier (signature.code assignment.bases)) :
    Assignment levels (signature :: familyList).get (List.get ([] : List (Mono parameters))) where
  bases := assignment.bases
  families index := Fin.cases family (fun i => assignment.families i) index
  observations index := Fin.elim0 index

def Assignment.extendObservation {levels : Fin parameters → Fin 32} {signatures : Fin familyCount → Signature parameters}
    {observations : List (Mono parameters)} (assignment : Assignment levels signatures observations.get)
    (domain : Mono parameters) (value : Finite.Carrier (domain.code assignment.bases)) :
    Assignment levels signatures (domain :: observations).get where
  bases := assignment.bases
  families := assignment.families
  observations index := Fin.cases value (fun i => assignment.observations i) index

def Assignment.extendParameter {levelList : List (Fin 32)}
    (assignment : Assignment levelList.get (List.get ([] : List (Signature levelList.length)))
      (List.get ([] : List (Mono levelList.length)))) (level : Fin 32)
    (code : Finite.Universe (.type ⟨level.val,by omega⟩)) :
    Assignment (level :: levelList).get (List.get ([] : List (Signature (level :: levelList).length)))
      (List.get ([] : List (Mono (level :: levelList).length))) where
  bases.codes index := Fin.cases code (fun i => assignment.bases.codes i) index
  families index := Fin.elim0 index
  observations index := Fin.elim0 index

abbrev sourceContext (levelList : List (Fin 32)) (familyList : List (Signature levelList.length))
    (observations : List (Mono levelList.length)) : Context := observationContext levelList.get familyList observations

theorem sourceContext_parameter (levelList : List (Fin 32)) (level : Fin 32) :
    sourceContext (level :: levelList) [] [] = ⟨.univ level.val,false⟩ :: sourceContext levelList [] [] := by
  simp only [sourceContext,observationContext,familyContext,MultiUniverse.universeContext_list,List.map_cons]

inductive Scheme : (levelList : List (Fin 32)) → List (Signature levelList.length) → List (Mono levelList.length) → Type where
  | body {levelList : List (Fin 32)} {familyList : List (Signature levelList.length)}
      {observations : List (Mono levelList.length)} {A : TypeCode levelList.length familyList.length observations.length} :
      Expression familyList.get observations.get [] A → Scheme levelList familyList observations
  | observation (domain : Mono levelList.length) : Scheme levelList familyList (domain :: observations) →
      Scheme levelList familyList observations
  | family (signature : Signature levelList.length) : Scheme levelList (signature :: familyList) [] → Scheme levelList familyList []
  | parameter (level : Fin 32) : Scheme (level :: levelList) [] [] → Scheme levelList [] []

def Scheme.syntax : Scheme levelList familyList observations → Term
  | .body expression => expression.syntax
  | .observation (familyList := familyList) (observations := observations) domain inner =>
    .lam false (domain.syntax (observations.length+familyList.length)) inner.syntax
  | .family (familyList := familyList) signature inner => .lam false (signature.term familyList.length) inner.syntax
  | .parameter level inner => .lam false (.univ level.val) inner.syntax

def Scheme.type : Scheme levelList familyList observations → Term
  | .body (A := A) _ => A.syntax 0
  | .observation (familyList := familyList) (observations := observations) domain inner =>
    .pi false (domain.syntax (observations.length+familyList.length)) inner.type
  | .family (familyList := familyList) signature inner => .pi false (signature.term familyList.length) inner.type
  | .parameter level inner => .pi false (.univ level.val) inner.type

def Scheme.sort : Scheme levelList familyList observations → Finite.LevelSort
  | .body (levelList := levelList) (familyList := familyList) (A := A) _ => A.sort levelList.get familyList.get
  | .observation (levelList := levelList) domain inner => (domain.semanticSort levelList.get).pi inner.sort
  | .family (levelList := levelList) signature inner => (signature.sort levelList.get).pi inner.sort
  | .parameter level inner => (Finite.LevelSort.type ⟨level.val+1,by omega⟩).pi inner.sort

def Scheme.code : (scheme : Scheme levelList familyList observations) →
    Assignment levelList.get familyList.get observations.get → Finite.Universe scheme.sort
  | .body (A := A) expression,assignment => A.meaning assignment expression.valid
  | .observation domain inner,assignment =>
    Finite.pi (domain.code assignment.bases) inner.sort
      (fun value => inner.code (assignment.extendObservation domain value))
  | .family signature inner,assignment =>
    Finite.pi (signature.code assignment.bases) inner.sort
      (fun family => inner.code (assignment.extendFamily signature family))
  | .parameter level inner,assignment =>
    Finite.pi (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extendParameter level (Finite.Values.decode level parameter)))

def Scheme.meaning : (scheme : Scheme levelList familyList observations) →
    (assignment : Assignment levelList.get familyList.get observations.get) → Finite.Carrier (scheme.code assignment)
  | .body expression,assignment => expression.meaning (assignment := assignment) .nil
  | .observation domain inner,assignment =>
    (Finite.piMeaning (domain.code assignment.bases) inner.sort
      (fun value => inner.code (assignment.extendObservation domain value))).lam
        (fun value => inner.meaning (assignment.extendObservation domain value))
  | .family signature inner,assignment =>
    (Finite.piMeaning (signature.code assignment.bases) inner.sort
      (fun family => inner.code (assignment.extendFamily signature family))).lam
        (fun family => inner.meaning (assignment.extendFamily signature family))
  | .parameter level inner,assignment =>
    (Finite.piMeaning (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extendParameter level (Finite.Values.decode level parameter)))).lam
        (fun parameter => inner.meaning (assignment.extendParameter level (Finite.Values.decode level parameter)))

theorem Scheme.typed (scheme : Scheme levelList familyList observations) :
    HasType env (sourceContext levelList familyList observations) true scheme.syntax scheme.type := by
  induction scheme with
  | body expression => simpa only [Scheme.syntax,Scheme.type,context,List.length_nil] using expression.typed (env := env)
  | observation domain inner ih =>
    exact .lam (.intro (s := .type (domain.nativeLevel _))
      (mono_formed_in domain (observationContext_parameters _ _))
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | family signature inner ih =>
    exact .lam (.intro (s := .type (max (signature.input.nativeLevel _) (signature.result.val+1)))
      (signature.formed (familyContext_parameters _))
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | parameter level inner ih =>
    rw [sourceContext_parameter] at ih
    exact .lam (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.formed (scheme : Scheme levelList familyList observations) :
    HasType env (sourceContext levelList familyList observations) true scheme.type scheme.sort.native.term := by
  induction scheme with
  | @body levelList familyList observations A expression =>
    simpa only [Scheme.type,Scheme.sort,context,List.length_nil,TypeCode.sort,Finite.LevelSort.native,SortTag.term] using
      A.formed (env := env) (Γ := []) expression.valid
  | observation domain inner ih =>
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native,MultiUniverse.Mono.semanticSort_native]
    exact .pi (.intro (s := .type (domain.nativeLevel _))
      (mono_formed_in domain (observationContext_parameters _ _))
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | family signature inner ih =>
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native,Signature.sort_native]
    exact .pi (.intro (s := .type (max (signature.input.nativeLevel _) (signature.result.val+1)))
      (signature.formed (familyContext_parameters _))
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | parameter level inner ih =>
    rw [sourceContext_parameter] at ih
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native]
    exact .pi (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.observation_application {levelList : List (Fin 32)}
    {familyList : List (Signature levelList.length)} {observations : List (Mono levelList.length)}
    (domain : Mono levelList.length)
    (inner : Scheme levelList familyList (domain :: observations))
    (assignment : Assignment levelList.get familyList.get observations.get)
    (value : Finite.Carrier (domain.code assignment.bases)) :
    (Finite.piMeaning (domain.code assignment.bases) inner.sort
      (fun value => inner.code (assignment.extendObservation (observations := observations) domain value))).app
        ((Scheme.observation domain inner).meaning assignment) value =
      inner.meaning (assignment.extendObservation (observations := observations) domain value) :=
  (Finite.piMeaning _ _ _).beta _ _

theorem Scheme.family_application {levelList : List (Fin 32)} {familyList : List (Signature levelList.length)}
    (signature : Signature levelList.length)
    (inner : Scheme levelList (signature :: familyList) [])
    (assignment : Assignment levelList.get familyList.get (List.get ([] : List (Mono levelList.length))))
    (family : Finite.Carrier (signature.code assignment.bases)) :
    (Finite.piMeaning (signature.code assignment.bases) inner.sort
      (fun family => inner.code (assignment.extendFamily (familyList := familyList) signature family))).app
        ((Scheme.family signature inner).meaning assignment) family =
      inner.meaning (assignment.extendFamily (familyList := familyList) signature family) :=
  (Finite.piMeaning _ _ _).beta _ _

inductive UniverseRecognized : (levelList : List (Fin 32)) → List (Signature levelList.length) → List (Mono levelList.length) → Term → Prop where
  | body {levelList : List (Fin 32)} {familyList : List (Signature levelList.length)}
      {observations : List (Mono levelList.length)} {termBody : Term} :
      Recognized familyList observations 0 termBody → UniverseRecognized levelList familyList observations termBody
  | observation (domain : Mono levelList.length) : UniverseRecognized levelList familyList (domain :: observations) termBody →
      UniverseRecognized levelList familyList observations
        (.lam false (domain.syntax (observations.length+familyList.length)) termBody)
  | family (signature : Signature levelList.length) : UniverseRecognized levelList (signature :: familyList) [] termBody →
      UniverseRecognized levelList familyList [] (.lam false (signature.term familyList.length) termBody)
  | parameter (level : Fin 32) : UniverseRecognized (level :: levelList) [] [] termBody →
      UniverseRecognized levelList [] [] (.lam false (.univ level.val) termBody)

theorem universe_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : UniverseRecognized levelList familyList observations term) :
    ∀ {mode type}, HasType env (sourceContext levelList familyList observations) mode term type →
      ∃ scheme : Scheme levelList familyList observations, scheme.syntax = term ∧ Conv env scheme.type type := by
  induction recognized with
  | @body levelList familyList observations termBody recognized =>
    intro mode type typed
    have validΓ : ContextValid familyList.get observations.get [] := by intro A member; cases member
    obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl validΓ typed
    exact ⟨.body expression,erased,converted⟩
  | observation domain recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.observation domain inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted
  | family signature recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.family signature inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted
  | parameter level recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    rw [←sourceContext_parameter] at bodyTyped
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.parameter level inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted

/-- Actual source typing constructs the full dependent Pi model value through
all three variable classes. In particular observation abstraction changes each
fiber B x with the newly supplied semantic argument x. -/
theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (sourceContext levelList familyList observations) mode term type)
    (recognized : UniverseRecognized levelList familyList observations term) :
    ∃ scheme : Scheme levelList familyList observations, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levelList.get familyList.get observations.get,
        Nonempty (Finite.Carrier (scheme.code assignment)) := by
  obtain ⟨scheme,erased,converted⟩ := universe_principal wf recognized typed
  exact ⟨scheme,erased,converted,fun assignment => ⟨scheme.meaning assignment⟩⟩

theorem checked_universe_fundamental
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env (sourceContext levelList familyList observations) mode term type)
    (recognized : UniverseRecognized levelList familyList observations term) :
    ∃ scheme : Scheme levelList familyList observations, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levelList.get familyList.get observations.get,
        Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental history.wellFormed typed recognized

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
