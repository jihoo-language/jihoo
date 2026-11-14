import Jihoo.NativeFamilySourceFundamental
set_option maxUniverseOffset 40

/-! Actual-source closure over arbitrary finite blocks of higher-kinded
families and independently leveled universe parameters. The model endpoint
is an iterated concrete dependent Pi code, not an interpretation interface. -/
namespace Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
open Jihoo.NativeKernel.Environment.Conversion

def Signature.sort (signature : Signature) : Finite.LevelSort :=
  (Finite.LevelSort.type ⟨signature.input.val+1,by omega⟩).pi
    (.type ⟨signature.result.val+1,by omega⟩)

theorem Signature.sort_native (signature : Signature) :
    signature.sort.native = .type (max (signature.input.val+1) (signature.result.val+1)) := rfl

def Assignment.extendParameter {levelList : List (Fin 32)} {signatures : Fin familyCount → Signature}
    (assignment : Assignment levelList.get signatures) (level : Fin 32)
    (code : Finite.Universe (.type ⟨level.val,by omega⟩)) : Assignment (level :: levelList).get signatures where
  parameters index := Fin.cases code (fun i => assignment.parameters i) index
  families := assignment.families

def Assignment.extendFamily {familyList : List Signature}
    (assignment : Assignment (List.get ([] : List (Fin 32))) familyList.get)
    (signature : Signature) (family : Finite.Carrier signature.kindCode) :
    Assignment (List.get ([] : List (Fin 32))) (signature :: familyList).get where
  parameters index := Fin.elim0 index
  families index := Fin.cases family (fun i => assignment.families i) index

def sourceContext (levelList : List (Fin 32)) (familyList : List Signature) : Context :=
  levelList.map (fun level => ⟨.univ level.val,false⟩) ++
    familyList.map (fun signature => ⟨signature.term,false⟩)

theorem baseContext_list (levelList : List (Fin 32)) (familyList : List Signature) :
    baseContext levelList.get familyList.get = sourceContext levelList familyList := by
  have parameters := congrArg (List.map (fun level : Fin 32 => (⟨.univ level.val,false⟩ : Binding)))
    (List.ofFn_getElem (xs := levelList))
  have families := congrArg (List.map (fun signature : Signature => (⟨signature.term,false⟩ : Binding)))
    (List.ofFn_getElem (xs := familyList))
  have appended {a b c d : Context} (first : a = b) (second : c = d) : a ++ c = b ++ d := by rw [first,second]
  simpa only [baseContext,sourceContext,List.map_ofFn,Function.comp_def,List.get_eq_getElem] using appended parameters families

inductive Scheme : List (Fin 32) → List Signature → Type where
  | body {levelList : List (Fin 32)} {familyList : List Signature}
      {A : TypeCode levelList.length familyList.length} :
      Expression levelList.get familyList.get [] A → Scheme levelList familyList
  | parameter (level : Fin 32) : Scheme (level :: levelList) familyList → Scheme levelList familyList
  | family (signature : Signature) : Scheme [] (signature :: familyList) → Scheme [] familyList

def Scheme.syntax : Scheme levelList familyList → Term
  | .body expression => expression.syntax
  | .parameter level inner => .lam false (.univ level.val) inner.syntax
  | .family signature inner => .lam false signature.term inner.syntax

def Scheme.type : Scheme levelList familyList → Term
  | .body (A := A) _ => A.syntax 0
  | .parameter level inner => .pi false (.univ level.val) inner.type
  | .family signature inner => .pi false signature.term inner.type

def Scheme.sort : Scheme levelList familyList → Finite.LevelSort
  | .body (levelList := levelList) (familyList := familyList) (A := A) _ => A.sort levelList.get familyList.get
  | .parameter level inner => (Finite.LevelSort.type ⟨level.val+1,by omega⟩).pi inner.sort
  | .family signature inner => signature.sort.pi inner.sort

def Scheme.code : (scheme : Scheme levelList familyList) →
    Assignment levelList.get familyList.get → Finite.Universe scheme.sort
  | .body (A := A) expression,assignment => A.meaning assignment expression.valid
  | .parameter level inner,assignment =>
    Finite.pi (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extendParameter level (Finite.Values.decode level parameter)))
  | .family signature inner,assignment =>
    Finite.pi signature.kindCode inner.sort (fun family => inner.code (assignment.extendFamily signature family))

def Scheme.meaning : (scheme : Scheme levelList familyList) →
    (assignment : Assignment levelList.get familyList.get) → Finite.Carrier (scheme.code assignment)
  | .body expression,assignment => expression.meaning (assignment := assignment) .nil
  | .parameter level inner,assignment =>
    (Finite.piMeaning (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extendParameter level (Finite.Values.decode level parameter)))).lam
        (fun parameter => inner.meaning (assignment.extendParameter level (Finite.Values.decode level parameter)))
  | .family signature inner,assignment =>
    (Finite.piMeaning signature.kindCode inner.sort
      (fun family => inner.code (assignment.extendFamily signature family))).lam
        (fun family => inner.meaning (assignment.extendFamily signature family))

theorem Scheme.typed (scheme : Scheme levelList familyList) :
    HasType env (sourceContext levelList familyList) true scheme.syntax scheme.type := by
  induction scheme with
  | body expression =>
    simpa only [Scheme.syntax,Scheme.type,context,List.length_nil,baseContext_list] using expression.typed (env := env)
  | parameter level inner ih =>
    exact .lam (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | family signature inner ih =>
    exact .lam (.intro (s := .type (max (signature.input.val+1) (signature.result.val+1))) signature.formed
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.formed (scheme : Scheme levelList familyList) :
    HasType env (sourceContext levelList familyList) true scheme.type scheme.sort.native.term := by
  induction scheme with
  | @body levelList familyList A expression =>
    simpa only [Scheme.type,Scheme.sort,context,List.length_nil,baseContext_list,
      TypeCode.sort,Finite.LevelSort.native,SortTag.term] using A.formed (env := env) (Γ := []) expression.valid
  | parameter level inner ih =>
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native]
    exact .pi (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih
  | family signature inner ih =>
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native,Signature.sort_native]
    exact .pi (.intro (s := .type (max (signature.input.val+1) (signature.result.val+1))) signature.formed
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.parameter_application (level : Fin 32) (inner : Scheme (level :: levelList) familyList)
    (assignment : Assignment levelList.get familyList.get) (parameter : Finite.Carrier (Finite.Values.codeUniverse level)) :
    (Finite.piMeaning (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extendParameter level (Finite.Values.decode level parameter)))).app
        ((Scheme.parameter level inner).meaning assignment) parameter =
      inner.meaning (assignment.extendParameter level (Finite.Values.decode level parameter)) :=
  (Finite.piMeaning _ _ _).beta _ _

theorem Scheme.family_application (signature : Signature) (inner : Scheme [] (signature :: familyList))
    (assignment : Assignment (List.get ([] : List (Fin 32))) familyList.get) (family : Finite.Carrier signature.kindCode) :
    (Finite.piMeaning signature.kindCode inner.sort
      (fun family => inner.code (assignment.extendFamily signature family))).app
        ((Scheme.family signature inner).meaning assignment) family =
      inner.meaning (assignment.extendFamily signature family) :=
  (Finite.piMeaning _ _ _).beta _ _

inductive UniverseRecognized : List (Fin 32) → List Signature → Term → Prop where
  | body : Recognized levelList.get familyList.get 0 termBody → UniverseRecognized levelList familyList termBody
  | parameter (level : Fin 32) : UniverseRecognized (level :: levelList) familyList termBody →
      UniverseRecognized levelList familyList (.lam false (.univ level.val) termBody)
  | family (signature : Signature) : UniverseRecognized [] (signature :: familyList) termBody →
      UniverseRecognized [] familyList (.lam false signature.term termBody)

theorem universe_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : UniverseRecognized levelList familyList term) :
    ∀ {mode type}, HasType env (sourceContext levelList familyList) mode term type →
      ∃ scheme : Scheme levelList familyList, scheme.syntax = term ∧ Conv env scheme.type type := by
  induction recognized with
  | @body termBody levelList familyList recognized =>
    intro mode type typed
    have validΓ : ContextValid levelList.get familyList.get [] := by intro A member; cases member
    have contextTyped := typed
    rw [←baseContext_list] at contextTyped
    obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl validΓ contextTyped
    exact ⟨.body expression,erased,converted⟩
  | parameter level recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.parameter level inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted
  | family signature recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.family signature inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted

/-- This endpoint interprets actual source typing with arbitrary finite family
and universe abstraction blocks by constructing the entire dependent Pi value. -/
theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (sourceContext levelList familyList) mode term type)
    (recognized : UniverseRecognized levelList familyList term) :
    ∃ scheme : Scheme levelList familyList, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levelList.get familyList.get,
        Nonempty (Finite.Carrier (scheme.code assignment)) := by
  obtain ⟨scheme,erased,converted⟩ := universe_principal wf recognized typed
  exact ⟨scheme,erased,converted,fun assignment => ⟨scheme.meaning assignment⟩⟩

theorem checked_universe_fundamental
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env (sourceContext levelList familyList) mode term type)
    (recognized : UniverseRecognized levelList familyList term) :
    ∃ scheme : Scheme levelList familyList, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levelList.get familyList.get,
        Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental history.wellFormed typed recognized

end Jihoo.NativeKernel.Environment.Semantics.FamilyCodes
