import Jihoo.NativeMultiUniverseFundamental
set_option maxUniverseOffset 40

/-! Nested abstractions over any finite sequence of native universe levels.
Their interpretation is an iterated concrete dependent Pi code, whose family
varies with each decoded argument; no model inhabitation is assumed. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
open Jihoo.NativeKernel.Environment.Conversion

abbrev parameterContext (levels : List (Fin 32)) : Context :=
  levels.map (fun level => ⟨.univ level.val,false⟩)

def Assignment.extend {levels : List (Fin 32)} (assignment : Assignment levels.get)
    (level : Fin 32) (code : Finite.Universe (.type ⟨level.val,by omega⟩)) :
    Assignment (level :: levels).get where
  codes index := Fin.cases code (fun i => assignment.codes i) index

inductive Scheme : List (Fin 32) → Type where
  | body {levels : List (Fin 32)} {A : Mono levels.length} : Expression [] A → Scheme levels
  | abstract (level : Fin 32) : Scheme (level :: levels) → Scheme levels

def Scheme.syntax : Scheme levels → Term
  | .body expression => expression.syntax
  | .abstract level inner => .lam false (.univ level.val) inner.syntax

def Scheme.type : Scheme levels → Term
  | .body (A := A) _ => A.syntax 0
  | .abstract level inner => .pi false (.univ level.val) inner.type

def Scheme.sort : Scheme levels → Finite.LevelSort
  | .body (levels := levels) (A := A) _ => A.semanticSort levels.get
  | .abstract level inner => (Finite.LevelSort.type ⟨level.val+1,by omega⟩).pi inner.sort

def Scheme.code : (scheme : Scheme levels) → Assignment levels.get → Finite.Universe scheme.sort
  | .body (A := A) _, assignment => A.code assignment
  | .abstract level inner, assignment =>
    Finite.pi (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extend level (Finite.Values.decode level parameter)))

def Scheme.meaning : (scheme : Scheme levels) → (assignment : Assignment levels.get) → Finite.Carrier (scheme.code assignment)
  | .body expression, assignment => expression.meaning (assignment := assignment) .nil
  | .abstract level inner, assignment =>
    (Finite.piMeaning (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extend level (Finite.Values.decode level parameter)))).lam
        (fun parameter => inner.meaning (assignment.extend level (Finite.Values.decode level parameter)))

theorem Scheme.typed (scheme : Scheme levels) :
    HasType env (parameterContext levels) true scheme.syntax scheme.type := by
  induction scheme with
  | @body levels A expression =>
    simpa only [Scheme.syntax,Scheme.type,context,List.length_nil,universeContext_list] using expression.typed levels.get
  | abstract level inner ih =>
    exact .lam (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.formed (scheme : Scheme levels) :
    HasType env (parameterContext levels) true scheme.type scheme.sort.native.term := by
  induction scheme with
  | @body levels A expression =>
    simp only [Scheme.type,Scheme.sort,Mono.semanticSort_native,SortTag.term]
    simpa only [context,List.length_nil,universeContext_list] using
      (A.formed (env := env) (Γ := []) (mode := true) levels.get)
  | abstract level inner ih =>
    rw [Scheme.type,Scheme.sort,Finite.LevelSort.pi_native]
    exact .pi (.intro (s := .type (level.val+1)) (.univ level.isLt)
      (Or.inl (by change SortTag.type _ ≠ SortTag.prop; intro h; cases h))) ih

theorem Scheme.meaning_application (level : Fin 32) (inner : Scheme (level :: levels))
    (assignment : Assignment levels.get) (parameter : Finite.Carrier (Finite.Values.codeUniverse level)) :
    (Finite.piMeaning (Finite.Values.codeUniverse level) inner.sort
      (fun parameter => inner.code (assignment.extend level (Finite.Values.decode level parameter)))).app
        ((Scheme.abstract level inner).meaning assignment) parameter =
      inner.meaning (assignment.extend level (Finite.Values.decode level parameter)) :=
  (Finite.piMeaning _ _ _).beta _ _

inductive UniverseRecognized : (levels : List (Fin 32)) → Term → Prop where
  | body : Recognized levels.length 0 termBody → UniverseRecognized levels termBody
  | abstract (level : Fin 32) : UniverseRecognized (level :: levels) termBody →
      UniverseRecognized levels (.lam false (.univ level.val) termBody)

theorem universe_principal (wf : UnifiedProgram.EnvWellFormed env)
    (recognized : UniverseRecognized levels term) :
    ∀ {mode type}, HasType env (parameterContext levels) mode term type →
      ∃ scheme : Scheme levels, scheme.syntax = term ∧ Conv env scheme.type type := by
  induction recognized with
  | @body termBody levels recognized =>
    intro mode type typed
    have contextTyped : HasType env (context levels.get []) mode termBody type := by
      simpa only [context,universeContext_list] using typed
    obtain ⟨A,expression,erased,converted⟩ := recognized_principal wf recognized [] rfl contextTyped
    exact ⟨.body expression,erased,converted⟩
  | abstract level recognized ih =>
    intro mode type typed
    obtain ⟨sort,result,binder,bodyTyped,converted⟩ := typed.lamView
    obtain ⟨inner,erased,bodyConverted⟩ := ih bodyTyped
    refine ⟨.abstract level inner,?_,?_⟩
    · simp only [Scheme.syntax,erased]
    · exact .trans (.node (.pi false) (.cons (.refl _) (.cons bodyConverted .nil))) converted

/-- Actual source typing plus a syntax-only recognizer constructs an entire
iterated Pi interpretation, including mixed universe levels and arbitrarily
many independently assigned carriers. -/
theorem universe_fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env (parameterContext levels) mode term type)
    (recognized : UniverseRecognized levels term) :
    ∃ scheme : Scheme levels, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levels.get, Nonempty (Finite.Carrier (scheme.code assignment)) := by
  obtain ⟨scheme,erased,converted⟩ := universe_principal wf recognized typed
  exact ⟨scheme,erased,converted,fun assignment => ⟨scheme.meaning assignment⟩⟩

theorem checked_universe_fundamental
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env (parameterContext levels) mode term type)
    (recognized : UniverseRecognized levels term) :
    ∃ scheme : Scheme levels, scheme.syntax = term ∧ Conv env scheme.type type ∧
      ∀ assignment : Assignment levels.get, Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental history.wellFormed typed recognized

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse
