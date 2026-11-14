import Jihoo.NativeFiniteUniverseValues
import Jihoo.NativeUniverseFundamental
set_option maxUniverseOffset 40

/-! A generic contextual model over every finite native universe. This module
provides concrete code-valued Pi closure and interpretation of reconstructed
expressions. The all-level actual-source reconstruction is a subsequent step;
this module does not supply or assume that missing fundamental theorem. -/
namespace Jihoo.NativeKernel.Environment.Semantics.UniverseContext

@[reducible] def Mono.semanticSort (parameterSort : Finite.LevelSort) : Mono → Finite.LevelSort
  | .parameter => parameterSort
  | .natural => .type ⟨0,by decide⟩
  | .arrow A B => (A.semanticSort parameterSort).pi (B.semanticSort parameterSort)

@[reducible] def Mono.atCode {sort : Finite.LevelSort} (parameter : Finite.Universe sort) :
    (A : Mono) → Finite.Universe (A.semanticSort sort)
  | .parameter => parameter
  | .natural => Finite.natural
  | .arrow A B => Finite.pi (A.atCode parameter) (B.semanticSort sort) (fun _ => B.atCode parameter)

def Mono.nativeLevel (parameterLevel : Nat) : Mono → Nat
  | .parameter => parameterLevel
  | .natural => 0
  | .arrow A B => max (A.nativeLevel parameterLevel) (B.nativeLevel parameterLevel)

theorem Mono.semanticSort_native (A : Mono) (level : Fin 32) :
    (A.semanticSort (.type ⟨level.val,by omega⟩)).native = .type (A.nativeLevel level.val) := by
  induction A with
  | parameter => rfl
  | natural => rfl
  | arrow A B ha hb =>
    simp only [Mono.semanticSort,Mono.nativeLevel,Finite.LevelSort.pi_native,ha,hb,SortTag.pi]

theorem Mono.nativeLevel_bound (A : Mono) (level : Nat) : A.nativeLevel level ≤ level := by
  induction A with
  | parameter => exact Nat.le_refl _
  | natural => exact Nat.zero_le _
  | arrow A B ha hb => exact Nat.max_le.mpr ⟨ha,hb⟩

inductive LevelValues {sort : Finite.LevelSort} (parameter : Finite.Universe sort) : List Mono → Type 34 where
  | nil : LevelValues parameter []
  | cons : Finite.Carrier (A.atCode parameter) → LevelValues parameter Γ → LevelValues parameter (A :: Γ)

def Member.levelValue {sort : Finite.LevelSort} {parameter : Finite.Universe sort}
    (member : Member A Γ i) (values : LevelValues parameter Γ) : Finite.Carrier (A.atCode parameter) :=
  match member, values with
  | .here, .cons value _ => value
  | .there previous, .cons _ rest => previous.levelValue rest

def Expression.levelMeaning {sort : Finite.LevelSort} {parameter : Finite.Universe sort} :
    Expression Γ A → LevelValues parameter Γ → Finite.Carrier (A.atCode parameter)
  | .var member, values => member.levelValue values
  | .natural value _, _ => ⟨value⟩
  | .lam (A := A) (B := B) body, values =>
    (Finite.piMeaning (A.atCode parameter) (B.semanticSort sort) (fun _ => B.atCode parameter)).lam
      (fun argument => body.levelMeaning (.cons argument values))
  | .app (A := A) (B := B) function argument, values =>
    (Finite.piMeaning (A.atCode parameter) (B.semanticSort sort) (fun _ => B.atCode parameter)).app
      (function.levelMeaning values) (argument.levelMeaning values)

theorem Expression.level_beta {sort : Finite.LevelSort} {parameter : Finite.Universe sort}
    (body : Expression (A :: Γ) B) (argument : Expression Γ A) (values : LevelValues parameter Γ) :
    (Expression.app (.lam body) argument).levelMeaning values =
      body.levelMeaning (.cons (argument.levelMeaning values) values) := by
  exact (Finite.piMeaning (A.atCode parameter) (B.semanticSort sort) (fun _ => B.atCode parameter)).beta _ _

def polyCodeAt (level : Fin 32) (A : Mono) :
    Finite.Universe ((Finite.LevelSort.type ⟨level.val+1,by omega⟩).pi
      (A.semanticSort (.type ⟨level.val,by omega⟩))) :=
  Finite.pi (Finite.Values.codeUniverse level) (A.semanticSort (.type ⟨level.val,by omega⟩))
    (fun parameter => A.atCode (Finite.Values.decode level parameter))

def Expression.polyInterpretAt (level : Fin 32) (expression : Expression [] A) :
    Finite.Carrier (polyCodeAt level A) :=
  (Finite.piMeaning (Finite.Values.codeUniverse level) (A.semanticSort (.type ⟨level.val,by omega⟩))
    (fun parameter => A.atCode (Finite.Values.decode level parameter))).lam
      (fun parameter => expression.levelMeaning (parameter := Finite.Values.decode level parameter) .nil)

theorem Expression.polyInterpretAt_application (level : Fin 32) (expression : Expression [] A)
    (parameter : Finite.Carrier (Finite.Values.codeUniverse level)) :
    (Finite.piMeaning (Finite.Values.codeUniverse level) (A.semanticSort (.type ⟨level.val,by omega⟩))
      (fun parameter => A.atCode (Finite.Values.decode level parameter))).app
        (expression.polyInterpretAt level) parameter =
      expression.levelMeaning (parameter := Finite.Values.decode level parameter) .nil :=
  (Finite.piMeaning _ _ _).beta _ _

theorem polyCodeAt_native_sort (level : Fin 32) (A : Mono) :
    ((Finite.LevelSort.type ⟨level.val+1,by omega⟩).pi
      (A.semanticSort (.type ⟨level.val,by omega⟩))).native = .type (level.val+1) := by
  rw [Finite.LevelSort.pi_native,Mono.semanticSort_native]
  change SortTag.type (max (level.val+1) (A.nativeLevel level.val)) = SortTag.type (level.val+1)
  rw [Nat.max_eq_left (Nat.le_trans (A.nativeLevel_bound _) (by omega))]

/-- The finite universe contains an actual empty carrier at every native
level. A dependent function selecting an element of every code cannot exist. -/
theorem polyCodeAt_bottom_uninhabited (level : Fin 32) :
    ¬ Nonempty (Finite.Carrier (polyCodeAt level .parameter)) := by
  rintro ⟨function⟩
  have value := (Finite.piMeaning (Finite.Values.codeUniverse level)
    (Mono.parameter.semanticSort (.type ⟨level.val,by omega⟩))
    (fun parameter => Mono.parameter.atCode (Finite.Values.decode level parameter))).app
      function (Finite.Values.encode level (Finite.Values.empty level))
  have emptyValue : Finite.Carrier (Finite.Values.empty level) := by
    simpa only [Mono.atCode,Mono.semanticSort,Finite.Values.decode_encode] using value
  exact Finite.Values.empty_uninhabited level ⟨emptyValue⟩

end Jihoo.NativeKernel.Environment.Semantics.UniverseContext
