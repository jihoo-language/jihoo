import Jihoo.NativeMultiUniverseClosure
set_option maxUniverseOffset 40

/-! Positive checks instantiate the quantified theorems with genuinely distinct
abstract domains and codomains, including the largest native input level. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Examples
open Jihoo.NativeKernel.Environment.Conversion

private def domain : Mono 2 := .parameter ⟨1,by decide⟩
private def codomain : Mono 2 := .parameter ⟨0,by decide⟩

def applyExpression : Expression [] (.arrow (.arrow domain codomain) (.arrow domain codomain)) :=
  .lam (.lam (.app (.var (.there .here)) (.var .here)))

def applyScheme (first second : Fin 32) : Scheme [] :=
  .abstract first (.abstract second (.body applyExpression))

theorem applyScheme_source (first second : Fin 32) :
    (applyScheme first second).syntax =
      .lam false (.univ first.val) (.lam false (.univ second.val)
        (.lam false (.pi false (.var 1) (.var 1))
          (.lam false (.var 2) (.app (.var 1) (.var 0))))) := by
  simp [applyScheme,Scheme.syntax,applyExpression,Expression.syntax,domain,codomain,
    Mono.syntax,Mono.instantiate,Term.rename,Term.pi,Term.lam,Term.app]

theorem applyScheme_typed (first second : Fin 32) :
    HasType env [] true (applyScheme first second).syntax (applyScheme first second).type :=
  (applyScheme first second).typed

theorem applyScheme_recognized (first second : Fin 32) :
    UniverseRecognized [] (applyScheme first second).syntax := by
  exact .abstract first (.abstract second
    (.body (.lam (.arrow domain codomain) (.lam domain (.app (.var (by decide)) (.var (by decide)))))))

theorem mixed_top_fundamental (wf : UnifiedProgram.EnvWellFormed env) :
    ∃ scheme : Scheme [], scheme.syntax = (applyScheme ⟨0,by decide⟩ ⟨31,by decide⟩).syntax ∧
      Conv env scheme.type (applyScheme ⟨0,by decide⟩ ⟨31,by decide⟩).type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))),
        Nonempty (Finite.Carrier (scheme.code assignment)) :=
  universe_fundamental wf (applyScheme_typed _ _) (applyScheme_recognized _ _)

theorem mixed_top_formed :
    HasType env [] true (applyScheme ⟨0,by decide⟩ ⟨31,by decide⟩).type (.univ 32) := by
  have formed := (applyScheme ⟨0,by decide⟩ ⟨31,by decide⟩).formed (env := env)
  have sortEquality : (applyScheme ⟨0,by decide⟩ ⟨31,by decide⟩).sort.native.term = .univ 32 := by
    simp [applyScheme,Scheme.sort,applyExpression,domain,codomain,Mono.semanticSort,
      Finite.LevelSort.pi,Finite.LevelSort.native,SortTag.term]
    decide
  rw [sortEquality] at formed
  exact formed

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.Examples
