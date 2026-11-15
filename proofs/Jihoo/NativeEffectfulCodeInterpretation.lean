import Jihoo.NativeDependentCodeFrames
set_option maxUniverseOffset 40

/-! A concrete finite interpretation of actual native type annotations with
Strict/Free at arbitrary positions, including Pi domains and codomains. The
source derivation reconstructs code validity and its exact native universe;
the ignored operand never becomes an assumed semantic value or heap step. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open Jihoo.NativeKernel.Environment.Conversion
open MultiUniverse (Mono)
variable {parameters familyCount observationCount : Nat}
variable {levels : Fin parameters → Fin 32} {signatures : Fin familyCount → Signature parameters}
variable {observed : Fin observationCount → Mono parameters}

inductive Annotation (parameters familyCount observationCount : Nat) where
  | pure (code : TypeCode parameters familyCount observationCount)
  | arrow (domain body : Annotation parameters familyCount observationCount)
  | strict (first : Term) (result : Annotation parameters familyCount observationCount)
  | free (owner : Term) (result : Annotation parameters familyCount observationCount)

def Annotation.code : Annotation parameters familyCount observationCount → TypeCode parameters familyCount observationCount
  | .pure code => code
  | .arrow domain body => .arrow domain.code body.code
  | .strict _ result | .free _ result => result.code

def Annotation.syntax (offset : Nat) : Annotation parameters familyCount observationCount → Term
  | .pure code => code.syntax offset
  | .arrow domain body => .pi false (domain.syntax offset) (body.syntax (offset+1))
  | .strict first result => .strict first (result.syntax offset)
  | .free owner result => .free owner (result.syntax offset)

theorem Annotation.project_syntax (source : Annotation parameters familyCount observationCount) :
    ValueErasure.project env (source.syntax offset) = source.code.syntax offset := by
  induction source generalizing offset with
  | pure code => exact code.project_syntax
  | arrow domain body hd hb =>
    simp only [Annotation.syntax,Annotation.code,TypeCode.syntax_arrow,ValueErasure.project_pi,hd,hb]
  | strict first result ih => simp only [Annotation.syntax,Annotation.code,ValueErasure.project_strict,ih]
  | free owner result ih => simp only [Annotation.syntax,Annotation.code,ValueErasure.project_free,ih]

/-- Even beneath an effectful Pi domain, validity and universe classification
follow from the original native HasType, never from output membership. -/
theorem Annotation.recover (source : Annotation parameters familyCount observationCount)
    (wf : UnifiedProgram.EnvWellFormed env) (frame : LookupFrame levels signatures observed offset ctx)
    (typed : HasType env ctx mode (source.syntax offset) actualType) :
    source.code.Valid signatures observed ∧ Conv env (.univ (source.code.level levels signatures)) actualType := by
  induction source generalizing offset ctx mode actualType with
  | pure code => exact code.classify_in wf frame typed
  | arrow domain body hd hb =>
    change HasType env ctx mode (.pi false (domain.syntax offset) (body.syntax (offset+1))) actualType at typed
    obtain ⟨domainSort,bodySort,binder,bodyTyped,converted⟩ := typed.piView
    have domainTyped := by cases binder with | intro formed allowed => exact formed
    have first := hd frame domainTyped
    have second := hb (frame.extend ⟨domain.syntax offset,false⟩) bodyTyped
    have firstSort : SortTag.type (domain.code.level levels signatures) = domainSort :=
      first.2.sort_injective wf.admissible
    have secondSort : SortTag.type (body.code.level levels signatures) = bodySort :=
      second.2.sort_injective wf.admissible
    subst domainSort
    subst bodySort
    exact ⟨⟨first.1,second.1⟩,converted⟩
  | strict first result ih =>
    obtain ⟨resultType,resultTyped,converted⟩ : ∃ resultType,
        HasType env ctx mode (result.syntax offset) resultType ∧ Conv env resultType actualType := typed.principalView
    have recovered := ih frame resultTyped
    exact ⟨recovered.1,recovered.2.trans converted⟩
  | free owner result ih =>
    obtain ⟨resultType,resultTyped,converted⟩ : ∃ resultType,
        HasType env ctx mode (result.syntax offset) resultType ∧ Conv env resultType actualType := typed.principalView
    have recovered := ih frame resultTyped
    exact ⟨recovered.1,recovered.2.trans converted⟩

/-- This produces an actual code in the existing finite universe model from
the actual source typing derivation. Validity is an output of recovery. -/
def Annotation.interpret_checked (source : Annotation parameters familyCount observationCount)
    (wf : UnifiedProgram.EnvWellFormed env) (frame : LookupFrame levels signatures observed offset ctx)
    (typed : HasType env ctx mode (source.syntax offset) actualType)
    (assignment : Assignment levels signatures observed) : Finite.Universe (source.code.sort levels signatures) :=
  source.code.meaning assignment (source.recover wf frame typed).1

/-- Arbitrary genuine source conversion, including family iota and delta,
cannot change the resulting concrete type-code denotation. -/
theorem Annotation.checked_model_coherent (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx)
    (first : Annotation parameters familyCount observationCount)
    (second : Annotation parameters familyCount observationCount)
    (firstTyped : HasType env ctx firstMode (first.syntax offset) firstType)
    (secondTyped : HasType env ctx secondMode (second.syntax offset) secondType)
    (converted : Conv env (first.syntax offset) (second.syntax offset))
    (assignment : Assignment levels signatures observed) :
    HEq (first.interpret_checked wf frame firstTyped assignment)
      (second.interpret_checked wf frame secondTyped assignment) := by
  have projected := ValueErasure.family_conversion wf.admissible converted
  rw [Annotation.project_syntax,Annotation.project_syntax] at projected
  exact TypeCode.model_coherent wf projected assignment
    (first.recover wf frame firstTyped).1 (second.recover wf frame secondTyped).1

/-- Projection coherence is enough even for Strict/Free erasure pairs that
are outside native source conversion. -/
theorem Annotation.checked_projected_coherent (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx)
    (first : Annotation parameters familyCount observationCount)
    (second : Annotation parameters familyCount observationCount)
    (firstTyped : HasType env ctx firstMode (first.syntax offset) firstType)
    (secondTyped : HasType env ctx secondMode (second.syntax offset) secondType)
    (related : ValueErasure.Coherent env (first.syntax offset) (second.syntax offset))
    (assignment : Assignment levels signatures observed) :
    HEq (first.interpret_checked wf frame firstTyped assignment)
      (second.interpret_checked wf frame secondTyped assignment) := by
  unfold ValueErasure.Coherent at related
  rw [Annotation.project_syntax,Annotation.project_syntax] at related
  exact TypeCode.model_coherent wf related assignment
    (first.recover wf frame firstTyped).1 (second.recover wf frame secondTyped).1

theorem Annotation.interpret_strict (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx) (first : Term)
    (result : Annotation parameters familyCount observationCount)
    (typed : HasType env ctx mode ((Annotation.strict first result).syntax offset) actualType)
    (resultTyped : HasType env ctx resultMode (result.syntax offset) resultType)
    (assignment : Assignment levels signatures observed) :
    (Annotation.strict first result).interpret_checked wf frame typed assignment =
      result.interpret_checked wf frame resultTyped assignment := rfl

theorem Annotation.interpret_free (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx) (owner : Term)
    (result : Annotation parameters familyCount observationCount)
    (typed : HasType env ctx mode ((Annotation.free owner result).syntax offset) actualType)
    (resultTyped : HasType env ctx resultMode (result.syntax offset) resultType)
    (assignment : Assignment levels signatures observed) :
    (Annotation.free owner result).interpret_checked wf frame typed assignment =
      result.interpret_checked wf frame resultTyped assignment := rfl

theorem Annotation.interpret_arrow (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx)
    (domain body : Annotation parameters familyCount observationCount)
    (typed : HasType env ctx mode ((Annotation.arrow domain body).syntax offset) actualType)
    (domainTyped : HasType env ctx domainMode (domain.syntax offset) domainType)
    (bodyTyped : HasType env (⟨domain.syntax offset,false⟩ :: ctx) bodyMode (body.syntax (offset+1)) bodyType)
    (assignment : Assignment levels signatures observed) :
    (Annotation.arrow domain body).interpret_checked wf frame typed assignment =
      Finite.pi (domain.interpret_checked wf frame domainTyped assignment) (body.code.sort levels signatures)
        (fun _ => body.interpret_checked wf (frame.extend ⟨domain.syntax offset,false⟩) bodyTyped assignment) := rfl

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
