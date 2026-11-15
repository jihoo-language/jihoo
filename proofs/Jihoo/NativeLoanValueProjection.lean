import Jihoo.NativeProjectedContextCoherence
import Jihoo.NativeLendRawConversion

/-! Compose genuine raw Lend expansion and value erasure. Each stage expands
only the actual admitted environment. The target remains the proved concrete
family/delta/beta/ACU theory, and no dependent callback typing is assumed. -/
namespace Jihoo.NativeKernel.Environment.Semantics.ValueErasure.Loan

def project (env : Environment) (term : Term) : Term :=
  ValueErasure.project env (RawLend.project env term)

theorem project_renaming (admissible : EnvironmentDelta.Admissible env) (term : Term) (indices : Nat → Nat) :
    project env (term.rename indices) = (project env term).rename indices := by
  rw [project,RawLend.project_renaming admissible,ValueErasure.project_renaming admissible]
  rfl

theorem project_substitution (admissible : EnvironmentDelta.Admissible env) (term : Term) (values : Nat → Term) :
    project env (term.subst values) = (project env term).subst (fun index => project env (values index)) := by
  rw [project,RawLend.project_substitution admissible,ValueErasure.project_substitution admissible]
  rfl

/-- Includes every unconditional raw Lend macro, family iota and original
conversion path, without asserting that an intermediate callback is typed. -/
theorem conversion (admissible : EnvironmentDelta.Admissible env) (converted : RawLend.Conv env first second) :
    FamilyIota.Extended.Conv env (project env first) (project env second) :=
  ValueErasure.family_conversion admissible (converted.projected admissible)

theorem forward (admissible : EnvironmentDelta.Admissible env) (steps : RawLend.Forward env first second) :
    FamilyIota.Extended.Conv env (project env first) (project env second) :=
  conversion admissible steps.toConv

theorem project_variable (env : Environment) (index : Nat) : project env (.var index) = .var index := by
  simp only [project,RawLend.project,EnvironmentDelta.expand,RawLend.unlend,ValueErasure.project_variable]

theorem project_ordinary_node (ordinary : GlobalEnvironment.ordinary op = true) (notLend : op ≠ .lend)
    (children : List Term) : project env (.node op children) = ValueErasure.emit op (children.map (project env)) := by
  rw [project,RawLend.project_ordinary ordinary,RawLend.rebuild_other notLend,
    ValueErasure.project_ordinary_node ordinary,List.map_map]
  rfl

theorem project_pi (env : Environment) (erased : Bool) (domain body : Term) :
    project env (.pi erased domain body) = .pi erased (project env domain) (project env body) := by
  rw [Term.pi,project_ordinary_node (by rfl) (by intro h; cases h)]
  rfl

theorem project_application (env : Environment) (function argument : Term) :
    project env (.app function argument) = .app (project env function) (project env argument) := by
  rw [Term.app,project_ordinary_node (by rfl) (by intro h; cases h)]
  rfl

theorem project_strict (env : Environment) (first result : Term) : project env (.strict first result) = project env result := by
  rw [Term.strict,project_ordinary_node (by rfl) (by intro h; cases h)]
  rfl

theorem project_free (env : Environment) (owner result : Term) : project env (.free owner result) = project env result := by
  rw [Term.free,project_ordinary_node (by rfl) (by intro h; cases h)]
  rfl

private theorem value_project_borrow (env : Environment) (term : Term) :
    ValueErasure.project env (.borrow term) = .borrow (ValueErasure.project env term) := by
  rw [Term.borrow,ValueErasure.project_ordinary_node (by rfl)]
  rfl

private theorem value_project_desugar (env : Environment) (owner reader continuation : Term) :
    ValueErasure.project env (RawLend.desugar owner reader continuation) =
      RawLend.desugar (ValueErasure.project env owner) (ValueErasure.project env reader)
        (ValueErasure.project env continuation) := by
  simp only [RawLend.desugar,ValueErasure.project_application,value_project_borrow]

/-- The real macro still duplicates the projected owner; it is never replaced
by an invented constant or erased along with a memory operand. -/
theorem project_lend (env : Environment) (owner reader continuation : Term) :
    project env (RawLend.lendTerm owner reader continuation) =
      RawLend.desugar (project env owner) (project env reader) (project env continuation) := by
  rw [project,RawLend.project_lend,value_project_desugar]
  rfl

def Coherent (env : Environment) (first second : Term) : Prop :=
  FamilyIota.Extended.Conv env (project env first) (project env second)

theorem Coherent.subst_congr (admissible : EnvironmentDelta.Admissible env)
    (values : ∀ index,Coherent env (first index) (second index)) (term : Term) :
    Coherent env (term.subst first) (term.subst second) := by
  unfold Coherent at *
  rw [project_substitution admissible,project_substitution admissible]
  exact FamilyIota.Extended.Conv.subst_congr admissible.closed values (project env term)

/-- Checked annotation alignment may use the entire raw Lend theory. Its
composed projection still agrees with the actual replay domain. -/
theorem closing_annotation_projection (admissible : EnvironmentDelta.Admissible env)
    (aligned : RawLend.Conv env (annotation.subst values) actualDomain) :
    FamilyIota.Extended.Conv env
      ((project env annotation).subst (fun index => project env (values index)))
      (project env actualDomain) := by
  simpa only [project_substitution admissible] using conversion admissible aligned

theorem closing_annotation_coherent (admissible : EnvironmentDelta.Admissible env)
    {original replacement : Nat → Term}
    (aligned : RawLend.Conv env (annotation.subst original) actualDomain)
    (values : ∀ index,Coherent env (original index) (replacement index)) :
    FamilyIota.Extended.Conv env
      ((project env annotation).subst (fun index => project env (replacement index)))
      (project env actualDomain) := by
  have changed : FamilyIota.Extended.Conv env (project env (annotation.subst original))
      (project env (annotation.subst replacement)) := Coherent.subst_congr admissible values annotation
  have result := changed.symm.trans (conversion admissible aligned)
  simpa only [project_substitution admissible] using result

end Jihoo.NativeKernel.Environment.Semantics.ValueErasure.Loan
