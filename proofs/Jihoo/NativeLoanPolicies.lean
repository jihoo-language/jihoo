import Jihoo.NativeLoanConversion
import Jihoo.NativeLendGhostRule

/-! Loan-local positive representation policies use the same raw Lend equality
as Loan64 typing. Lookup tables, representation flags and the default60 policy
predicates remain unchanged. Old witnesses embed explicitly through Raw.old. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

abbrev nonFunction := RawLend.NonFunction
abbrev fixedRepresentation := Environment.fixedRepresentation

def pureBinderAllowed (env : Environment) (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  if erased then sort = .prop ∨ Conversion.Conv env domain .u64 else sort ≠ .prop

theorem pureBinderAllowed_renaming (closed : Conversion.Closed env)
    (h : pureBinderAllowed env erased domain sort) (ρ : Nat → Nat) :
    pureBinderAllowed env erased (domain.rename ρ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.rename, renameArgs] using hu.renaming ρ closed)

theorem pureBinderAllowed_substitution (closed : Conversion.Closed env)
    (h : pureBinderAllowed env erased domain sort) (σ : Nat → Term) :
    pureBinderAllowed env erased (domain.subst σ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.subst, substArgs] using hu.substitution σ closed)


def dataBinderAllowed (env : Environment) (domain : Term) : Prop :=
  ∃ family count indices entry, env.families[family]? = some entry ∧
    entry.declaration.data = true ∧ Conversion.Conv env domain (.node (.ind family count) indices)

def binderAllowed (env : Environment) (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  pureBinderAllowed env erased domain sort ∨
    (erased = true ∧ dataBinderAllowed env domain)

def applicationAllowed (env : Environment) (ghost : Bool) (domain argument : Term) : Prop :=
  ghost = true ∨ ∃ domainNormal, Conversion.Conv env domain domainNormal ∧ globalFree domainNormal = true ∧
    (kindOf domainNormal = false ∨
      (firstOrderKind domainNormal = true ∧
        ∃ argumentNormal, Conversion.Conv env argument argumentNormal ∧ plain env argumentNormal = true))

def absurdAllowed (env : Environment) (ghost : Bool) (term : Term) : Prop :=
  ghost = true ∨ nonFunction env term

def loopMotiveAllowed (env : Environment) (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨ ∃ normal, Conversion.Conv env motive normal ∧ scalarLoopMotive normal = true

def continuationAllowed (env : Environment) (ghost : Bool) (result : Term) : Prop :=
  ghost = true ∨ nonFunction env result

/-- Ownership comes from a buffer head or the actual boxed-family metadata. -/
inductive Owned (env : Environment) : Term → Prop where
  | buffer : Conversion.Conv env T (.buffer n) → Owned env T
  | family : env.families[family]? = some entry → entry.boxed = true →
      Conversion.Conv env T (.node (.ind family count) indices) → Owned env T

def BackRepresentation (env : Environment) (ghost erased : Bool) (motive : Term) : Prop :=
  ghost = true ∨ erased = true ∨
    ∃ flag domain body, Conversion.Conv env motive (.lam flag domain body) ∧
      fixedRepresentation env body = true

/-- A repeated expression is either a full native callback telescope or
certifiably memory-free. Ghost substitution has no runtime repetition duties. -/
def IterationBodyAllowed (env : Environment) (ghost : Bool) (body : Term) : Prop :=
  ghost = true ∨ hasLeadingLambdas 3 body = true ∨ iterationMemoryFree env body = true

/-- Runtime motives have a scalar/refinement or an owned representation at
every index. Proposition induction and ghost derivations remain unrestricted. -/
def IterationMotiveAllowed (env : Environment) (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨
    (∃ normal, Conversion.Conv env motive normal ∧ scalarLoopMotive normal = true) ∨
    ∃ flag domain body, Conversion.Conv env motive (.lam flag domain body) ∧ Owned env body

/-- The native dependent-view result has one fixed runtime representation.
Ghost derivations are closed under arbitrary typed motive substitution. -/
def ViewMotiveAllowed (env : Environment) (ghost dependent : Bool) (motive : Term) : Prop :=
  ghost = true ∨ dependent = false ∨
    ∃ erased domain body,Conversion.Conv env motive (.lam erased domain body) ∧
      viewRepresentation 128 1 body = true

/-- The source outlives head classifier is unchanged; only its equality
witness is extended to the genuine raw Lend relation. -/
def Outlived (env : Environment) (type : Term) : Prop :=
  ∃ normal,Conversion.Conv env type normal ∧ Lending.outlivedHead env normal = true

 theorem nonFunction_ofEnvironment (source : Environment.nonFunction env type) : nonFunction env type := by
  obtain ⟨normal,converted,head⟩ := source
  exact ⟨normal,.old converted,head⟩

 theorem pureBinderAllowed_ofEnvironment (source : Environment.pureBinderAllowed env erased domain sort) :
    pureBinderAllowed env erased domain sort := by
  cases erased with
  | false => exact source
  | true =>
      rcases source with prop | scalar
      · exact Or.inl prop
      · exact Or.inr (.old scalar)

 theorem binderAllowed_ofEnvironment (source : Environment.binderAllowed env erased domain sort) :
    binderAllowed env erased domain sort := by
  rcases source with pure | ⟨erased,family,count,indices,entry,found,data,converted⟩
  · exact Or.inl (pureBinderAllowed_ofEnvironment pure)
  · exact Or.inr ⟨erased,family,count,indices,entry,found,data,.old converted⟩

 theorem applicationAllowed_ofEnvironment (source : Environment.applicationAllowed env ghost domain argument) :
    applicationAllowed env ghost domain argument := by
  rcases source with erased | ⟨normal,converted,free,represented⟩
  · exact Or.inl erased
  · refine Or.inr ⟨normal,.old converted,free,?_⟩
    rcases represented with ordinary | ⟨kind,value,converted,plain⟩
    · exact Or.inl ordinary
    · exact Or.inr ⟨kind,value,.old converted,plain⟩

 theorem absurdAllowed_ofEnvironment (source : Environment.absurdAllowed env ghost type) : absurdAllowed env ghost type := by
  rcases source with ghost | head
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_ofEnvironment head)

 theorem continuationAllowed_ofEnvironment (source : Environment.continuationAllowed env ghost type) :
    continuationAllowed env ghost type := by
  rcases source with ghost | head
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_ofEnvironment head)

 theorem Owned.ofEnvironment (source : Environment.Owned env type) : Owned env type := by
  cases source with
  | buffer converted => exact .buffer (.old converted)
  | family found boxed converted => exact .family found boxed (.old converted)

 theorem BackRepresentation.ofEnvironment (source : Environment.BackRepresentation env ghost erased motive) :
    BackRepresentation env ghost erased motive := by
  rcases source with ghost | erased | ⟨flag,domain,body,converted,fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag,domain,body,.old converted,fixed⟩)

 theorem loopMotiveAllowed_ofEnvironment (source : Environment.loopMotiveAllowed env ghost proof motive) :
    loopMotiveAllowed env ghost proof motive := by
  rcases source with ghost | proof | ⟨normal,converted,scalar⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr ⟨normal,.old converted,scalar⟩)

 theorem IterationMotiveAllowed.ofEnvironment (source : Environment.IterationMotiveAllowed env ghost proof motive) :
    IterationMotiveAllowed env ghost proof motive := by
  rcases source with ghost | proof | ⟨normal,converted,scalar⟩ | ⟨erased,domain,body,converted,owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl ⟨normal,.old converted,scalar⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨erased,domain,body,.old converted,Owned.ofEnvironment owned⟩))

 theorem ViewMotiveAllowed.ofEnvironment (source : Environment.ViewMotiveAllowed env ghost dependent motive) :
    ViewMotiveAllowed env ghost dependent motive := by
  rcases source with ghost | dependent | ⟨erased,domain,body,converted,represented⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl dependent)
  · exact Or.inr (Or.inr ⟨erased,domain,body,.old converted,represented⟩)

 theorem Outlived.ofEnvironment (source : Lending.Outlived env type) : Outlived env type := by
  obtain ⟨normal,converted,head⟩ := source
  exact ⟨normal,.old converted,head⟩

end Jihoo.NativeKernel.Environment.LoanTyping
