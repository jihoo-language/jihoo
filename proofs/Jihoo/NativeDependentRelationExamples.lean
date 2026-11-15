import Jihoo.NativeDependentRelationalContexts
set_option maxUniverseOffset 40

/-! Actual native source instances of the general dependent clauses. The
identity has arbitrary source annotations and arbitrary semantic dependent
fibers; numeric addition has no false bound on its mathematical result. These
instances do not reconstruct the missing generic universe candidate. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

theorem dependent_identity_typed
    (domainBinder : Binder env ctx false domain domainSort)
    (familyBinder : Binder env (⟨domain,false⟩ :: ctx) false family familySort) :
    HasType env ctx true (.lam false domain (.lam false family (.var 0)))
      (.pi false domain (.pi false family (family.rename Nat.succ))) :=
  .lam domainBinder (.lam familyBinder (.var (b := ⟨family.rename Nat.succ,false⟩) rfl (Or.inl rfl)))

/-- Arbitrary genuine dependent fibers are used in the model; there is no
finite source-code grammar or supplied result realization in this theorem. -/
theorem dependent_identity_realizes (Γ : Ctx env) (A : Ty env Γ.meaning domainSort)
    (B : Ty env (Contextual.extend Γ.meaning A.code) familySort) (domain family : Term) :
    ∃ meaning,Realizes Γ (pi A (pi B (B.substitution (Contextual.weaken (A := B.code)))))
      (.lam false domain (.lam false family (.var 0))) meaning := by
  have newest := newest_realizes (Γ.extend A) B
  have inner := lambda_realizes (Γ.extend A) B (B.substitution (Contextual.weaken (A := B.code)))
    newest false family
  exact ⟨_,lambda_realizes Γ A (pi B (B.substitution (Contextual.weaken (A := B.code)))) inner false domain⟩

theorem dependent_identity_fundamental (Γ : Ctx env) (A : Ty env Γ.meaning domainSort)
    (B : Ty env (Contextual.extend Γ.meaning A.code) familySort)
    (domainBinder : Binder env ctx false domain domainNativeSort)
    (familyBinder : Binder env (⟨domain,false⟩ :: ctx) false family familyNativeSort) :
    HasType env ctx true (.lam false domain (.lam false family (.var 0)))
      (.pi false domain (.pi false family (family.rename Nat.succ))) ∧
    ∃ meaning,Realizes Γ (pi A (pi B (B.substitution (Contextual.weaken (A := B.code)))))
      (.lam false domain (.lam false family (.var 0))) meaning :=
  ⟨dependent_identity_typed domainBinder familyBinder,dependent_identity_realizes Γ A B domain family⟩

/-- Both source literal bounds are checked, while the resulting mathematical
natural is allowed to exceed the machine word through a valid additive tree. -/
theorem source_addition_fundamental (Γ : Ctx env) (first second : Nat)
    (firstBound : first < 2^64) (secondBound : second < 2^64) :
    HasType env ctx mode (.uadd (.natural first) (.natural second)) .u64 ∧
    Realizes Γ (natural env Γ.meaning) (.uadd (.natural first) (.natural second))
      (Contextual.add (Contextual.numeral first) (Contextual.numeral second)) :=
  ⟨.uadd (.natural firstBound) (.natural secondBound),
    addition_realizes Γ (numeral_realizes Γ first firstBound) (numeral_realizes Γ second secondBound)⟩

theorem closed_realizes (A : Ty env (empty env).meaning sort)
    {term : Term} {meaning : Contextual.Tm A.code}
    (realized : Realizes (empty env) A term meaning) :
    A.realizes ⟨()⟩ term (meaning ⟨()⟩) := by
  simpa only [Term.subst_id] using realized Term.var ⟨()⟩ trivial

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
