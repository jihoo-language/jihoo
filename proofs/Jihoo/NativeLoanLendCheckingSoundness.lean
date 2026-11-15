import Jihoo.NativeLoanLendChecking
import Jihoo.NativeLoanCheckerPolicySoundness
import Jihoo.NativeLoanGhostPromotion

namespace Jihoo.NativeKernel.Environment.LoanTyping.Checker

theorem genericLend_sound
    (recursive : ∀ mode expression type, inferSub mode expression = some type →
      HasType env loans ctx mode expression type)
    (ownerTyped : HasType env loans ctx ghost owner ownerType)
    (owned : Owned env ownerType)
    (accepted : genericLend inferSub fuel env ghost ownerType reader continuation = some outside) :
    HasType env loans ctx ghost (.lend owner reader continuation) outside := by
  unfold genericLend at accepted
  obtain ⟨readerType, readerInferred, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨readerNormal, readerNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i readerDomain readerResult readerShape
    obtain ⟨rawDomain, readerRemoved, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨domain, domainNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted
    · rename_i outlived
      obtain ⟨continuationType, continuationInferred, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨continuationNormal, continuationNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      split at accepted
      · rename_i first again result continuationShape
        obtain ⟨normal, resultNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
        obtain ⟨actualOutside, resultRemoved, accepted⟩ := Option.bind_eq_some_iff.mp accepted
        split at accepted
        · rename_i checked
          cases accepted
          exact HasType.lendGeneric ownerTyped owned ⟨domain,.refl _,outlived⟩
            ((recursive ghost reader readerType readerInferred).convert (Conversion.equal_sound checked.1))
            ((recursive ghost continuation continuationType continuationInferred).convert
              (Conversion.equal_sound checked.2.1))
            (takeNonFunctionGate_sound checked.2.2)
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem dependentLend_sound
    (recursive : ∀ stack mode expression type, inferStack stack mode expression = some type →
      HasType env stack ctx mode expression type)
    (binderRecursive : ∀ erased annotation sort, inferBinder erased annotation = some sort →
      Binder env loans ctx erased annotation sort)
    (ownerTyped : HasType env loans ctx ghost (.var owner) ownerType)
    (owned : Owned env ownerType)
    (accepted : dependentLend inferStack inferBinder fuel env loans ctx ghost
      owner ownerType domain readerBody first again body = some outside) :
    HasType env loans ctx ghost
      (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) outside := by
  unfold dependentLend at accepted
  obtain ⟨sort, binderInferred, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i domainChecked
    obtain ⟨resultType, readExposed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted
    · rename_i readChecked
      obtain ⟨restored, restoreInferred, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨restoreNormal, restoreNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      split at accepted
      · rename_i restoreDomain result restoreShape
        split at accepted
        · rename_i restoreChecked
          obtain ⟨normal, resultNormalized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨actualOutside, resultRemoved, accepted⟩ := Option.bind_eq_some_iff.mp accepted
          split at accepted
          · rename_i allowed
            cases accepted
            obtain ⟨readActual, readInferred, readConverted⟩ := expose_elim readExposed
            have readerTyped := (recursive _ ghost _ readActual readInferred).convert readConverted
            have continuationTyped := (recursive loans ghost _ restored restoreInferred).convert
              (Conversion.equal_sound restoreChecked)
            cases ghost with
            | false =>
                exact HasType.lendDependentCode ownerTyped owned (binderRecursive _ _ _ binderInferred)
                  (Conversion.equal_sound domainChecked) readerTyped
                  ⟨resultType,.refl _,readChecked.1⟩ (Conversion.equal_sound readChecked.2.1)
                  (Conversion.equal_sound readChecked.2.2) continuationTyped
                  (Conversion.normalize?_sound resultNormalized) resultRemoved
                  (takeNonFunctionGate_sound allowed)
            | true =>
                exact HasType.lendDependentGhost ownerTyped owned (binderRecursive _ _ _ binderInferred)
                  (Conversion.equal_sound domainChecked) readerTyped
                  ⟨resultType,.refl _,readChecked.1⟩ (Conversion.equal_sound readChecked.2.1)
                  (Conversion.equal_sound readChecked.2.2) continuationTyped
                  (Conversion.normalize?_sound resultNormalized) resultRemoved
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem borrowAllowed_sound
    (ownerTyped : HasType env loans ctx true owner ownerType)
    (owned : Owned env ownerType)
    (allowed : borrowAllowed loans ctx.length ghost owner = true) :
    HasType env loans ctx ghost (.borrow owner) (.ref ownerType) := by
  cases ghost with
  | true => exact .ghostBorrowOwned ownerTyped owned
  | false =>
      cases owner with
      | var index => exact .codeBorrowOwned ownerTyped owned (by simpa only [borrowAllowed, Bool.false_or] using allowed)
      | node op children => simp only [borrowAllowed, Bool.false_or, Bool.false_eq_true] at allowed

end Jihoo.NativeKernel.Environment.LoanTyping.Checker
