import Jihoo.NativeLoanCheckerPolicy
import Jihoo.NativeLoanPolicyTransport

/-! Policy and comparison soundness for the Loan-local raw relation. These
lemmas precede mutual inference so generic/dependent Lend helpers share the
same actual normalizer and never fall back to default60 policy comparisons. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Checker

theorem accepts_elim {fuel : Nat} {inferred : Option Term} {expected : Term}
    (h : accepts fuel env inferred expected = true) :
    ∃ actual, inferred = some actual ∧ Conversion.Conv env actual expected := by
  cases inferred with
  | none => simp [accepts] at h
  | some actual => exact ⟨actual, rfl, Conversion.equal_sound h⟩

theorem expose_elim {fuel : Nat} {inferred : Option Term} {expected : Term}
    (h : expose fuel env inferred = some expected) :
    ∃ actual, inferred = some actual ∧ Conversion.Conv env actual expected := by
  cases inferred with
  | none => simp [expose] at h
  | some actual =>
      simp only [expose, Option.bind_some] at h
      exact ⟨actual,rfl,Conversion.normalize?_sound h⟩

theorem dataBinderOK_sound (h : dataBinderOK env domain = true) : dataBinderAllowed env domain := by
  unfold dataBinderOK at h
  split at h
  · rename_i family count indices
    cases found : env.families[family]? with
    | none => simp [found] at h
    | some entry =>
        exact ⟨family, count, indices, entry, found, by simpa only [found, Option.any_some] using h, .refl _⟩
  · contradiction

theorem pureBinderOK_sound {sort : SortTag} (h : pureBinderOK fuel env erased domain sort = true) :
    pureBinderAllowed env erased domain sort := by
  cases erased with
  | false => change sort ≠ .prop; exact of_decide_eq_true h
  | true =>
      rcases Bool.or_eq_true_iff.mp h with hp | hu
      · exact Or.inl (of_decide_eq_true hp)
      · exact Or.inr (Conversion.equal_sound hu)

theorem binderOK_sound {fuel : Nat} {e : Bool} {A : Term} {s : SortTag}
    (h : binderOK fuel env e A s = true) : binderAllowed env e A s := by
  obtain old | data := Bool.or_eq_true_iff.mp h
  · exact Or.inl (pureBinderOK_sound old)
  · obtain ⟨erased, data⟩ := Bool.and_eq_true_iff.mp data
    obtain ⟨family, count, indices, entry, found, isData, converted⟩ := dataBinderOK_sound data
    exact Or.inr ⟨erased, family, count, indices, entry, found, isData,
      .trans (Conversion.normalize_sound env fuel A) converted⟩

theorem applicationOK_sound (h : applicationOK fuel env ghost A a = true) : applicationAllowed env ghost A a := by
  unfold applicationOK at h
  rcases Bool.or_eq_true_iff.mp h with erased | checked
  · exact Or.inl erased
  · cases normalized : Conversion.normalize? env fuel A with
    | none => simp only [normalized] at checked; contradiction
    | some domain =>
        have both : globalFree domain = true ∧
            (!kindOf domain || (firstOrderKind domain && plain env (Conversion.normalize env fuel a))) = true := by
          simpa only [normalized, Bool.and_eq_true] using checked
        refine Or.inr ⟨domain, Conversion.normalize?_sound normalized, both.1, ?_⟩
        cases kind : kindOf domain with
        | false => exact Or.inl rfl
        | true =>
            have properties : firstOrderKind domain = true ∧ plain env (Conversion.normalize env fuel a) = true := by
              simpa only [kind, Bool.not_true, Bool.false_or, Bool.and_eq_true] using both.2
            exact Or.inr ⟨properties.1, _, Conversion.normalize_sound env fuel a, properties.2⟩

/-- A rigid canonical nonfunction head cannot become a Pi by conversion. -/
theorem nonFunctionHead_sound {T : Term} (h : nonFunctionHead T = true) : nonFunction env T :=
  RawLend.NonFunction.ofHead (RawLend.legacy_nonFunctionHead h)

theorem nonFunction_of_conversion {A B : Term} (conv : Conversion.Conv env A B)
    (h : nonFunction env B) : nonFunction env A :=
  RawLend.NonFunction.of_conversion conv h

/-- Runtime continuation results remain nonfunctions; ghost substitution may
expose arbitrary type heads without introducing runtime captures. -/
theorem nonFunctionGate_sound
    (h : (ghost || nonFunctionHead (Conversion.normalize env fuel result)) = true) :
    ghost = true ∨ nonFunction env result := by
  rcases Bool.or_eq_true_iff.mp h with erased | rigid
  · exact Or.inl erased
  · exact Or.inr (nonFunction_of_conversion (Conversion.normalize_sound env fuel result)
      (nonFunctionHead_sound rigid))

theorem ownedHead_sound (h : ownedHead env T = true) : Owned env T := by
  unfold ownedHead at h
  split at h
  · exact .buffer (.refl _)
  · rename_i family count indices
    cases found : env.families[family]? with
    | none => simp [found] at h
    | some entry =>
        exact .family found (by simpa only [found, Option.any_some] using h) (.refl _)
  · contradiction

theorem ownedHead_normalize_sound
    (h : ownedHead env (Conversion.normalize env fuel T) = true) : Owned env T := by
  cases ownedHead_sound h with
  | buffer converted => exact .buffer (.trans (Conversion.normalize_sound env fuel T) converted)
  | family found boxed converted =>
      exact .family found boxed (.trans (Conversion.normalize_sound env fuel T) converted)

theorem backMotiveOK_sound (h : backMotiveOK fuel env erased motive = true) :
    BackRepresentation env ghost erased motive := by
  rcases Bool.or_eq_true_iff.mp h with erased | represented
  · exact Or.inr (Or.inl erased)
  · unfold BackRepresentation
    refine Or.inr (Or.inr ?_)
    split at represented
    · rename_i flag domain body normal
      exact ⟨flag, domain, body, by change Conversion.Conv env motive (.node (.lam flag) [domain, body]); rw [← normal]; exact Conversion.normalize_sound env fuel motive, represented⟩
    · contradiction

theorem resourceNonFunctionHead_sound (h : resourceNonFunctionHead T = true) : nonFunction env T := by
  apply RawLend.NonFunction.ofHead
  fun_cases resourceNonFunctionHead T <;>
    simp_all only [resourceNonFunctionHead, RawLend.nonFunctionHead,
      RawLend.nonFunctionOp, Bool.false_eq_true]

theorem takeNonFunctionGate_sound
    (h : (ghost || takeNonFunctionHead (Conversion.normalize env fuel result)) = true) :
    continuationAllowed env ghost result := by
  rcases Bool.or_eq_true_iff.mp h with erased | rigid
  · exact Or.inl erased
  · apply Or.inr
    apply nonFunction_of_conversion (Conversion.normalize_sound env fuel result)
    rcases Bool.or_eq_true_iff.mp rigid with scalar | resource
    · exact nonFunctionHead_sound scalar
    · exact resourceNonFunctionHead_sound resource

/-- Successful evidence-binder removal proves exact reweakening, including
when the result is a function type with its own binders. -/
theorem branch_type_reweakens {Y B : Term}
    (h : PartialRenaming.shift (-1) 0 Y = some B) : B.rename Nat.succ = Y := by
  have shifted := PartialRenaming.shift_negative_reweakens (delta := -1) (by decide) h
  change B.rename (PartialRenaming.raiseIndex 0 1) = Y at shifted
  have raised : PartialRenaming.raiseIndex 0 1 = Nat.succ := by
    funext x
    simp [PartialRenaming.raiseIndex]
  rw [raised] at shifted
  exact shifted

theorem loopSort_sound {level : Term} {proof : Bool}
    (h : loopSort level = some proof) : level = loopSortTerm proof := by
  unfold loopSort at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · contradiction

theorem loopMotiveOK_sound {fuel : Nat} {ghost proof : Bool} {motive : Term}
    (h : loopMotiveOK fuel env proof motive = true) : loopMotiveAllowed env ghost proof motive := by
  rcases Bool.or_eq_true_iff.mp h with hp | hm
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨_, Conversion.normalize_sound env fuel motive, hm⟩)

theorem iterationBodyOK_sound (h : iterationBodyOK env body = true) :
    IterationBodyAllowed env ghost body := Or.inr (Bool.or_eq_true_iff.mp h)

theorem iterationMotiveOK_sound (h : iterationMotiveOK fuel env proof motive = true) :
    IterationMotiveAllowed env ghost proof motive := by
  rcases Bool.or_eq_true_iff.mp h with scalar | owned
  · rcases loopMotiveOK_sound (ghost := ghost) scalar with ghost | proof | scalar
    · exact Or.inl ghost
    · exact Or.inr (Or.inl proof)
    · exact Or.inr (Or.inr (Or.inl scalar))
  · unfold ownedLoopMotiveOK at owned
    split at owned
    · rename_i flag domain body normal
      exact Or.inr (Or.inr (Or.inr ⟨flag, domain, body,
        by change Conversion.Conv env motive (.node (.lam flag) [domain, body]);
           rw [← normal]; exact Conversion.normalize_sound env fuel motive,
        ownedHead_sound owned⟩))
    · contradiction


end Jihoo.NativeKernel.Environment.LoanTyping.Checker
