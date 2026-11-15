import Jihoo.NativeFamilyIotaComputation

/-! Soundness of the concrete pure family root contractor. No assumed
normalization/typing oracle or confluence premise is used. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

theorem eliminate_sound
    (h : eliminate env analysis family count motive children = some result) :
    Root env (.node (if analysis then .caseOf family count else .elim family count)
      (motive :: children)) result := by
  unfold eliminate at h
  cases found : env.families[family]? with
  | none => simp [found] at h
  | some entry =>
    simp only [found,Bind.bind,Option.bind] at h
    cases decoded : Checker.splitCases count children with
    | none => simp [decoded] at h
    | some pair =>
      rcases pair with ⟨cases,scrutinee⟩
      simp only [decoded] at h
      split at h
      · rename_i actual constructor arity values
        cases sigFound : entry.signatures[constructor]? with
        | none => simp [sigFound] at h
        | some signature =>
          simp only [sigFound] at h
          cases selected : cases[constructor]? with
          | none => simp [selected] at h
          | some branch =>
            simp only [selected] at h
            split at h
            · rename_i guards
              obtain ⟨sameFamily,sameArity,caseCount,fieldCount⟩ := guards
              subst actual
              subst arity
              obtain ⟨length,layout⟩ := Checker.splitCases_sound decoded
              rw [layout,← length]
              cases analysis with
              | false =>
                simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq] at h
                subst result
                exact .elim found sigFound selected caseCount fieldCount
              | true =>
                simp only [↓reduceIte] at h
                split at h
                · rename_i data
                  cases h
                  exact .caseOf found data sigFound selected caseCount fieldCount
                · contradiction
            · contradiction
      · contradiction

theorem view_sound
    (h : view env recursion family count motive children = some result) :
    Root env (.node (.view recursion family count) (motive :: children)) result := by
  unfold view at h
  cases found : env.families[family]? with
  | none => simp [found] at h
  | some entry =>
    simp only [found,Bind.bind,Option.bind] at h
    cases decoded : Checker.splitCases count children with
    | none => simp [decoded] at h
    | some pair =>
      rcases pair with ⟨cases,scrutinee⟩
      simp only [decoded] at h
      split at h
      · rename_i actual constructor arity values
        cases sigFound : entry.signatures[constructor]? with
        | none => simp [sigFound] at h
        | some signature =>
          simp only [sigFound] at h
          cases selected : cases[constructor]? with
          | none => simp [selected] at h
          | some branch =>
            simp only [selected] at h
            split at h
            · rename_i guards
              obtain ⟨sameFamily,sameArity,caseCount,fieldCount,boxed,params⟩ := guards
              subst actual
              subst arity
              cases planned : viewPlan env family (signature.fields.drop entry.declaration.params) with
              | none => simp [planned] at h
              | some plans =>
                simp only [planned,Option.some.injEq] at h
                subst result
                obtain ⟨length,layout⟩ := Checker.splitCases_sound decoded
                rw [layout,← length]
                exact .view found boxed sigFound selected caseCount fieldCount params planned
            · contradiction
      · contradiction

theorem contract_sound (accepted : contract env term = some result) : Root env term result := by
  fun_cases contract env term
  · exact eliminate_sound accepted
  · exact eliminate_sound accepted
  · exact view_sound accepted
  · simp only [contract,Option.some.injEq] at accepted
    subst result
    exact .drop _ _ _
  · simp_all [contract]

end Jihoo.NativeKernel.Environment.FamilyIota
