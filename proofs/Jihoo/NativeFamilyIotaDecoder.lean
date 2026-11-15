import Jihoo.NativeSyntax

/-! Pure exact family-case child decoding, independent of typing/conversion. -/
namespace Jihoo.NativeKernel.Environment.Checker

/-- Decode the exact native motive/cases/scrutinee child layout. -/
def splitCases : Nat → List Term → Option (List Term × Term)
  | 0, [scrutinee] => some ([], scrutinee)
  | n + 1, branch :: children => do
      let (branches, scrutinee) ← splitCases n children
      pure (branch :: branches, scrutinee)
  | _, _ => none

theorem splitCases_sound {count : Nat} {children branches : List Term} {scrutinee : Term}
    (h : splitCases count children = some (branches, scrutinee)) :
    branches.length = count ∧ children = branches ++ [scrutinee] := by
  induction count generalizing children branches with
  | zero =>
      cases children with
      | nil => simp [splitCases] at h
      | cons value rest =>
          cases rest with
          | nil =>
              simp only [splitCases, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨rfl, rfl⟩
          | cons _ _ => simp [splitCases] at h
  | succ count ih =>
      cases children with
      | nil => simp [splitCases] at h
      | cons branch rest =>
          simp only [splitCases] at h
          cases decoded : splitCases count rest with
          | none => simp [decoded] at h
          | some result =>
              rcases result with ⟨cases, value⟩
              simp only [decoded] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨length, layout⟩ := ih decoded
              exact ⟨by simp only [List.length_cons, length], by simp only [List.cons_append, layout]⟩


end Jihoo.NativeKernel.Environment.Checker
