import Jihoo.NativeLoanMixedProgram

/-! Replay the executable mixed declaration checker from a checked prefix.
The schedule keeps already checked families before new families at the same
global count. Forward or backward errors in the suffix propagate unchanged. -/
namespace Jihoo.NativeKernel.FamilyEnvironment

private theorem prepend_scheduled (event : Event) (before : List Event)
    (after : Option (List Event)) :
    ((after.map (before ++ ·)).bind fun events => some (event :: events)) =
      after.map ((event :: before) ++ ·) := by
  cases after <;> rfl

/-- The old schedule consumes one unit of fuel per declaration. After those
events, the full schedule resumes at the old global count with exactly the
suffix budget. Families at that count are emitted in table order. -/
theorem schedule_append
    {oldDefinitions newDefinitions : List Definitions.Definition}
    {oldFamilies newFamilies : List Declaration}
    (earlier : schedule prefixBudget index oldDefinitions oldFamilies = some prefixEvents)
    (boundary : ∀ first, newFamilies.head? = some first →
      index + oldDefinitions.length ≤ first.globals) (suffixBudget : Nat) :
    schedule (oldDefinitions.length + oldFamilies.length + suffixBudget) index
      (oldDefinitions ++ newDefinitions) (oldFamilies ++ newFamilies) =
        (schedule suffixBudget (index + oldDefinitions.length) newDefinitions newFamilies).map
          (prefixEvents ++ ·) := by
  induction prefixBudget generalizing index oldDefinitions oldFamilies prefixEvents with
  | zero => simp [schedule] at earlier
  | succ prefixBudget ih =>
      cases oldFamilies with
      | nil =>
          cases oldDefinitions with
          | nil =>
              simp only [schedule, Option.some.injEq] at earlier
              subst prefixEvents
              simp
          | cons definition oldDefinitions =>
              simp only [schedule] at earlier
              cases scheduled : schedule prefixBudget (index+1) oldDefinitions [] with
              | none => simp [scheduled] at earlier
              | some prefixTail =>
                  simp only [scheduled, Bind.bind, Option.bind, Option.some.injEq] at earlier
                  subst prefixEvents
                  have checkpoint : index + 1 + oldDefinitions.length =
                      index + (definition :: oldDefinitions).length := by
                    simp only [List.length_cons]
                    omega
                  have resumed := ih scheduled (by simpa only [checkpoint] using boundary)
                  simp only [checkpoint, List.length_nil, List.nil_append] at resumed
                  have budget : (definition :: oldDefinitions).length + ([] : List Declaration).length +
                      suffixBudget = (oldDefinitions.length + 0 + suffixBudget) + 1 := by
                    simp only [List.length_cons, List.length_nil]
                    omega
                  rw [budget]
                  simp only [List.cons_append, List.nil_append]
                  cases newFamilies with
                  | nil =>
                      simp only [schedule]
                      rw [resumed]
                      exact prepend_scheduled _ _ _
                  | cons first fresh =>
                      have forward : index < first.globals := by
                        have after := boundary first rfl
                        simp only [List.length_cons] at after
                        omega
                      simp only [schedule, ite_eq_right (Nat.ne_of_gt forward), ite_eq_left forward]
                      rw [resumed]
                      exact prepend_scheduled _ _ _
      | cons family oldFamilies =>
          by_cases atIndex : family.globals = index
          · simp only [schedule, ite_eq_left atIndex] at earlier
            cases scheduled : schedule prefixBudget index oldDefinitions oldFamilies with
            | none => simp [scheduled] at earlier
            | some prefixTail =>
                simp only [scheduled, Bind.bind, Option.bind, Option.some.injEq] at earlier
                subst prefixEvents
                have budget : oldDefinitions.length + (family :: oldFamilies).length +
                    suffixBudget = (oldDefinitions.length + oldFamilies.length + suffixBudget) + 1 := by
                  simp only [List.length_cons]
                  omega
                rw [budget]
                simp only [List.cons_append, schedule, ite_eq_left atIndex]
                rw [ih scheduled boundary]
                exact prepend_scheduled _ _ _
          · by_cases forward : index < family.globals
            · cases oldDefinitions with
              | nil => simp [schedule, atIndex, forward] at earlier
              | cons definition oldDefinitions =>
                  simp only [schedule, ite_eq_right atIndex, ite_eq_left forward] at earlier
                  cases scheduled : schedule prefixBudget (index+1) oldDefinitions
                      (family :: oldFamilies) with
                  | none => simp [scheduled] at earlier
                  | some prefixTail =>
                      simp only [scheduled, Bind.bind, Option.bind, Option.some.injEq] at earlier
                      subst prefixEvents
                      have checkpoint : index + 1 + oldDefinitions.length =
                          index + (definition :: oldDefinitions).length := by
                        simp only [List.length_cons]
                        omega
                      have resumed := ih scheduled (by simpa only [checkpoint] using boundary)
                      simp only [checkpoint, List.cons_append] at resumed
                      have budget : (definition :: oldDefinitions).length + (family :: oldFamilies).length +
                          suffixBudget = (oldDefinitions.length + (family :: oldFamilies).length +
                            suffixBudget) + 1 := by
                        simp only [List.length_cons]
                        omega
                      rw [budget]
                      simp only [List.cons_append, schedule, ite_eq_right atIndex, ite_eq_left forward]
                      rw [resumed]
                      exact prepend_scheduled _ _ _
            · simp [schedule, atIndex, forward] at earlier

end Jihoo.NativeKernel.FamilyEnvironment

namespace Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram
open UnifiedProgram

theorem checkEvents_append (fuel quantityFuel : Nat) (env : Environment)
    (prefixEvents suffixEvents : List FamilyEnvironment.Event) :
    checkEvents fuel quantityFuel env (prefixEvents ++ suffixEvents) =
      (checkEvents fuel quantityFuel env prefixEvents).bind
        (fun checked => checkEvents fuel quantityFuel checked suffixEvents) := by
  induction prefixEvents generalizing env with
  | nil => rfl
  | cons event events ih =>
      cases event with
      | definition source =>
          cases checked : checkDeclaration fuel quantityFuel env source <;>
            simp only [List.cons_append, checkEvents, checked, Bind.bind, Option.bind, ih]
      | family source =>
          cases checked : Families.checkFamily fuel env source <;>
            simp only [List.cons_append, checkEvents, checked, Bind.bind, Option.bind, ih]

/-- Successful replay retains every checked entry at its original index. -/
theorem checkEvents_extends
    (accepted : checkEvents fuel quantityFuel env events = some result) :
    Environment.Extends env result := by
  induction events generalizing env with
  | nil =>
      cases accepted
      exact Environment.Extends.refl result
  | cons event events ih =>
      cases event with
      | definition source =>
          simp only [checkEvents] at accepted
          obtain ⟨expanded, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
          exact (Environment.Extends.pushGlobal env expanded).trans (ih checked)
      | family source =>
          simp only [checkEvents] at accepted
          obtain ⟨entry, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
          exact (Environment.Extends.pushFamily env entry).trans (ih checked)

/-- Replay only appended declarations from the cached mixed environment.
Family positions continue to count globals from the start of the program. -/
def checkSuffix (fuel quantityFuel : Nat) (env : Environment)
    (definitions : List GlobalDeclaration) (families : List FamilyDeclaration) : Option Environment := do
  let events ← FamilyEnvironment.schedule (definitions.length + families.length + 1)
    env.globals.size definitions families
  checkEvents fuel quantityFuel env events

/-- Reusing the actual accepted environment is equivalent to a complete
check, whether the suffix succeeds or rejects, with identical check budgets. -/
theorem checkProgram_append
    {oldDefinitions newDefinitions : List GlobalDeclaration}
    {oldFamilies newFamilies : List FamilyDeclaration}
    (accepted : checkProgram fuel quantityFuel oldDefinitions oldFamilies = some env)
    (boundary : ∀ first, newFamilies.head? = some first → oldDefinitions.length ≤ first.globals) :
    checkProgram fuel quantityFuel (oldDefinitions ++ newDefinitions) (oldFamilies ++ newFamilies) =
      checkSuffix fuel quantityFuel env newDefinitions newFamilies := by
  have checkpoint := (checkProgram_sound accepted).globalLength
  unfold checkProgram at accepted ⊢
  cases scheduled : FamilyEnvironment.schedule (oldDefinitions.length + oldFamilies.length + 1)
      0 oldDefinitions oldFamilies with
  | none => simp [scheduled] at accepted
  | some events =>
      simp only [scheduled, Bind.bind, Option.bind] at accepted
      have budget : (oldDefinitions ++ newDefinitions).length + (oldFamilies ++ newFamilies).length + 1 =
          oldDefinitions.length + oldFamilies.length + (newDefinitions.length + newFamilies.length + 1) := by
        simp only [List.length_append]
        omega
      have mixed := FamilyEnvironment.schedule_append
        (newDefinitions := newDefinitions) scheduled (by simpa only [Nat.zero_add] using boundary)
        (newDefinitions.length + newFamilies.length + 1)
      simp only [Nat.zero_add] at mixed
      rw [budget, mixed]
      unfold checkSuffix
      rw [checkpoint]
      cases FamilyEnvironment.schedule (newDefinitions.length + newFamilies.length + 1)
          oldDefinitions.length newDefinitions newFamilies <;>
        simp only [Option.map, Bind.bind, Option.bind, checkEvents_append, accepted]

theorem checkSuffix_sound
    (history : History oldDefinitions oldFamilies env)
    (accepted : checkSuffix fuel quantityFuel env newDefinitions newFamilies = some result) :
    History (oldDefinitions ++ newDefinitions) (oldFamilies ++ newFamilies) result := by
  unfold checkSuffix at accepted
  obtain ⟨_, scheduled, checked⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨definitions, families⟩ := FamilyEnvironment.schedule_sound scheduled
  simpa only [definitions, families] using checkEvents_sound history checked

theorem checkSuffix_extends
    (accepted : checkSuffix fuel quantityFuel env newDefinitions newFamilies = some result) :
    Environment.Extends env result := by
  unfold checkSuffix at accepted
  obtain ⟨_, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
  exact checkEvents_extends checked

end Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram
