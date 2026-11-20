import Jihoo.NativeCoreGlobalNormal

/-! Core.normal visits the count and initializer of Fold and Loop before
selecting the zero-count branch. That branch returns the initializer's
existing reference and leaves the body and dependent motive unvisited. -/
namespace Jihoo.NativeKernel.NativeCoreZeroLoopNormal

open NativeArena NativeProgramWire
open NativeCoreGlobalNormal (Atomic Error Result runPure runPure_refines run_delta)
open Environment.LoanTyping.MixedProgram (History)

private inductive Operands (α : Type) : Op → List α → α → α → Prop where
  | fold : Operands α .fold [count, initial, body] count initial
  | loop : Operands α .loop [count, motive, initial, body] count initial

private def operands (op : Op) (arguments : List Nat) : Option (Nat × Nat) :=
  match op, arguments with
  | .fold, [count, initial, _] | .loop, [count, _, initial, _] => some (count, initial)
  | _, _ => none

private theorem operands_sound (found : operands op refs = some (count, initial)) :
    Operands Nat op refs count initial := by
  fun_cases operands op refs <;> simp_all [operands]
  · exact .fold
  · exact .loop

private theorem Operands.represented (layout : Operands Nat op refs count initial)
    (children : RepresentsList arena refs terms) :
    ∃ n init, Operands Term op terms n init ∧ Represents arena count n ∧ Represents arena initial init := by
  cases layout with
  | fold =>
      cases children with
      | cons countRep rest =>
          cases rest with
          | cons initialRep rest =>
              cases rest with
              | cons _ tail =>
                  cases tail
                  exact ⟨_, _, .fold, countRep, initialRep⟩
  | loop =>
      cases children with
      | cons countRep rest =>
          cases rest with
          | cons _ rest =>
              cases rest with
              | cons initialRep rest =>
                  cases rest with
                  | cons _ tail =>
                      cases tail
                      exact ⟨_, _, .loop, countRep, initialRep⟩

/-- This allocation-free path accepts a count that reaches a zero literal
through transparent aliases and an initializer that follows the pure
Free/Drop/alias path to an atom. The initializer runs before the zero test. -/
def run (arena : Arena) (roots : List Roots) (visible limit depth steps root : Nat) : Result :=
  let next := steps + 1
  if limit < next then (.error (.stepLimit root), next) else
  match depth with
  | 0 => (.error (.depthLimit root), next)
  | remaining + 1 =>
      match arena[root]? with
      | none => (.error (.invalidReference root), next)
      | some (.var _) => (.error (.outsideFragment root), next)
      | some (.node op refs) =>
          match operands op refs with
          | none => (.error (.outsideFragment root), next)
          | some (count, initial) =>
              match NativeCoreGlobalNormal.run arena roots visible limit remaining next count with
              | (.error reason, spent) => (.error reason, spent)
              | (.ok normalized, spent) =>
                  match runPure arena roots visible limit remaining spent initial with
                  | (.error reason, spent) => (.error reason, spent)
                  | (.ok selected, spent) =>
                      if arena[normalized]? = some (.node (.natural 0) []) then (.ok selected, spent)
                      else (.error (.outsideFragment root), spent)

private theorem Operands.zero_preserves (layout : Operands Term op terms count initial)
    (zero : EnvironmentDelta.expand env count = .natural 0)
    (typed : Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env (.node op terms)) type) :
    Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env initial) type := by
  cases layout with
  | fold =>
      simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs, zero] at typed
      exact Environment.LoanTyping.value_root_ghost_preservation (.foldZero _ _) typed
  | loop =>
      simp only [EnvironmentDelta.expand_node_cons, EnvironmentDelta.expandArgs, zero] at typed
      exact Environment.LoanTyping.value_root_ghost_preservation (.loopZero _ _ _) typed

/-- The selected existing node retains the original checked ghost type of
the expanded Fold or Loop, including the dependent type at count zero. -/
theorem run_refines (aligned : RepresentsDefinitions arena roots definitions)
    (history : History definitions families env) (source : Represents arena root (.node op terms))
    (typed : Environment.LoanTyping.HasType env [] ctx true (EnvironmentDelta.expand env (.node op terms)) type)
    (computed : run arena roots visible limit depth steps root = (.ok selected, counter)) :
    ∃ output, Atomic output ∧ Represents arena selected output ∧
      Environment.LoanTyping.HasType env [] ctx true output type := by
  have input : ∃ refs, arena[root]? = some (.node op refs) ∧ RepresentsList arena refs terms := by
    cases source with
    | node found _ children => exact ⟨_, found, children⟩
  obtain ⟨refs, found, children⟩ := input
  by_cases over : limit < steps + 1
  · simp [run, over] at computed
  cases depth with
  | zero => simp [run, over] at computed
  | succ remaining =>
      simp only [run, ite_eq_right over, found] at computed
      cases args : operands op refs with
      | none => simp [args] at computed
      | some operands =>
          obtain ⟨count, initial⟩ := operands
          simp only [args] at computed
          rcases countRun : NativeCoreGlobalNormal.run arena roots visible limit remaining (steps + 1) count with
            ⟨countResult, countSpent⟩
          cases countResult with
          | error reason => simp [countRun] at computed
          | ok normalized =>
              rcases initialRun : runPure arena roots visible limit remaining countSpent initial with
                ⟨initialResult, initialSpent⟩
              cases initialResult with
              | error reason => simp [countRun, initialRun] at computed
              | ok output =>
                  by_cases zero : arena[normalized]? = some (.node (.natural 0) [])
                  · simp only [countRun, initialRun, zero, ite_true, Prod.mk.injEq, Except.ok.injEq] at computed
                    obtain ⟨rfl, rfl⟩ := computed
                    obtain ⟨n, value, layout, countRep, initialRep⟩ := (operands_sound args).represented children
                    have normalRep := (run_delta aligned history countRep countRun).1
                    have zeroRep : Represents arena normalized (.natural 0) := .node zero rfl .nil
                    have valueTyped := layout.zero_preserves (normalRep.unique zeroRep) typed
                    obtain ⟨result, atomic, selectedRep, _, retained, _, _⟩ :=
                      runPure_refines aligned history initialRep valueTyped initialRun
                    exact ⟨result, atomic, selectedRep, retained⟩
                  · simp [countRun, initialRun, zero] at computed

/-- Exact mixed-program admission supplies the original declaration type
when zero-count normalization starts from a stored definition. -/
theorem run_admitted_definition_refines {index : Nat}
    (admitted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel (NativeFamilyWire.encodeSnapshot snapshot) = true)
    (row : snapshot.definitions[index]? = some definition)
    (computed : run snapshot.arena snapshot.definitions visible limit depth steps definition.valueRoot =
      (.ok selected, counter)) :
    ∃ definitions families env entry raw output,
      History definitions families env ∧ env.globals[index]? = some entry ∧
      RepresentsDefinition snapshot.arena definition raw ∧
      Atomic output ∧ Represents snapshot.arena selected output ∧
      Environment.LoanTyping.HasType env [] [] true output entry.type := by
  obtain ⟨decoded, definitions, _, env, exactBytes, _, _, aligned, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound admitted
  have same := NativeFamilyWire.encodeSnapshot_injective exactBytes
  subst decoded
  obtain ⟨entry, raw, found, represented, typed⟩ := NativeCoreGlobalNormal.checked_definition_at aligned history row
  have body := represented.2
  cases shape : raw.value with
  | var x =>
      rw [shape] at body
      cases body with
      | var read =>
          cases depth <;> by_cases over : limit < steps + 1 <;> simp [run, over, read] at computed
  | node op terms =>
      rw [shape] at body typed
      obtain ⟨output, atomic, outputRep, kept⟩ := run_refines aligned history body typed computed
      exact ⟨definitions, _, env, entry, raw, output, history, found, represented, atomic, outputRep, kept⟩

/-- A transparent count points through a later arena row to zero. The
initializer's Free prefix is skipped, as are the motive and loop body. -/
theorem zero_count_alias_example :
    let arena : Arena := #[.node (.natural 0) [], .node (.integer 7) [],
      .node .free [0, 1], .node (.global 0) [], .node .fold [3, 2, 0],
      .node .loop [3, 0, 2, 0]]
    run arena [⟨0, 0⟩] 1 5 3 0 4 = (.ok 1, 5) ∧
      run arena [⟨0, 0⟩] 1 5 3 0 5 = (.ok 1, 5) ∧
      run arena [⟨0, 0⟩] 1 4 3 0 5 = (.error (.stepLimit 1), 5) := by
  exact ⟨rfl, rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreZeroLoopNormal
