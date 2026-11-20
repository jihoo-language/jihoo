import Jihoo.NativeCoreCompareWire

/-! Core.canonical inserts variables by increasing index. Ghost arithmetic
inserts remaining atoms by the live Core.compare ordering. Runtime arithmetic
retains the original order of nonvariable atoms. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedOrder

open NativeArena NativeCoreCompare

private abbrev CompareRefs := Nat → Nat → Nat → Option (Bool × Nat)

private def insert (back : CompareRefs) (ref : Nat) : List Nat → Nat → Option (List Nat × Nat)
  | [], work => some ([ref], work)
  | later :: rest, work => do
      let (moveBack, remaining) ← back work later ref
      if moveBack then
        let (ordered, budget) ← insert back ref rest remaining
        some (later :: ordered, budget)
      else some (ref :: later :: rest, remaining)

private def sort (back : CompareRefs) : List Nat → List Nat → Nat → Option (List Nat × Nat)
  | [], reversed, work => some (reversed.reverse, work)
  | ref :: rest, reversed, work => do
      let (ordered, remaining) ← insert back ref reversed work
      sort back rest ordered remaining

private def partition (arena : Arena) : List Nat → Option (List Nat × List Nat)
  | [] => some ([], [])
  | ref :: rest => do
      let row ← arena[ref]?
      let (variables, others) ← partition arena rest
      match row with
      | .var _ => some (ref :: variables, others)
      | .node .. => some (variables, ref :: others)

private def variableBack (arena : Arena) : CompareRefs
  | 0, _, _ => none
  | work + 1, later, fresh =>
      match arena[later]?, arena[fresh]? with
      | some (.var x), some (.var y) => some (decide (y < x), work)
      | _, _ => none

private def ghostBack (arena : Arena) : CompareRefs :=
  fun work later ref => (compareArena arena 128 work later ref).map (fun (order, rest) => (order == .gt, rest))

/-- On represented atoms the uncharged partition can be computed first.
Variable insertions then spend the same work in source order, before the
ghost-only comparison pass. The state here records remaining work. -/
def run (runtime : Bool) (arena : Arena) (atoms : List Nat) (work : Nat) :
    Option (List Nat × Nat) := do
  let (variables, other) ← partition arena atoms
  let (orderedVars, remaining) ← sort (variableBack arena) variables [] work
  if runtime then some (orderedVars ++ other, remaining)
  else
    let (ordered, budget) ← sort (ghostBack arena) other [] remaining
    some (orderedVars ++ ordered, budget)

private def insertTerm (back : Term → Term → Bool) (term : Term) : List Term → List Term
  | [] => [term]
  | later :: rest =>
      if back later term then later :: insertTerm back term rest
      else term :: later :: rest

private def sortTerms (back : Term → Term → Bool) (reversed terms : List Term) : List Term :=
  (terms.foldl (fun ordered term => insertTerm back term ordered) reversed).reverse

private def isVariable : Term → Bool
  | .var _ => true
  | _ => false

private def variableBackTerm : Term → Term → Bool
  | .var x, .var y => decide (y < x)
  | _, _ => false

private def ghostBackTerm (later fresh : Term) : Bool :=
  compareShape (project later) (project fresh) == .gt

/-- Independent term ordering with the same stable insertion criterion. -/
def orderedTerms (runtime : Bool) (inputs : List Term) : List Term :=
  let vars := sortTerms variableBackTerm [] (inputs.filter isVariable)
  let other := inputs.filter (fun term => !isVariable term)
  vars ++ if runtime then other else sortTerms ghostBackTerm [] other

private theorem represents_append (left : RepresentsList arena xs terms) (right : RepresentsList arena ys more) :
    RepresentsList arena (xs ++ ys) (terms ++ more) := by
  induction xs generalizing terms with
  | nil => cases left; exact right
  | cons x xs ih =>
      cases left with
      | cons head tail => exact .cons head (ih tail)

private theorem represents_reverse (represented : RepresentsList arena refs terms) :
    RepresentsList arena refs.reverse terms.reverse := by
  induction refs generalizing terms with
  | nil => cases represented; exact .nil
  | cons x xs ih =>
      cases represented with
      | cons head rest =>
          simpa only [List.reverse_cons] using represents_append (ih rest) (.cons head .nil)

private def Consistent (arena : Arena) (back : CompareRefs) (termBack : Term → Term → Bool) : Prop :=
  ∀ {work x y a b move remaining}, Represents arena x a → Represents arena y b →
    back work x y = some (move, remaining) → move = termBack a b

private theorem insert_refines (consistent : Consistent arena back termBack)
    (fresh : Represents arena ref term) (observed : RepresentsList arena refs terms)
    (ran : insert back ref refs work = some (ordered, budget)) :
    RepresentsList arena ordered (insertTerm termBack term terms) := by
  induction refs generalizing terms work ordered budget with
  | nil =>
      cases observed
      cases ran
      exact .cons fresh .nil
  | cons x refs ih =>
      cases observed with
      | cons head tail =>
          simp only [insert] at ran
          obtain ⟨⟨move, remaining⟩, compared, ran⟩ := Option.bind_eq_some_iff.mp ran
          have branch := consistent head fresh compared
          rw [insertTerm, ← branch]
          cases move
          · cases ran
            exact .cons fresh (.cons head tail)
          · simp only [ite_true] at ran
            obtain ⟨⟨rest, steps⟩, inserted, ran⟩ := Option.bind_eq_some_iff.mp ran
            cases ran
            exact .cons head (ih tail inserted)

private theorem sort_refines (consistent : Consistent arena back termBack)
    (observed : RepresentsList arena refs terms) (accumulated : RepresentsList arena reversed seen)
    (ran : sort back refs reversed work = some (ordered, budget)) :
    RepresentsList arena ordered (sortTerms termBack seen terms) := by
  induction refs generalizing terms reversed seen work ordered budget with
  | nil =>
      cases observed
      cases ran
      exact represents_reverse accumulated
  | cons x refs ih =>
      cases observed with
      | cons head tail =>
          simp only [sort] at ran
          obtain ⟨⟨inserted, remaining⟩, didInsert, ran⟩ := Option.bind_eq_some_iff.mp ran
          have after := insert_refines consistent head accumulated didInsert
          have sorted := ih tail after ran
          exact sorted

private theorem partition_refines (represented : RepresentsList arena refs terms)
    (ran : partition arena refs = some (vars, rest)) :
    RepresentsList arena vars (terms.filter isVariable) ∧
      RepresentsList arena rest (terms.filter (fun term => !isVariable term)) := by
  induction refs generalizing terms vars rest with
  | nil =>
      cases represented
      cases ran
      exact ⟨.nil, .nil⟩
  | cons ref refs ih =>
      cases represented with
      | cons head tail =>
          simp only [partition] at ran
          obtain ⟨node, read, ran⟩ := Option.bind_eq_some_iff.mp ran
          obtain ⟨⟨otherVars, otherTerms⟩, parted, ran⟩ := Option.bind_eq_some_iff.mp ran
          obtain ⟨variables, others⟩ := ih tail parted
          cases head with
          | var lookup =>
              rw [lookup] at read
              cases read
              cases ran
              simpa only [List.filter_cons, isVariable, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] using
                And.intro (RepresentsList.cons (.var lookup) variables) others
          | node lookup arity kids =>
              rw [lookup] at read
              cases read
              cases ran
              simpa only [List.filter_cons, isVariable, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] using
                And.intro variables (RepresentsList.cons (.node lookup arity kids) others)

private theorem variableBack_sound : Consistent arena (variableBack arena) variableBackTerm := by
  intro work x y a b move remaining left right ran
  cases work with
  | zero => simp [variableBack] at ran
  | succ work =>
      cases left <;> cases right
      all_goals simp_all [variableBack, variableBackTerm]

private theorem ghostBack_sound : Consistent arena (ghostBack arena) ghostBackTerm := by
  intro work ref fresh a b move remaining left right ran
  unfold ghostBack at ran
  obtain ⟨⟨order, spent⟩, compared, result⟩ := Option.map_eq_some_iff.mp ran
  cases result
  rw [ghostBackTerm, compareArena_refines left right compared]

theorem run_refines (inputs : RepresentsList arena refs terms)
    (ran : run runtime arena refs work = some (result, remaining)) :
    RepresentsList arena result (orderedTerms runtime terms) := by
  unfold run at ran
  obtain ⟨⟨vars, other⟩, parted, ran⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨varRep, otherRep⟩ := partition_refines inputs parted
  obtain ⟨⟨ordered, available⟩, varSort, ran⟩ := Option.bind_eq_some_iff.mp ran
  have sorted := sort_refines variableBack_sound varRep .nil varSort
  cases runtime
  · simp only [Bool.false_eq_true, ite_false] at ran
    obtain ⟨⟨newRefs, budget⟩, otherSort, ran⟩ := Option.bind_eq_some_iff.mp ran
    cases ran
    exact represents_append sorted (sort_refines ghostBack_sound otherRep .nil otherSort)
  · cases ran
    exact represents_append sorted otherRep

private theorem insertTerm_perm (back : Term → Term → Bool) (term : Term) (rev : List Term) :
    (insertTerm back term rev).Perm (term :: rev) := by
  induction rev with
  | nil => exact .refl _
  | cons head rest ih =>
      rw [insertTerm]
      split
      · exact (ih.cons head).trans (List.Perm.swap term head rest)
      · exact .refl _

private theorem sortTerms_perm (back : Term → Term → Bool) (rev terms : List Term) :
    (sortTerms back rev terms).Perm (terms.reverse ++ rev) := by
  induction terms generalizing rev with
  | nil => exact List.reverse_perm _
  | cons head rest ih =>
      change (sortTerms back (insertTerm back head rev) rest).Perm ((head :: rest).reverse ++ rev)
      rw [List.reverse_cons, List.append_assoc]
      exact (ih _).trans ((insertTerm_perm back head rev).append_left rest.reverse)

/-- Both modes preserve every atom occurrence, including equal-order ties
whose raw evidence may differ. -/
theorem orderedTerms_perm (runtime : Bool) (terms : List Term) :
    (orderedTerms runtime terms).Perm terms := by
  have vars : (sortTerms variableBackTerm [] (terms.filter isVariable)).Perm (terms.filter isVariable) := by
    have ordered := sortTerms_perm variableBackTerm [] (terms.filter isVariable)
    rw [List.append_nil] at ordered
    exact ordered.trans (List.reverse_perm _)
  have ghost : (sortTerms ghostBackTerm [] (terms.filter (fun term => !isVariable term))).Perm
      (terms.filter (fun term => !isVariable term)) := by
    have ordered := sortTerms_perm ghostBackTerm [] (terms.filter (fun term => !isVariable term))
    rw [List.append_nil] at ordered
    exact ordered.trans (List.reverse_perm _)
  have partitioned : ((terms.filter isVariable) ++ (terms.filter (fun term => !isVariable term))).Perm terms := by
    clear vars ghost
    induction terms with
    | nil => exact .refl _
    | cons term rest ih =>
        cases isVar : isVariable term
        · simpa only [List.filter_cons, isVar, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
            using List.perm_middle.trans (ih.cons term)
        · simpa only [List.filter_cons, isVar, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
            List.cons_append] using ih.cons term
  cases runtime
  · exact (vars.append ghost).trans partitioned
  · exact (vars.append_right _).trans partitioned

end Jihoo.NativeKernel.NativeCoreUnsignedOrder
