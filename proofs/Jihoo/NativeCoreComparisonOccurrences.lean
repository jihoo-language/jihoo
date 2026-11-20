import Jihoo.NativeCoreCompareWire

/-! Structural occurrence alignment for the original native identity walk. -/
namespace Jihoo.NativeKernel.NativeCoreCompare

open ACU.Canonical (rank payload)
open NativeKernel.Conversion (ListRel)

/-- Aligned terms retain the constructor and recursively align all visited
children. Only the documented evidence fields and Strict prefixes may be
omitted by this structural relation. -/
inductive OccurrenceAlignment : Term → Term → Prop where
  | variable (index : Nat) : OccurrenceAlignment (.var index) (.var index)
  | strictLeft (effect : Term) : OccurrenceAlignment tail right → OccurrenceAlignment (.strict effect tail) right
  | strictRight (effect : Term) : OccurrenceAlignment left tail → OccurrenceAlignment left (.strict effect tail)
  | node (ordinary : op ≠ .strict) :
      ListRel OccurrenceAlignment (conversionChildren op left) (conversionChildren op right) →
      OccurrenceAlignment (.node op left) (.node op right)

private def omitted (header : Header) : Nat :=
  if header = (rank .usub,payload .usub) ∨ header = (rank .pack,payload .pack) ∨
      header = (rank (.give true),payload (.give true)) then 1 else 0

private theorem arity_from_retained (written : args.length = op.arity) :
    (conversionChildren op args).length + omitted (rank op,payload op) = op.arity := by
  cases op <;> try (change args.length + 0 = _; simpa only [Nat.add_zero] using written)
  case usub | pack =>
    have count : args.length = 3 := written
    change (args.take 2).length + 1 = 3
    simp [count]
  case give erased =>
    cases erased
    · change args.length + 0 = _
      simpa only [Nat.add_zero] using written
    · have count : args.length = 3 := written
      change (args.take 2).length + 1 = 3
      simp [count]

private theorem retained_member (selected : arg ∈ conversionChildren op args) : arg ∈ args := by
  cases op <;> try exact selected
  case usub | pack => exact List.mem_of_mem_take selected
  case give erased => cases erased <;> first | exact selected | exact List.mem_of_mem_take selected

private theorem projected_arguments_map (args : List Term) : projectArgs args = args.map project := by
  induction args with
  | nil => simp only [projectArgs,List.map_nil]
  | cons term tail ih => simp only [projectArgs,List.map_cons,ih]

private theorem retained_projection_map (op : Op) (args : List Term) :
    conversionChildren op (args.map project) = (conversionChildren op args).map project := by
  cases op <;> try rfl
  case usub | pack => exact List.map_take.symm
  case give erased => cases erased <;> first | rfl | exact List.map_take.symm

private theorem project_ordinary (op : Op) (args : List Term) (ordinary : op ≠ .strict) :
    project (.node op args) = .node (rank op,payload op) ((conversionChildren op args).map project) := by
  rw [project,projected_arguments_map]
  simp only [syntaxView,ite_eq_right ordinary]
  change Shape.node (rank op,payload op) (conversionChildren op (args.map project)) = _
  rw [retained_projection_map]

private theorem project_strict (effect tail : Term) : project (.strict effect tail) = project tail := by
  simp only [Term.strict,project,projectArgs] <;> rfl

private theorem rank_positive (op : Op) : rank op ≠ 0 := by cases op <;> simp [rank]

private theorem strict_arguments (arity : args.length = Op.strict.arity) : ∃ effect tail, args = [effect,tail] := by
  have length : args.length = 2 := arity
  rcases args with _ | ⟨first,_ | ⟨second,_ | ⟨_,_⟩⟩⟩
  · cases length
  · cases length
  · exact ⟨first,second,rfl⟩
  · simp only [List.length_cons] at length
    omega

private theorem child_size_lt (selected : child ∈ args) : sizeOf child < sizeOf (Term.node op args) := by
  have smaller := List.sizeOf_lt_of_mem selected
  simp only [Term.node.sizeOf_spec]
  omega

private theorem aligned_retained_lists
    (align : ∀ left ∈ inputs, ∀ right ∈ outputs, project left = project right → OccurrenceAlignment left right)
    (compared : inputs.map project = outputs.map project) : ListRel OccurrenceAlignment inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp_all; exact .nil
  | cons first rest ih =>
    cases outputs with
    | nil => simp at compared
    | cons second tail =>
      have same := List.cons.inj compared
      refine .cons (align _ List.mem_cons_self _ List.mem_cons_self same.1) (ih ?_ same.2)
      intro left leftMember right rightMember matching
      exact align left (List.mem_cons_of_mem _ leftMember) right (List.mem_cons_of_mem _ rightMember) matching

private theorem occurrences_within (budget : Nat) (bound : sizeOf left + sizeOf right ≤ budget)
    (leftFormed : left.WellFormed) (rightFormed : right.WellFormed) (same : project left = project right) :
    OccurrenceAlignment left right := by
  induction budget generalizing left right with
  | zero =>
    have positive : 0 < sizeOf left := by
      cases left <;> simp only [Term.var.sizeOf_spec,Term.node.sizeOf_spec] <;> omega
    omega
  | succ budget ih =>
    cases left with
    | var index =>
      cases right with
      | var other =>
        simp only [project] at same
        have header := (Shape.node.inj same).1
        have matching := Int.ofNat.inj (List.cons.inj (Prod.mk.inj header).2).1
        subst other
        exact .variable index
      | node op args =>
        simp only [Term.WellFormed] at rightFormed
        by_cases strict : op = .strict
        · subst op
          obtain ⟨effect,tail,rfl⟩ := strict_arguments rightFormed.1
          rw [project_strict] at same
          have smaller := child_size_lt (op := .strict) (show tail ∈ [effect,tail] by simp)
          exact .strictRight effect (ih (by omega) leftFormed (rightFormed.2 _ (by simp)) same)
        · rw [project,project_ordinary op args strict] at same
          have eqRank : 0 = rank op := (Prod.mk.inj (Shape.node.inj same).1).1
          exact False.elim (rank_positive op eqRank.symm)
    | node first before =>
      simp only [Term.WellFormed] at leftFormed
      by_cases strict : first = .strict
      · subst first
        obtain ⟨effect,tail,rfl⟩ := strict_arguments leftFormed.1
        rw [project_strict] at same
        have smaller := child_size_lt (op := .strict) (show tail ∈ [effect,tail] by simp)
        exact .strictLeft effect (ih (by omega) (leftFormed.2 _ (by simp)) rightFormed same)
      · rw [project_ordinary first before strict] at same
        cases right with
        | var index =>
          simp only [project] at same
          have eqRank : rank first = 0 := (Prod.mk.inj (Shape.node.inj same).1).1
          exact False.elim (rank_positive first eqRank)
        | node second after =>
          simp only [Term.WellFormed] at rightFormed
          by_cases strictRight : second = .strict
          · subst second
            obtain ⟨effect,tail,rfl⟩ := strict_arguments rightFormed.1
            rw [project_strict,← project_ordinary first before strict] at same
            have smaller := child_size_lt (op := .strict) (show tail ∈ [effect,tail] by simp)
            have checked : (Term.node first before).WellFormed := by simpa only [Term.WellFormed] using leftFormed
            exact .strictRight effect (ih (by omega) checked (rightFormed.2 _ (by simp)) same)
          · rw [project_ordinary second after strictRight] at same
            obtain ⟨header,children⟩ := Shape.node.inj same
            have length : (conversionChildren first before).length = (conversionChildren second after).length := by
              simpa only [List.length_map] using congrArg List.length children
            have arity : first.arity = second.arity := by
              rw [← arity_from_retained leftFormed.1,← arity_from_retained rightFormed.1,length,header]
            have sameOp := header_injective header arity
            subst second
            refine .node strict (aligned_retained_lists ?_ children)
            intro a aMember b bMember compared
            have inFirst := retained_member aMember
            have inSecond := retained_member bMember
            have aSmaller := child_size_lt (op := first) inFirst
            have bSmaller := child_size_lt (op := first) inSecond
            exact ih (by omega) (leftFormed.2 a inFirst) (rightFormed.2 b inSecond) compared

/-- Structural identity supplies nested evidence positions without requiring
all fields to be retained. Each aligned ordinary node has the same full
opcode and aligns its original retained children in order. -/
theorem project_aligns_occurrences (left : first.WellFormed) (right : second.WellFormed)
    (same : project first = project second) : OccurrenceAlignment first second :=
  occurrences_within _ (Nat.le_refl _) left right same

end Jihoo.NativeKernel.NativeCoreCompare
