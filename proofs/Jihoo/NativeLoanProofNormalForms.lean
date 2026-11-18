import Jihoo.NativeLoanProofNormalization

/-! A successful run of the typed source normalizer is stable under larger
resource bounds. The residual is a fixed point at the original bounds. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ProofNormalization
open NativeKernel.Conversion (treeSize)

private def visitChildren (visit : Term → Option Term) : Term → Option Term
  | .var index => some (.var index)
  | .node op children =>
    if op = .lend then some (.node op children) else (children.mapM visit).map (.node op)

private def finish (env : Environment) (budget : Nat) (visit : Term → Option Term) (term : Term) : Option Term :=
  if 4*(treeSize term+1)^2 > budget then none else
    match contract env term with
    | none => some term
    | some next => visit next

private theorem normalize_succ (env : Environment) (budget fuel : Nat) (term : Term) :
    normalize? env budget (fuel+1) term =
      if treeSize term > budget then none
      else (visitChildren (normalize? env budget fuel) term).bind (finish env budget (normalize? env budget fuel)) := by
  unfold normalize?
  split
  · rfl
  · cases term with
    | var => rfl
    | node op children => by_cases lending : op = .lend <;> simp [visitChildren,finish,lending] <;> rfl

private theorem mapM_stable {α : Type} {original replay : α → Option α} {input output : List α}
    (stable : ∀ {x y}, original x = some y → replay x = some y ∧ replay y = some y)
    (visited : input.mapM original = some output) :
    input.mapM replay = some output ∧ output.mapM replay = some output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil,pure,Option.some.injEq] at visited
    subst output
    exact ⟨rfl,rfl⟩
  | cons head tail ih =>
    simp only [List.mapM_cons] at visited
    cases oldHead : original head with
    | none => simp [oldHead] at visited
    | some next =>
      simp only [oldHead,Bind.bind,Option.bind] at visited
      cases oldTail : tail.mapM original with
      | none => simp [oldTail] at visited
      | some nextTail =>
        simp only [oldTail,pure,Option.some.injEq] at visited
        subst output
        obtain ⟨headReplayed,headFixed⟩ := stable oldHead
        obtain ⟨tailReplayed,tailFixed⟩ := ih oldTail
        constructor <;> simp [List.mapM_cons,headReplayed,headFixed,tailReplayed,tailFixed]

private theorem visitChildren_stable {original replay : Term → Option Term}
    (stable : ∀ {x y}, original x = some y → replay x = some y ∧ replay y = some y)
    (visited : visitChildren original input = some output) :
    visitChildren replay input = some output ∧ visitChildren replay output = some output := by
  cases input with
  | var => cases visited; exact ⟨rfl,rfl⟩
  | node op children =>
    by_cases lending : op = .lend
    · simp only [visitChildren,lending,↓reduceIte,Option.some.injEq] at visited
      subst output
      simp [visitChildren,lending]
    · simp only [visitChildren,lending,↓reduceIte] at visited
      obtain ⟨rebuilt,mapped,rfl⟩ := Option.map_eq_some_iff.mp visited
      obtain ⟨replayed,fixed⟩ := mapM_stable (original := original) (replay := replay) stable mapped
      simp [visitChildren,lending,replayed,fixed]

private theorem input_bound (fits : 4*(treeSize term+1)^2 ≤ budget) : treeSize term ≤ budget := by
  have growth : treeSize term+1 ≤ (treeSize term+1)^2 := by
    calc
      treeSize term+1 = (treeSize term+1)*1 := (Nat.mul_one _).symm
      _ ≤ (treeSize term+1)*(treeSize term+1) := Nat.mul_le_mul_left _ (by omega)
      _ = (treeSize term+1)^2 := by simp [Nat.pow_succ]
  omega

/-- More budget and fuel preserve any successful result. With the same or
larger bounds, normalizing the result again returns that exact term. -/
theorem normalize?_stable (accepted : normalize? env budget fuel input = some output)
    (budgetLe : budget ≤ replayBudget) (fuelLe : fuel ≤ replayFuel) :
    normalize? env replayBudget replayFuel input = some output ∧
    normalize? env replayBudget replayFuel output = some output := by
  induction fuel generalizing input output replayFuel with
  | zero => simp [normalize?] at accepted
  | succ fuel ih =>
    cases replayFuel with
    | zero => omega
    | succ replayFuel =>
      have innerFuel : fuel ≤ replayFuel := Nat.le_of_succ_le_succ fuelLe
      rw [normalize_succ] at accepted
      split at accepted
      · contradiction
      rename_i inputFits
      obtain ⟨rebuilt,visited,finished⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨visitInput,visitOutput⟩ := visitChildren_stable (fun accepted => ih accepted innerFuel) visited
      unfold finish at finished
      split at finished
      · contradiction
      rename_i rebuiltFits
      have inputFits' : ¬treeSize input > replayBudget := by omega
      have rebuiltFits' : ¬4*(treeSize rebuilt+1)^2 > replayBudget := by omega
      cases root : contract env rebuilt with
      | none =>
        rw [root] at finished
        have exactResult : rebuilt = output := Option.some.inj finished
        subst output
        have outputFits : ¬treeSize rebuilt > replayBudget := by
          have bound := input_bound (term := rebuilt) (budget := replayBudget) (by omega)
          omega
        constructor
        · rw [normalize_succ,ite_eq_right inputFits',visitInput]
          simp [finish,rebuiltFits',root]
        · rw [normalize_succ,ite_eq_right outputFits,visitOutput]
          simp [finish,rebuiltFits',root]
      | some next =>
        rw [root] at finished
        obtain ⟨replayed,fixed⟩ := ih finished innerFuel
        constructor
        · rw [normalize_succ,ite_eq_right inputFits',visitInput]
          simp [finish,rebuiltFits',root,replayed]
        · exact (ih finished (Nat.le_succ_of_le innerFuel)).2

/-- Runs with different resources agree whenever both reach a normal result. -/
theorem normalize?_unique (first : normalize? env firstBudget firstFuel input = some firstResult)
    (second : normalize? env secondBudget secondFuel input = some secondResult) : firstResult = secondResult :=
  Option.some.inj
    ((normalize?_stable first (Nat.le_max_left _ _) (Nat.le_max_left _ _)).1.symm.trans
      (normalize?_stable second (Nat.le_max_right _ _) (Nat.le_max_right _ _)).1)

/-- No contractor redex occurs at the root or at a descendant visited by the
source normalizer. A Lend node protects its callback bodies. -/
inductive Normal (env : Environment) : Term → Prop where
  | var (index : Nat) : Normal env (.var index)
  | node {op children} (root : contract env (.node op children) = none)
      (descendants : op ≠ .lend → ∀ t ∈ children, Normal env t) : Normal env (.node op children)

private theorem mapM_normal {visit : Term → Option Term} {input output : List Term}
    (sound : ∀ {input output}, visit input = some output → Normal env output)
    (visited : input.mapM visit = some output) : ∀ t ∈ output, Normal env t := by
  induction input generalizing output with
  | nil => simp only [List.mapM_nil,pure,Option.some.injEq] at visited; subst output; simp
  | cons head tail ih =>
    simp only [List.mapM_cons] at visited
    cases first : visit head with
    | none => simp [first] at visited
    | some next =>
      simp only [first,Bind.bind,Option.bind] at visited
      cases remaining : tail.mapM visit with
      | none => simp [remaining] at visited
      | some nextTail =>
        simp only [remaining,pure,Option.some.injEq] at visited
        subst output
        intro t member
        rcases List.mem_cons.mp member with rfl | member
        · exact sound first
        · exact ih remaining t member

private theorem visitChildren_normal {visit : Term → Option Term}
    (sound : ∀ {input output}, visit input = some output → Normal env output)
    (visited : visitChildren visit input = some output) (root : contract env output = none) : Normal env output := by
  cases input with
  | var index => cases visited; exact .var index
  | node op children =>
    by_cases lending : op = .lend
    · simp only [visitChildren,lending,↓reduceIte,Option.some.injEq] at visited
      subst output
      exact .node root fun ordinary => False.elim (ordinary rfl)
    · simp only [visitChildren,lending,↓reduceIte] at visited
      obtain ⟨rebuilt,mapped,rfl⟩ := Option.map_eq_some_iff.mp visited
      exact .node root fun _ => mapM_normal (visit := visit) sound mapped

/-- The executable computation establishes normality on all visited paths. -/
theorem normalize?_normal (accepted : normalize? env budget fuel input = some output) : Normal env output := by
  induction fuel generalizing input output with
  | zero => simp [normalize?] at accepted
  | succ fuel ih =>
    rw [normalize_succ] at accepted
    split at accepted
    · contradiction
    obtain ⟨rebuilt,visited,finished⟩ := Option.bind_eq_some_iff.mp accepted
    unfold finish at finished
    split at finished
    · contradiction
    cases root : contract env rebuilt with
    | none =>
      rw [root] at finished
      have exactResult : rebuilt = output := Option.some.inj finished
      subst output
      exact visitChildren_normal (fun accepted => ih accepted) visited root
    | some next =>
      rw [root] at finished
      exact ih finished

end Jihoo.NativeKernel.Environment.LoanTyping.ProofNormalization
