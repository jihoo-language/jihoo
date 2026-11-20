import Jihoo.NativeDependentNumericCoherence
import Jihoo.NativeDependentRelationalContexts
import Jihoo.NativeLoanTyping

set_option maxUniverseOffset 40

/-! Inequality evidence in the dependent gluing model supplies the numerical
precondition of ghost subtraction. Premises refer to values in the current
dependent context and therefore include erased hypotheses and computed words. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

def less (env : Environment) {Γ : Contextual.Context}
    (left right : Contextual.Tm (natural env Γ).code) : Ty env Γ .proposition :=
  proposition env Γ fun point => (left point).down < (right point).down

private def Decided (env : Environment) : Term → Prop
  | .decide a b =>
    ∃ left right, left < 2^64 ∧ right < 2^64 ∧ left < right ∧
      RawLend.Conv env a (.natural left) ∧ RawLend.Conv env b (.natural right)
  | _ => True

private theorem decided_literals (typed : LoanTyping.HasType env loans ctx mode term type) : Decided env term := by
  apply LoanTyping.HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => Decided env term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | exact True.intro | assumption | skip
  case decide leftFits rightFits smaller =>
    exact ⟨_,_,leftFits,rightFits,smaller,.refl _, .refl _⟩
  case decideConverted _ _ leftNormal rightNormal leftFits rightFits smaller _ _ =>
    exact ⟨_,_,leftFits,rightFits,smaller,leftNormal,rightNormal⟩
  case dataElim => split <;> trivial

/-- Any realized valuation of a checked Decide has a true strict inequality
between the two interpreted input words. The checker determines the literal
normal forms even when the written operands are computations. -/
theorem checked_decision_order (wf : UnifiedProgram.EnvWellFormed env) (Γ : Ctx env)
    (typed : LoanTyping.HasType env loans ctx mode (.decide a b) requested)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    (first : Realizes Γ (natural env Γ.meaning) a left)
    (second : Realizes Γ (natural env Γ.meaning) b right)
    {values : Nat → Term} {point : Γ.meaning} (assigned : Γ.realizes values point) :
    (left point).down < (right point).down := by
  obtain ⟨m,n,mFits,nFits,ordered,mConv,nConv⟩ := decided_literals typed
  have mClosed := mConv.substitution values wf.closed
  have nClosed := nConv.substitution values wf.closed
  simp only [Term.natural,Term.subst,substArgs] at mClosed nClosed
  have firstValue := natural_value_unique wf.admissible Γ.meaning point (first values point assigned)
    (mClosed.trans (natural_literal (Γ := Γ.meaning) (point := point) m mFits))
  have secondValue := natural_value_unique wf.admissible Γ.meaning point (second values point assigned)
    (nClosed.trans (natural_literal (Γ := Γ.meaning) (point := point) n nFits))
  rw [firstValue,secondValue]
  exact ordered

theorem checked_closed_decision_realizes (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans [] mode (.decide a b) requested)
    {left right : Contextual.Tm (natural env (empty env).meaning).code}
    (first : Realizes (empty env) (natural env (empty env).meaning) a left)
    (second : Realizes (empty env) (natural env (empty env).meaning) b right) :
    ∃ meaning : Contextual.Tm (less env left right).code,
      Realizes (empty env) (less env left right) (.decide a b) meaning := by
  refine ⟨fun point => ⟨⟨checked_decision_order wf (empty env) typed first second
    (values := Term.var) (point := point) trivial⟩⟩,?_⟩
  intro values point assigned
  trivial

theorem zeroLe_realizes (Γ : Ctx env) (word : Term)
    (value : Contextual.Tm (natural env Γ.meaning).code) :
    Realizes Γ (less env (Contextual.numeral 0) (Contextual.add value (Contextual.numeral 1)))
      (.zeroLe word) (Contextual.zeroLe value) := by
  intro values point assigned
  trivial

/-- Translating both endpoints by a realized mathematical word preserves
strict inequality, including sums that exceed a physical word. -/
theorem ltAdd_realizes (Γ : Ctx env)
    {left right delta : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (less env left right).code}
    (_evidence : Realizes Γ (less env left right) proof proofMeaning) (a b k : Term) :
    ∃ meaning : Contextual.Tm (less env (Contextual.add left delta) (Contextual.add right delta)).code,
      Realizes Γ (less env (Contextual.add left delta) (Contextual.add right delta))
        (.ltAdd a b k proof) meaning := by
  refine ⟨fun point => ⟨⟨Nat.add_lt_add_right (proofMeaning point).down.down (delta point).down⟩⟩,?_⟩
  intro values point assigned
  trivial

theorem ltCancel_realizes (Γ : Ctx env)
    {left right delta : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (less env (Contextual.add left delta) (Contextual.add right delta)).code}
    (_evidence : Realizes Γ (less env (Contextual.add left delta) (Contextual.add right delta)) proof proofMeaning)
    (a b k : Term) :
    ∃ meaning : Contextual.Tm (less env left right).code,
      Realizes Γ (less env left right) (.ltCancel a b k proof) meaning := by
  refine ⟨fun point => ⟨⟨Nat.lt_of_add_lt_add_right (proofMeaning point).down.down⟩⟩,?_⟩
  intro values point assigned
  trivial

theorem ltLe_realizes (Γ : Ctx env)
    {left middle right : Contextual.Tm (natural env Γ.meaning).code}
    {strictMeaning : Contextual.Tm (less env left middle).code}
    {weakMeaning : Contextual.Tm (less env middle (Contextual.add right (Contextual.numeral 1))).code}
    (_strict : Realizes Γ (less env left middle) first strictMeaning)
    (_weak : Realizes Γ (less env middle (Contextual.add right (Contextual.numeral 1))) second weakMeaning)
    (a b c : Term) :
    ∃ meaning : Contextual.Tm (less env left right).code,
      Realizes Γ (less env left right) (.ltLe a b c first second) meaning := by
  refine ⟨fun point => ⟨⟨Nat.lt_of_lt_of_le (strictMeaning point).down.down
    (Nat.lt_succ_iff.mp (weakMeaning point).down.down)⟩⟩,?_⟩
  intro values point assigned
  trivial

/-- An impossible upper endpoint eliminates into the actual dependent fiber,
without a semantic inhabitant of that fiber supplied as a premise. -/
theorem absurd_realizes (Γ : Ctx env) (A : Ty env Γ.meaning sort)
    {left : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (less env left (Contextual.numeral 0)).code}
    (_evidence : Realizes Γ (less env left (Contextual.numeral 0)) proof proofMeaning) (target : Term) :
    ∃ meaning : Contextual.Tm A.code, Realizes Γ A (.absurd target proof) meaning := by
  have impossible (point : Γ.meaning) : False := Nat.not_lt_zero _ (proofMeaning point).down.down
  exact ⟨fun point => (impossible point).elim,fun _ point _ => (impossible point).elim⟩

private theorem bounded_subtraction (point : Γ)
    {left right : Finite.Carrier Finite.natural}
    (first : (natural env Γ).realizes point a left) (second : (natural env Γ).realizes point b right)
    (ordered : right.down ≤ left.down) (fits : left.down < 2^64) (proof : Term) :
    (natural env Γ).realizes point (.usub a b proof) ⟨left.down-right.down⟩ := by
  have firstLiteral : RawLend.Conv env a (.natural left.down) :=
    first.trans (natural_literal (Γ := Γ) (point := point) left.down fits).symm
  have secondLiteral : RawLend.Conv env b (.natural right.down) :=
    second.trans (natural_literal (Γ := Γ) (point := point) right.down (Nat.lt_of_le_of_lt ordered fits)).symm
  have exposed : RawLend.Conv env (.usub a b proof) (.usub (.natural left.down) (.natural right.down) proof) :=
    .node .usub (.cons firstLiteral (.cons secondLiteral (.cons (.refl _) .nil)))
  have reduced : RawLend.Conv env (.usub (.natural left.down) (.natural right.down) proof)
      (.natural (left.down-right.down)) := .old (.legacy (.sub _ _ _ ordered fits))
  exact exposed.trans (reduced.trans (natural_literal (Γ := Γ) (point := point) _ (Nat.lt_of_le_of_lt (Nat.sub_le ..) fits)))

/-- Each valuation of the formed bound justifies the actual literal
subtraction rule. The proof term can contain any earlier erased hypotheses. -/
theorem bounded_subtraction_realizes (Γ : Ctx env)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (less env right (Contextual.add left (Contextual.numeral 1))).code}
    (first : Realizes Γ (natural env Γ.meaning) a left)
    (second : Realizes Γ (natural env Γ.meaning) b right)
    (_proof : Realizes Γ (less env right (Contextual.add left (Contextual.numeral 1))) evidence proofMeaning)
    (fits : ∀ values point, Γ.realizes values point → (left point).down < 2^64) :
    Realizes Γ (natural env Γ.meaning) (.usub a b evidence) (Contextual.subtract left right) := by
  intro values point assigned
  have ordered : (right point).down ≤ (left point).down :=
    Nat.lt_succ_iff.mp (proofMeaning point).down.down
  simpa only [Term.usub,Term.subst,substArgs,Op.binders,liftSub,Contextual.subtract] using
    bounded_subtraction point (first values point assigned) (second values point assigned)
      ordered (fits values point assigned) (evidence.subst values)

/-- Two valid proof terms for the original dependent bound yield the same
value in any interpreted result family, in every open valuation. -/
theorem bounded_subtractions_share_meaning (Γ : Ctx env)
    (returns : Ty env (Contextual.extend Γ.meaning (natural env Γ.meaning).code) sort)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    {firstProof secondProof : Contextual.Tm (less env right (Contextual.add left (Contextual.numeral 1))).code}
    {function : Contextual.Tm (pi (natural env Γ.meaning) returns).code}
    (callee : Realizes Γ (pi (natural env Γ.meaning) returns) f function)
    (first : Realizes Γ (natural env Γ.meaning) a left)
    (second : Realizes Γ (natural env Γ.meaning) b right)
    (firstEvidence : Realizes Γ (less env right (Contextual.add left (Contextual.numeral 1))) e firstProof)
    (secondEvidence : Realizes Γ (less env right (Contextual.add left (Contextual.numeral 1))) e' secondProof)
    (fits : ∀ values point, Γ.realizes values point → (left point).down < 2^64) :
    let result := Contextual.subtract left right
    let fiber := returns.substitution (Contextual.pair Contextual.identity result)
    ∃ meaning : Contextual.Tm fiber.code,
      Realizes Γ fiber (.app f (.usub a b e)) meaning ∧ Realizes Γ fiber (.app f (.usub a b e')) meaning := by
  exact ⟨_,application_realizes Γ _ returns callee (bounded_subtraction_realizes Γ first second firstEvidence fits),
    application_realizes Γ _ returns callee (bounded_subtraction_realizes Γ first second secondEvidence fits)⟩

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
