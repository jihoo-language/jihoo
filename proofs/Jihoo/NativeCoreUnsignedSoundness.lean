import Jihoo.NativeCoreUnsignedCollect
import Jihoo.NativeCoreUnsignedCanonical
import Jihoo.NativeBindingMachineReaderResume
import Jihoo.NativeBindingMachineOwnedReader
import Jihoo.NativeLoanPureConversion

/-! Typed arithmetic meaning of the native collector and canonicalizer.
The mathematical presentation symbolically expands only the constants.
The executable graph code stores one widened word and a balanced tree. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedSoundness

open NativeArena Environment NativeConstantAccumulator
open NativeCoreUnsignedCollect (Agreement Collects View termView)
open ACU (Arithmetic sumTerms)

private theorem arithmetic (step : Arithmetic a b) : RawValue.Conv env a b :=
  .old (.old (.acu step.toConv))

private theorem add_congr (left : RawValue.Conv env a a') (right : RawValue.Conv env b b') :
    RawValue.Conv env (.uadd a b) (.uadd a' b') :=
  .node .uadd (.cons left (.cons right .nil))

private inductive SourceView : Term → View Term → Prop where
  | sum : SourceView (.uadd a b) (.sum a b)
  | strict : SourceView (.strict a b) (.strict a b)
  | literal : SourceView (.natural n) (.literal (UInt64.ofNat n))
  | atom : SourceView term .atom

private theorem source_view (shape : term.WellFormed) : SourceView term (termView term) := by
  cases term with
  | var => exact .atom
  | node op terms =>
      rw [Term.WellFormed] at shape
      cases op
      all_goals try exact .atom
      case natural =>
        cases terms with
        | nil => exact .literal
        | cons => cases shape.1
      case uadd =>
        rcases terms with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
        · cases shape.1
        · cases shape.1
        · exact .sum
        · cases shape.1
      case strict =>
        rcases terms with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
        · cases shape.1
        · cases shape.1
        · exact .strict
        · cases shape.1

private theorem natural_updates_append (first second : List Update) (value : Nat) :
    runNatural (first ++ second) value = (runNatural first value).bind (runNatural second) := by
  induction first generalizing value with
  | nil => rfl
  | cons update rest ih =>
      cases update with
      | literal => exact ih _
      | cancel =>
          simp only [List.cons_append, runNatural]
          split
          · exact ih _
          · rfl

private theorem shuffle (a b c d : List Term) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simpa only [List.append_assoc] using ((List.perm_append_comm (l₁ := b) (l₂ := c)).append_right d).append_left a

private theorem sum_linear (left : RawValue.Conv env a (sumTerms (ats ++ List.replicate x (.natural 1))))
    (right : RawValue.Conv env b (sumTerms (bts ++ List.replicate y (.natural 1)))) :
    RawValue.Conv env (.uadd a b) (sumTerms ((ats ++ bts) ++ List.replicate (x+y) (.natural 1))) := by
  apply (add_congr left right).trans
  apply arithmetic
  apply (Arithmetic.sumTerms_append _ _).trans
  apply Arithmetic.sumTerms_perm
  rw [← List.replicate_append_replicate]
  exact shuffle _ _ _ _

structure TypedCollection (env : Environment) (ctx : Context) (term : Term)
    (atoms pending : List Term) (updates : List Update) (value : Nat) : Prop where
  accumulation : ∀ initial, runNatural updates initial = some (initial + value)
  converted : RawValue.Conv env term (sumTerms (atoms ++ List.replicate value (.natural 1)))
  atomsTyped : ∀ atom ∈ atoms, LoanTyping.HasType env [] ctx true atom .u64
  pendingTyped : ∀ prefixTerm ∈ pending, ∃ type, LoanTyping.HasType env [] ctx true prefixTerm type

/-- Checking supplies every literal width and the type of each surviving atom
and Strict prefix. Conversion allows the exact reordered mathematical sum. -/
theorem typed_trace (trace : Collects term atoms pending updates visits)
    (shape : term.WellFormed) (checked : LoanTyping.HasType env [] ctx true term .u64) :
    ∃ value, TypedCollection env ctx term atoms pending updates value := by
  induction trace with
  | sum viewed _ _ leftIH rightIH =>
      have source := source_view shape
      rw [viewed] at source
      cases source
      simp only [Term.uadd, Term.WellFormed] at shape
      obtain ⟨leftTyped, rightTyped, _⟩ := checked.uadd_inputs
      obtain ⟨x, left⟩ := leftIH (shape.2 _ List.mem_cons_self) leftTyped
      obtain ⟨y, right⟩ := rightIH (shape.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)) rightTyped
      refine ⟨x + y, ⟨?_, sum_linear left.converted right.converted, ?_, ?_⟩⟩
      · intro initial
        rw [natural_updates_append, left.accumulation]
        simp only [Option.bind_some, right.accumulation, Nat.add_assoc]
      · intro atom member
        rcases List.mem_append.mp member with member | member
        · exact left.atomsTyped atom member
        · exact right.atomsTyped atom member
      · intro prefixTerm member
        rcases List.mem_append.mp member with member | member
        · exact left.pendingTyped prefixTerm member
        · exact right.pendingTyped prefixTerm member
  | strict viewed _ resultIH =>
      have source := source_view shape
      rw [viewed] at source
      cases source
      simp only [Term.strict, Term.WellFormed] at shape
      obtain ⟨value, result⟩ := resultIH (shape.2 _ (List.mem_cons_of_mem _ List.mem_cons_self))
        checked.strict_tail
      refine ⟨value, ⟨result.accumulation, (RawValue.Conv.strict _ _).trans result.converted, result.atomsTyped, ?_⟩⟩
      intro prefixTerm member
      rcases List.mem_cons.mp member with rfl | member
      · exact checked.strict_first
      · exact result.pendingTyped prefixTerm member
  | literal viewed =>
      have source := source_view shape
      rw [viewed] at source
      cases source
      rename_i n
      have bound := checked.natural_bound
      refine ⟨n, ⟨?_, ?_, by simp, by simp⟩⟩
      · intro initial
        simp only [runNatural, UInt64.toNat_ofNat_of_lt' bound]
      · exact arithmetic (Arithmetic.literal_ones _ bound)
  | atom _ =>
      refine ⟨0, ⟨by simp [runNatural], ?_, ?_, by simp⟩⟩
      · exact arithmetic (Arithmetic.zero _).symm
      · intro atom member
        rcases List.mem_singleton.mp member with rfl
        exact checked

structure Emission (env : Environment) (ctx : Context) (arena finalArena : Arena)
    (original originalType : Term) (effects : List Nat) (output : Nat) : Prop where
  frame : Prefix arena finalArena
  result : ∃ term pending, Represents finalArena output term ∧ RepresentsList arena effects pending ∧
    RawValue.Conv env original term ∧ LoanTyping.HasType env [] ctx true term originalType ∧
    ∀ prefixTerm ∈ pending, ∃ type, LoanTyping.HasType env [] ctx true prefixTerm type
  backward : Backward arena → Backward finalArena

private theorem agreement_emit_typed (agreement : Agreement arena source {} after visits)
    (bounded : ∀ {atoms pending updates}, Collects source atoms pending updates visits →
      literalVisits updates ≤ 1000000)
    (shaped : source.WellFormed) (checked : LoanTyping.HasType env [] ctx true source .u64)
    (emitted : (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).result =
      .ok (some output)) :
    Emission env ctx arena (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).arena
      source .u64 after.pending.toList output := by
  obtain ⟨atoms, pending, updates, refs, prefixes, trace, refsRep, pendingRep, atomsEq, pendingEq, wordSum⟩ :=
    agreement.trace
  have ceiling := bounded trace
  have precise := runWord_within_core_steps updates ceiling
  change runWord updates 0 = some after.constant at wordSum
  rw [wordSum, Option.map_some] at precise
  obtain ⟨value, typed⟩ := typed_trace trace shaped checked
  have valueEq : after.constant.toNat = value :=
    Option.some.inj (precise.trans (by simpa only [Nat.zero_add] using typed.accumulation 0))
  rw [← valueEq] at typed
  change after.atoms.toList = refs at atomsEq
  change after.pending.toList = prefixes at pendingEq
  have atomsRep : RepresentsList arena after.atoms.toList atoms := atomsEq ▸ refsRep
  have prefixesRep : RepresentsList arena after.pending.toList pending := pendingEq ▸ pendingRep
  obtain ⟨frame, outputRep, backwards⟩ := NativeCoreUnsignedCanonical.run_refines atomsRep emitted
  let term := NativeCoreUnsignedCanonical.canonicalTerm runtime atoms after.constant.toNat
  have same := (NativeCoreUnsignedCanonical.canonicalTerm_linear runtime atoms after.constant.toNat).symm
  exact ⟨frame, ⟨term, pending, outputRep, prefixesRep, typed.converted.trans (arithmetic same),
    NativeCoreUnsignedCanonical.canonicalTerm_typed typed.atomsTyped, typed.pendingTyped⟩, backwards⟩

/-- A live collection followed by canonical emission represents a
definitionally equal U64 expression, retaining the typed Strict prefixes. -/
theorem collect_and_emit_typed
    (represented : Represents arena root source)
    (checked : LoanTyping.HasType env loans ctx mode source .u64)
    (limitBound : limit ≤ 1000000)
    (collected : NativeCoreUnsignedCollect.run arena limit depth initial root {} = (.ok after, spent))
    (emitted : (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).result =
      .ok (some output)) :
    Emission env ctx arena (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).arena
      source .u64 after.pending.toList output := by
  obtain ⟨visits, counted, within, agreement⟩ := NativeCoreUnsignedCollect.run_refines represented collected
  apply agreement_emit_typed agreement ?_ represented.wellFormed (checked.ghost []) emitted
  intro _ _ _ trace
  have count := trace.literal_budget
  omega

/-- The two walks used by Core.sum start at the original operands. Their
canonical emission keeps the exact original type through result conversions. -/
theorem collect_operands_and_emit_typed
    (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (limitBound : limit ≤ 1000000)
    (collected : NativeCoreUnsignedCollect.runOperands arena limit depth initial a b = (.ok after, spent))
    (emitted : (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).result =
      .ok (some output)) :
    Emission env ctx arena (NativeCoreUnsignedCanonical.run runtime arena after.atoms.toList after.constant work).arena
      (.uadd first second) originalType after.pending.toList output := by
  obtain ⟨visits, counted, within, agreement⟩ :=
    NativeCoreUnsignedCollect.runOperands_refines left right collected
  obtain ⟨leftTyped, rightTyped, converted⟩ := checked.uadd_inputs
  have shaped : (Term.uadd first second).WellFormed := by
    simp only [Term.uadd, Term.WellFormed, Op.arity, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false, true_and]
    rintro term (rfl | rfl)
    · exact left.wellFormed
    · exact right.wellFormed
  have budget : ∀ {atoms pending updates}, Collects (.uadd first second) atoms pending updates (visits+1) →
      literalVisits updates ≤ 1000000 := by
    intro _ _ _ trace
    have occurrences := trace.sum_literal_budget
    omega
  have built := agreement_emit_typed agreement budget shaped (.uadd leftTyped rightTyped) emitted
  obtain ⟨term, pending, result, effects, same, typed, effectTypes⟩ := built.result
  exact ⟨built.frame, ⟨term, pending, result, effects, same, typed.convert converted, effectTypes⟩, built.backward⟩

end Jihoo.NativeKernel.NativeCoreUnsignedSoundness
