import Jihoo.NativeDependentRelationalContexts
import Jihoo.NativeDependentNumericCoherence
import Jihoo.NativeLoanArithmeticProofConsistency
import Jihoo.NativeLoanComparisonEvidence
import Jihoo.NativeLoanIndexedPropositionModel

set_option maxUniverseOffset 40

/-! The dependent relation interprets Refine in Type0 as a natural paired
with evidence in the actual Prop carrier. Native witness and proof
projections realize those components. Equal realized words determine the
same semantic value even when their native evidence terms differ. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

open Finite (Carrier Universe decodeProp)

abbrev Predicate (env : Environment) (Γ : Contextual.Context) :=
  Ty env (Contextual.extend Γ (natural env Γ).code) .proposition

private theorem propositionProof (code : Universe .proposition) (value : Carrier code) : decodeProp code := by
  cases code
  exact value.down.down

private def propositionValue : (code : Universe .proposition) → decodeProp code → Carrier code
  | .proposition _, value => ⟨⟨value⟩⟩

private theorem proposition_roundtrip (code : Universe .proposition) (value : Carrier code) :
    propositionValue code (propositionProof code value) = value := by
  cases code
  rfl

def refinement (predicate : Predicate env Γ) : Ty env Γ (.type ⟨0,by decide⟩) where
  code point := .type0 { word : Nat // decodeProp (predicate.code ⟨point,⟨word⟩⟩) }
  realizes point term value :=
    (natural env Γ).realizes point (.witness term) ⟨value.down.val⟩ ∧
    predicate.realizes ⟨point,⟨value.down.val⟩⟩ (.proof term)
      (propositionValue _ value.down.property)
  conversion := by
    intro point _ _ _ converted
    exact and_congr ((natural env Γ).conversion point (.node .witness (.cons converted .nil)))
      (predicate.conversion _ (.node .proof (.cons converted .nil)))

def packed (predicate : Predicate env Γ) (point : Γ) (word : Carrier ((natural env Γ).code point))
    (evidence : Carrier (predicate.code ⟨point,word⟩)) :
    Carrier ((refinement predicate).code point) :=
  ⟨⟨word.down, propositionProof _ evidence⟩⟩

private theorem pack_value_realizes (predicate : Predicate env Γ) {point : Γ}
    {word : Carrier ((natural env Γ).code point)} {evidence : Carrier (predicate.code ⟨point,word⟩)}
    (wordRealized : (natural env Γ).realizes point witness word)
    (proofRealized : predicate.realizes ⟨point,word⟩ proof evidence) (annotation : Term) :
    (refinement predicate).realizes point (.pack annotation witness proof) (packed predicate point word evidence) := by
  have witnessProjection : RawLend.Conv env (.witness (.pack annotation witness proof)) witness :=
    .old (.legacy (.witnessPack annotation witness proof))
  have proofProjection : RawLend.Conv env (.proof (.pack annotation witness proof)) proof :=
    .old (.legacy (.proofPack annotation witness proof))
  refine ⟨((natural env Γ).conversion point witnessProjection).mpr wordRealized, ?_⟩
  change predicate.realizes ⟨point,word⟩ (.proof (.pack annotation witness proof))
    (propositionValue _ (propositionProof _ evidence))
  rw [proposition_roundtrip]
  exact (predicate.conversion _ proofProjection).mpr proofRealized

/-- Pack uses the word's actual dependent fiber. Both input realizations
are used directly, including under arbitrary earlier valuation binders. -/
theorem pack_realizes (Γ : Ctx env) (predicate : Predicate env Γ.meaning)
    {wordMeaning : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (Contextual.typeSubst predicate.code (Contextual.pair Contextual.identity wordMeaning))}
    (word : Realizes Γ (natural env Γ.meaning) witness wordMeaning)
    (evidence : Realizes Γ (predicate.substitution (Contextual.pair Contextual.identity wordMeaning)) proof proofMeaning)
    (annotation : Term) :
    Realizes Γ (refinement predicate) (.pack annotation witness proof)
      (fun point => packed predicate point (wordMeaning point) (proofMeaning point)) := by
  intro values point assigned
  simpa only [Term.pack, Term.subst, substArgs, Op.binders, liftSub] using
    pack_value_realizes predicate (word values point assigned) (evidence values point assigned)
      (annotation.subst values)

def witnessMeaning (predicate : Predicate env Γ) (refined : Contextual.Tm (refinement predicate).code) :
    Contextual.Tm (natural env Γ).code :=
  fun point => ⟨(refined point).down.val⟩

theorem witness_realizes (Γ : Ctx env) (predicate : Predicate env Γ.meaning)
    {meaning : Contextual.Tm (refinement predicate).code}
    (refined : Realizes Γ (refinement predicate) source meaning) :
    Realizes Γ (natural env Γ.meaning) (.witness source) (witnessMeaning predicate meaning) := by
  intro values point assigned
  simpa only [Term.witness, Term.subst, substArgs, Op.binders, liftSub, witnessMeaning] using
    (refined values point assigned).1

def proofMeaning (predicate : Predicate env Γ) (refined : Contextual.Tm (refinement predicate).code) :
    Contextual.Tm
      (Contextual.typeSubst predicate.code (Contextual.pair Contextual.identity (witnessMeaning predicate refined))) :=
  fun point => propositionValue _ (refined point).down.property

theorem proof_realizes (Γ : Ctx env) (predicate : Predicate env Γ.meaning)
    {meaning : Contextual.Tm (refinement predicate).code}
    (refined : Realizes Γ (refinement predicate) source meaning) :
    Realizes Γ (predicate.substitution (Contextual.pair Contextual.identity (witnessMeaning predicate meaning)))
      (.proof source) (proofMeaning predicate meaning) := by
  intro values point assigned
  simpa only [Term.proof, Term.subst, substArgs, Op.binders, liftSub, proofMeaning, witnessMeaning,
    Ty.substitution, Contextual.typeSubst, Function.comp_apply, Contextual.pair, Contextual.identity, id_eq] using
    (refined values point assigned).2

/-- The dependent predicate can expose a proof term at the source level.
The semantic Type0 value still depends only on the realized word. -/
theorem packed_proofs_agree (predicate : Predicate env Γ) (point : Γ)
    {word : Carrier ((natural env Γ).code point)}
    (first second : Carrier (predicate.code ⟨point,word⟩)) :
    packed predicate point word first = packed predicate point word second := by
  apply congrArg ULift.up
  exact Subtype.ext rfl

theorem refinement_witness_determines_value (admissible : EnvironmentDelta.Admissible env)
    (predicate : Predicate env Γ) (point : Γ) {first second : Carrier ((refinement predicate).code point)}
    (firstRealized : (refinement predicate).realizes point firstTerm first)
    (secondRealized : (refinement predicate).realizes point secondTerm second)
    (sameWord : RawLend.Conv env (.witness firstTerm) (.witness secondTerm)) :
    first = second := by
  have firstWord := ((natural env Γ).conversion point sameWord).mp firstRealized.1
  have same := natural_value_unique admissible Γ point firstWord secondRealized.1
  cases first
  cases second
  exact congrArg ULift.up (Subtype.ext (congrArg ULift.down same))

/-- Any semantic codomain under a refinement binder has the same fiber for
packs of the same word, by host proof irrelevance at the checked predicate. -/
theorem dependent_pack_fibers_agree (predicate : Predicate env Γ)
    (family : Contextual.Ty (Contextual.extend Γ (refinement predicate).code) sort) (point : Γ)
    {word : Carrier ((natural env Γ).code point)}
    (first second : Carrier (predicate.code ⟨point,word⟩)) :
    family ⟨point,packed predicate point word first⟩ = family ⟨point,packed predicate point word second⟩ :=
  congrArg (fun value => family ⟨point,value⟩) (packed_proofs_agree predicate point first second)

def literalUpperBound (env : Environment) (bound : Nat) : Predicate env (empty env).meaning :=
  proposition env _ fun point => point.2.down < bound

private def writtenUpperBound (bound : Nat) : Term :=
  .lam false .u64 (.lt (.var 0) (.natural bound))

/-- A checked Pack guarded by a literal upper bound reconstructs the
concrete semantic inhabitant from its source judgment and arithmetic
evidence. Its word interpretation is the original U64 literal. -/
theorem checked_literal_pack_realizes (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.HasType env loans [] mode
      (.pack (writtenUpperBound bound) (.natural word) evidence) requested)
    (supported : Semantics.LoanArithmetic.Supported evidence) :
    ∃ meaning : Contextual.Tm (refinement (literalUpperBound env bound)).code,
      Realizes (empty env) (refinement (literalUpperBound env bound))
        (.pack (writtenUpperBound bound) (.natural word) evidence) meaning ∧
      ∀ point, (meaning point).down.val = word := by
  have unpacked : LoanTyping.HasType env loans [] mode
      (.pack (writtenUpperBound bound) (.natural word) evidence) (.refine (writtenUpperBound bound)) :=
    typed.convert typed.principalView.symm
  have wordTyped := LoanTyping.compute_ghost_preservation wf
    (.witnessPack (writtenUpperBound bound) (.natural word) evidence) (LoanTyping.HasType.witness unpacked)
  have wordWidth : word < 2^64 := IndexedProposition.natural_bound wordTyped
  have formed : LoanTyping.ComparisonEvidence.HasEvidence env []
      (.app (writtenUpperBound bound) (.natural word)) evidence :=
    LoanTyping.ComparisonEvidence.checked_evidence typed
  have beta : RawLend.Conv env (.app (writtenUpperBound bound) (.natural word)) (.lt (.natural word) (.natural bound)) := by
    have source : RawLend.Conv env (.app (writtenUpperBound bound) (.natural word))
        ((Term.lt (.var 0) (.natural bound)).subst (single (.natural word))) :=
      .old (.legacy (.beta false .u64 _ _))
    simpa only [Term.lt,Term.natural,Term.subst,substArgs,Op.binders,liftSub,single] using source
  have ordered : word < bound :=
    Semantics.LoanArithmetic.supported_affine_bound wf (.literal word) (formed.2.convert beta)
      supported (.refl _) (.refl _) (fun _ => 0)
  let context := empty env
  let predicate := literalUpperBound env bound
  let numeral : Contextual.Tm (natural env context.meaning).code := Contextual.numeral word
  let proofValue : Contextual.Tm (Contextual.typeSubst predicate.code (Contextual.pair Contextual.identity numeral)) :=
    fun _ => ⟨⟨ordered⟩⟩
  have realizedEvidence : Realizes context
      (predicate.substitution (Contextual.pair Contextual.identity numeral)) evidence proofValue := by
    intro _ _ _
    exact True.intro
  exact ⟨_, pack_realizes context predicate (numeral_realizes context word wordWidth)
    realizedEvidence (writtenUpperBound bound), fun _ => rfl⟩

theorem checked_literal_packs_have_same_meaning (wf : UnifiedProgram.EnvWellFormed env)
    (leftTyped : LoanTyping.HasType env loans [] mode
      (.pack (writtenUpperBound bound) (.natural word) leftEvidence) leftType)
    (rightTyped : LoanTyping.HasType env loans [] mode
      (.pack (writtenUpperBound bound) (.natural word) rightEvidence) rightType)
    (leftSupported : Semantics.LoanArithmetic.Supported leftEvidence)
    (rightSupported : Semantics.LoanArithmetic.Supported rightEvidence) :
    ∃ meaning : Contextual.Tm (refinement (literalUpperBound env bound)).code,
      Realizes (empty env) (refinement (literalUpperBound env bound))
        (.pack (writtenUpperBound bound) (.natural word) leftEvidence) meaning ∧
      Realizes (empty env) (refinement (literalUpperBound env bound))
        (.pack (writtenUpperBound bound) (.natural word) rightEvidence) meaning := by
  obtain ⟨first,leftRealized,firstWord⟩ := checked_literal_pack_realizes wf leftTyped leftSupported
  obtain ⟨second,rightRealized,secondWord⟩ := checked_literal_pack_realizes wf rightTyped rightSupported
  have same : first = second := by
    funext point
    exact congrArg ULift.up (Subtype.ext ((firstWord point).trans (secondWord point).symm))
  exact ⟨first,leftRealized,same.symm ▸ rightRealized⟩

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
