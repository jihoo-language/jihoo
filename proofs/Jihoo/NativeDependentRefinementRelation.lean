import Jihoo.NativeDependentRelationalContexts
import Jihoo.NativeDependentNumericCoherence

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

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
