import Jihoo.NativeDependentRefinementRelation
import Jihoo.NativeLoanDeltaPreservation

set_option maxUniverseOffset 40

/-! The concrete equality relation tracks both semantic agreement of two
U64 values and a raw conversion to canonical reflexivity. Transport uses
the former to identify the semantic fibers and the latter to preserve
the payload's raw realization. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation

open Finite (Carrier Universe)

def equality (env : Environment) {Γ : Contextual.Context}
    (left right : Contextual.Tm (natural env Γ).code) : Ty env Γ .proposition where
  code := Contextual.equal left right
  realizes point term _ := RawLend.Conv env term (.refl (numeralTree (left point).down))
  conversion := by
    intro point first second value converted
    exact ⟨fun proved => converted.symm.trans proved,fun proved => converted.trans proved⟩

/-- A realized endpoint supplies the canonical representative of Refl.
The host proposition is inhabited by reflexivity in every valuation. -/
theorem reflexivity_realizes (Γ : Ctx env) {word : Contextual.Tm (natural env Γ.meaning).code}
    (realized : Realizes Γ (natural env Γ.meaning) endpoint word) :
    Realizes Γ (equality env word word) (.refl endpoint) (Contextual.refl word) := by
  intro values point assigned
  have canonical := RawLend.Conv.node .refl (.cons (realized values point assigned) .nil)
  change RawLend.Conv env ((Term.refl endpoint).subst values) (.refl (numeralTree (word point).down))
  simpa only [Term.refl, Term.subst, substArgs, Op.binders, liftSub] using canonical

private theorem endpoints_agree {left right : Carrier Finite.natural}
    (proof : Carrier (Finite.equal left.down right.down)) : left = right := by
  cases left
  cases right
  exact congrArg ULift.up proof.down.down

def transportedValue (predicate : Predicate env Γ) (point : Γ)
    {left right : Carrier Finite.natural} (proof : Carrier (Finite.equal left.down right.down))
    (payload : Carrier (predicate.code ⟨point,left⟩)) : Carrier (predicate.code ⟨point,right⟩) :=
  cast (congrArg (fun value => Carrier (predicate.code ⟨point,value⟩)) (endpoints_agree proof)) payload

private theorem transport_value_realizes (predicate : Predicate env Γ) (point : Γ)
    {left right : Carrier Finite.natural} (semantic : Carrier (Finite.equal left.down right.down))
    (reflexive : RawLend.Conv env equation (.refl (numeralTree left.down)))
    {value : Carrier (predicate.code ⟨point,left⟩)}
    (payload : predicate.realizes ⟨point,left⟩ term value) (annotation : Term) :
    predicate.realizes ⟨point,right⟩ (.transport annotation equation term)
      (transportedValue predicate point semantic value) := by
  have same := endpoints_agree semantic
  subst right
  have exposed : RawLend.Conv env (.transport annotation equation term)
      (.transport annotation (.refl (numeralTree left.down)) term) :=
    .node .transport (.cons (.refl _) (.cons reflexive (.cons (.refl _) .nil)))
  have normalized := exposed.trans (.old (.legacy (.transportRefl annotation (numeralTree left.down) term)))
  exact (predicate.conversion ⟨point,left⟩ normalized).mpr payload

/-- Transport preserves realization in the destination fiber of an
arbitrary interpreted dependent proposition. In particular a family may
itself require a raw canonical shape from its proofs. -/
theorem transport_realizes (Γ : Ctx env) (predicate : Predicate env Γ.meaning)
    {left right : Contextual.Tm (natural env Γ.meaning).code}
    {proofMeaning : Contextual.Tm (equality env left right).code}
    {payloadMeaning : Contextual.Tm (predicate.substitution (Contextual.pair Contextual.identity left)).code}
    (proof : Realizes Γ (equality env left right) equation proofMeaning)
    (payload : Realizes Γ (predicate.substitution (Contextual.pair Contextual.identity left)) term payloadMeaning)
    (annotation : Term) :
    Realizes Γ (predicate.substitution (Contextual.pair Contextual.identity right))
      (.transport annotation equation term)
      (fun point => transportedValue predicate point (proofMeaning point) (payloadMeaning point)) := by
  intro values point assigned
  simpa only [Term.transport, Term.subst, substArgs, Op.binders, liftSub, Ty.substitution,
    Contextual.typeSubst, Function.comp_apply, Contextual.pair, Contextual.identity, id_eq] using
    transport_value_realizes predicate point (proofMeaning point) (proof values point assigned)
      (payload values point assigned) (annotation.subst values)

/-- The equality relation determines whether any particular closed pair of
realized words can have a proof. No assumption on the raw proof is needed
once the semantic realization is constructed. -/
theorem unequal_words_unrealizable (point : Γ) {left right : Contextual.Tm (natural env Γ).code}
    (different : (left point).down ≠ (right point).down) :
    ¬ ∃ value,(equality env left right).realizes point term value := by
  rintro ⟨⟨⟨proof⟩⟩,_⟩
  exact different proof

/-- When the actual typed computation exposes Refl, its principal type
determines both endpoint values. The canonical equality realization is then
constructed from the typed reduction and the two original numeric meanings. -/
theorem checked_reflexive_residual_realizes
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans [] mode equation (.eq left right))
    (closed : equation.Scoped 0)
    (steps : LoanTyping.DeltaEvaluation.Steps env equation (.refl witness))
    (first : RawLend.Conv env left (numeralTree m)) (second : RawLend.Conv env right (numeralTree n)) :
    let Γ := empty env
    let proposition := equality env (Contextual.numeral (Γ := Γ.meaning) m) (Contextual.numeral n)
    ∃ meaning : Contextual.Tm proposition.code, Realizes Γ proposition equation meaning := by
  obtain ⟨forward,reflexive⟩ := history.delta_computation_preservation steps typed
  have principal : RawLend.Conv env (.eq witness witness) (.eq left right) := reflexive.principalView
  obtain ⟨leftEndpoint,rightEndpoint⟩ := principal.eq_injective history.wellFormed.admissible
  have agree := numeralTree_injective history.wellFormed.admissible
    ((leftEndpoint.trans first).symm.trans (rightEndpoint.trans second))
  refine ⟨fun _ => ⟨⟨agree⟩⟩,?_⟩
  intro values point assigned
  change RawLend.Conv env (equation.subst values) (.refl (numeralTree m))
  rw [Environment.closed_subst closed values]
  exact forward.toConv.trans (.node .refl (.cons (leftEndpoint.trans first) .nil))

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
