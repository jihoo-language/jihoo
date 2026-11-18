import Jihoo.NativeEnvironmentBindingAlgebra
import Jihoo.NativeLoanHigherKindSubstitution
import Jihoo.NativeLoanMixedAdmission
import Jihoo.NativeLoanProofNormalForms

set_option maxUniverseOffset 40

/-! Executable recognition of the existing higher-kind grammar, followed by
reconstruction from a successful typed source normalization. Native mixed
admission supplies the environment and exact stored annotation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64

open LoanTyping
open NativeKernel.Conversion (treeSize)

private def parseKind : Term → Option Kind
  | .univ level =>
      if valid : level < 33 then some (.base ⟨level, valid⟩) else none
  | .pi false domain codomain => do
      let left ← parseKind domain
      let right ← parseKind codomain
      pure (.arrow left right)
  | _ => none
termination_by term => sizeOf term

private theorem parseKind_sound (parsed : parseKind term = some kind) :
    kind.syntax = term := by
  fun_induction parseKind term generalizing kind with
  | case1 => cases parsed; rfl
  | case2 => contradiction
  | case3 domain codomain domainIH codomainIH =>
    cases first : parseKind domain with
    | none => simp [first] at parsed
    | some left =>
      cases second : parseKind codomain with
      | none => simp [first, second] at parsed
      | some right =>
        have combined : Kind.arrow left right = kind := by simpa [first, second] using parsed
        subst kind
        simp only [Kind.syntax, domainIH first, codomainIH second]
  | case4 => contradiction

private theorem parseKind_syntax (kind : Kind) : parseKind kind.syntax = some kind := by
  induction kind with
  | base level => simp [Kind.syntax, parseKind, level.isLt]
  | arrow domain codomain domainIH codomainIH =>
    simp [Kind.syntax, parseKind, domainIH, codomainIH]

private theorem raise_one : PartialRenaming.raiseIndex 0 1 = Nat.succ := by
  funext index
  simp [PartialRenaming.raiseIndex, Nat.succ_eq_add_one]

/-- The arrow codomain is lowered first, rejecting any use of the removed Pi binder. -/
private def recognizesAt : Nat → Term → Bool
  | 0, _ => false
  | _ + 1, .var _ => true
  | _ + 1, .u64 => true
  | _ + 1, .univ level => decide (level < 32)
  | fuel + 1, .lam false domain body => (parseKind domain).isSome && recognizesAt fuel body
  | fuel + 1, .app function argument => recognizesAt fuel function && recognizesAt fuel argument
  | fuel + 1, .pi false domain codomain =>
      match PartialRenaming.lower 0 1 codomain with
      | some body => recognizesAt fuel domain && recognizesAt fuel body
      | none => false
  | _ + 1, _ => false

private theorem recognizesAt_sound (recognized : recognizesAt fuel term = true) : Recognized term := by
  fun_induction recognizesAt fuel term with
  | case1 => contradiction
  | case2 => exact .var
  | case3 => exact .u64
  | case4 _ level =>
    exact .univ ⟨level, of_decide_eq_true recognized⟩
  | case5 _ domain body bodyIH =>
    obtain ⟨kind, parsed⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp recognized).1
    rw [← parseKind_sound parsed]
    exact .lam kind (bodyIH (Bool.and_eq_true_iff.mp recognized).2)
  | case6 _ function argument functionIH argumentIH =>
    exact .app (functionIH (Bool.and_eq_true_iff.mp recognized).1)
      (argumentIH (Bool.and_eq_true_iff.mp recognized).2)
  | case7 _ domain codomain body lowered domainIH bodyIH =>
    have restored := PartialRenaming.lower_reweakens lowered
    rw [raise_one] at restored
    rw [← restored]
    exact .arrowCode (domainIH (Bool.and_eq_true_iff.mp recognized).1)
      (bodyIH (Bool.and_eq_true_iff.mp recognized).2)
  | case8 => contradiction
  | case9 => contradiction

private theorem treeSize_rename (term : Term) (indices : Nat → Nat) :
    treeSize (term.rename indices) = treeSize term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset indices,
      ((renameArgs op indices offset terms).map treeSize).sum = (terms.map treeSize).sum)
    generalizing indices with
  | var => simp [Term.rename, treeSize]
  | node op terms ih => simp [treeSize, Term.rename, ih]
  | nil => simp [renameArgs]
  | cons term terms headIH tailIH => simp [renameArgs, headIH, tailIH]

private theorem recognizesAt_complete (recognized : Recognized term) :
    ∀ fuel, treeSize term ≤ fuel → recognizesAt fuel term = true := by
  induction recognized with
  | var =>
    intro fuel enough
    cases fuel with
    | zero => simp [treeSize] at enough
    | succ => rfl
  | u64 =>
    intro fuel enough
    cases fuel with
    | zero => simp [Term.u64, treeSize] at enough
    | succ => rfl
  | univ level =>
    intro fuel enough
    cases fuel with
    | zero => simp [Term.univ, treeSize] at enough
    | succ => simp [recognizesAt, level.isLt]
  | @lam body domain _ bodyIH =>
    intro fuel enough
    simp only [Term.lam, treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at enough
    cases fuel with
    | zero => omega
    | succ fuel => simp [recognizesAt, parseKind_syntax, bodyIH fuel (by omega)]
  | @app function argument _ _ functionIH argumentIH =>
    intro fuel enough
    simp only [Term.app, treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at enough
    cases fuel with
    | zero => omega
    | succ fuel => simp [recognizesAt, functionIH fuel (by omega), argumentIH fuel (by omega)]
  | @arrowCode domain codomain _ _ domainIH codomainIH =>
    intro fuel enough
    simp only [Term.pi, treeSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      treeSize_rename] at enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      have lowered := lower_raised codomain 1
      rw [show (fun x : Nat => x + 1) = Nat.succ by rfl] at lowered
      simp [recognizesAt, lowered, domainIH fuel (by omega), codomainIH fuel (by omega)]

/-- Decide precisely the source-reconstruction grammar, using a sufficient
depth bound computed from the input syntax. -/
def recognizes (term : Term) : Bool := recognizesAt (treeSize term) term

theorem recognizes_iff (term : Term) : recognizes term = true ↔ Recognized term :=
  ⟨recognizesAt_sound, fun recognized => recognizesAt_complete recognized _ (Nat.le_refl _)⟩

private theorem member_index_bound (member : Member kind source index) : index < source.length := by
  induction member with
  | here => simp
  | there previous ih => exact Nat.succ_lt_succ ih

/-- Check the original source and every replacement used by the source
context. A successful check supplies the coverage for typed substitution. -/
def recognizesSubstitution (source : List Kind) (term : Term) (values : Nat → Term) : Bool :=
  recognizes term && (List.range source.length).all (fun index => recognizes (values index))

theorem checked_substitution_observation
    (history : MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans (context source) mode term type)
    (substitution : LoanTyping.Ghost.Substitution env (context source) (context target) values)
    (observed : recognizesSubstitution source term values = true) :
    ∃ kind, ∃ original : Expression source kind, ∃ result : Expression target kind,
      ∃ replacement : IntrinsicSubstitution source target,
        original.syntax = term ∧ LoanTyping.Conversion.Conv env kind.syntax type ∧
        LoanTyping.HasType env [] (context target) true (term.subst values) (type.subst values) ∧
        LoanTyping.Conversion.Conv env kind.syntax (type.subst values) ∧
        replacement.Matches values ∧ result.syntax = term.subst values ∧
        ∀ assignment : Values target, result.meaning assignment = original.meaning (replacement.values assignment) := by
  obtain ⟨termChecked, replacementsChecked⟩ := Bool.and_eq_true_iff.mp observed
  apply checked_substitution_coherence history typed ((recognizes_iff term).mp termChecked) substitution
  intro kind index member
  exact (recognizes_iff (values index)).mp
    (List.all_eq_true.mp replacementsChecked index (List.mem_range.mpr (member_index_bound member)))

def observeKind? (env : Environment) (budget normalizationFuel : Nat)
    (input : Term) : Option Term := do
  let residual ← ProofNormalization.normalize? env budget normalizationFuel input
  if recognizes residual then some residual else none

private theorem observeKind?_result
    (observed : observeKind? env budget normalizationFuel input = some residual) :
    ProofNormalization.normalize? env budget normalizationFuel input = some residual ∧
      recognizes residual = true := by
  unfold observeKind? at observed
  cases normalized : ProofNormalization.normalize? env budget normalizationFuel input with
  | none => simp [normalized] at observed
  | some output =>
    simp only [normalized, Bind.bind, Option.bind] at observed
    split at observed
    · rename_i recognized
      cases observed
      exact ⟨rfl, recognized⟩
    · contradiction

theorem observeKind?_sound
    (history : MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans ctx mode input type)
    (observed : observeKind? env budget normalizationFuel input = some residual) :
    LoanTyping.HasType env [] ctx true residual type ∧
      ProofNormalization.Normal env residual ∧ Recognized residual := by
  obtain ⟨normalized, recognized⟩ := observeKind?_result observed
  exact ⟨ProofNormalization.normalize?_preserves history typed normalized,
    ProofNormalization.normalize?_normal normalized, (recognizes_iff residual).mp recognized⟩

/-- The reconstructed expression provides a concrete semantic value in any
intrinsic valuation. Its kind converts to the original Loan64 annotation. -/
theorem checked_kind_observation
    (history : MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans (context kinds) mode input type)
    (observed : observeKind? env budget normalizationFuel input = some residual) :
    LoanTyping.HasType env [] (context kinds) true residual type ∧ ProofNormalization.Normal env residual ∧
      ∃ kind, ∃ expression : Expression kinds kind, expression.syntax = residual ∧
        LoanTyping.Conversion.Conv env kind.syntax type ∧
        ∀ _values : Values kinds, Nonempty (Finite.Carrier kind.code) := by
  obtain ⟨preserved, normal, recognized⟩ := observeKind?_sound history typed observed
  exact ⟨preserved, normal, checked_fundamental history preserved recognized⟩

theorem checked_code_observation
    (history : MixedProgram.History definitions familyDeclarations env) (level : Fin 33)
    (typed : LoanTyping.HasType env loans (context kinds) mode input (.univ level.val))
    (observed : observeKind? env budget normalizationFuel input = some residual) :
    LoanTyping.HasType env [] (context kinds) true residual (.univ level.val) ∧
      ProofNormalization.Normal env residual ∧
      ∃ expression : Expression kinds (.base level), expression.syntax = residual ∧
        ∀ values : Values kinds, ∃ code : Finite.Universe (.type ⟨level.val, by omega⟩),
          code = Finite.AdministrativeValues.decode level (expression.meaning values) := by
  obtain ⟨preserved, normal, recognized⟩ := observeKind?_sound history typed observed
  exact ⟨preserved, normal, checked_code_fundamental history level preserved recognized⟩

theorem checked_global_observation
    (history : MixedProgram.History definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration)
    (observed : observeKind? env budget normalizationFuel
      (.node (.global index) []) = some residual) :
    LoanTyping.HasType env [] [] true residual declaration.type ∧ ProofNormalization.Normal env residual ∧
      ∃ kind, ∃ expression : Expression [] kind, expression.syntax = residual ∧
        LoanTyping.Conversion.Conv env kind.syntax declaration.type ∧ Nonempty (Finite.Carrier kind.code) := by
  have typed : LoanTyping.HasType env [] [] true (.node (.global index) []) (declaration.type.rename id) :=
    .global found
  rw [Term.rename_id] at typed
  obtain ⟨preserved, normal, kind, expression, exactSyntax, converted, values⟩ :=
    checked_kind_observation (kinds := []) history typed observed
  exact ⟨preserved, normal, kind, expression, exactSyntax, converted, values .nil⟩

/-- Observe a stored global directly from native version-6 bytes. The
result records its checked annotation and the observed source residual. -/
def observeNativeGlobal? (typingFuel quantityFuel budget normalizationFuel index : Nat)
    (bytes : ByteArray) : Option (Term × Term) := do
  let snapshot ← NativeFamilyWire.decodeSnapshot bytes
  let (definitions, families) ← NativeFamilyWire.decodeProgram snapshot
  let env ← MixedProgram.checkProgram typingFuel quantityFuel definitions
    (families.map NativeLoanMixedAdmission.declaration)
  let declaration ← env.globals[index]?
  let residual ← observeKind? env budget normalizationFuel (.node (.global index) [])
  pure (declaration.type, residual)

/-- A single successful observation establishes actual native admission,
typed normalization at the original annotation, and a concrete finite
denotation reconstructed from the executable residual grammar. -/
theorem observeNativeGlobal?_sound
    (observed : observeNativeGlobal? typingFuel quantityFuel budget normalizationFuel
      index bytes = some (type, residual)) :
    NativeLoanMixedAdmission.checkBytes typingFuel quantityFuel bytes = true ∧
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List GlobalDeclaration)
      (families : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      NativeFamilyWire.decodeProgram snapshot = some (definitions, families) ∧
      MixedProgram.History definitions (families.map NativeLoanMixedAdmission.declaration) env ∧
      (∃ declaration, env.globals[index]? = some declaration ∧ declaration.type = type) ∧
      DeltaEvaluation.Steps env (.node (.global index) []) residual ∧
      LoanTyping.HasType env [] [] true residual type ∧ ProofNormalization.Normal env residual ∧
      ∃ kind, ∃ expression : Expression [] kind, expression.syntax = residual ∧
        LoanTyping.Conversion.Conv env kind.syntax type ∧ Nonempty (Finite.Carrier kind.code) := by
  unfold observeNativeGlobal? at observed
  cases decoded : NativeFamilyWire.decodeSnapshot bytes with
  | none => simp [decoded] at observed
  | some snapshot =>
    cases source : NativeFamilyWire.decodeProgram snapshot with
    | none => simp [decoded, source] at observed
    | some program =>
      obtain ⟨definitions, families⟩ := program
      cases checked : MixedProgram.checkProgram typingFuel quantityFuel definitions
          (families.map NativeLoanMixedAdmission.declaration) with
      | none => simp [decoded, source, checked] at observed
      | some env =>
        cases found : env.globals[index]? with
        | none => simp [decoded, source, checked, found] at observed
        | some declaration =>
          cases normalized : observeKind? env budget normalizationFuel
              (.node (.global index) []) with
          | none => simp [decoded, source, checked, found, normalized] at observed
          | some output =>
            have pair : (declaration.type, output) = (type, residual) := by
              simpa only [decoded, source, checked, found, normalized, Bind.bind, Option.bind,
                Pure.pure, Option.some.injEq] using observed
            cases pair
            have accepted : NativeLoanMixedAdmission.checkBytes typingFuel quantityFuel bytes = true := by
              simp [NativeLoanMixedAdmission.checkBytes, NativeLoanMixedAdmission.checkSnapshot,
                decoded, source, checked]
            have history := MixedProgram.checkProgram_sound checked
            exact ⟨accepted, snapshot, definitions, families, env,
              NativeFamilyWire.decodeSnapshot_exact decoded, source, history, ⟨declaration, found, rfl⟩,
              ProofNormalization.normalize?_steps (observeKind?_result normalized).1,
              checked_global_observation history found normalized⟩

private def identityCode : Term := .lam false (.univ 0) (.var 0)

private def identityKind : Term := .pi false (.univ 0) (.univ 0)

private def storedAnnotation : Term := .ifEq (.natural 0) (.natural 1) identityKind identityKind

private def storedValue : Term := .ifEq (.natural 0) (.natural 1) identityCode identityCode

private def identityDeclaration : GlobalDeclaration := ⟨storedAnnotation, storedValue⟩

private def identityEnvironment : Environment := ⟨#[identityDeclaration], #[]⟩

private def identitySnapshot : NativeFamilyWire.Snapshot :=
  let (typeArena, typeRef) := NativeArena.emit storedAnnotation #[]
  let (valueArena, valueRef) := NativeArena.emit storedValue typeArena
  ⟨[⟨typeRef, valueRef⟩], [], valueArena⟩

/-- Version-6 admission and reduction expose the identity code even with
computations in both its original body and its exact stored annotation. -/
theorem observes_computed_native_kind :
    observeNativeGlobal? 32 32 8192 16 0 (NativeFamilyWire.encodeSnapshot identitySnapshot) =
      some (storedAnnotation, identityCode) := by
  have source : NativeFamilyWire.decodeProgram identitySnapshot = some ([identityDeclaration], []) := by cbv
  have checked : MixedProgram.checkProgram 32 32 [identityDeclaration] [] = some identityEnvironment := by cbv
  have normalized : observeKind? identityEnvironment 8192 16 (.node (.global 0) []) =
      some identityCode := by cbv
  have found : identityEnvironment.globals[0]? = some identityDeclaration := rfl
  simp only [observeNativeGlobal?, NativeFamilyWire.decodeSnapshot_encode, source, List.map_nil, checked,
    found, normalized, Bind.bind, Option.bind]
  rfl

example : recognizes (.pi false .u64 (.var 0)) = false := by cbv

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64
