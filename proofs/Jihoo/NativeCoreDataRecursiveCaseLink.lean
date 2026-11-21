import Jihoo.NativeCoreDataRecursiveFieldAlignment
import Jihoo.NativeCoreDataSignatureConversion

namespace Jihoo.NativeKernel.NativeCoreDataRecursiveFieldAlignment

open Environment NativeArena NativeFamilyWire
open EnvironmentDelta (expand expandArgs)

open NativeCoreDataCaseAlignment (expand_data_case_type)
open NativeCoreTransformExact (State)


/-- For formed word parameters, the recursive graph type converts to the
case expected from the actual checked constructor's normalized signature. -/
theorem run_matches_checked_case
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (familyRep : RepresentsFamilies state.arena familyRows familyTerms)
    (selectedFamily : familyRows[family]? = some row)
    (selectedConstructor : row.constructors[constructor]? = some written) (data : row.data = true)
    (paramRep : RepresentsList state.arena argumentRefs parameters)
    (paramTyped : ∀ value ∈ parameters, LoanTyping.HasType env [] ctx true (expand env value) .u64)
    (motiveRep : Represents state.arena motiveRef motive)
    (success : (NativeCoreDataRecursionCase.run limit depth state family constructor row.params motiveRef written argumentRefs proof).result =
      .ok selected) :
    let after := (NativeCoreDataRecursionCase.run limit depth state family constructor row.params motiveRef written argumentRefs proof).state.arena
    ∃ entry signature expected observed,
      env.families[family]? = some entry ∧ entry.declaration.data = true ∧
      entry.declaration.params = row.params ∧ entry.signatures[constructor]? = some signature ∧
      dataCaseType family constructor row.params ctx.length signature (expandArgs env parameters) (expand env motive) true proof = some expected ∧
      Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected observed ∧ RawLend.Conv env (expand env observed) expected := by
  have width : argumentRefs.length = row.params := by
    unfold NativeCoreDataRecursionCase.run at success
    obtain ⟨_,opened,_⟩ := NativeCorePureComputationNormal.Outcome.next_success success
    unfold NativeCoreDataCaseTelescope.run at opened
    split at opened
    · assumption
    · cases opened
  have parameterWidth := (NativeCoreIdentical.represented_length paramRep).symm.trans width
  obtain ⟨entry,signature,source,prior,declaration,found,signatureFound,_,kind,sourceRep,extension,telescope⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_constructor_source history familyRep selectedFamily selectedConstructor
  obtain ⟨entry',found',_,alignedParams,_⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_family_layout history familyRep selectedFamily
  have sameEntry := Option.some.inj (found'.symm.trans found)
  subst entry'
  obtain ⟨raw,writtenEq,markers,scope,converted⟩ := written_signature_conversion extension telescope
  have rawRep : Represents state.arena written (signatureTerm family raw) := by rw [writtenEq]; exact sourceRep
  obtain ⟨_,_,parametersValid⟩ := LoanTyping.FamilyIota.signature_metadata history found signatureFound
  have rawWidth : raw.fields.length = signature.fields.length := by
    simpa only [expandSignature,List.length_map] using converted.fields.length
  have bound : row.params ≤ raw.fields.length := by
    rw [←alignedParams,rawWidth]
    exact parametersValid.1
  have noFamily : ∀ value ∈ parameters, recursiveIndices family value = none :=
    fun value member => word_parameter_has_no_family_head history.wellFormed (paramTyped value member)
  obtain ⟨kept,safe,observed,expected,holds⟩ := run_matches_source_case (contextDepth := ctx.length)
    rawRep scope markers paramRep parameterWidth bound noFamily motiveRep success
  have expanded := expand_data_case_type (family := family) (constructor := constructor)
    (params := row.params) (depth := ctx.length) (recursion := true) (proof := proof)
    history.wellFormed.admissible raw parameters motive
  rw [expected,Option.map_some] at expanded
  obtain ⟨checked,accepts,related⟩ := converted.data_case history.wellFormed.closed expanded.symm
  exact ⟨entry,signature,checked,observed,found,kind.trans data,alignedParams,signatureFound,accepts,kept,safe,holds,related⟩

end Jihoo.NativeKernel.NativeCoreDataRecursiveFieldAlignment
