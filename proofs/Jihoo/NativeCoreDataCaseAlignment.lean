import Jihoo.NativeCoreConstructorGraphLink
import Jihoo.NativeCoreDataCaseTelescope
import Jihoo.NativeLoanFamilyIotaParameterInstantiation

/-! The graph reads a data case from the written constructor. Conversion
aligns its instantiated field domains and result indices with the
expanded signature in the checked family table. -/
namespace Jihoo.NativeKernel.NativeCoreDataCaseAlignment

open Environment NativeArena NativeFamilyWire
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta (expand expandArgs)
open LoanTyping.FamilyIota (consume_signature_leading fieldSubstitution_lift_scoped
  transform_fields_parameters dataCaseResult_parameters_congr)
open LoanTyping.FamilyIota (consume)
open FamilyEnvironment (RelList)

theorem parameters_preserve_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (left : ParametersInstantiated ps first A) (right : ParametersInstantiated ps second B)
    (related : RawLend.Conv env first second) : RawLend.Conv env A B := by
  induction left generalizing second B with
  | nil =>
    cases right
    exact related
  | cons next ih =>
    cases right with
    | cons tail =>
      exact ih tail ((related.pi_injective wf.admissible).2.2.substitution _ wf.closed)

theorem expanded_parameters (wf : UnifiedProgram.EnvWellFormed env)
    (opened : ParametersInstantiated ps written result) :
    ParametersInstantiated (expandArgs env ps) (expand env written) (expand env result) := by
  induction opened with
  | nil => simp only [expandArgs]; exact .nil
  | @cons ps result p erased domain rest tail ih =>
    have maps :
        (fun i => expand env (single p i)) = single (expand env p) := by
      funext i
      cases i <;> simp only [single,expand]
    change ParametersInstantiated (expandArgs env ps) (expand env (rest.subst (single p))) (expand env result) at ih
    rw [EnvironmentDelta.expand_substitution wf.admissible _ _,maps] at ih
    simp only [expandArgs,Term.pi,EnvironmentDelta.expand_node_cons]
    exact .cons ih

private theorem consume_eq_instantiate (ps : List Term) (term : Term) :
    consume term ps = instantiateParameters ps term := by
  induction ps generalizing term with
  | nil => rfl
  | cons p ps ih =>
    cases term with
    | var => rfl
    | node op args =>
      cases op <;> try rfl
      case pi erased =>
        rcases args with _ | ⟨domain,_ | ⟨body,_ | ⟨_,_⟩⟩⟩
        all_goals first | rfl | exact ih _

/-- The instantiated signature in the semantic rule has the same opened
parameter telescope that the graph obtains by successive substitutions. -/
theorem checked_opened_telescope (scope : UnifiedProgram.SignatureScoped signature)
    (width : ps.length = params) (bound : params ≤ signature.fields.length) :
    let remaining := signature.fields.drop params
    let fields := instantiatedFields depth ps false 0 remaining
    let indices := signature.result.map (Term.subst (parameterAt depth remaining.length ps))
    ParametersInstantiated ps (signatureTerm family signature)
      (closeDataFields fields (.node (.ind family signature.result.length) indices)) := by
  have instantiated := consume_signature_leading family signature params ps bound width
  rw [consume_eq_instantiate] at instantiated
  rw [show LoanTyping.FamilyIota.fieldSubstitution ps = liftSub 0 (LoanTyping.FamilyIota.fieldSubstitution ps) from rfl,
    closeDataFields_subst] at instantiated
  simp only [Nat.zero_add] at instantiated
  have scopedDomains : ∀ (j : Nat) field,(signature.fields.drop params)[j]? = some field →
      field.domain.Scoped (0+j+ps.length) := by
    intro j field found
    have original := scope.domains (params+j) field (by simpa only [List.getElem?_drop] using found)
    simpa only [Nat.zero_add,width,Nat.add_comm j] using original
  rw [transform_fields_parameters _ ps 0 depth scopedDomains] at instantiated
  have indexSubstitutions :
      signature.result.map (Term.subst (liftSub (signature.fields.length-params) (LoanTyping.FamilyIota.fieldSubstitution ps))) =
      signature.result.map (Term.subst (parameterAt depth (signature.fields.length-params) ps)) := by
    apply List.map_congr_left
    intro value member
    exact fieldSubstitution_lift_scoped (by
      have normalized := scope.result value member
      rwa [show signature.fields.length-params+ps.length = signature.fields.length by omega])
  simp only [List.length_map,List.length_drop,Term.subst,substArgs_dataInd] at instantiated
  rw [indexSubstitutions] at instantiated
  apply instantiateParameters_sound
  simpa only [List.length_drop] using instantiated

private theorem same_fields_and_result (wf : UnifiedProgram.EnvWellFormed env)
    (converted : RawLend.Conv env (closeDataFields first (.node (.ind actual arity) indices))
      (closeDataFields second (.node (.ind expected semanticArity) values))) :
    RelList (fun f g : Bool × Term => f.1 = g.1 ∧ RawLend.Conv env f.2 g.2) first second ∧
      actual = expected ∧ arity = semanticArity ∧ ListRel (RawLend.Conv env) indices values := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => exact ⟨.nil,converted.ind_injective wf.admissible⟩
    | cons head rest =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .ind actual arity) (op' := .pi head.1)
        rfl rfl (by intro equality; cases equality) converted wf.admissible)
  | cons head rest ih =>
    cases second with
    | nil =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .pi head.1) (op' := .ind expected semanticArity)
        rfl rfl (by intro equality; cases equality) converted wf.admissible)
    | cons next remaining =>
      obtain ⟨flag,domain,body⟩ := RawLend.Conv.pi_injective converted wf.admissible
      obtain ⟨fields,ending⟩ := ih body
      exact ⟨.cons ⟨flag,domain⟩ fields,ending⟩

private theorem fields_length (related : RelList R first second) : first.length = second.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem close_related
    (related : RelList (fun f g : Bool × Term => f.1 = g.1 ∧ RawLend.Conv env f.2 g.2) first second)
    (result : RawLend.Conv env A B) :
    RawLend.Conv env (closeDataFields first A) (closeDataFields second B) := by
  induction related with
  | nil => exact result
  | cons head _ ih =>
    simp only [closeDataFields,List.foldr_cons,head.1]
    exact .node (.pi _) (.cons head.2 (.cons ih .nil))

private theorem parameters_refl (ps : List Term) : ListRel (RawLend.Conv env) ps ps := by
  induction ps with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.refl head) ih

theorem nonrecursive_case_matches (wf : UnifiedProgram.EnvWellFormed env)
    (scope : UnifiedProgram.SignatureScoped signature)
    (width : ps.length = params) (bound : params ≤ signature.fields.length)
    (observed : ParametersInstantiated ps written (closeDataFields fields (.node (.ind actual arity) indices)))
    (aligned : RawLend.Conv env written (signatureTerm family signature)) :
    actual = family ∧ arity = signature.result.length ∧
      ∃ expected, dataCaseType family constructor params depth signature ps motive false proof = some expected ∧
        RawLend.Conv env (closeDataFields fields
          (dataCaseResult family constructor params fields.length 0 ps motive indices)) expected := by
  have checked := checked_opened_telescope (family := family) (depth := depth) scope width bound
  obtain ⟨domains,familyEq,arityEq,results⟩ :=
    same_fields_and_result wf (parameters_preserve_conversion wf observed checked aligned)
  let remaining := signature.fields.drop params
  let type := closeDataFields (instantiatedFields depth ps false 0 remaining)
    (dataCaseResult family constructor params remaining.length 0 ps motive
      (signature.result.map (Term.subst (parameterAt depth remaining.length ps))))
  refine ⟨familyEq,arityEq,type,?_,?_⟩
  · simp [dataCaseType,width,Nat.not_lt_of_ge bound,dataHypothesisTelescope,type,remaining]
  · have sameSize := (fields_length domains).trans (instantiatedFields_length depth 0 ps false remaining)
    rw [sameSize]
    exact close_related domains (dataCaseResult_parameters_congr wf.closed (parameters_refl ps) results)

private def expandFields (env : Environment) (fields : List (Bool × Term)) : List (Bool × Term) :=
  fields.map fun field => (field.1,expand env field.2)

private theorem expand_field_telescope (env : Environment) (fields : List (Bool × Term)) (body : Term) :
    expand env (closeDataFields fields body) = closeDataFields (expandFields env fields) (expand env body) := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    simp only [closeDataFields,List.foldr_cons,Term.pi,expandFields,List.map_cons,EnvironmentDelta.expand_node_cons,expandArgs] at ih ⊢
    rw [ih]

private theorem expand_applications (env : Environment) (callee : Term) (arguments : List Term) :
    expand env (applications callee arguments) = applications (expand env callee) (expandArgs env arguments) := by
  induction arguments generalizing callee with
  | nil => simp only [applications,List.foldl_nil,expandArgs]
  | cons argument rest ih =>
    change expand env (applications (.app callee argument) rest) = _
    rw [ih]
    simp only [Term.app,EnvironmentDelta.expand_node_cons,expandArgs,applications,List.foldl_cons]

private theorem expanded_case_result (admissible : EnvironmentDelta.Admissible env) (ps indices : List Term) (motive : Term) :
    expand env (dataCaseResult family constructor params fields 0 ps motive indices) =
      dataCaseResult family constructor params fields 0 (expandArgs env ps) (expand env motive) (expandArgs env indices) := by
  have unchanged (value : Term) : value.rename (fun x => x) = value := Term.rename_id value
  unfold dataCaseResult
  simp only [Nat.add_zero,Term.app,EnvironmentDelta.expand_node_cons,expandArgs]
  rw [expand_applications,EnvironmentDelta.expand_renaming admissible]
  simp only [expand,EnvironmentDelta.expandArgs_map,List.map_drop,List.map_append,List.map_map]
  have shifted : (expand env ∘ Term.rename (fun x => x+fields)) =
      (Term.rename (fun x => x+fields) ∘ expand env) := by
    funext term
    exact EnvironmentDelta.expand_renaming admissible term _
  simp only [shifted,Function.comp_def,expand,unchanged,List.length_append,List.length_map]

/-- Under the declared parameter width, the same mixed history supplies
the graph root and the expected nonrecursive branch of the typing rule. -/
theorem run_matches_checked_case
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (familyRep : RepresentsFamilies state.arena familyRows familyTerms)
    (selectedFamily : familyRows[family]? = some row)
    (selectedConstructor : row.constructors[constructor]? = some written) (data : row.data = true)
    (paramRep : RepresentsList state.arena arguments parameters)
    (motiveRep : Represents state.arena motive M)
    (success : (NativeCoreDataCaseTelescope.run limit depth state family constructor row.params motive written arguments).result = .ok selected) :
    let after := (NativeCoreDataCaseTelescope.run limit depth state family constructor row.params motive written arguments).state.arena
    ∃ entry signature expected observed,
      env.families[family]? = some entry ∧ entry.declaration.data = true ∧
      entry.declaration.params = row.params ∧ entry.signatures[constructor]? = some signature ∧
      dataCaseType family constructor row.params contextDepth signature (expandArgs env parameters)
        (expand env M) false proof = some expected ∧
      Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected observed ∧ RawLend.Conv env (expand env observed) expected := by
  have width : arguments.length = row.params := by
    unfold NativeCoreDataCaseTelescope.run at success
    split at success
    · assumption
    · cases success
  have widthWords : (expandArgs env parameters).length = row.params := by
    simpa only [EnvironmentDelta.expandArgs_map,List.length_map] using
      (NativeCoreIdentical.represented_length paramRep).symm.trans width
  obtain ⟨entry,signature,source,found,signatureFound,_,graph,aligned⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_constructor_root history familyRep selectedFamily selectedConstructor
  obtain ⟨familyEntry,familyFound,familyData,entryParams,_⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_family_layout history familyRep selectedFamily
  have sameEntry := Option.some.inj (familyFound.symm.trans found)
  subst familyEntry
  obtain ⟨scope,_,parametersValid⟩ := LoanTyping.FamilyIota.signature_metadata history found signatureFound
  obtain ⟨kept,backward,fields,resultFamily,arity,indices,opened,openedGraph,openedShape,observedGraph⟩ :=
    NativeCoreDataCaseTelescope.run_refines graph motiveRep paramRep success
  let writtenFields := fields.map fun field => (field.erased,field.domain)
  have fold_as_close (body : Term) : fields.foldr (fun field rest => .pi field.erased field.domain rest) body =
      closeDataFields writtenFields body := by
    simp only [writtenFields,closeDataFields,List.foldr_map]
  rw [fold_as_close] at openedShape observedGraph
  have openedSemantic := instantiateParameters_sound (openedGraph.trans (congrArg some openedShape))
  have expanded := expanded_parameters history.wellFormed openedSemantic
  rw [expand_field_telescope] at expanded
  have expandInd :
      expand env (.node (.ind resultFamily arity) indices) =
        .node (.ind resultFamily arity) (expandArgs env indices) := by
    cases indices <;> simp [expand,expandArgs]
  rw [expandInd] at expanded
  obtain ⟨_,_,expected,expectedType,converted⟩ :=
    nonrecursive_case_matches (depth := contextDepth) (proof := proof) history.wellFormed scope widthWords
      (entryParams ▸ parametersValid.1) expanded aligned
  refine ⟨entry,signature,expected,_,found,familyData.trans data,entryParams,signatureFound,expectedType,kept,backward,observedGraph,?_⟩
  rw [expand_field_telescope,expanded_case_result history.wellFormed.admissible]
  simpa only [expandFields,List.length_map,writtenFields] using converted

end Jihoo.NativeKernel.NativeCoreDataCaseAlignment
