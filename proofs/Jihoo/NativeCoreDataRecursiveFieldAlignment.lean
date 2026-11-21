import Jihoo.NativeCorePropSignatureAuthentication
import Jihoo.NativeCoreDataRecursionCase
import Jihoo.NativeCoreDataCaseAlignment
import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanFamilyIotaElimHypotheses

/-! The written telescope contains the same recursive markers as the
checked signature. Substitution of word parameters preserves each marker
and applies the ordinary scoped substitution to its indices. -/
namespace Jihoo.NativeKernel.NativeCoreDataRecursiveFieldAlignment

open Environment UnifiedProgram
open FamilyEnvironment (RelList)
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta (expand expandArgs)
open NativeCorePropSignatureAuthentication (ObservedField ObservedTelescope)

def recursiveIndices (family : Nat) : Term → Option (List Term)
  | .node (.ind selected _) indices => if selected = family then some indices else none
  | _ => none

def FieldMarkers (family : Nat) (fields : List Field) : Prop :=
  ∀ field ∈ fields, field.recursive = recursiveIndices family field.domain

private theorem ordinary_marker (absent : Families.selfFree family term = true) :
    recursiveIndices family term = none := by
  cases term with
  | var => rfl
  | node op args =>
    cases op <;> try rfl
    case ind found count =>
      by_cases same : found = family
      · subst found
        simp [Families.selfFree] at absent
      · simp [recursiveIndices,same]

private theorem reflexive_indices (terms : List Term) : ListRel (RawLend.Conv env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons head _ ih => exact .cons (.refl head) ih

/-- The raw graph supplies the written field terms and the declaration's
original recursive positions, before any normalization. -/
theorem observed_written_field (checked : Families.FieldChecked prior family declaration ctx erased domain field) :
    ObservedField env family erased domain ⟨erased,domain,recursiveIndices family domain⟩ := by
  cases checked with
  | ordinary absent _ _ _ _ _ =>
    rw [ordinary_marker absent]
    exact .ordinary absent (.refl _)
  | recursive _ _ _ _ _ =>
    simp only [recursiveIndices,ite_true]
    exact .recursive (.refl _) (reflexive_indices _)

private theorem indices_scope (checked : Families.IndicesChecked prior family ctx written normal) :
    ∀ index ∈ written, index.Scoped ctx.length := by
  intro index member
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨_,_,expanded⟩ := checked.left found
  obtain ⟨_,_,source,typed,_,_⟩ := expanded
  exact FamilyEnvironment.expansion_scoped_source source _ typed.term_scoped

private theorem written_field_scope (checked : Families.FieldChecked prior family declaration ctx erased domain field) :
    domain.Scoped ctx.length ∧
      ∀ indices, recursiveIndices family domain = some indices → ∀ index ∈ indices, index.Scoped ctx.length := by
  cases checked with
  | ordinary free expanded binder _ _ _ =>
    cases binder with
    | intro typed _ =>
      refine ⟨FamilyEnvironment.expansion_scoped_source expanded _ typed.term_scoped,?_⟩
      intro indices order
      rw [ordinary_marker free] at order
      cases order
  | recursive _ _ checked _ _ =>
    refine ⟨.node ?_,?_⟩
    · intro index term found
      exact indices_scope checked term (List.mem_of_getElem? found)
    · intro indices found
      simp only [recursiveIndices,ite_true,Option.some.injEq] at found
      subst indices
      exact indices_scope checked

theorem observed_written_telescope
    (checked : Families.TelescopeChecked prior family declaration checkedPrefix written signature)
    (markers : FieldMarkers family rawPrefix) (scope : Families.FieldsScoped rawPrefix)
    (width : rawPrefix.length = checkedPrefix.length) :
    ∃ raw, ObservedTelescope env family rawPrefix written raw ∧ FieldMarkers family raw.fields ∧
      SignatureScoped raw ∧
      signatureTerm family raw = rawPrefix.foldr (fun field rest => .pi field.erased field.domain rest) written := by
  induction checked generalizing rawPrefix with
  | @field checkedPrefix erased domain field rest signature first remaining ih =>
    let source : Field := ⟨erased,domain,recursiveIndices family domain⟩
    have more : FieldMarkers family (rawPrefix ++ [source]) := by
      intro selected member
      rcases List.mem_append.mp member with earlier | last
      · exact markers selected earlier
      · cases List.mem_singleton.mp last
        rfl
    obtain ⟨domainScope,markerScope⟩ := written_field_scope first
    rw [FamilyEnvironment.fieldContext_length,←width] at domainScope markerScope
    have nextScope : Families.FieldsScoped (rawPrefix ++ [source]) := scope.append domainScope markerScope
    have nextWidth : (rawPrefix ++ [source]).length = (checkedPrefix ++ [field]).length := by simp [width]
    obtain ⟨raw,replayed,marked,sourceScope,writtenEq⟩ := ih more nextScope nextWidth
    refine ⟨raw,.field (observed_written_field first) replayed,marked,sourceScope,?_⟩
    simpa only [List.foldr_append,List.foldr_cons,List.foldr_nil,source] using writtenEq
  | result count arity typed params =>
    refine ⟨⟨rawPrefix,_⟩,.result (reflexive_indices _),markers,?_,?_⟩
    · refine ⟨fun j field found => (scope j field found).1,
        fun j field indices found selected => (scope j field found).2 indices selected,?_⟩
      intro index member
      simpa only [FamilyEnvironment.fieldContext_length,←width] using indices_scope typed index member
    · simp only [signatureTerm,count,arity]

theorem written_signature_conversion
    (extension : prior.Extends env) (checked : Families.TelescopeChecked prior family declaration [] written signature) :
    ∃ raw, signatureTerm family raw = written ∧ FieldMarkers family raw.fields ∧ SignatureScoped raw ∧
      SignatureConversion env (expandSignature env raw) signature := by
  obtain ⟨raw,replayed,markers,scope,spelling⟩ :=
    observed_written_telescope (rawPrefix := []) checked (by intro field absent; cases absent) .empty rfl
  exact ⟨raw,spelling,markers,scope,NativeCorePropSignatureAuthentication.checked_telescope extension replayed checked .nil⟩

/-- A value admitted at U64 cannot have a family type expression at its
raw head. Expansion preserves an existing Ind head. -/
theorem word_parameter_has_no_family_head (wf : EnvWellFormed env)
    (typed : LoanTyping.HasType env [] ctx true (expand env parameter) .u64) :
    recursiveIndices family parameter = none := by
  cases parameter with
  | var => rfl
  | node op args =>
    cases op <;> try rfl
    case ind found arity =>
      simp only [expand] at typed
      obtain ⟨entry,_,principal⟩ := typed.principalView
      cases data : entry.declaration.data <;> rw [data] at principal
      · exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .prop) (op' := .u64)
          rfl rfl (by intro same; cases same) principal wf.admissible)
      · exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .universe 0) (op' := .u64)
          rfl rfl (by intro same; cases same) principal wf.admissible)

private theorem rename_keeps_nonfamily (absent : recursiveIndices family term = none) (ρ : Nat → Nat) :
    recursiveIndices family (term.rename ρ) = none := by
  cases term with
  | var => simp only [Term.rename,recursiveIndices]
  | node op args =>
    cases op <;> simp only [Term.rename,recursiveIndices] at absent ⊢
    case ind actual arity =>
      by_cases same : actual = family
      · simp only [same,ite_true] at absent
        cases absent
      · simp only [same,ite_false]

theorem parameter_replacement_has_no_family_head {arguments : List Term}
    (word : ∀ parameter ∈ arguments, recursiveIndices family parameter = none) (depth position index : Nat) :
    recursiveIndices family (parameterAt depth position arguments index) = none := by
  unfold parameterAt
  split
  · rfl
  · cases found : arguments.reverse[index-position]? with
    | none => rfl
    | some term =>
      simp only [Option.map_some,Option.getD_some]
      exact rename_keeps_nonfamily (word term (List.mem_reverse.mp (List.mem_of_getElem? found))) _

theorem substitution_keeps_marker
    (noFamily : ∀ index, recursiveIndices family (values index) = none) (source : Term) :
    recursiveIndices family (source.subst values) =
      (recursiveIndices family source).map (List.map (Term.subst values)) := by
  cases source with
  | var index => simpa only [Term.subst,recursiveIndices,Option.map_none] using noFamily index
  | node op args =>
    cases op <;> simp only [Term.subst,recursiveIndices,Option.map_none]
    case ind actual arity =>
      rw [substArgs_dataInd]
      split <;> rfl

private theorem mark_shape (family : Nat) (field : Field) :
    NativeCoreDataRecursionCase.markRecursive family field =
      ⟨if (recursiveIndices family field.domain).isSome then true else field.erased,
        field.domain,recursiveIndices family field.domain⟩ := by
  obtain ⟨erased,domain,old⟩ := field
  cases domain with
  | var => rfl
  | node op args =>
    cases op <;> try rfl
    case ind actual arity =>
      by_cases same : actual = family <;> simp [NativeCoreDataRecursionCase.markRecursive,recursiveIndices,same]

private def markOpened (family : Nat) (fields : List (Bool × Term)) : List Field :=
  fields.map (fun field => NativeCoreDataRecursionCase.markRecursive family ⟨field.1,field.2,none⟩)

private theorem marker_present (values : Option (List Term)) (rename : Term → Term) :
    (values.map (List.map rename)).isSome = values.isSome := by cases values <;> rfl

private theorem marked_domains (marked : FieldMarkers family fields)
    (parameters : ∀ argument ∈ values, recursiveIndices family argument = none) (position : Nat) :
    (markOpened family (instantiatedFields depth values false position fields)).map
      (fun field => (field.erased,field.domain)) = instantiatedFields depth values true position fields := by
  induction fields generalizing position with
  | nil => rfl
  | cons first rest ih =>
    have marker := marked first (.head _)
    have remaining : FieldMarkers family rest := fun field member => marked field (.tail _ member)
    simp only [instantiatedFields,markOpened,List.map_cons,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,mark_shape]
    rw [substitution_keeps_marker (parameter_replacement_has_no_family_head parameters depth position),
      marker_present,←marker]
    have tail := ih remaining (position+1)
    simp only [markOpened,mark_shape] at tail
    exact congrArg (List.cons _) tail

private theorem instantiated_field_markers (marked : FieldMarkers family fields)
    (parameters : ∀ argument ∈ values, recursiveIndices family argument = none) (position : Nat) :
    ((markOpened family (instantiatedFields depth values false position fields)).zipIdx position).filterMap
        (fun (field,j) => field.recursive.map fun indices => (j,indices)) =
      ((fields.zipIdx position).filterMap (fun (field,j) => field.recursive.map fun indices => (j,indices))).map
        (fun (j,indices) => (j,indices.map (Term.subst (parameterAt depth j values)))) := by
  induction fields generalizing position with
  | nil => rfl
  | cons first rest ih =>
    have marker := marked first (.head _)
    have remaining : FieldMarkers family rest := fun field member => marked field (.tail _ member)
    simp only [instantiatedFields,markOpened,List.map_cons,Bool.false_and,Bool.false_eq_true,ite_false,mark_shape,List.zipIdx_cons,List.filterMap_cons]
    rw [substitution_keeps_marker (parameter_replacement_has_no_family_head parameters depth position),←marker]
    have tail := ih remaining (position+1)
    simp only [markOpened,mark_shape] at tail
    cases first.recursive with
    | none => simpa only [Option.map_none] using tail
    | some indices => simpa only [Option.map_some,List.map_cons] using congrArg (List.cons _) tail

private theorem opened_recursive_positions (marked : FieldMarkers family fields)
    (parameters : ∀ argument ∈ values, recursiveIndices family argument = none) :
    recursiveFields (markOpened family (instantiatedFields depth values false 0 fields)) =
      instantiatedRecursive depth values fields :=
  instantiated_field_markers marked parameters 0

private theorem closeFields_shape
    (same : closeDataFields left (.node (.ind lf la) lis) = closeDataFields right (.node (.ind rf ra) ris)) :
    left = right ∧ lf = rf ∧ la = ra ∧ lis = ris := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil =>
      cases same
      exact ⟨rfl,rfl,rfl,rfl⟩
    | cons first rest =>
      obtain ⟨erased,domain⟩ := first
      cases same
  | cons first rest ih =>
    cases right with
    | nil =>
      obtain ⟨erased,domain⟩ := first
      cases same
    | cons second remaining =>
      obtain ⟨firstFlag,firstDom⟩ := first
      obtain ⟨secondFlag,secondDom⟩ := second
      change Term.pi firstFlag firstDom (closeDataFields rest _) =
        Term.pi secondFlag secondDom (closeDataFields remaining _) at same
      have shape : firstFlag = secondFlag ∧ firstDom = secondDom ∧
          closeDataFields rest (.node (.ind lf la) lis) = closeDataFields remaining (.node (.ind rf ra) ris) := by
        injection same with head children
        have flags := Op.pi.inj head
        injection children with domain tail
        exact ⟨flags,domain,List.cons.inj tail |>.1⟩
      obtain ⟨flag,dom,tail⟩ := shape
      obtain ⟨sameTail,family,arity,indices⟩ := ih tail
      exact ⟨by rw [flag,dom,sameTail],family,arity,indices⟩

private theorem instantiated_exact (opened : ParametersInstantiated parameters written term) :
    instantiateParameters parameters written = some term := by
  induction opened with
  | nil => rfl
  | cons _ ih => exact ih


open NativeArena
open NativeCoreTransformExact (State)

/-- With source marker metadata and word parameters, the selected graph
type is exactly the semantic recursive case of the written constructor. -/
theorem run_matches_source_case
    (source : Represents state.arena constructorRef (signatureTerm family raw))
    (scope : SignatureScoped raw) (marked : FieldMarkers family raw.fields)
    (parameters : RepresentsList state.arena argumentRefs arguments)
    (width : arguments.length = params) (bound : params ≤ raw.fields.length)
    (noFamily : ∀ argument ∈ arguments, recursiveIndices family argument = none)
    (motiveRep : Represents state.arena motiveRef motive) (back : Backward state.arena)
    (success : (NativeCoreDataRecursionCase.run limit depth state family constructor params motiveRef constructorRef argumentRefs proof).result =
      .ok output) :
    let after := (NativeCoreDataRecursionCase.run limit depth state family constructor params motiveRef constructorRef argumentRefs proof).state.arena
    Prefix state.arena after ∧ Backward after ∧
      ∃ branch, dataCaseType family constructor params contextDepth raw arguments motive true proof = some branch ∧
        Represents after output branch := by
  obtain ⟨kept,safe,fields,resultFamily,arity,indices,opened,instantiated,shape,graph⟩ :=
    NativeCoreDataRecursionCase.run_refines back motiveRep source parameters success
  let suffix := raw.fields.drop params
  have form := instantiated_exact (NativeCoreDataCaseAlignment.checked_opened_telescope
    (family := family) (depth := contextDepth) scope width bound)
  have openedEq := Option.some.inj (instantiated.symm.trans form)
  rw [openedEq] at shape
  have shape :
      closeDataFields (instantiatedFields contextDepth arguments false 0 suffix)
        (.node (.ind family raw.result.length)
          (raw.result.map (Term.subst (parameterAt contextDepth suffix.length arguments)))) =
      closeDataFields (fields.map (fun field => (field.erased,field.domain))) (.node (.ind resultFamily arity) indices) := by
    simpa only [closeDataFields,List.foldr_map,suffix] using shape
  obtain ⟨fieldsEq,_,_,indicesEq⟩ := closeFields_shape shape
  have suffixMarkers : FieldMarkers family suffix :=
    fun field member => marked field (List.mem_of_mem_drop member)
  have markedEq : fields.map (NativeCoreDataRecursionCase.markRecursive family) =
      markOpened family (instantiatedFields contextDepth arguments false 0 suffix) := by
    rw [fieldsEq,markOpened,List.map_map]
    apply List.map_congr_left
    intro field _
    simp only [Function.comp_def,mark_shape]
  have lengthEq : fields.length = suffix.length := by
    have same := congrArg List.length fieldsEq
    rw [instantiatedFields_length,List.length_map] at same
    exact same.symm
  have positions := opened_recursive_positions (depth := contextDepth) suffixMarkers noFamily
  have domains := marked_domains (depth := contextDepth) suffixMarkers noFamily 0
  let recursive := instantiatedRecursive contextDepth arguments suffix
  have unfoldType : dataCaseType family constructor params contextDepth raw arguments motive true proof =
      some (closeDataFields (instantiatedFields contextDepth arguments true 0 suffix)
        (dataHypothesisTelescope params suffix.length 0 recursive proof motive
          (dataCaseResult family constructor params suffix.length recursive.length arguments motive
            (raw.result.map (Term.subst (parameterAt contextDepth suffix.length arguments)))))) := by
    simp [dataCaseType,width,Nat.not_lt_of_ge bound,recursive,suffix]
  refine ⟨kept,safe,_,unfoldType,?_⟩
  change Represents _ output ((fields.map (NativeCoreDataRecursionCase.markRecursive family)).foldr
    (fun field body => .pi field.erased field.domain body)
      (dataHypothesisTelescope params fields.length 0 (recursiveFields (fields.map (NativeCoreDataRecursionCase.markRecursive family)))
        proof motive ((dataCaseResult family constructor params fields.length 0 arguments motive indices).rename
          (fun i => i + (recursiveFields (fields.map (NativeCoreDataRecursionCase.markRecursive family))).length)))) at graph
  have fold_case (fields : List Field) (body : Term) :
      fields.foldr (fun field rest => .pi field.erased field.domain rest) body =
        closeDataFields (fields.map (fun field => (field.erased,field.domain))) body := by
    simp only [closeDataFields,List.foldr_map]
  rw [fold_case,markedEq,domains,positions,lengthEq,←indicesEq,←LoanTyping.FamilyIota.dataCaseResult_hypotheses_shift] at graph
  exact graph

end Jihoo.NativeKernel.NativeCoreDataRecursiveFieldAlignment
