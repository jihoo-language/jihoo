import Jihoo.NativeCoreGhostViewInference
import Jihoo.NativeCoreViewCheckedPlan
import Jihoo.NativeCoreViewCaseExpansion
import Jihoo.NativeCoreViewCaseType
import Jihoo.NativeCoreDataCaseAlignment

/-! The live read of a borrowed field rewrites exactly the part of the
opened telescope under its binder. Constructor conversion therefore
commutes with the dependent field types in a checked View plan. -/
namespace Jihoo.NativeKernel.NativeCoreViewFieldAlignment

open NativeArena Environment FamilyEnvironment
open NativeCoreViewCaseType (FieldRoot FieldLayout)
open EnvironmentDelta (expand expandArgs)

private theorem expand_reading (admissible : EnvironmentDelta.Admissible env) (term : Term) :
    expand env (reading term) = reading (expand env term) := by
  unfold reading
  rw [EnvironmentDelta.expand_substitution admissible]
  congr 1
  funext index
  cases index <;> simp only [Term.deref,EnvironmentDelta.expand_node_cons,expandArgs,expand]

private theorem reading_conversion (wf : UnifiedProgram.EnvWellFormed env) (converted : RawLend.Conv env A B) :
    RawLend.Conv env (reading A) (reading B) := by
  exact converted.substitution _ wf.closed

private def fieldFlags (field : FieldRoot) : Bool × Bool := (field.borrowed,field.recursive)
private def planFlags (field : ViewFieldPlan) : Bool × Bool := (field.borrowed,field.self)

private def ClosedFields (depth : Nat) (ps : List Term) (position : Nat) (plans : List ViewFieldPlan) (ending : Term) : Term :=
  closeDataFields (instantiatedFields depth ps false position (plans.map ViewFieldPlan.field)) ending

/-- The output field telescope has the same erasure bits and converted
domains as the specified View telescope, under a common recorded plan.
The comparison recurses through the actual retained Deref substitutions. -/
theorem FieldLayout.matches_fields (wf : UnifiedProgram.EnvWellFormed env)
    (layout : FieldLayout env family arena term roots fields)
    (shapes : roots.map fieldFlags = plans.map planFlags)
    (related : RawLend.Conv env (expand env term) (viewRead prior (ClosedFields depth ps prior.length plans ending))) :
    RelList (fun observed expected : Bool × Term => observed.1 = expected.1 ∧ RawLend.Conv env observed.2 expected.2)
      (fields.map fun field => (field.erased,expand env field.domain)) (viewInstFields depth ps prior plans) := by
  induction layout generalizing prior plans with
  | done =>
    cases plans with
    | nil => exact .nil
    | cons => cases shapes
  | @field roots fields erased borrowed recursive domain tail shape selected normalized row normalizedShape shapeRep
      lookup observed output rest ih =>
    cases plans with
    | nil => cases shapes
    | cons plan plans =>
      have paired := List.cons.inj shapes
      have borrowMatches : borrowed = plan.borrowed := (Prod.mk.inj paired.1).1
      let oldDomain := plan.field.domain.subst (parameterAt depth prior.length ps)
      let oldTail := ClosedFields depth ps (prior.length+1) plans ending
      have visible : viewRead prior (ClosedFields depth ps prior.length (plan :: plans) ending) =
          .pi plan.field.erased (viewRead prior oldDomain) (oldTail.subst (liftSubOne (viewReadAt prior))) := by
        simp only [viewRead,ClosedFields,List.map_cons,instantiatedFields,Bool.false_and,Bool.false_eq_true,ite_false,
          closeDataFields,List.foldr_cons,Term.pi,Term.subst,substArgs,Op.binders,liftSub,oldDomain,oldTail]
      rw [visible] at related
      have expanded : expand env (.pi erased domain tail) = .pi erased (expand env domain) (expand env tail) := by
        simp only [Term.pi,EnvironmentDelta.expand_node_cons,expandArgs]
      rw [expanded] at related
      obtain ⟨same,typedDomain,typedTail⟩ := related.pi_injective wf.admissible
      have plannedLength : (prior ++ [plan.borrowed]).length = prior.length+1 := by simp
      have recursiveTail : RawLend.Conv env (expand env (if borrowed then reading tail else tail))
          (viewRead (prior ++ [plan.borrowed])
            (ClosedFields depth ps (prior ++ [plan.borrowed]).length plans ending)) := by
        rw [plannedLength,NativeCoreViewReading.viewRead_append]
        change RawLend.Conv env (expand env (if borrowed then reading tail else tail))
          (if plan.borrowed then reading (oldTail.subst (liftSubOne (viewReadAt prior)))
            else oldTail.subst (liftSubOne (viewReadAt prior)))
        rw [←borrowMatches]
        cases borrowed
        · exact typedTail
        · simp only [ite_true,expand_reading wf.admissible]
          exact reading_conversion wf typedTail
      have solved := ih paired.2 recursiveTail
      simp only [List.map_cons,viewInstFields]
      apply RelList.cons
      · simp only [←borrowMatches,same]
        cases borrowed
        · exact ⟨True.intro,typedDomain⟩
        · simp only [ite_true,Term.ref,expand,expandArgs]
          exact ⟨True.intro,.node .ref (.cons typedDomain .nil)⟩
      · exact solved


open NativeCoreViewCaseExpansion (viewCaseResult_expand viewHypothesisTelescope_expand)

private theorem closeFields_expand (fields : List Environment.Field) (result : Term) :
    expand env (fields.foldr (fun field rest => .pi field.erased field.domain rest) result) =
      closeDataFields (fields.map fun field => (field.erased,expand env field.domain)) (expand env result) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.foldr_cons,List.map_cons,closeDataFields,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs] at ih ⊢
    rw [ih]

private theorem closeFields_conv (related : RelList
    (fun observed expected : Bool × Term => observed.1 = expected.1 ∧ RawLend.Conv env observed.2 expected.2) first second)
    (body : RawLend.Conv env T U) : RawLend.Conv env (closeDataFields first T) (closeDataFields second U) := by
  induction related with
  | nil => exact body
  | cons same _ ih =>
    simp only [closeDataFields,List.foldr_cons,same.1]
    exact .node (.pi _) (.cons same.2 (.cons ih .nil))

private theorem borrow_bits {roots : List FieldRoot} {plans : List ViewFieldPlan} (shapes : roots.map fieldFlags = plans.map planFlags) :
    roots.map FieldRoot.borrowed = plans.map ViewFieldPlan.borrowed := by
  have borrowed := congrArg (List.map (Prod.fst : Bool × Bool → Bool)) shapes
  simpa only [List.map_map,Function.comp_def,fieldFlags,planFlags] using borrowed

private theorem recursive_positions {roots : List FieldRoot} {plans : List ViewFieldPlan}
    (shapes : roots.map fieldFlags = plans.map planFlags) (offset : Nat) :
    (roots.zipIdx offset).filterMap (fun (field,position) => if field.recursive then some position else none) =
      (plans.zipIdx offset).filterMap (fun (plan,position) => if plan.self then some position else none) := by
  induction roots generalizing plans offset with
  | nil => cases plans <;> simp at shapes ⊢
  | cons field fields ih =>
    cases plans with
    | nil => simp at shapes
    | cons plan rest =>
      have paired := List.cons.inj shapes
      have same : field.recursive = plan.self := (Prod.mk.inj paired.1).2
      simp only [List.zipIdx_cons,List.filterMap_cons,same,ih paired.2]

/-- When two constructors have corresponding borrowed fields, the original
case type and the checked case type have the same resulting binder scopes.
Conversion includes the rebuilt constructor and every recursive hypothesis. -/
theorem case_type_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (recursive : Bool) (layout : FieldLayout env family arena telescope roots fields)
    (shapes : roots.map fieldFlags = plans.map planFlags)
    (related : RawLend.Conv env (expand env telescope) (ClosedFields depth (expandArgs env ps) 0 plans ending)) :
    let actual := if recursive then (roots.zipIdx).filterMap (fun (field,position) =>
      if field.recursive then some position else none) else []
    let planned := if recursive then viewPositions plans else []
    let given := fields.foldr (fun field tail => .pi field.erased field.domain tail)
      (viewHypothesisTelescope roots.length 0 actual motive dependent
        (viewCaseResult family constructor roots.length actual.length ps motive (roots.map FieldRoot.borrowed) dependent))
    let expected := closeDataFields (viewInstFields depth (expandArgs env ps) [] plans)
      (viewHypothesisTelescope plans.length 0 planned (expand env motive) dependent
        (viewCaseResult family constructor plans.length planned.length (expandArgs env ps)
          (expand env motive) (plans.map ViewFieldPlan.borrowed) dependent))
    RawLend.Conv env (expand env given) expected := by
  dsimp only
  have initial_read (term : Term) : viewRead [] term = term := by
    have noBorrow : viewReadAt [] = Term.var := by
      funext index
      simp [viewReadAt]
    rw [viewRead,noBorrow,Term.subst_id]
  have fieldsRelated := FieldLayout.matches_fields (prior := []) wf layout shapes (by simpa only [initial_read,List.length_nil] using related)
  have width : roots.length = plans.length := by simpa only [List.length_map] using congrArg List.length shapes
  have positions : (if recursive then (roots.zipIdx).filterMap (fun (field,position) =>
      if field.recursive then some position else none) else []) = (if recursive then viewPositions plans else []) := by
    simp only [viewPositions,recursive_positions shapes 0]
  rw [closeFields_expand,viewHypothesisTelescope_expand wf.admissible,viewCaseResult_expand wf.admissible,
    width,positions,borrow_bits shapes]
  exact closeFields_conv fieldsRelated (.refl _)


open NativeFamilyWire
open NativeCoreGhostViewInference (CaseReplay)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCorePureComputationNormal (ExpandedNormalization)
open NativeCoreGhostSpineInference (Visit)

private theorem familyRows_frame (rows : RepresentsFamilies arena familyRows familyTerms)
    (kept : Prefix arena after) : RepresentsFamilies after familyRows familyTerms := by
  induction rows with
  | nil => exact .nil
  | cons represented _ ih =>
    exact .cons ⟨represented.1,represented.2.1,represented.2.2.1,represented.2.2.2.1,
      represented.2.2.2.2.frame kept⟩ ih

/-- Relate the exact constructor selected by the graph to its checked source
signature. Shape evidence concerns the recorded field normalizations and
the motive mode used by this branch builder. -/
theorem checked_case_replay
    {entry : Environment.CheckedFamily} {row : FamilyRoots}
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies base familyRows familyTerms)
    (familyRow : familyRows[family]? = some row) (entryFound : env.families[family]? = some entry)
    (data : entry.declaration.data = true)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (motiveRep : Represents base motive M) (parameterRep : RepresentsList base parameters values)
    (width : values.length = entry.declaration.params)
    (classification : ∀ {arena : Arena} {constructor : Nat} {signature : Environment.Signature}
      {telescope : Term} {roots : List FieldRoot} {fields : List Environment.Field} {motiveShape : Term} {plans : List ViewFieldPlan},
      entry.signatures[constructor]? = some signature →
      viewPlan env family (signature.fields.drop entry.declaration.params) = some plans →
      FieldLayout env family arena telescope roots fields →
      ExpandedNormalization env M motiveShape →
      roots.map fieldFlags = plans.map planFlags ∧ LoanTyping.Checker.viewDependent motiveShape = dependent) :
    CaseReplay env base ctx normal limit depth family motive row entry parameters values M recursive dependent := by
  intro start constructor written selected onBase chosen success
  obtain ⟨actual,signature,source,found,signatureFound,_,sourceRep,conversion⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_constructor_root history (familyRows_frame rows onBase) familyRow chosen
  have sameEntry := Option.some.inj (found.symm.trans entryFound)
  subst actual
  obtain ⟨scope,_,parameterBounds⟩ := LoanTyping.FamilyIota.signature_metadata history entryFound signatureFound
  obtain ⟨kept,safe,telescope,fields,roots,motiveShape,opened,layout,motiveChanged,observed⟩ :=
    NativeCoreViewCaseType.run_refines normalSound onBase sourceRep (motiveRep.frame onBase)
      (parameterRep.frame onBase) success
  obtain ⟨plans,planned⟩ := NativeCoreViewCheckedPlan.checked_constructor_plan history entryFound signatureFound data
  obtain ⟨flags,mode⟩ := classification signatureFound planned layout motiveChanged
  have expandedWidth : (expandArgs env values).length = entry.declaration.params := by
    simpa only [EnvironmentDelta.expandArgs_map,List.length_map] using width
  let finalIndices := signature.result.map (Term.subst
    (parameterAt ctx.length (signature.fields.length - entry.declaration.params) (expandArgs env values)))
  let ending := Term.node (.ind family signature.result.length) finalIndices
  have openedPlan : ParametersInstantiated (expandArgs env values) (signatureTerm family signature)
      (ClosedFields ctx.length (expandArgs env values) 0 plans ending) := by
    have instantiated := NativeCoreDataCaseAlignment.checked_opened_telescope (depth := ctx.length)
      (family := family) scope expandedWidth parameterBounds.1
    simpa only [ClosedFields,viewPlan_source planned,List.length_drop,ending,finalIndices] using instantiated
  have expandedOpened := NativeCoreDataCaseAlignment.expanded_parameters history.wellFormed
    (instantiateParameters_sound opened)
  have telescopes := NativeCoreDataCaseAlignment.parameters_preserve_conversion history.wellFormed
    expandedOpened openedPlan conversion
  let positions := if recursive then viewPositions plans else []
  let expected := closeDataFields (viewInstFields ctx.length (expandArgs env values) [] plans)
    (viewHypothesisTelescope plans.length 0 positions (expand env M) dependent
      (viewCaseResult family constructor plans.length positions.length (expandArgs env values)
        (expand env M) (plans.map ViewFieldPlan.borrowed) dependent))
  rw [mode] at observed
  refine ⟨kept,safe,signature,expected,_,signatureFound,?_,observed,?_⟩
  · simp [viewCaseType,expandedWidth,Nat.not_lt_of_ge parameterBounds.1,planned,expected,positions]
  · exact case_type_conversion history.wellFormed recursive layout flags telescopes

end Jihoo.NativeKernel.NativeCoreViewFieldAlignment
