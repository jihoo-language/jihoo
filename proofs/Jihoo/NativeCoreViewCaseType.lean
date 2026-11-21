import Jihoo.NativeCoreDataCaseTelescope
import Jihoo.NativeCoreViewShape
import Jihoo.NativeCoreViewReading
import Jihoo.NativeCoreGhostLiteralAddition

/-! A view case reads the opened constructor telescope in source order.
Each retained heap field gets a borrowed domain, and the rest of the
telescope reads that field through its borrow. The original motive is
then weakened under the fields and the recursive hypotheses. -/
namespace Jihoo.NativeKernel.NativeCoreViewCaseType

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreGhostSpineInference (Visit)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreDataMotiveDomain (addVariable variable_progress variable_refines parameters_refines represented_append)
open NativeCoreShiftedApplications (shiftRoot shift_progress shift_refines)
open NativeCorePropCaseType (wrapFields wrapFields_progress)

structure FieldRoot where
  erased : Bool
  domain : Nat
  borrowed : Bool
  recursive : Bool

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

def readFields (normal : Visit) (env : Environment) (family limit depth : Nat) :
    Nat → State → Nat → Outcome (List FieldRoot)
  | 0,state,root => reject state root
  | fuel+1,state,root =>
    match NativeCoreViewShape.piAt state.arena root with
    | none => ⟨state,.ok []⟩
    | some (erased,domain,tail) =>
      (normal state domain).next fun normalized shape =>
        match normalized.arena[shape]? with
        | none => reject normalized shape
        | some row =>
          let (borrowed,recursive) := NativeCoreViewShape.classify env family erased row
          if borrowed then
            (append normalized .ref [domain]).next fun referenced reference =>
              (NativeCoreViewReading.run limit depth referenced tail).next fun reading rest =>
                (readFields normal env family limit depth fuel reading rest).next fun after fields =>
                  ⟨after,.ok (⟨false,reference,true,recursive⟩ :: fields)⟩
          else
            (readFields normal env family limit depth fuel normalized tail).next fun after fields =>
              ⟨after,.ok (⟨erased,domain,false,false⟩ :: fields)⟩

theorem readFields_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (readFields normal env family limit depth fuel state root) := by
  induction fuel generalizing state root with
  | zero => exact Progress.atState _ _
  | succ fuel ih =>
    unfold readFields
    split
    · exact Progress.atState _ _
    · apply (normalProgress _ _).next
      intro shape
      split
      · exact Progress.atState _ _
      · dsimp only
        split
        · exact (append_progress _ _ _).next fun _ =>
            NativeCoreViewReading.run_progress.next fun _ => ih.next (fun _ => Progress.atState _ _)
        · exact ih.next (fun _ => Progress.atState _ _)

private def fieldValues (total extra : Nat) : List FieldRoot → Nat → State → Outcome (List Nat)
  | [],_,state => ⟨state,.ok []⟩
  | field :: rest,position,state =>
    (addVariable state (total-1-position+extra)).next fun allocated variableRoot =>
      let fieldValue := if field.borrowed then append allocated .deref [variableRoot] else ⟨allocated,.ok variableRoot⟩
      fieldValue.next fun read value =>
        (fieldValues total extra rest (position+1) read).next fun after values =>
          ⟨after,.ok (value :: values)⟩

private theorem fieldValues_progress : Progress limit state (fieldValues total extra fields position state) := by
  induction fields generalizing position state with
  | nil => exact Progress.atState _ _
  | cons first rest ih =>
    unfold fieldValues
    apply variable_progress.next
    intro ref
    split
    · exact (append_progress _ _ _).next fun _ => ih.next fun _ => Progress.atState _ _
    · exact (Progress.atState _ (.ok ref)).next fun _ => ih.next fun _ => Progress.atState _ _

def hypotheses (limit depth motive total : Nat) (dependent : Bool) :
    List Nat → Nat → State → Nat → Outcome Nat
  | [],_,state,result => ⟨state,.ok result⟩
  | position :: rest,offset,state,result =>
    (hypotheses limit depth motive total dependent rest (offset+1) state result).next fun later body =>
      (shiftRoot limit depth later motive (total+offset)).next fun shifted hypothesis =>
        let type := if dependent then
          (addVariable shifted (total+offset-1-position)).next fun allocated field =>
            append allocated .app [hypothesis,field]
        else ⟨shifted,.ok hypothesis⟩
        type.next fun announced domain =>
          append announced (.pi false) [domain,body]

theorem hypotheses_progress :
    Progress limit state (hypotheses limit depth motive total dependent positions offset state result) := by
  induction positions generalizing offset state result with
  | nil => exact Progress.atState _ _
  | cons first rest ih =>
    unfold hypotheses
    apply ih.next
    intro body
    apply shift_progress.next
    intro hypothesis
    split
    · exact (variable_progress.next fun _ => append_progress _ _ _).next (fun _ => append_progress _ _ _)
    · exact append_progress _ _ _

private def resultType (limit depth family constructor motive : Nat) (parameters : List Nat)
    (fields : List FieldRoot) (extra : Nat) (dependent : Bool) (state : State) : Outcome Nat :=
  (shiftRoot limit depth state motive (fields.length+extra)).next fun shifted result =>
    if dependent then
      (NativeCoreDataMotiveDomain.parameters limit depth (fields.length+extra) parameters shifted).next fun weakened ps =>
        (fieldValues fields.length extra fields 0 weakened).next fun framed refs =>
          (append framed (.con family constructor (ps ++ refs).length) (ps ++ refs)).next fun built value =>
            (append built .borrow [value]).next fun borrowed reference =>
              append borrowed .app [result,reference]
    else ⟨shifted,.ok result⟩

private theorem resultType_progress :
    Progress limit state (resultType limit depth family constructor motive parameters fields extra dependent state) := by
  unfold resultType
  apply shift_progress.next
  intro result
  split
  · exact NativeCoreDataMotiveDomain.parameters_progress.next fun _ =>
      fieldValues_progress.next fun _ => (append_progress _ _ _).next fun _ =>
        (append_progress _ _ _).next fun _ => append_progress _ _ _
  · exact Progress.atState _ _

def dependentAt (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node (.lam _) [_,_]) => true
  | _ => false

def run (normal : Visit) (env : Environment) (limit depth : Nat) (state : State)
    (family constructor count motive written : Nat) (parameters : List Nat) (recursive : Bool) : Outcome Nat :=
  if parameters.length = count then
    (NativeCoreDataCaseTelescope.instantiate limit depth parameters state written).next fun opened telescope =>
      (readFields normal env family limit depth (opened.arena.size+1) opened telescope).next fun scanned fields =>
        (normal scanned motive).next fun checked shape =>
          let dependent := dependentAt checked.arena shape
          let positions := if recursive then (fields.zipIdx).filterMap (fun (field,position) =>
            if field.recursive then some position else none) else []
          (resultType limit depth family constructor motive parameters fields positions.length dependent checked).next
            fun built result =>
              (hypotheses limit depth motive fields.length dependent positions 0 built result).next fun announced body =>
                wrapFields (fields.map fun field => (field.erased,field.domain)) announced body
  else reject state written

theorem run_progress (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (run normal env limit depth state family constructor count motive written parameters recursive) := by
  unfold run
  split
  · exact NativeCoreDataCaseTelescope.instantiate_progress.next fun _ =>
      (readFields_progress normalProgress).next fun _ => (normalProgress _ _).next fun _ =>
        resultType_progress.next fun _ => hypotheses_progress.next fun _ => wrapFields_progress _ _ _
  · exact Progress.atState _ _

private def fieldTerms (fields : List FieldRoot) (total extra first : Nat) : List Term :=
  (fields.zipIdx first).map fun (field,position) =>
    let reference := Term.var (total-1-position+extra)
    if field.borrowed then .deref reference else reference

private theorem fieldValues_refines
    (success : (fieldValues total extra fields position state).result = .ok selected) :
    let after := (fieldValues total extra fields position state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RepresentsList after selected (fieldTerms fields total extra position) := by
  induction fields generalizing position state selected with
  | nil => cases success; exact ⟨.refl _,id,.nil⟩
  | cons field fields ih =>
    unfold fieldValues at success ⊢
    obtain ⟨reference,referenceOk,referenceNext⟩ := Outcome.next_success success
    rw [referenceNext] at success ⊢
    obtain ⟨value,valueOk,valueNext⟩ := Outcome.next_success success
    rw [valueNext] at success ⊢
    obtain ⟨first,firstBack,referenceRep⟩ := variable_refines referenceOk
    have fieldRep :
        let after := (if field.borrowed then append (addVariable state (total-1-position+extra)).state .deref [reference]
          else ⟨(addVariable state (total-1-position+extra)).state,.ok reference⟩ : Outcome Nat).state.arena
        Prefix (addVariable state (total-1-position+extra)).state.arena after ∧
        (Backward (addVariable state (total-1-position+extra)).state.arena → Backward after) ∧
        Represents after value (if field.borrowed then Term.deref (.var (total-1-position+extra))
          else .var (total-1-position+extra)) := by
      split at valueOk
      · rename_i borrowed
        simp only [ite_eq_left borrowed]
        exact append_refines (.cons referenceRep .nil) rfl valueOk
      · rename_i scalar
        simp only [ite_eq_right scalar]
        cases valueOk
        exact ⟨.refl _,id,referenceRep⟩
    obtain ⟨second,secondBack,valueRep⟩ := fieldRep
    obtain ⟨rest,tailOk,tailNext⟩ := Outcome.next_success success
    rw [tailNext] at success ⊢
    cases success
    obtain ⟨third,thirdBack,restRep⟩ := ih tailOk
    exact ⟨first.trans (second.trans third),thirdBack ∘ secondBack ∘ firstBack,
      by simpa only [fieldTerms,List.zipIdx_cons,List.map_cons] using RepresentsList.cons (valueRep.frame third) restRep⟩

private theorem range_field_terms (fields : List FieldRoot) (extra : Nat) :
    fieldTerms fields fields.length extra 0 =
      (List.range fields.length).map (fun j =>
        let field := Term.var (fields.length - 1 - j + extra)
        if (fields.map FieldRoot.borrowed)[j]?.getD false then Term.deref field else field) := by
  apply List.ext_getElem
  · simp only [fieldTerms,List.length_map,List.length_zipIdx,List.length_range]
  · intro i left right
    have within : i < fields.length := by
      simpa only [fieldTerms,List.length_map,List.length_zipIdx] using left
    have flag : (fields.map FieldRoot.borrowed)[i]? = some (fields[i].borrowed) := by
      simp only [List.getElem?_map,List.getElem?_eq_getElem within,Option.map_some]
    simp only [fieldTerms,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,List.getElem_range,flag,Option.getD_some]

theorem resultType_refines (motiveRep : Represents state.arena motive M)
    (paramRep : RepresentsList state.arena parameters values)
    (success : (resultType limit depth family constructor motive parameters fields extra dependent state).result = .ok selected) :
    let after := (resultType limit depth family constructor motive parameters fields extra dependent state).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (viewCaseResult family constructor fields.length extra values M
        (fields.map FieldRoot.borrowed) dependent) := by
  unfold resultType at success ⊢
  obtain ⟨shifted,shiftedOk,shiftedNext⟩ := Outcome.next_success success
  rw [shiftedNext] at success ⊢
  obtain ⟨shiftKept,shiftBack,shiftRep⟩ := shift_refines motiveRep shiftedOk
  cases dependent
  · cases success
    exact ⟨shiftKept,shiftBack,by simpa only [viewCaseResult,Bool.false_eq_true,ite_false,Nat.add_assoc] using shiftRep⟩
  · simp only [ite_true] at success ⊢
    obtain ⟨ps,psOk,psNext⟩ := Outcome.next_success success
    rw [psNext] at success ⊢
    obtain ⟨refs,refsOk,refsNext⟩ := Outcome.next_success success
    rw [refsNext] at success ⊢
    obtain ⟨value,valueOk,valueNext⟩ := Outcome.next_success success
    rw [valueNext] at success ⊢
    obtain ⟨borrowed,borrowedOk,borrowedNext⟩ := Outcome.next_success success
    rw [borrowedNext] at success ⊢
    obtain ⟨paramKept,paramBack,shiftedParams⟩ := parameters_refines (paramRep.frame shiftKept) psOk
    obtain ⟨fieldKept,fieldBack,fieldRep⟩ := fieldValues_refines refsOk
    have arguments := represented_append (shiftedParams.frame fieldKept) fieldRep
    obtain ⟨conKept,conBack,conRep⟩ := append_refines arguments rfl valueOk
    obtain ⟨borrowKept,borrowBack,borrowRep⟩ := append_refines (.cons conRep .nil) rfl borrowedOk
    have tailKept := paramKept.trans (fieldKept.trans (conKept.trans borrowKept))
    obtain ⟨appKept,appBack,output⟩ := append_refines (.cons (shiftRep.frame tailKept) (.cons borrowRep .nil)) rfl success
    have width := NativeCoreIdentical.represented_length arguments
    refine ⟨shiftKept.trans (tailKept.trans appKept),appBack ∘ borrowBack ∘ conBack ∘ fieldBack ∘ paramBack ∘ shiftBack,?_⟩
    let args := (values.map fun term => term.rename (fun index => index+(fields.length+extra))) ++
      fieldTerms fields fields.length extra 0
    let observed := Term.app (M.rename (fun index => index+(fields.length+extra)))
      (.borrow (.node (.con family constructor (ps++refs).length) args))
    have reported : Represents _ selected observed := output
    have same : observed = viewCaseResult family constructor fields.length extra values M
        (fields.map FieldRoot.borrowed) true := by
      simp only [observed,args,viewCaseResult,ite_true,Nat.add_assoc,width,range_field_terms]
    exact same ▸ reported

theorem hypotheses_refines (motiveRep : Represents state.arena motive M)
    (bodyRep : Represents state.arena result final)
    (success : (hypotheses limit depth motive total dependent positions offset state result).result = .ok selected) :
    let after := (hypotheses limit depth motive total dependent positions offset state result).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (viewHypothesisTelescope total offset positions M dependent final) := by
  induction positions generalizing offset state result final selected with
  | nil =>
    cases success
    exact ⟨.refl _,id,bodyRep⟩
  | cons position positions ih =>
    unfold hypotheses at success ⊢
    obtain ⟨tail,tailOk,tailNext⟩ := Outcome.next_success success
    rw [tailNext] at success ⊢
    obtain ⟨hypothesis,hypothesisOk,hypothesisNext⟩ := Outcome.next_success success
    rw [hypothesisNext] at success ⊢
    obtain ⟨domain,domainOk,domainNext⟩ := Outcome.next_success success
    rw [domainNext] at success ⊢
    obtain ⟨tailKept,tailBack,tailRep⟩ := ih motiveRep bodyRep tailOk
    obtain ⟨shiftKept,shiftBack,shiftRep⟩ := shift_refines (motiveRep.frame tailKept) hypothesisOk
    cases dependent
    · cases domainOk
      obtain ⟨added,addedBack,represented⟩ := append_refines
        (.cons shiftRep (.cons (tailRep.frame shiftKept) .nil)) rfl success
      exact ⟨tailKept.trans (shiftKept.trans added),addedBack ∘ shiftBack ∘ tailBack,
        by simpa only [viewHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,viewHypothesisType,
          Bool.false_eq_true,ite_false,Nat.add_assoc,Term.pi] using represented⟩
    · simp only [ite_true] at domainOk success ⊢
      obtain ⟨field,fieldOk,fieldNext⟩ := Outcome.next_success domainOk
      rw [fieldNext] at domainOk success ⊢
      obtain ⟨fieldKept,fieldBack,fieldRep⟩ := variable_refines fieldOk
      obtain ⟨appKept,appBack,appRep⟩ := append_refines (.cons (shiftRep.frame fieldKept) (.cons fieldRep .nil)) rfl domainOk
      have beforePi := shiftKept.trans (fieldKept.trans appKept)
      obtain ⟨added,addedBack,represented⟩ := append_refines
        (.cons appRep (.cons (tailRep.frame beforePi) .nil)) rfl success
      exact ⟨tailKept.trans (beforePi.trans added),addedBack ∘ appBack ∘ fieldBack ∘ shiftBack ∘ tailBack,
        by simpa only [viewHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,viewHypothesisType,
          ite_true,Nat.add_assoc,Term.pi,Term.app] using represented⟩


open NativeCoreBinderTraversal (VisitsFrom)
open NativeCorePureComputationNormal (ExpandedNormalization)

/-- The graph's field layout records the actual unnormalized domain, the
normalization used to classify it, and the exact scope of the remaining
fields. Evidence that the source is the checked constructor is separate. -/
inductive FieldLayout (env : Environment) (family : Nat) (arena : Arena) :
    Term → List FieldRoot → List Field → Prop where
  | done (final : ∀ erased domain tail, term ≠ .pi erased domain tail) : FieldLayout env family arena term [] []
  | field {erased borrowed recursive : Bool} {domain tail shape : Term} {selected normalized : Nat} {row : Node} :
      ExpandedNormalization env domain shape → Represents arena normalized shape → arena[normalized]? = some row →
      NativeCoreViewShape.classify env family erased row = (borrowed,recursive) →
      Represents arena selected (if borrowed then .ref domain else domain) →
      FieldLayout env family arena (if borrowed then reading tail else tail) roots fields →
      FieldLayout env family arena (.pi erased domain tail)
        (⟨if borrowed then false else erased,selected,borrowed,recursive⟩ :: roots)
        (⟨if borrowed then false else erased,if borrowed then .ref domain else domain,none⟩ :: fields)

private theorem not_pi (source : Represents arena root term)
    (found : NativeCoreViewShape.piAt arena root = none) : ∀ erased domain tail, term ≠ .pi erased domain tail := by
  intro erased domain tail same
  cases same
  cases source with
  | node row _ children =>
    cases children with
    | cons first rest =>
      cases rest with
      | cons second rest =>
        cases rest
        simp only [NativeCoreViewShape.piAt,row,reduceCtorEq] at found

private theorem represented_pi (source : Represents arena root term)
    (found : NativeCoreViewShape.piAt arena root = some (erased,domain,tail)) :
    ∃ D R, Represents arena domain D ∧ Represents arena tail R ∧ term = .pi erased D R := by
  cases source with
  | var row => simp only [NativeCoreViewShape.piAt,row,reduceCtorEq] at found
  | @node _ op refs terms row arity children =>
    cases op <;> simp only [NativeCoreViewShape.piAt,row] at found <;> try contradiction
    case pi erased' =>
      cases children with
      | nil => cases arity
      | cons first rest =>
        cases rest with
        | nil => cases arity
        | cons second rest =>
          cases rest with
          | nil =>
            cases found
            exact ⟨_,_,first,second,rfl⟩
          | cons => cases arity

private theorem not_borrowed_not_recursive
    (flags : NativeCoreViewShape.classify env family erased row = (false,recursive)) : recursive = false := by
  cases recursive with
  | false => rfl
  | true =>
    unfold NativeCoreViewShape.classify at flags
    split at flags
    · cases flags
    · split at flags <;> try cases flags
      split at flags
      · cases flags
      · have impossible := congrArg Prod.snd flags
        cases impossible

/-- A successful dynamic walk constructs an exact layout for its own
opened telescope. In particular, a later domain mentions the previous
borrow through Deref, and the field type retains the raw domain. -/
theorem readFields_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena root term)
    (success : (readFields normal env family limit depth fuel state root).result = .ok roots) :
    let after := (readFields normal env family limit depth fuel state root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ fields, FieldLayout env family after term roots fields := by
  induction fuel generalizing state root term roots with
  | zero => cases success
  | succ fuel ih =>
    unfold readFields at success ⊢
    split at success
    · rename_i found
      cases success
      exact ⟨.refl _,id,[],.done (not_pi source found)⟩
    · rename_i erased domain tail found
      obtain ⟨D,R,domainRep,tailRep,rfl⟩ := represented_pi source found
      obtain ⟨normalized,normalizedOk,normalizedNext⟩ := Outcome.next_success success
      rw [normalizedNext] at success ⊢
      obtain ⟨first,firstBack,shape,shapeRep,converted⟩ := normalSound onBase domainRep normalizedOk
      split at success
      · cases success
      · rename_i row lookup
        generalize flags : NativeCoreViewShape.classify env family erased row = layout at success ⊢
        obtain ⟨borrowed,recursive⟩ := layout
        dsimp only at success ⊢
        cases borrowed
        · simp only [Bool.false_eq_true,ite_false] at success ⊢
          obtain ⟨rest,restOk,restNext⟩ := Outcome.next_success success
          rw [restNext] at success ⊢
          cases success
          obtain ⟨later,laterBack,fields,held⟩ := ih (onBase.trans first) (tailRep.frame first) restOk
          have same := not_borrowed_not_recursive flags
          subst recursive
          exact ⟨first.trans later,laterBack ∘ firstBack,_,.field converted (shapeRep.frame later)
            (later.2 lookup) flags ((domainRep.frame first).frame later) held⟩
        · simp only [ite_true] at success ⊢
          obtain ⟨reference,referenceOk,referenceNext⟩ := Outcome.next_success success
          rw [referenceNext] at success ⊢
          obtain ⟨afterRef,refBack,referenceRep⟩ := append_refines (.cons (domainRep.frame first) .nil) rfl referenceOk
          obtain ⟨rewritten,readingOk,readingNext⟩ := Outcome.next_success success
          rw [readingNext] at success ⊢
          have added := first.trans afterRef
          obtain ⟨afterRead,readBack,readingRep⟩ := NativeCoreViewReading.run_refines (tailRep.frame added) readingOk
          obtain ⟨rest,restOk,restNext⟩ := Outcome.next_success success
          rw [restNext] at success ⊢
          cases success
          obtain ⟨later,laterBack,fields,held⟩ := ih (onBase.trans (added.trans afterRead)) readingRep restOk
          have preserved := afterRead.trans later
          exact ⟨added.trans preserved,laterBack ∘ readBack ∘ refBack ∘ firstBack,_,
            .field converted (shapeRep.frame (afterRef.trans preserved)) ((afterRef.trans preserved).2 lookup)
              flags (referenceRep.frame preserved) held⟩


private theorem FieldLayout.represented (layout : FieldLayout env family arena term roots fields) :
    NativeCorePropCaseType.FieldsRep arena (roots.map fun field => (field.erased,field.domain)) fields := by
  induction layout with
  | done => exact .nil
  | field _ _ _ _ represented _ tail => exact .cons (field := ⟨_,_,none⟩) represented tail

private theorem FieldLayout.frame (layout : FieldLayout env family before term roots fields)
    (kept : Prefix before after) : FieldLayout env family after term roots fields := by
  induction layout with
  | done final => exact .done final
  | field normal normalRep lookup flags domainRep _ tail =>
    exact .field normal (normalRep.frame kept) (kept.2 lookup) flags (domainRep.frame kept) tail

private theorem dependentAt_refines (represented : Represents arena selected shape) :
    dependentAt arena selected = LoanTyping.Checker.viewDependent shape := by
  cases represented with
  | var read => simp only [dependentAt,read,LoanTyping.Checker.viewDependent]
  | @node _ op refs terms read arity children =>
    cases op <;> simp only [dependentAt,read,LoanTyping.Checker.viewDependent] <;> try rfl
    case lam erased =>
      cases children with
      | nil => cases arity
      | cons first rest =>
        cases rest with
        | nil => cases arity
        | cons second rest => cases rest <;> first | rfl | cases arity

/-- Successful construction returns a type over exactly the fields seen by
this visit of the parameter-opened telescope, in their original order.
Motive classification comes from the graph's own normalized motive. -/
theorem run_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (writtenRep : Represents state.arena written T)
    (motiveRep : Represents state.arena motive M) (paramRep : RepresentsList state.arena parameters ps)
    (success : (run normal env limit depth state family constructor count motive written parameters recursive).result = .ok selected) :
    let after := (run normal env limit depth state family constructor count motive written parameters recursive).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ telescope fields roots motiveShape,
        instantiateParameters ps T = some telescope ∧
        FieldLayout env family after telescope roots fields ∧
        ExpandedNormalization env M motiveShape ∧
        let dependent := LoanTyping.Checker.viewDependent motiveShape
        let positions := if recursive then (roots.zipIdx).filterMap (fun (field,position) =>
          if field.recursive then some position else none) else []
        Represents after selected (fields.foldr (fun field tail => .pi field.erased field.domain tail)
          (viewHypothesisTelescope roots.length 0 positions M dependent
            (viewCaseResult family constructor roots.length positions.length ps M
              (roots.map FieldRoot.borrowed) dependent))) := by
  unfold run at success ⊢
  split at success
  · rename_i countEq
    simp only [ite_eq_left countEq]
    obtain ⟨opened,openedOk,openedNext⟩ := Outcome.next_success success
    rw [openedNext] at success ⊢
    obtain ⟨scanned,scannedOk,scannedNext⟩ := Outcome.next_success success
    rw [scannedNext] at success ⊢
    obtain ⟨shape,shapeOk,shapeNext⟩ := Outcome.next_success success
    rw [shapeNext] at success ⊢
    dsimp only at success ⊢
    obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
    rw [resultNext] at success ⊢
    obtain ⟨body,bodyOk,bodyNext⟩ := Outcome.next_success success
    rw [bodyNext] at success ⊢
    obtain ⟨openedKept,openedBack,telescope,telescopeRep,instantiated⟩ :=
      NativeCoreDataCaseTelescope.instantiate_refines writtenRep paramRep openedOk
    obtain ⟨scannedKept,scannedBack,fields,layout⟩ := readFields_refines normalSound
      (onBase.trans openedKept) telescopeRep scannedOk
    have beforeShape := openedKept.trans scannedKept
    obtain ⟨shapeKept,shapeBack,motiveShape,shapeRep,shapeChanged⟩ := normalSound
      (onBase.trans beforeShape) (motiveRep.frame beforeShape) shapeOk
    have beforeResult := beforeShape.trans shapeKept
    have motiveHeld := motiveRep.frame beforeResult
    obtain ⟨resultKept,resultBack,resultRep⟩ := resultType_refines motiveHeld (paramRep.frame beforeResult) resultOk
    obtain ⟨bodyKept,bodyBack,bodyRep⟩ := hypotheses_refines (motiveHeld.frame resultKept) resultRep bodyOk
    have afterScan := shapeKept.trans (resultKept.trans bodyKept)
    obtain ⟨outKept,outBack,output⟩ := NativeCorePropCaseType.wrapFields_refines
      (layout.represented.frame afterScan) bodyRep success
    refine ⟨beforeShape.trans (afterScan.trans outKept),outBack ∘ bodyBack ∘ resultBack ∘ shapeBack ∘ scannedBack ∘ openedBack,
      telescope,fields,scanned,motiveShape,instantiated,layout.frame (afterScan.trans outKept),shapeChanged,?_⟩
    rw [dependentAt_refines shapeRep] at output ⊢
    exact output
  · cases success


namespace Examples

private abbrev normalWithLiterals := NativeCoreGhostLiteralAddition.run

private def box : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration := ⟨true,0,0,[box,.pi false box box],0⟩
private def entry : CheckedFamily := ⟨declaration,[⟨[],[]⟩,⟨[⟨false,box,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[entry]⟩

private def initial : Arena := #[.node .u64 [],.node (.ind 0 0) [],.node (.pi false) [1,1],
  .node .ref [1],.node (.lam false) [3,0],.node (.universe 0) [],.node (.universe 0) [],.node (.universe 0) []]

private def fields : Array Node := #[.node .ref [1],.var 0,.node .deref [9]]

/-- Native construction borrows the recursive field in all modes. Only
recursive View adds an induction hypothesis. A dependent motive receives a
borrow of the constructor rebuilt from the original field value. -/
theorem view_case_type_matches_native_modes :
    (run (normalWithLiterals [] 0 4 16) env 4 16 ⟨initial,0⟩ 0 1 0 0 2 [] false =
      ⟨⟨initial ++ fields ++ #[.node (.pi false) [8,0]],4⟩,.ok 11⟩) ∧
    (run (normalWithLiterals [] 0 5 16) env 5 16 ⟨initial,0⟩ 0 1 0 0 2 [] true =
      ⟨⟨initial ++ fields ++ #[.node (.pi false) [0,0],.node (.pi false) [8,11]],5⟩,.ok 12⟩) ∧
    (run (normalWithLiterals [] 0 10 16) env 10 16 ⟨initial,0⟩ 0 1 0 4 2 [] false =
      ⟨⟨initial ++ fields ++ #[.var 0,.node .deref [11],.node (.con 0 1 1) [12],.node .borrow [13],
        .node .app [4,14],.node (.pi false) [8,15]],10⟩,.ok 16⟩) ∧
    (run (normalWithLiterals [] 0 14 16) env 14 16 ⟨initial,0⟩ 0 1 0 4 2 [] true =
      ⟨⟨initial ++ fields ++ #[.var 1,.node .deref [11],.node (.con 0 1 1) [12],.node .borrow [13],
        .node .app [4,14],.var 0,.node .app [4,16],.node (.pi false) [17,15],.node (.pi false) [8,18]],14⟩,.ok 19⟩) := by
  cbv

end Examples

end Jihoo.NativeKernel.NativeCoreViewCaseType
