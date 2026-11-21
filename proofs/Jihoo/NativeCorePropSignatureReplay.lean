import Jihoo.NativeCorePropSignatureAuthentication
import Jihoo.NativeCoreGhostPropCases
import Jihoo.NativeCoreConstructorGraphLink
import Jihoo.NativeCoreGhostDataCases

/-! A proposition declaration reads its written telescope before any
normalization. The graph replay retains distinct roots for the normalized
recursive indices and for the separately normalized field domain. -/
namespace Jihoo.NativeKernel.NativeCorePropSignatureReplay

open NativeArena Environment NativeFamilyWire
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization visitOperands visitOperands_progress)
open NativeCorePropCaseType (SignatureRoots FieldsRep RecursiveRep SignatureRep)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta (expand expandArgs)
open NativeCorePropSignatureAuthentication (ObservedField ObservedTelescope)

abbrev Bindings := List (Bool × Nat)
abbrev CheckBinder := Bindings → State → Nat → Bool → Outcome Unit
abbrev CheckIndices := Bindings → State → Nat → List Nat → Outcome Unit
abbrev Normalize := State → Nat → Outcome Nat

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def mapped (outcome : Outcome α) (f : α → β) : Outcome β :=
  ⟨outcome.state,outcome.result.map f⟩

private def selfIndices (arena : Arena) (family root : Nat) : Option (List Nat) :=
  match arena[root]? with
  | some (.node (.ind found _) indices) => if found = family then some indices else none
  | _ => none

private def parameterFreeField (checkBinder : CheckBinder) (checkIndices : CheckIndices) (normal : Normalize)
    (family : Nat) (context : Bindings) (state : State) (erased : Bool) (domain : Nat) :
    Outcome (Nat × Option (List Nat)) :=
  let indices := match selfIndices state.arena family domain with
    | some roots => if erased then
        (checkIndices context state domain roots).next fun checked _ =>
          mapped (visitOperands normal checked roots) some
      else reject state domain
    | none => mapped (checkBinder context state domain erased) fun _ => none
  indices.next fun checked recursive =>
    (normal checked domain).next fun after selected =>
      if erased || after.arena[selected]? == some (.node .u64 []) then ⟨after,.ok (selected,recursive)⟩
      else reject after selected

/-- Only the proposition declaration path has no parameters. The binder
and index checks run before either result or field roots are normalized. -/
def run (checkBinder : CheckBinder) (checkIndices : CheckIndices) (normal : Normalize)
    (family : Nat) : Nat → Bindings → State → Nat → Outcome SignatureRoots
  | 0, _, state, root => reject state root
  | fuel+1, context, state, root =>
      match state.arena[root]? with
      | some (.node (.pi erased) [domain,tail]) =>
        (parameterFreeField checkBinder checkIndices normal family context state erased domain).next
          fun after (selected,recurse) =>
            (run checkBinder checkIndices normal family fuel ((erased,selected) :: context) after tail).next
              fun done result =>
                let recursive := match recurse with
                  | none => result.recursive
                  | some roots => (context.length,roots) :: result.recursive
                ⟨done,.ok ⟨(erased,selected) :: result.fields,recursive,result.result⟩⟩
      | some (.node (.ind found _) indices) =>
        if found = family then
          (checkIndices context state root indices).next fun checked _ =>
            mapped (visitOperands normal checked indices) fun result => ⟨[],[],result⟩
        else reject state root
      | _ => reject state root

private theorem finishField_progress (state : State) (erased : Bool) (selected : Nat)
    (recursive : Option (List Nat)) :
    Progress limit state (if erased || state.arena[selected]? == some (.node .u64 []) then
      ⟨state,.ok (selected,recursive)⟩ else reject state selected) := by
  split <;> exact Progress.atState _ _

private theorem parameterFreeField_progress
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (parameterFreeField checkBinder checkIndices normal family ctx state erased domain) := by
  unfold parameterFreeField
  apply Progress.next
  · split
    · split
      · exact (indicesProgress _ _ _ _).next (fun _ => (visitOperands_progress normalProgress _ _).map some)
      · exact Progress.atState _ _
    · exact (binderProgress _ _ _ _).map (fun _ => none)
  · intro recursive
    exact (normalProgress _ _).next (fun selected => finishField_progress _ erased selected recursive)

theorem run_progress
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (run checkBinder checkIndices normal family fuel context state root) := by
  induction fuel generalizing context state root with
  | zero => exact Progress.atState _ _
  | succ fuel ih =>
    unfold run
    split
    · exact (parameterFreeField_progress binderProgress indicesProgress normalProgress).next (fun selected =>
        (ih (context := _ :: context)).next (fun _ => Progress.atState _ _))
    · split
      · exact (indicesProgress _ _ _ _).next (fun _ => (visitOperands_progress normalProgress _ _).map _)
      · exact Progress.atState _ _
    · exact Progress.atState _ _

private theorem mapped_success (success : (mapped result f).result = .ok selected) :
    ∃ value, result.result = .ok value ∧ f value = selected := by
  unfold mapped at success
  cases checked : result.result with
  | error reason => simp [checked,Except.map] at success
  | ok value => exact ⟨value,rfl,by simpa only [checked,Except.map,Except.ok.injEq] using success⟩

private theorem converted_indices
    (replayed : ListRel (ExpandedNormalization env) written normalized) :
    ListRel (RawLend.Conv env) (expandArgs env written) (expandArgs env normalized) := by
  induction replayed with
  | nil => simp only [expandArgs]; exact .nil
  | cons first _ tail => simp only [expandArgs]; exact .cons first.converted tail

private theorem matched_indices (domainRep : Represents arena domain source)
    (observed : selfIndices arena family domain = some refs) :
    ∃ count indices, source = .node (.ind family count) indices ∧ RepresentsList arena refs indices := by
  unfold selfIndices at observed
  split at observed
  · rename_i found count selected read
    split at observed
    · rename_i same
      subst found
      simp only [Option.some.injEq] at observed
      subst selected
      cases domainRep with
      | var lookup => rw [read] at lookup; cases lookup
      | node lookup _ represented => rw [read] at lookup; cases lookup; exact ⟨count,_,rfl,represented⟩
    · cases observed
  · cases observed

inductive OptionalIndexRep (arena : Arena) :
    Option (List Nat) → Option (List Term) → Prop where
  | ordinary : OptionalIndexRep arena none none
  | recursive : RepresentsList arena refs indices → OptionalIndexRep arena (some refs) (some indices)

private theorem OptionalIndexRep.frame (held : OptionalIndexRep arena roots indices) (kept : Prefix arena after) :
    OptionalIndexRep after roots indices := by
  cases held with
  | ordinary => exact .ordinary
  | recursive held => exact .recursive (held.frame kept)

private theorem finish_observes
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (domainRep : Represents state.arena domain written)
    (previous : OptionalIndexRep state.arena recRoots recTerms)
    (observed : ∀ domain, RawLend.Conv env (expand env written) (expand env domain) →
      ObservedField env family erased written ⟨erased,domain,recTerms⟩)
    (success : ((normal state domain).next fun after selected =>
      if erased || after.arena[selected]? == some (.node .u64 []) then ⟨after,.ok (selected,recRoots)⟩
      else reject after selected).result = .ok (selected,selectedIndices)) :
    let result := ((normal state domain).next fun after selected =>
      if erased || after.arena[selected]? == some (.node .u64 []) then ⟨after,.ok (selected,recRoots)⟩
      else reject after selected)
    Prefix state.arena result.state.arena ∧
      ∃ field, Represents result.state.arena selected field.domain ∧ field.erased = erased ∧
        OptionalIndexRep result.state.arena selectedIndices field.recursive ∧
        ObservedField env family erased written field := by
  obtain ⟨root,normalizes,entered⟩ := Outcome.next_success success
  rw [entered] at success ⊢
  obtain ⟨kept,_,canonical,represented,related⟩ := normalSound onBase domainRep normalizes
  split at success
  · rename_i allowed
    simp only [ite_eq_left allowed]
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    exact ⟨kept,_,represented,rfl,previous.frame kept,observed canonical related.converted⟩
  · cases success

/-- The raw domain is normalized separately from its recursive indices.
The original checked telescope will supply the self-free ordinary domain. -/
theorem field_observes
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (domainRep : Represents state.arena domain written)
    (absent : selfIndices state.arena family domain = none → UnifiedProgram.Families.selfFree family written = true)
    (success : (parameterFreeField checkBinder checkIndices normal family context state erased domain).result =
      .ok (selected,recursive)) :
    let result := parameterFreeField checkBinder checkIndices normal family context state erased domain
    Prefix state.arena result.state.arena ∧
      ∃ field, Represents result.state.arena selected field.domain ∧ field.erased = erased ∧
        OptionalIndexRep result.state.arena recursive field.recursive ∧ ObservedField env family erased written field := by
  unfold parameterFreeField at success ⊢
  cases recursiveRead : selfIndices state.arena family domain with
  | none =>
    simp only [recursiveRead] at success ⊢
    obtain ⟨marker,prepared,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨_,_,same⟩ := mapped_success prepared
    subst marker
    have checked := binderProgress context state domain erased
    obtain ⟨kept,field,represented,erasure,indices,observed⟩ :=
      finish_observes normalSound (onBase.trans checked.kept) (domainRep.frame checked.kept)
        .ordinary (fun _ converted => .ordinary (absent recursiveRead) converted) success
    exact ⟨checked.kept.trans kept,field,represented,erasure,indices,observed⟩
  | some refs =>
    simp only [recursiveRead] at success ⊢
    cases erased with
    | false => cases success
    | true =>
      simp only [ite_true] at success ⊢
      obtain ⟨marker,prepared,next⟩ := Outcome.next_success success
      rw [next] at success ⊢
      obtain ⟨⟨⟩,_,checkedNext⟩ := Outcome.next_success prepared
      rw [checkedNext] at prepared success ⊢
      obtain ⟨roots,normalized,same⟩ := mapped_success prepared
      subst marker
      obtain ⟨count,writtenIndices,shape,sourceIndices⟩ := matched_indices domainRep recursiveRead
      subst written
      let checked := checkIndices context state domain refs
      have checkedCost := indicesProgress context state domain refs
      obtain ⟨indexKept,_,_,observedIndices,held,related⟩ :=
        NativeCorePureComputationNormal.visitOperands_relatesFrom (onBase.trans checkedCost.kept)
          (sourceIndices.frame checkedCost.kept) normalSound normalized
      have kept := checkedCost.kept.trans indexKept
      obtain ⟨last,field,represented,erasure,indices,observed⟩ :=
        finish_observes normalSound (onBase.trans kept) (domainRep.frame kept)
          (.recursive held) (fun _ converted => .recursive converted (converted_indices related)) success
      exact ⟨kept.trans last,field,represented,erasure,indices,observed⟩

private def recursiveAt (offset : Nat) (fields : List Field) : List (Nat × List Term) :=
  (fields.zipIdx offset).filterMap (fun (field,index) => field.recursive.map (fun refs => (index,refs)))

private theorem field_absent (checked : UnifiedProgram.Families.FieldChecked prior family decl ctx erased domain trusted)
    (represented : Represents arena root domain) (notRecursive : selfIndices arena family root = none) :
    UnifiedProgram.Families.selfFree family domain = true := by
  cases checked with
  | ordinary selfFree _ _ _ _ _ => exact selfFree
  | recursive _ _ _ _ _ =>
    cases represented with
    | node read _ children => simp [selfIndices,read] at notRecursive

private theorem prepared_field_roots (represented : Represents arena root (.pi erased domain body)) :
    ∃ first next, arena[root]? = some (.node (.pi erased) [first,next]) ∧
      Represents arena first domain ∧ Represents arena next body := by
  cases represented with
  | node read _ children =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons next last =>
        cases last
        exact ⟨_,_,read,first,next⟩

private theorem result_roots (represented : Represents arena root (.node (.ind family count) indices)) :
    ∃ refs, arena[root]? = some (.node (.ind family count) refs) ∧ RepresentsList arena refs indices := by
  cases represented with
  | node read _ children => exact ⟨_,read,children⟩

/-- Native field replay interprets an original checked source telescope.
Recursive marks use the actual position in the live declaration context. -/
theorem observes_checked_telescope
    (checked : UnifiedProgram.Families.TelescopeChecked prior family decl checkedPrefix written trusted)
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena root written)
    (prefixLength : observedPrefix.length = context.length)
    (success : (run checkBinder checkIndices normal family fuel context state root).result = .ok roots) :
    let after := (run checkBinder checkIndices normal family fuel context state root).state.arena
    Prefix state.arena after ∧
      ∃ fields indices, FieldsRep after roots.fields fields ∧
        RecursiveRep after roots.recursive (recursiveAt context.length fields) ∧
        RepresentsList after roots.result indices ∧
        ObservedTelescope env family observedPrefix written ⟨observedPrefix ++ fields,indices⟩ := by
  induction checked generalizing observedPrefix fuel context state root roots with
  | field checked tail ih =>
    cases fuel with
    | zero => cases success
    | succ fuel =>
      obtain ⟨domain,body,read,domainRep,bodyRep⟩ := prepared_field_roots source
      simp only [run,read] at success ⊢
      obtain ⟨⟨selected,recursive⟩,selectedOk,selectedNext⟩ := Outcome.next_success success
      rw [selectedNext] at success ⊢
      obtain ⟨remaining,restOk,restNext⟩ := Outcome.next_success success
      rw [restNext] at success ⊢
      obtain ⟨kept,field,fieldRep,erasure,recursiveRep,observed⟩ :=
        field_observes binderProgress indicesProgress normalSound onBase domainRep (field_absent checked domainRep) selectedOk
      have nextLength (erased : Bool) : (observedPrefix ++ [field]).length = ((erased,selected) :: context).length := by
        simp only [List.length_append,List.length_cons,List.length_nil,prefixLength]
      obtain ⟨restKept,fields,indices,remainingFields,remainingRec,remainingIndices,restObserved⟩ :=
        ih (onBase.trans kept) (bodyRep.frame kept) (nextLength _) restOk
      simp only [Except.ok.injEq] at success
      subst roots
      obtain ⟨flag,domainTerm,marker⟩ := field
      change flag = _ at erasure
      subst flag
      refine ⟨kept.trans restKept,_ :: fields,indices,.cons (fieldRep.frame restKept) remainingFields,?_,remainingIndices,?_⟩
      · have nested : OptionalIndexRep _ recursive marker := recursiveRep.frame restKept
        cases nested
        · simpa only [recursiveAt,List.zipIdx_cons,List.filterMap_cons,Option.map_none,List.length_cons] using remainingRec
        · rename_i held
          exact .cons held remainingRec
      · exact .field observed (by simpa only [List.append_assoc,List.singleton_append] using restObserved)
  | result width arity checked params =>
    cases fuel with
    | zero => cases success
    | succ fuel =>
      obtain ⟨refs,read,represented⟩ := result_roots source
      simp only [run,read,ite_true] at success ⊢
      obtain ⟨⟨⟩,_,next⟩ := Outcome.next_success success
      rw [next] at success ⊢
      obtain ⟨out,normalized,shape⟩ := mapped_success success
      subst roots
      have checked := indicesProgress context state root refs
      obtain ⟨kept,_,_,values,resultRep,converted⟩ :=
        NativeCorePureComputationNormal.visitOperands_relatesFrom (onBase.trans checked.kept) (represented.frame checked.kept)
          normalSound normalized
      exact ⟨checked.kept.trans kept,[],values,.nil,.nil,resultRep,
        by simpa only [List.append_nil] using (ObservedTelescope.result (fields := observedPrefix) (converted_indices converted))⟩

/-- An admitted written proposition constructor yields the signature
used by the subsequent case checks. -/
theorem observed_signature
    (checked : UnifiedProgram.Families.TelescopeChecked prior family decl [] written trusted)
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena root written)
    (success : (run checkBinder checkIndices normal family fuel [] state root).result = .ok roots) :
    let after := (run checkBinder checkIndices normal family fuel [] state root).state.arena
    Prefix state.arena after ∧ ∃ signature, SignatureRep after roots signature ∧
      ObservedTelescope env family [] written signature := by
  obtain ⟨kept,fields,indices,fieldRep,recur,result,observed⟩ :=
    observes_checked_telescope (observedPrefix := []) checked binderProgress indicesProgress normalSound
      onBase source rfl success
  exact ⟨kept,⟨fields,indices⟩,⟨fieldRep,recur,result⟩,observed⟩

/-- A successful observed signature is the one used for the expected case
type of its admitted source constructor. -/
theorem checked_signature_at
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (selected : familyRows[family]? = some row) (read : row.constructors[(constructor : Nat)]? = some root)
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (success : (run checkBinder checkIndices normal family fuel [] state root).result = .ok roots) :
    let after := (run checkBinder checkIndices normal family fuel [] state root).state.arena
    Prefix state.arena after ∧
      ∃ entry signature, env.families[family]? = some entry ∧ entry.signatures[constructor]? = some signature ∧
        NativeCoreGhostPropCases.CheckedSignature env after roots signature := by
  obtain ⟨entry,signature,source,_,_,found,signatureFound,_,_,sourceRep,extension,telescope⟩ :=
    NativeCoreConstructorTelescopeAlignment.checked_constructor_source history rows selected read
  obtain ⟨kept,observed,graph,replayed⟩ :=
    observed_signature telescope binderProgress indicesProgress normalSound onBase sourceRep success
  have converted := NativeCorePropSignatureAuthentication.checked_telescope extension replayed telescope .nil
  exact ⟨kept,entry,signature,found,signatureFound,⟨observed,graph,converted⟩⟩

def runTable (checkBinder : CheckBinder) (checkIndices : CheckIndices) (normal : Normalize)
    (family fuel : Nat) : List Nat → State → Outcome (List SignatureRoots)
  | [],state => ⟨state,.ok []⟩
  | root :: remaining,state =>
    (run checkBinder checkIndices normal family fuel [] state root).next fun parsed signature =>
      (runTable checkBinder checkIndices normal family fuel remaining parsed).next fun after others =>
        ⟨after,.ok (signature :: others)⟩

theorem runTable_progress
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (runTable checkBinder checkIndices normal family fuel sources state) := by
  induction sources generalizing state with
  | nil => exact Progress.atState _ _
  | cons root rest ih =>
    exact (run_progress binderProgress indicesProgress normalProgress).next fun _ =>
      ih.next (fun _ => Progress.atState _ _)

private theorem next_entry {α : Type} {entries : List α} {index : Nat} {first : α} {rest : List α}
    (present : entries.drop index = first :: rest) :
    entries[index]? = some first ∧ entries.drop (index+1) = rest := by
  constructor
  · have read := congrArg (fun (items : List α) => items[0]?) present
    simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] using read
  · have dropped := congrArg (List.drop 1) present
    simpa only [List.drop_drop,List.drop_succ_cons,List.drop_zero,Nat.add_comm 1] using dropped

private theorem table_from
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (read : familyRows[family]? = some row) (found : env.families[family]? = some entry)
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (sourceTail : row.constructors.drop offset = sources) (signatureTail : entry.signatures.drop offset = signatures)
    (width : sources.length = signatures.length)
    (success : (runTable checkBinder checkIndices normal family fuel sources state).result = .ok roots) :
    let after := (runTable checkBinder checkIndices normal family fuel sources state).state.arena
    Prefix state.arena after ∧ FamilyEnvironment.RelList (NativeCoreGhostPropCases.CheckedSignature env after) roots signatures := by
  induction sources generalizing signatures offset state roots with
  | nil =>
    have empty : signatures = [] := List.length_eq_zero_iff.mp width.symm
    rw [empty] at signatureTail ⊢
    cases success
    exact ⟨.refl _,.nil⟩
  | cons source sources ih =>
    cases signatures with
    | nil => simp at width
    | cons expected signatures =>
      unfold runTable at success ⊢
      obtain ⟨selected,selectedOk,entered⟩ := Outcome.next_success success
      rw [entered] at success ⊢
      obtain ⟨remaining,remainingOk,continued⟩ := Outcome.next_success success
      rw [continued] at success ⊢
      cases success
      obtain ⟨sourceAt,sourceNext⟩ := next_entry sourceTail
      obtain ⟨expectedAt,expectedNext⟩ := next_entry signatureTail
      obtain ⟨kept,observedEntry,observedSignature,observedFound,observedAt,header⟩ :=
        checked_signature_at history rows read sourceAt binderProgress indicesProgress normalSound onBase selectedOk
      have sameEntry := Option.some.inj (found.symm.trans observedFound)
      subst observedEntry
      have sameSignature := Option.some.inj (expectedAt.symm.trans observedAt)
      subst observedSignature
      obtain ⟨through,tail⟩ := ih (NativeCoreGhostDataCases.families_frame rows kept) (onBase.trans kept)
        sourceNext expectedNext (Nat.succ.inj width) remainingOk
      obtain ⟨compared,represented,related⟩ := header.represented
      exact ⟨kept.trans through,.cons ⟨compared,represented.frame through,related⟩ tail⟩

/-- Replaying the native declaration's constructor order supplies a
complete checked table for proposition elimination in the resulting arena. -/
theorem runTable_refines
    (history : ScopedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env)
    (rows : RepresentsFamilies state.arena familyRows familyTerms)
    (read : familyRows[family]? = some row) (found : env.families[family]? = some entry)
    (binderProgress : ∀ ctx state root erased, Progress limit state (checkBinder ctx state root erased))
    (indicesProgress : ∀ ctx state root refs, Progress limit state (checkIndices ctx state root refs))
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal) (onBase : Prefix base state.arena)
    (success : (runTable checkBinder checkIndices normal family fuel row.constructors state).result = .ok roots) :
    let after := (runTable checkBinder checkIndices normal family fuel row.constructors state).state.arena
    Prefix state.arena after ∧
      FamilyEnvironment.RelList (NativeCoreGhostPropCases.CheckedSignature env after) roots entry.signatures := by
  have widths := NativeCoreConstructorTelescopeAlignment.checked_family_widths history rows read found
  exact table_from history rows read found binderProgress indicesProgress normalSound onBase
    List.drop_zero List.drop_zero widths.2 success

end Jihoo.NativeKernel.NativeCorePropSignatureReplay
