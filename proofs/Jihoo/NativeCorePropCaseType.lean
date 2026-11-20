import Jihoo.NativeCoreShiftedApplications
import Jihoo.NativeEnvironmentBindingAlgebra

/-! Core.case_type first builds the motive at the constructor's result
indices. It then wraps the recursive hypotheses and original fields in
reverse declaration order, retaining their scopes and original graph roots. -/
namespace Jihoo.NativeKernel.NativeCorePropCaseType

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)

structure SignatureRoots where
  fields : List (Bool × Nat)
  recursive : List (Nat × List Nat)
  result : List Nat

inductive FieldsRep (arena : Arena) : List (Bool × Nat) → List Field → Prop where
  | nil : FieldsRep arena [] []
  | cons : Represents arena root field.domain → FieldsRep arena roots fields →
      FieldsRep arena ((field.erased,root) :: roots) (field :: fields)

inductive RecursiveRep (arena : Arena) : List (Nat × List Nat) → List (Nat × List Term) → Prop where
  | nil : RecursiveRep arena [] []
  | cons : RepresentsList arena refs indices → RecursiveRep arena roots fields →
      RecursiveRep arena ((position,refs) :: roots) ((position,indices) :: fields)

structure SignatureRep (arena : Arena) (roots : SignatureRoots) (signature : Signature) : Prop where
  fields : FieldsRep arena roots.fields signature.fields
  recursive : RecursiveRep arena roots.recursive (recursiveFields signature.fields)
  result : RepresentsList arena roots.result signature.result

private theorem FieldsRep.frame (represented : FieldsRep before roots fields) (kept : Prefix before after) :
    FieldsRep after roots fields := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.frame kept) ih

private theorem FieldsRep.length_eq (represented : FieldsRep arena roots fields) : roots.length = fields.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private theorem RecursiveRep.frame (represented : RecursiveRep before roots fields) (kept : Prefix before after) :
    RecursiveRep after roots fields := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.frame kept) ih

theorem SignatureRep.frame (represented : SignatureRep before roots signature) (kept : Prefix before after) :
    SignatureRep after roots signature :=
  ⟨represented.fields.frame kept,represented.recursive.frame kept,represented.result.frame kept⟩

private theorem RecursiveRep.length_eq (represented : RecursiveRep arena roots fields) : roots.length = fields.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private def wrapFields : List (Bool × Nat) → State → Nat → Outcome Nat
  | [], state, body => ⟨state,.ok body⟩
  | (erased,domain) :: rest, state, body =>
      (wrapFields rest state body).next fun after result => append after (.pi erased) [domain,result]

private def hypotheses (limit depth fields motive : Nat) : List (Nat × List Nat) → Nat → State → Nat → Outcome Nat
  | [], _, state, body => ⟨state,.ok body⟩
  | (position,indices) :: rest, offset, state, body =>
      (hypotheses limit depth fields motive rest (offset+1) state body).next fun after result =>
        (NativeCoreShiftedApplications.run limit depth after motive (fields+offset) (fields+offset-position) indices).next
          fun formed expected => append formed (.pi true) [expected,result]

def run (limit depth : Nat) (state : State) (motive : Nat) (roots : SignatureRoots) : Outcome Nat :=
  (NativeCoreShiftedApplications.run limit depth state motive
    (roots.fields.length+roots.recursive.length) roots.recursive.length roots.result).next fun after result =>
    (hypotheses limit depth roots.fields.length motive roots.recursive 0 after result).next fun withProofs telescope =>
      wrapFields roots.fields withProofs telescope

private theorem wrapFields_progress (fields : List (Bool × Nat)) (state : State) (body : Nat) :
    Progress limit state (wrapFields fields state body) := by
  induction fields generalizing state body with
  | nil => exact Progress.atState _ _
  | cons field rest ih =>
    obtain ⟨erased,domain⟩ := field
    exact (ih _ _).next (fun _ => append_progress _ _ _)

private theorem hypotheses_progress (recursive : List (Nat × List Nat)) (offset : Nat) (state : State) (body : Nat) :
    Progress limit state (hypotheses limit depth fields motive recursive offset state body) := by
  induction recursive generalizing offset state body with
  | nil => exact Progress.atState _ _
  | cons field rest ih =>
    obtain ⟨position,indices⟩ := field
    exact (ih _ _ _).next (fun _ => NativeCoreShiftedApplications.run_progress.next (fun _ => append_progress _ _ _))

theorem run_progress : Progress limit state (run limit depth state motive roots) :=
  NativeCoreShiftedApplications.run_progress.next
    (fun _ => (hypotheses_progress _ _ _ _).next (fun _ => wrapFields_progress _ _ _))

private theorem wrapFields_refines (represented : FieldsRep state.arena roots fields)
    (bodyRep : Represents state.arena body written)
    (success : (wrapFields roots state body).result = .ok selected) :
    let after := (wrapFields roots state body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (fields.foldr (fun field rest => .pi field.erased field.domain rest) written) := by
  induction roots generalizing fields state body written selected with
  | nil =>
    cases represented
    simp only [wrapFields,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,bodyRep⟩
  | cons root rest ih =>
    cases represented with
    | cons domainRep tail =>
      unfold wrapFields at success ⊢
      obtain ⟨inner,restOk,restNext⟩ := Outcome.next_success success
      rw [restNext] at success ⊢
      obtain ⟨restKept,restBack,innerRep⟩ := ih tail bodyRep restOk
      obtain ⟨newKept,newBack,output⟩ := append_refines (.cons (domainRep.frame restKept) (.cons innerRep .nil)) rfl success
      exact ⟨restKept.trans newKept,newBack ∘ restBack,output⟩

private theorem hypotheses_refines (motiveRep : Represents state.arena motive M)
    (recursive : RecursiveRep state.arena roots fields) (bodyRep : Represents state.arena body written)
    (success : (hypotheses limit depth total motive roots offset state body).result = .ok selected) :
    let after := (hypotheses limit depth total motive roots offset state body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (hypothesisTelescope total offset fields M written) := by
  induction roots generalizing fields offset state body written selected with
  | nil =>
    cases recursive
    simp only [hypotheses,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,bodyRep⟩
  | cons root rest ih =>
    cases recursive with
    | cons indicesRep restRep =>
      unfold hypotheses at success ⊢
      obtain ⟨inner,firstOk,firstNext⟩ := Outcome.next_success success
      rw [firstNext] at success ⊢
      obtain ⟨hypothesis,secondOk,secondNext⟩ := Outcome.next_success success
      rw [secondNext] at success ⊢
      obtain ⟨firstKept,firstBack,innerRep⟩ := ih motiveRep restRep bodyRep firstOk
      obtain ⟨secondKept,secondBack,hypothesisRep⟩ := NativeCoreShiftedApplications.run_refines
        (motiveRep.frame firstKept) (indicesRep.frame firstKept) secondOk
      obtain ⟨lastKept,lastBack,resultRep⟩ := append_refines (.cons hypothesisRep (.cons (innerRep.frame secondKept) .nil)) rfl success
      refine ⟨firstKept.trans (secondKept.trans lastKept),lastBack ∘ secondBack ∘ firstBack,?_⟩
      simpa only [hypothesisTelescope,List.zipIdx_cons,List.foldr_cons,hypothesisType,Term.pi,Nat.add_assoc] using resultRep

/-- The represented result is the full specified constructor case, including
all recursive hypotheses at their original relative field positions. -/
theorem run_refines (motiveRep : Represents state.arena motive M) (signature : SignatureRep state.arena roots checked)
    (success : (run limit depth state motive roots).result = .ok selected) :
    let after := (run limit depth state motive roots).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (propCaseType checked M) := by
  unfold run at success ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ⊢
  obtain ⟨withProofs,hypothesesOk,hypothesesNext⟩ := Outcome.next_success success
  rw [hypothesesNext] at success ⊢
  obtain ⟨resultKept,resultBack,resultRep⟩ := NativeCoreShiftedApplications.run_refines motiveRep signature.result resultOk
  obtain ⟨hypKept,hypBack,hypRep⟩ := hypotheses_refines
    (motiveRep.frame resultKept) (signature.recursive.frame resultKept) resultRep hypothesesOk
  have computed := signature.fields.length_eq
  have recursiveCount := signature.recursive.length_eq
  have kept := resultKept.trans hypKept
  obtain ⟨fieldsKept,fieldsBack,output⟩ := wrapFields_refines (signature.fields.frame kept) hypRep success
  refine ⟨kept.trans fieldsKept,fieldsBack ∘ hypBack ∘ resultBack,?_⟩
  simpa only [propCaseType_eq,← computed,← recursiveCount,Nat.add_assoc] using output

private def caseArena : Arena := #[.node (.natural 0) [],.node .u64 [],.var 0,.var 1,.var 2,
  .node (.ind 0 1) [0],.node (.ind 0 1) [2],.node (.ind 0 1) [3],.node (.ind 0 1) [4],
  .node (.pi true) [7,8],.node (.pi true) [6,9],.node (.pi false) [1,10]]

private def caseRoots : SignatureRoots := ⟨[(false,1),(true,6),(true,7)],[(1,[2]),(2,[3])],[4]⟩

/-- Two recursive fields retain different original index scopes. The last
hypothesis is built first, and all new hypotheses follow the original fields. -/
theorem two_recursive_fields_keep_shifted_indices :
    let built := run 6 16 ⟨caseArena,0⟩ 2 caseRoots
    built.state.steps = 6 ∧ built.result = .ok 25 ∧ built.state.arena = caseArena ++
      #[.var 5,.var 4,.node .app [12,13],.var 4,.var 3,.node .app [15,16],.node (.pi true) [17,14],
        .var 3,.var 2,.node .app [19,20],.node (.pi true) [21,18],.node (.pi true) [7,22],
        .node (.pi true) [6,23],.node (.pi false) [1,24]] := by cbv

end Jihoo.NativeKernel.NativeCorePropCaseType
