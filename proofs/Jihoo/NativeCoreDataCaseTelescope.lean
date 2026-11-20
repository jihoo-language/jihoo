import Jihoo.NativeCoreDataCaseResult

/-! Native data_case_type substitutes actual parameters into the written
closed telescope. It then reads the remaining field binders and result
without normalizing either. -/
namespace Jihoo.NativeKernel.NativeCoreDataCaseTelescope

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCorePropCaseType (FieldsRep)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def substitute (limit depth : Nat) (state : State) (root value : Nat) : Outcome Nat :=
  let changed := NativeCoreTransformExact.substitute limit depth state root value
  ⟨changed.state,changed.result.mapError .substitution⟩

def instantiate (limit depth : Nat) : List Nat → State → Nat → Outcome Nat
  | [],state,root => ⟨state,.ok root⟩
  | param :: rest,state,root =>
    match state.arena[root]? with
    | some (.node (.pi _) [_,body]) =>
      (substitute limit depth state body param).next fun after result => instantiate limit depth rest after result
    | _ => reject state root

structure Telescope where
  fields : List (Bool × Nat)
  family : Nat
  arity : Nat
  indices : List Nat

def read (arena : Arena) : Nat → Nat → Option Telescope
  | 0,_ => none
  | fuel+1,root =>
    match arena[root]? with
    | some (.node (.pi erased) [domain,body]) =>
      (read arena fuel body).map fun telescope => {telescope with fields := (erased,domain) :: telescope.fields}
    | some (.node (.ind family arity) indices) => some ⟨[],family,arity,indices⟩
    | _ => none

def run (limit depth : Nat) (state : State) (family constructor params motive written : Nat) (arguments : List Nat) : Outcome Nat :=
  if arguments.length = params then
    (instantiate limit depth arguments state written).next fun after opened =>
      match read after.arena (after.arena.size+1) opened with
      | some telescope => NativeCoreDataCaseResult.run limit depth after family constructor params motive
          arguments telescope.indices telescope.fields
      | none => reject after opened
  else reject state written

private theorem substitute_ok (accepted : (substitute limit depth state root value).result = .ok selected) :
    (NativeCoreTransformExact.substitute limit depth state root value).result = .ok selected := by
  unfold substitute at accepted
  cases computed : (NativeCoreTransformExact.substitute limit depth state root value).result <;>
    simp only [computed,Except.mapError,reduceCtorEq,Except.ok.injEq] at accepted ⊢
  exact accepted

private theorem substitute_progress : Progress limit state (substitute limit depth state root value) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.replace .substitute value) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ accepted =>
    progress.accepted room _ (substitute_ok accepted)⟩

theorem instantiate_progress : Progress limit state (instantiate limit depth parameters state root) := by
  induction parameters generalizing state root with
  | nil => exact Progress.atState _ _
  | cons p ps ih =>
    unfold instantiate
    split
    · exact substitute_progress.next fun _ => ih
    · exact Progress.atState _ _

theorem run_progress : Progress limit state (run limit depth state family constructor params motive written arguments) := by
  unfold run
  split
  · exact instantiate_progress.next (fun _ => by
    split
    · exact NativeCoreDataCaseResult.run_progress
    · exact Progress.atState _ _)
  · exact Progress.atState _ _

private theorem represented_pi (source : Represents arena root term)
    (found : arena[root]? = some (.node (.pi erased) [domain,body])) :
    ∃ D R, Represents arena domain D ∧ Represents arena body R ∧ term = .pi erased D R := by
  cases source with
  | var read => rw [found] at read; cases read
  | node read _ children =>
    rw [found] at read
    cases read
    cases children with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail
        exact ⟨_,_,first,second,rfl⟩

/-- Each graph substitution is the capture-avoiding instantiation of the
next parameter in the actual written telescope. -/
theorem instantiate_refines (source : Represents state.arena root term) (params : RepresentsList state.arena parameters values)
    (success : (instantiate limit depth parameters state root).result = .ok selected) :
    let after := (instantiate limit depth parameters state root).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ opened, Represents after selected opened ∧ instantiateParameters values term = some opened := by
  induction parameters generalizing state root term values selected with
  | nil =>
    cases params
    cases success
    exact ⟨.refl _,id,term,source,rfl⟩
  | cons param params ih =>
    cases params with
    | cons actual rest =>
      unfold instantiate at success ⊢
      split at success
      · rename_i erased domain body found
        obtain ⟨first,firstOk,firstNext⟩ := Outcome.next_success success
        rw [firstNext] at success ⊢
        obtain ⟨D,R,_,bodyRep,rfl⟩ := represented_pi source found
        obtain ⟨kept,back,substituted⟩ := NativeCoreTransformExact.substitute_refines bodyRep actual (substitute_ok firstOk)
        obtain ⟨later,laterBack,opened,represented,expanded⟩ := ih substituted (rest.frame kept) success
        exact ⟨kept.trans later,laterBack ∘ back,opened,represented,expanded⟩
      · cases success

/-- The unmetered telescope scan preserves the constructor's written
field flags and the original result-index roots. -/
theorem read_refines (source : Represents arena root term) (found : read arena fuel root = some telescope) :
    ∃ fields indices, FieldsRep arena telescope.fields fields ∧ RepresentsList arena telescope.indices indices ∧
      term = fields.foldr (fun field rest => .pi field.erased field.domain rest)
        (.node (.ind telescope.family telescope.arity) indices) := by
  induction fuel generalizing root term telescope with
  | zero => cases found
  | succ fuel ih =>
    unfold read at found
    split at found
    · rename_i erased domain body seen
      cases result : read arena fuel body with
      | none => simp only [result,Option.map_none,reduceCtorEq] at found
      | some prior =>
        simp only [result,Option.map_some,Option.some.injEq] at found
        subst telescope
        obtain ⟨_,_,domainRep,bodyRep,rfl⟩ := represented_pi source seen
        obtain ⟨fields,indices,held,represented,shape⟩ := ih bodyRep result
        exact ⟨_,indices,.cons (field := ⟨erased,_,none⟩) domainRep held,represented,congrArg (Term.pi erased _) shape⟩
    · rename_i family arity indices seen
      cases found
      cases source with
      | var found => rw [seen] at found; cases found
      | node found _ children =>
        rw [seen] at found
        cases found
        exact ⟨[],_,.nil,children,rfl⟩
    · cases found

/-- Successful case construction identifies the instantiated source
telescope and the representation of the generated branch at that exact
telescope. The graph never infers a replacement field annotation. -/
theorem run_refines (source : Represents state.arena written ctor) (motiveRep : Represents state.arena motive M)
    (parameterRep : RepresentsList state.arena arguments parameters)
    (success : (run limit depth state family constructor params motive written arguments).result = .ok selected) :
    let after := (run limit depth state family constructor params motive written arguments).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ (fields : List Field) (resultFamily arity : Nat) (indices : List Term) (opened : Term),
        instantiateParameters parameters ctor = some opened ∧
        opened = fields.foldr (fun field rest => .pi field.erased field.domain rest) (.node (.ind resultFamily arity) indices) ∧
        Represents after selected (fields.foldr (fun field rest => .pi field.erased field.domain rest)
          (dataCaseResult family constructor params fields.length 0 parameters M indices)) := by
  unfold run at success ⊢
  split at success
  · rename_i correct
    simp only [ite_eq_left correct]
    obtain ⟨opened,openedOk,next⟩ := Outcome.next_success success
    rw [next] at success ⊢
    obtain ⟨kept,backward,raw,expanded,through⟩ := instantiate_refines source parameterRep openedOk
    split at success
    · rename_i telescope found
      obtain ⟨fields,indices,fieldsRep,indicesRep,observed⟩ := read_refines expanded found
      obtain ⟨resultKept,resultBack,result⟩ := NativeCoreDataCaseResult.run_refines
        (motiveRep.frame kept) (parameterRep.frame kept) indicesRep fieldsRep success
      exact ⟨kept.trans resultKept,resultBack ∘ backward,fields,telescope.family,telescope.arity,indices,raw,
        through,observed,result⟩
    · cases success
  · cases success

/-- The native example substitutes the parameter under one written
field, then builds the branch with the recreated constructor value. -/
theorem one_parameter_one_field_matches_native_case :
    let input : Arena := #[.node (.natural 2) [],.node .u64 [],.var 0,.var 1,.node .i64 [],
      .node (.ind 0 2) [3,0],.node (.pi false) [4,5],.node (.pi true) [1,6],
      .node .u64 [],.node .u64 [],.node .u64 [],.node .u64 []]
    let checked := run 8 16 ⟨input,0⟩ 0 0 1 2 7 [2]
    let short := run 7 16 ⟨input,0⟩ 0 0 1 2 7 [2]
    checked = ⟨⟨input ++ #[.var 1,.node (.ind 0 2) [12,0],.node (.pi false) [4,13],
      .var 1,.node .app [15,0],.var 1,.var 0,.node (.con 0 0 2) [17,18],
      .node .app [16,19],.node (.pi false) [4,20]],8⟩,.ok 21⟩ ∧
      short.state.steps = 8 ∧ short.state.arena.size = 17 := by cbv

end Jihoo.NativeKernel.NativeCoreDataCaseTelescope
