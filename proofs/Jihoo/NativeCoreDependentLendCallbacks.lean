import Jihoo.NativeCoreGhostTypeRequirement

/-! The dependent lend branch specializes the original reader and
continuation. The same owner root is borrowed in the reader and shifted
under the result binder before being returned to the continuation. -/
namespace Jihoo.NativeKernel.NativeCoreDependentLendCallbacks

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreCaseStrict (append append_progress append_refines)

structure Callbacks where
  domain : Nat
  readerBody : Nat
  first : Nat
  again : Nat
  resumeBody : Nat

structure Prepared where
  domain : Nat
  reader : Nat
  continuation : Nat

private def relevantLambda (arena : Arena) (root : Nat) : Option (Nat × Nat) :=
  match arena[root]? with
  | some (.node (.lam false) [domain,body]) => some (domain,body)
  | _ => none

def select (arena : Arena) (owner reader continuation : Nat) : Option Callbacks :=
  match arena[owner]? with
    | some (.var _) => do
      let (domain,read) ← relevantLambda arena reader
      let (first,inner) ← relevantLambda arena continuation
      let (again,resume) ← relevantLambda arena inner
      some ⟨domain,read,first,again,resume⟩
    | _ => none

private def mapped (outcome : NativeCoreTransformExact.Outcome Nat) : Outcome Nat :=
  ⟨outcome.state,outcome.result.mapError .substitution⟩

private theorem mapped_ok (success : (mapped outcome).result = .ok selected) : outcome.result = .ok selected := by
  cases status : outcome.result <;> simp only [mapped,status,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

private theorem mapped_progress (progress : NativeCoreTransformExact.Progress limit state outcome) :
    Progress limit state (mapped outcome) :=
  ⟨progress.kept,progress.monotone,progress.bounded,fun room _ success => progress.accepted room _ (mapped_ok success)⟩

def build (limit depth : Nat) (state : State) (owner : Nat) (found : Callbacks) : Outcome Prepared :=
  (append state .borrow [owner]).next fun borrowed borrow =>
    (mapped (NativeCoreTransformExact.substitute limit depth borrowed found.readerBody borrow)).next fun reading read =>
      (mapped (NativeCoreTransformExact.shift limit depth reading owner 1 0)).next fun shifted returned =>
        (mapped (NativeCoreTransformExact.substitute limit depth shifted found.resumeBody returned)).next fun resumed rest =>
          (append resumed (.lam false) [found.first,rest]).next fun after continuation =>
            ⟨after,.ok ⟨found.domain,read,continuation⟩⟩

def run (limit depth : Nat) (state : State) (owner reader continuation : Nat) : Outcome (Option Prepared) :=
  match select state.arena owner reader continuation with
  | some found => (build limit depth state owner found).next fun after prepared => ⟨after,.ok (some prepared)⟩
  | none => ⟨state,.ok none⟩

theorem build_progress : Progress limit state (build limit depth state owner found) := by
  unfold build
  apply (append_progress _ _ _).next
  intro borrow
  apply (mapped_progress (NativeCoreTransformExact.run_progress _ _ _ _ _ _)).next
  intro read
  apply (mapped_progress (NativeCoreTransformExact.run_progress _ _ _ _ _ _)).next
  intro returned
  apply (mapped_progress (NativeCoreTransformExact.run_progress _ _ _ _ _ _)).next
  intro rest
  exact (append_progress _ _ _).next (fun _ => Progress.atState _ _)

theorem run_progress : Progress limit state (run limit depth state owner reader continuation) := by
  unfold run
  split
  · exact build_progress.next (fun _ => Progress.atState _ _)
  · exact Progress.atState _ _

private theorem relevantLambda_refines
    (represented : Represents arena root term) (success : relevantLambda arena root = some (domain,body)) :
    ∃ A B, term = .lam false A B ∧ Represents arena domain A ∧ Represents arena body B := by
  unfold relevantLambda at success
  split at success
  · rename_i first rest read
    have same := Option.some.inj success
    cases same
    cases represented with
    | var found => rw [read] at found; cases found
    | node found _ children =>
      rw [read] at found
      cases found
      cases children with
      | cons firstRep tail =>
        cases tail with
        | cons bodyRep tail =>
          cases tail
          exact ⟨_,_,rfl,firstRep,bodyRep⟩
  · cases success

theorem select_refines
    (ownerRep : Represents arena owner x) (readerRep : Represents arena reader f)
    (continuationRep : Represents arena continuation g) (selected : select arena owner reader continuation = some shape) :
    ∃ index A read B C rest, x = .var index ∧ f = .lam false A read ∧ g = .lam false B (.lam false C rest) ∧
      Represents arena shape.domain A ∧ Represents arena shape.readerBody read ∧ Represents arena shape.first B ∧
      Represents arena shape.again C ∧ Represents arena shape.resumeBody rest := by
  unfold select at selected
  split at selected
  · rename_i index ownerRead
    obtain ⟨⟨domain,readerBody⟩,first,selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨firstType,inner⟩,second,selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨again,rest⟩,third,selected⟩ := Option.bind_eq_some_iff.mp selected
    cases selected
    obtain ⟨A,read,readerShape,domainRep,readRep⟩ := relevantLambda_refines readerRep first
    obtain ⟨B,nested,continuationShape,firstRep,innerRep⟩ := relevantLambda_refines continuationRep second
    obtain ⟨C,resume,nestedShape,againRep,resumeRep⟩ := relevantLambda_refines innerRep third
    refine ⟨index,A,read,B,C,resume,?_,readerShape,continuationShape.trans (congrArg (Term.lam false B) nestedShape),
      domainRep,readRep,firstRep,againRep,resumeRep⟩
    exact ownerRep.unique (.var ownerRead)
  · cases selected

/-- Every successful specialization retains the original reader annotation
and produces precisely the two capture-avoiding source substitutions. -/
theorem build_refines (ownerRep : Represents state.arena owner (.var index))
    (domainRep : Represents state.arena found.domain A) (readerRep : Represents state.arena found.readerBody readerTerm)
    (firstRep : Represents state.arena found.first B) (resumeRep : Represents state.arena found.resumeBody rest)
    (success : (build limit depth state owner found).result = .ok prepared) :
    let after := (build limit depth state owner found).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after prepared.domain A ∧
      Represents after prepared.reader (Lending.read (.var index) readerTerm) ∧
      Represents after prepared.continuation (Lending.restore (.var index) B rest) := by
  unfold build at success ⊢
  obtain ⟨lent,lentOk,lentNext⟩ := Outcome.next_success success
  rw [lentNext] at success ⊢
  obtain ⟨reading,readingOk,readingNext⟩ := Outcome.next_success success
  rw [readingNext] at success ⊢
  obtain ⟨ownerLift,shiftOk,shiftNext⟩ := Outcome.next_success success
  rw [shiftNext] at success ⊢
  obtain ⟨resumed,resumedOk,resumedNext⟩ := Outcome.next_success success
  rw [resumedNext] at success ⊢
  obtain ⟨continuation,continuationOk,continuationNext⟩ := Outcome.next_success success
  rw [continuationNext] at success ⊢
  cases success
  obtain ⟨borrowKept,borrowBack,borrowRep⟩ := append_refines (.cons ownerRep .nil) rfl lentOk
  obtain ⟨readKept,readBack,readRep⟩ := NativeCoreTransformExact.substitute_refines
    (readerRep.frame borrowKept) borrowRep (mapped_ok readingOk)
  have throughRead := borrowKept.trans readKept
  obtain ⟨shiftKept,shiftBack,_,shifted,shiftRep⟩ := NativeCoreTransformExact.shift_refines
    (ownerRep.frame throughRead) (mapped_ok shiftOk)
  have output : PartialRenaming.shift 1 0 (.var index) = some ((Term.var index).rename Nat.succ) := by
    rw [PartialRenaming.shift_nonnegative (by decide)]
    simp [PartialRenaming.raiseIndex,Term.rename,Nat.succ_eq_add_one]
  change PartialRenaming.shift 1 0 (.var index) = _ at shifted
  rw [output] at shifted
  cases shifted
  have throughShift := throughRead.trans shiftKept
  obtain ⟨resumedKept,resumedBack,resumedRep⟩ := NativeCoreTransformExact.substitute_refines
    (resumeRep.frame throughShift) shiftRep (mapped_ok resumedOk)
  have throughResume := throughShift.trans resumedKept
  obtain ⟨contKept,contBack,contRep⟩ := append_refines
    (.cons (firstRep.frame throughResume) (.cons resumedRep .nil)) rfl continuationOk
  have kept := throughResume.trans contKept
  exact ⟨kept,contBack ∘ resumedBack ∘ shiftBack ∘ readBack ∘ borrowBack,domainRep.frame kept,
    readRep.frame (shiftKept.trans (resumedKept.trans contKept)),contRep⟩

private def input : Arena := #[.var 0,.node (.natural 1) [],.node .buffer [1],.node .ref [2],
  .node (.natural 0) [],.node .decide [4,1],.node .index [0,4,5],.node (.lam false) [3,6],
  .node .i64 [],.var 1,.node .free [0,9],.node (.lam false) [2,10],.node (.lam false) [8,11],
  .node .lend [0,7,12],.node .ref [2]]

/-- The reader receives the borrowed original slot, and its result binder
still shadows the shifted owner when the continuation frees that owner. -/
theorem callback_graph_keeps_original_owner :
    let prepared := run 13 31 ⟨input,0⟩ 0 7 12
    prepared.state.steps = 13 ∧
      prepared.result.map (Option.map fun selected => (selected.domain,selected.reader,selected.continuation)) =
        .ok (some (3,16,20)) ∧
      prepared.state.arena = input ++ #[.node .borrow [0],.node .index [15,4,5],
        .var 1,.var 0,.node .free [17,18],.node (.lam false) [8,19]] := by cbv

end Jihoo.NativeKernel.NativeCoreDependentLendCallbacks
