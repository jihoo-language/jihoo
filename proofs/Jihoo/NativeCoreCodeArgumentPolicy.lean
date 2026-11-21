import Jihoo.NativeCoreCodeKind
import Jihoo.NativeCoreCodePlain
import Jihoo.NativeCoreGhostLiteralAddition

/-! Runtime App applies the first-order argument policy after checking the
argument against the original product domain and before substitution. -/
namespace Jihoo.NativeKernel.NativeCoreCodeArgumentPolicy

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open EnvironmentDelta (expand)

private def reject (state : State) (arg : Nat) : Outcome Unit := ⟨state,.error (.outsideFragment arg)⟩

def run (normal : Nat → State → Nat → Outcome Nat) (env : Environment) (limit depth : Nat)
    (state : State) (domain argument : Nat) : Outcome Unit :=
  (NativeCoreCodeKind.classify (normal depth) state domain).next fun classified typeArgument =>
    if typeArgument then
      (NativeCoreCodeKind.firstOrder normal depth classified domain).next fun checked kind =>
        if kind then
          (NativeCoreCodePlain.run (normal depth) env limit depth checked argument).next fun inspected plain =>
            if plain then ⟨inspected,.ok ()⟩ else reject inspected argument
        else reject checked argument
    else ⟨classified,.ok ()⟩

theorem run_progress
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root)) :
    Progress limit state (run normal env limit depth state domain argument) := by
  unfold run
  apply (NativeCoreCodeKind.classify_progress (normalProgress depth)).next
  intro typeArgument
  split
  · apply (NativeCoreCodeKind.firstOrder_progress normalProgress).next
    intro kind
    split
    · exact (NativeCoreCodePlain.run_progress (normalProgress depth)).next
        (fun plain => by split <;> exact Progress.atState _ _)
    · exact Progress.atState _ _
  · exact Progress.atState _ _

/-- The domain and argument normalizer has discharged transparent global
references before the graph inspectors read the retained terms. -/
def GlobalFreeOutputs (normal : Nat → State → Nat → Outcome Nat) : Prop :=
  ∀ {depth state root selected term}, (normal depth state root).result = .ok selected →
    Represents (normal depth state root).state.arena selected term → globalFree term = true

private theorem classify_false_refines
    (normalSound : VisitsFrom base (ExpandedNormalization env) (normal depth))
    (free : GlobalFreeOutputs normal) (onBase : Prefix base state.arena)
    (source : Represents state.arena domain D)
    (success : (NativeCoreCodeKind.classify (normal depth) state domain).result = .ok false) :
    ∃ residual, RawLend.Conv env (expand env D) residual ∧ globalFree residual = true ∧ kindOf residual = false := by
  unfold NativeCoreCodeKind.classify at success
  obtain ⟨selected,selectedOk,next⟩ := Outcome.next_success success
  rw [next] at success
  obtain ⟨_,_,residual,represented,converted⟩ := normalSound onBase source selectedOk
  have freeResidual := free selectedOk represented
  have conversion := converted.converted
  rw [EnvironmentDelta.expand_globalFree ((globalFree_correct _).mp freeResidual)] at conversion
  have head := NativeCoreCodeKind.sortAt_represents represented
  rw [head,Except.ok.injEq] at success
  exact ⟨_,conversion,freeResidual,success⟩

/-- Successful policy checks establish the source application rule. The
kind witness and the normalized plain argument come from the actual scan. -/
theorem run_refines (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (free : GlobalFreeOutputs normal) (onBase : Prefix base state.arena)
    (domainRep : Represents state.arena domain D) (argRep : Represents state.arena argument A)
    (success : (run normal env limit depth state domain argument).result = .ok ()) :
    LoanTyping.applicationAllowed env false (expand env D) (expand env A) := by
  unfold run at success
  obtain ⟨typeArgument,classified,classificationNext⟩ := Outcome.next_success success
  rw [classificationNext] at success
  cases typeArgument with
  | false =>
    obtain ⟨residual,conversion,global,ordinary⟩ :=
      classify_false_refines (normalSound depth) free onBase domainRep classified
    exact .inr ⟨residual,conversion,global,.inl ordinary⟩
  | true =>
    simp only [ite_true] at success
    obtain ⟨kind,checked,nextKind⟩ := Outcome.next_success success
    rw [nextKind] at success
    cases kind with
    | false => cases success
    | true =>
      simp only [ite_true] at success
      obtain ⟨plain,observed,nextPlain⟩ := Outcome.next_success success
      rw [nextPlain] at success
      cases plain with
      | false => cases success
      | true =>
        let classified := NativeCoreCodeKind.classify (normal depth) state domain
        have first := NativeCoreCodeKind.classify_progress (state := state) (domain := domain)
          (normalProgress depth)
        obtain ⟨kept,_,normalKind,kindConverted,kindAccepted,kindFree⟩ :=
          NativeCoreCodeKind.firstOrder_refines normalSound (onBase.trans first.kept) (domainRep.frame first.kept) checked
        obtain ⟨val,argConv,valPlain⟩ := NativeCoreCodePlain.run_refines (normalSound depth)
          (onBase.trans (first.kept.trans kept)) (argRep.frame (first.kept.trans kept))
          (fun _ _ done held => free done held) observed
        exact .inr ⟨normalKind,kindConverted,kindFree,.inr ⟨kindAccepted,val,argConv,valPlain⟩⟩

/-- Ordinary values bypass the type-argument checks. A higher kind is
rejected before the argument is visited, while a buffer result reaches
the representation gate and is rejected there. -/
theorem policy_preserves_distinct_checking_schedules :
    let input : Arena := #[.node .u64 [],.node .i64 [],.node (.universe 0) [],
      .node (.pi false) [0,2],.node (.pi false) [1,2],.node (.lam false) [0,0],
      .node (.natural 1) [],.node .buffer [6],.node (.lam false) [0,7]]
    let normal := NativeCoreGhostLiteralAddition.run [] 0 14
    run normal empty 14 8 ⟨input,0⟩ 0 5 = ⟨⟨input,1⟩,.ok ()⟩ ∧
      run normal empty 14 8 ⟨input,0⟩ 3 5 = ⟨⟨input,13⟩,.ok ()⟩ ∧
      run normal empty 14 8 ⟨input,0⟩ 4 5 = ⟨⟨input,7⟩,.error (.outsideFragment 5)⟩ ∧
      run normal empty 14 8 ⟨input,0⟩ 3 8 = ⟨⟨input,14⟩,.error (.outsideFragment 8)⟩ := by cbv

/-- The kind and plain-argument phases keep all established graph references
backward. The metered scan itself allocates no nodes. -/
theorem run_backward (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (onBase : Prefix base state.arena) (backward : Backward state.arena)
    (domainRep : Represents state.arena domain D) (argRep : Represents state.arena argument A)
    (success : (run normal env limit depth state domain argument).result = .ok ()) :
    Backward (run normal env limit depth state domain argument).state.arena := by
  unfold run at success ⊢
  obtain ⟨typeArgument,classified,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨classKept,classBack,_,_,_⟩ :=
    NativeCoreCodeKind.classify_refines (normalSound depth) onBase domainRep classified
  cases typeArgument with
  | false => exact classBack backward
  | true =>
    simp only [ite_true] at success ⊢
    obtain ⟨kind,checked,nextKind⟩ := Outcome.next_success success
    rw [nextKind] at success ⊢
    cases kind with
    | false => cases success
    | true =>
      simp only [ite_true] at success ⊢
      obtain ⟨plain,observed,nextPlain⟩ := Outcome.next_success success
      rw [nextPlain] at success ⊢
      cases plain with
      | false => cases success
      | true =>
        simp only [ite_true]
        obtain ⟨kindKept,kindBack,_,_,_,_⟩ :=
          NativeCoreCodeKind.firstOrder_refines normalSound (onBase.trans classKept) (domainRep.frame classKept) checked
        have kept := classKept.trans kindKept
        unfold NativeCoreCodePlain.run at observed ⊢
        obtain ⟨_,normalized,after⟩ := Outcome.next_success observed
        rw [after,NativeCoreCodePlain.scan_arena]
        exact (normalSound depth (onBase.trans kept) (argRep.frame kept) normalized).2.1 (kindBack (classBack backward))

end Jihoo.NativeKernel.NativeCoreCodeArgumentPolicy
