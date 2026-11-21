import Jihoo.NativeCoreDataCaseTelescope
import Jihoo.NativeCoreDataMotiveDomain
import Jihoo.NativeCoreCaseNormal

/-! Structural data recursion starts from the generated nonrecursive
case. Its raw recursive field heads determine the erased binders and
the additional dependent hypotheses. -/
namespace Jihoo.NativeKernel.NativeCoreDataRecursionCase

open NativeArena Environment NativeCoreGraph
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress)
open NativeCoreShiftedApplications (shiftRoot shift_progress shift_refines)
open NativeCorePropCaseType (FieldsRep RecursiveRep wrapFields wrapFields_progress wrapFields_refines)
open NativeCoreCaseStrict (append append_progress append_refines)
open NativeCoreDataMotiveDomain (addVariable variable_progress variable_refines)
open NativeCoreCaseNormal (represented_drop)

structure CasePlan where
  fields : List (Bool × Nat)
  recursive : List (Nat × List Nat)
  terminal : Nat

private def prepend (arena : Arena) (family position : Nat) (erased : Bool) (domain : Nat) (tail : CasePlan) : CasePlan :=
  match arena[domain]? with
  | some (.node (.ind found _) indices) =>
    if found = family then ⟨(true,domain) :: tail.fields,(position,indices) :: tail.recursive,tail.terminal⟩
    else {tail with fields := (erased,domain) :: tail.fields}
  | _ => {tail with fields := (erased,domain) :: tail.fields}

def readPlan (arena : Arena) (family : Nat) : Nat → Nat → Nat → CasePlan
  | 0,_,root => ⟨[],[],root⟩
  | fuel+1,position,root =>
    match arena[root]? with
    | some (.node (.pi erased) [domain,body]) =>
      prepend arena family position erased domain (readPlan arena family fuel (position+1) body)
    | _ => ⟨[],[],root⟩

def markRecursive (family : Nat) (field : Field) : Field :=
  match field.domain with
  | .node (.ind actual _) indices =>
    if actual = family then ⟨true,field.domain,some indices⟩ else ⟨field.erased,field.domain,none⟩
  | _ => ⟨field.erased,field.domain,none⟩

private def recursiveAt (offset : Nat) (fields : List Field) : List (Nat × List Term) :=
  (fields.zipIdx offset).filterMap fun (field,position) => field.recursive.map fun indices => (position,indices)

structure PlanRep (arena : Arena) (offset : Nat) (plan : CasePlan) (fields : List Field) (body : Term) : Prop where
  fieldsRep : FieldsRep arena plan.fields fields
  recursiveRep : RecursiveRep arena plan.recursive (recursiveAt offset fields)
  bodyRep : Represents arena plan.terminal body

private theorem prepend_refines (domainRep : Represents arena domain field.domain)
    (tail : PlanRep arena (position+1) plan fields body) :
    PlanRep arena position (prepend arena family position field.erased domain plan)
      (markRecursive family field :: fields) body := by
  obtain ⟨erased,T,marker⟩ := field
  cases domainRep with
  | var read =>
    simp only [prepend,read,markRecursive]
    refine ⟨FieldsRep.cons (field := ⟨erased,.var _,none⟩) (.var read) tail.fieldsRep,?_,tail.bodyRep⟩
    exact tail.recursiveRep
  | @node domain op refs values read width children =>
    have represented : Represents arena domain (.node op values) := .node read width children
    cases op
    case ind found arity =>
      by_cases same : found = family
      · subst found
        simp only [prepend,read,markRecursive,ite_true]
        refine ⟨FieldsRep.cons (field := ⟨true,_,some values⟩) represented tail.fieldsRep,?_,tail.bodyRep⟩
        exact .cons children tail.recursiveRep
      · simp only [prepend,read,markRecursive,same,ite_false]
        refine ⟨FieldsRep.cons (field := ⟨erased,_,none⟩) represented tail.fieldsRep,?_,tail.bodyRep⟩
        exact tail.recursiveRep
    all_goals
      simp only [prepend,read,markRecursive]
      refine ⟨FieldsRep.cons (field := ⟨erased,_,none⟩) represented tail.fieldsRep,?_,tail.bodyRep⟩
      exact tail.recursiveRep

/-- The source graph's field order and raw recursive indices determine the
read plan. The terminal application is the rebuilt motive result. -/
theorem readPlan_refines {fields : List Field} (backward : Backward arena) (inside : root < fuel)
    (source : Represents arena root (fields.foldr (fun field tail => .pi field.erased field.domain tail) (.app M value))) :
    PlanRep arena offset (readPlan arena family fuel offset root) (fields.map (markRecursive family)) (.app M value) := by
  induction fields generalizing fuel root offset with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases source with
      | node read width children =>
        simp only [readPlan,read,List.map_nil]
        exact ⟨.nil,.nil,.node read width children⟩
  | cons field fields ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases source with
      | node read width children =>
        cases children with
        | cons domain tail =>
          cases tail with
          | @cons bodyRoot bodyTerm refs values body last =>
            cases last
            have below : bodyRoot < root := backward root _ read bodyRoot (by simp [Node.references])
            simp only [readPlan,read,List.map_cons]
            exact prepend_refines domain (ih (by omega) body)

def hypotheses (limit depth params fields motive : Nat) (proof : Bool) :
    List (Nat × List Nat) → Nat → State → Nat → Outcome Nat
  | [],_,state,body => ⟨state,.ok body⟩
  | (position,indices) :: rest,offset,state,body =>
    (hypotheses limit depth params fields motive proof rest (offset+1) state body).next fun after suffix =>
      (NativeCoreShiftedApplications.run limit depth after motive (fields+offset) (fields+offset-position)
        (indices.drop params)).next fun indexed motiveApp =>
          (addVariable indexed (fields-1-position+offset)).next fun argument field =>
            (append argument .app [motiveApp,field]).next fun typed ih =>
              append typed (.pi proof) [ih,suffix]

theorem hypotheses_progress (recursive : List (Nat × List Nat)) (offset : Nat) (state : State) (body : Nat) :
    Progress limit state (hypotheses limit depth params fields motive proof recursive offset state body) := by
  induction recursive generalizing offset state body with
  | nil => exact Progress.atState _ _
  | cons field rest ih =>
    obtain ⟨index,indices⟩ := field
    exact (ih _ _ _).next fun _ =>
      NativeCoreShiftedApplications.run_progress.next fun _ =>
        (variable_progress (index := fields-1-index+offset)).next fun _ =>
          (append_progress _ _ _).next fun _ => append_progress _ _ _

/-- Hypothesis construction uses the original recursive field positions
and weakens each retained index from its own scope. -/
theorem hypotheses_refines (motiveRep : Represents state.arena motive M)
    (recursive : RecursiveRep state.arena roots fields) (bodyRep : Represents state.arena body final)
    (success : (hypotheses limit depth params total motive proof roots offset state body).result = .ok selected) :
    let after := (hypotheses limit depth params total motive proof roots offset state body).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (dataHypothesisTelescope params total offset fields proof M final) := by
  induction roots generalizing fields offset state body final selected with
  | nil =>
    cases recursive
    simp only [hypotheses,Except.ok.injEq] at success
    subst selected
    exact ⟨.refl _,id,bodyRep⟩
  | cons root roots ih =>
    cases recursive with
    | cons indicesRep remaining =>
      unfold hypotheses at success ⊢
      obtain ⟨suffix,tailOk,tailNext⟩ := Outcome.next_success success
      rw [tailNext] at success ⊢
      obtain ⟨motiveApp,motiveOk,motiveNext⟩ := Outcome.next_success success
      rw [motiveNext] at success ⊢
      obtain ⟨field,fieldOk,fieldNext⟩ := Outcome.next_success success
      rw [fieldNext] at success ⊢
      obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
      rw [expectedNext] at success ⊢
      obtain ⟨tailKept,tailBack,tailRep⟩ := ih motiveRep remaining bodyRep tailOk
      obtain ⟨motiveKept,motiveBack,appRep⟩ := NativeCoreShiftedApplications.run_refines
        (motiveRep.frame tailKept) (represented_drop (indicesRep.frame tailKept) params) motiveOk
      obtain ⟨fieldKept,fieldBack,fieldRep⟩ := variable_refines fieldOk
      obtain ⟨argKept,argBack,expectedRep⟩ :=
        append_refines (.cons (appRep.frame fieldKept) (.cons fieldRep .nil)) rfl expectedOk
      have beforePi := motiveKept.trans (fieldKept.trans argKept)
      obtain ⟨piKept,piBack,finalRep⟩ := append_refines (.cons expectedRep (.cons (tailRep.frame beforePi) .nil)) rfl success
      refine ⟨tailKept.trans (beforePi.trans piKept),piBack ∘ argBack ∘ fieldBack ∘ motiveBack ∘ tailBack,?_⟩
      simpa only [dataHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,dataHypothesisType,Term.pi,Term.app,
        Nat.add_assoc] using finalRep

def build (limit depth params motive : Nat) (proof : Bool) (state : State) (plan : CasePlan) : Outcome Nat :=
  (shiftRoot limit depth state plan.terminal plan.recursive.length).next fun shifted residual =>
    (hypotheses limit depth params plan.fields.length motive proof plan.recursive 0 shifted residual).next
      fun withHypotheses body => wrapFields plan.fields withHypotheses body

def run (limit depth : Nat) (state : State) (family constructor params motive written : Nat)
    (parameters : List Nat) (proof : Bool) : Outcome Nat :=
  (NativeCoreDataCaseTelescope.run limit depth state family constructor params motive written parameters).next fun built base =>
    build limit depth params motive proof built (readPlan built.arena family (built.arena.size+1) 0 base)

theorem build_progress : Progress limit state (build limit depth params motive proof state plan) :=
  shift_progress.next fun residual =>
    (hypotheses_progress _ _ _ residual).next (fun body => wrapFields_progress _ _ body)

theorem run_progress :
    Progress limit state (run limit depth state family constructor params motive written parameters proof) :=
  NativeCoreDataCaseTelescope.run_progress.next (fun _ => build_progress)

private theorem recursive_width (represented : RecursiveRep arena roots fields) :
    roots.length = fields.length := by
  induction represented with
  | nil => rfl
  | cons _ _ tail => exact congrArg Nat.succ tail

private theorem frame_recursive (represented : RecursiveRep before roots fields) (kept : Prefix before after) :
    RecursiveRep after roots fields := by
  induction represented with
  | nil => exact .nil
  | cons first _ tail => exact .cons (first.frame kept) tail

theorem build_refines (motiveRep : Represents state.arena motive M)
    (bodyRep : Represents state.arena plan.terminal source)
    (fieldRep : FieldsRep state.arena plan.fields fields)
    (recursive : RecursiveRep state.arena plan.recursive indices)
    (success : (build limit depth params motive proof state plan).result = .ok selected) :
    let after := (build limit depth params motive proof state plan).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      Represents after selected (fields.foldr (fun field body => .pi field.erased field.domain body)
        (dataHypothesisTelescope params fields.length 0 indices proof M
          (source.rename (fun index => index + indices.length)))) := by
  unfold build at success ⊢
  obtain ⟨residual,shifted,shiftNext⟩ := Outcome.next_success success
  rw [shiftNext] at success ⊢
  obtain ⟨body,built,builtNext⟩ := Outcome.next_success success
  rw [builtNext] at success ⊢
  obtain ⟨shiftKept,shiftBackward,shiftedRep⟩ := shift_refines bodyRep shifted
  obtain ⟨hypKept,hypBackward,bodyResult⟩ := hypotheses_refines
    (motiveRep.frame shiftKept) (frame_recursive recursive shiftKept) shiftedRep built
  obtain ⟨fieldKept,fieldBackward,closed⟩ := wrapFields_refines
    (fieldRep.frame (shiftKept.trans hypKept)) bodyResult success
  exact ⟨shiftKept.trans (hypKept.trans fieldKept),fieldBackward ∘ hypBackward ∘ shiftBackward,
    by simpa only [fieldRep.length_eq,recursive_width recursive] using closed⟩

private theorem represented_inside (source : Represents arena root term) : root < arena.size := by
  cases source with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1

theorem run_refines (backward : Backward state.arena)
    (motiveRep : Represents state.arena motive M) (source : Represents state.arena written signature)
    (parametersRep : RepresentsList state.arena parameters values)
    (success : (run limit depth state family constructor params motive written parameters proof).result = .ok selected) :
    let after := (run limit depth state family constructor params motive written parameters proof).state.arena
    Prefix state.arena after ∧ Backward after ∧
      ∃ (fields : List Field) (resultFamily arity : Nat) (indices : List Term) (opened : Term),
        instantiateParameters values signature = some opened ∧
        opened = fields.foldr (fun field tail => .pi field.erased field.domain tail) (.node (.ind resultFamily arity) indices) ∧
        let marked := fields.map (markRecursive family)
        let recursive := recursiveAt 0 marked
        Represents after selected (marked.foldr (fun field tail => .pi field.erased field.domain tail)
          (dataHypothesisTelescope params fields.length 0 recursive proof M
            ((dataCaseResult family constructor params fields.length 0 values M indices).rename (fun i => i+recursive.length)))) := by
  unfold run at success ⊢
  obtain ⟨base,built,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,baseBackward,fields,resultFamily,arity,indices,opened,instantiated,shape,caseRep⟩ :=
    NativeCoreDataCaseTelescope.run_refines source motiveRep parametersRep built
  have within := Nat.lt_succ_of_lt (represented_inside caseRep)
  have plan := readPlan_refines (family := family) (offset := 0) (baseBackward backward) within caseRep
  obtain ⟨suffix,finalBackward,builtRep⟩ := build_refines
    (motiveRep.frame kept) plan.bodyRep plan.fieldsRep plan.recursiveRep success
  exact ⟨kept.trans suffix,finalBackward (baseBackward backward),fields,resultFamily,arity,indices,opened,instantiated,shape,
    by simpa [List.length_map,Nat.succ_eq_add_one,dataCaseResult] using builtRep⟩

/-- The checked native example erases the recursive field in both result
modes. Only the hypothesis binder changes erasure with the result sort. -/
theorem recursion_case_matches_native :
    let arena : Arena := #[.node (.natural 2) [],.var 0,.node (.ind 0 1) [0],.node (.pi false) [2,2],
      .node .u64 [],.node .u64 [],.node .u64 [],.node .u64 [],.node .u64 [],.node .u64 []]
    let rows := arena ++ #[.var 1,.node .app [10,0],.var 0,.node (.con 0 1 1) [12],.node .app [11,13],
      .node (.pi false) [2,14],.var 2,.node .app [16,0],.var 1,.node (.con 0 1 1) [18],.node .app [17,19],
      .var 1,.node .app [21,0],.var 0,.node .app [22,23]]
    run 9 16 ⟨arena,0⟩ 0 1 0 1 3 [] false =
        ⟨⟨rows ++ #[.node (.pi false) [24,20],.node (.pi true) [2,25]],9⟩,.ok 26⟩ ∧
      run 9 16 ⟨arena,0⟩ 0 1 0 1 3 [] true =
        ⟨⟨rows ++ #[.node (.pi true) [24,20],.node (.pi true) [2,25]],9⟩,.ok 26⟩ ∧
      run 8 16 ⟨arena,0⟩ 0 1 0 1 3 [] true =
        ⟨⟨rows.extract 0 22,9⟩,.error (.substitution (.tick (.stepLimit 0)))⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreDataRecursionCase
