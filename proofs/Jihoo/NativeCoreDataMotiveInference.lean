import Jihoo.NativeCoreDataMotiveDomain
import Jihoo.NativeCoreGhostBackMotive
import Jihoo.NativeCoreGhostLiteralAddition

/-! A data motive takes only the nonparameter U64 indices and the family
value. The native checker compares the full family domain before it
normalizes the final sort and selects proof or data mode. -/
namespace Jihoo.NativeKernel.NativeCoreDataMotiveInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Visit next_progress requireTypes requireTypes_progress requireTypes_refines PairRetained)
open EnvironmentDelta (expand expandArgs)

structure Motive where
  proof : Bool
  compared : Nat × Nat

private def reject (state : State) (motive : Nat) : Outcome α := ⟨state,.error (.outsideFragment motive)⟩

private def product (arena : Arena) (root : Nat) : Option (Nat × Nat) :=
  match arena[root]? with
  | some (.node (.pi false) [domain,body]) => some (domain,body)
  | _ => none

def telescope (arena : Arena) : Nat → Nat → Option (Nat × Nat)
  | 0,root => product arena root
  | count+1,root => do
    let (index,body) ← product arena root
    if arena[index]? = some (.node .u64 []) then telescope arena count body else none

private def chosenSort : Option Node → Option Bool
  | some (.node .prop []) => some true
  | some (.node (.universe 0) []) => some false
  | _ => none

def run (normal : Visit) (limit depth : Nat) (state : State)
    (family params arity motive inferred : Nat) (values : List Nat) : Outcome Motive :=
  (normal state inferred).next fun exposed root =>
    match telescope exposed.arena (arity-params) root with
    | none => reject exposed motive
    | some (domain,sort) =>
      (NativeCoreDataMotiveDomain.run limit depth exposed family params arity values).next fun formed familyType =>
        (requireTypes normal limit depth formed domain familyType motive).next fun checked compared =>
          (normal checked sort).next fun after level =>
            match chosenSort after.arena[level]? with
            | some proof => ⟨after,.ok ⟨proof,compared⟩⟩
            | none => reject after motive

theorem run_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run normal limit depth state family params arity motive inferred values) := by
  unfold run
  apply next_progress (normalProgress _ _) room
  intro selected _ normalRoom
  split
  · exact Progress.atState _ _
  · apply next_progress NativeCoreDataMotiveDomain.run_progress normalRoom
    intro _ _ formedRoom
    apply next_progress (requireTypes_progress (fun state root _ => normalProgress state root) formedRoom) formedRoom
    intro _ _ _
    exact (normalProgress _ _).next (fun _ => by split <;> exact Progress.atState _ _)

private theorem product_refines (source : Represents arena root term) (found : product arena root = some (domain,body)) :
    ∃ A B, Represents arena domain A ∧ Represents arena body B ∧ term = .pi false A B := by
  unfold product at found
  split at found
  · rename_i a b read
    cases Option.some.inj found
    cases source with
    | var observed => rw [read] at observed; cases observed
    | node observed _ children =>
      rw [read] at observed
      cases observed
      cases children with
      | cons first tail =>
        cases tail with
        | cons second tail =>
          cases tail
          exact ⟨_,_,first,second,rfl⟩
  · cases found

private theorem word_rep (source : Represents arena root term) (found : arena[root]? = some (.node .u64 [])) :
    term = .u64 := by
  cases source with
  | var read => rw [found] at read; cases read
  | node read _ children => rw [found] at read; cases read; cases children; rfl

theorem telescope_refines (source : Represents arena root term)
    (found : telescope arena count root = some (domain,sort)) :
    ∃ A S, Represents arena domain A ∧ Represents arena sort S ∧ term = u64Telescope count (.pi false A S) := by
  induction count generalizing root term with
  | zero => exact product_refines source found
  | succ count ih =>
    unfold telescope at found
    obtain ⟨⟨index,root⟩,pair,selected⟩ := Option.bind_eq_some_iff.mp found
    change (if arena[index]? = some (.node .u64 []) then telescope arena count root else none) = some (domain,sort) at selected
    by_cases word : arena[index]? = some (.node .u64 [])
    · rw [ite_eq_left word] at selected
      obtain ⟨domain,tail,indexRep,tailRep,rfl⟩ := product_refines source pair
      cases word_rep indexRep word
      obtain ⟨A,S,domainRep,sortRep,rfl⟩ := ih tailRep selected
      exact ⟨A,S,domainRep,sortRep,rfl⟩
    · rw [ite_eq_right word] at selected
      cases selected

private theorem telescope_expand (env : Environment) (count : Nat) (term : Term) :
    expand env (u64Telescope count term) = u64Telescope count (expand env term) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [u64Telescope,Term.pi,Term.u64,expand,expandArgs,ih]

private theorem telescope_convert (converted : RawLend.Conv env A B) (count : Nat) :
    RawLend.Conv env (u64Telescope count A) (u64Telescope count B) := by
  induction count with
  | zero => exact converted
  | succ count ih => exact .node _ (.cons (.refl _) (.cons ih .nil))

private theorem chosenSort_refines (source : Represents arena root term)
    (selected : chosenSort arena[root]? = some proof) : term = loopSortTerm proof := by
  unfold chosenSort at selected
  split at selected
  · rename_i read
    cases selected
    cases source with
    | var observed => rw [read] at observed; cases observed
    | node observed _ children => rw [read] at observed; cases observed; cases children; rfl
  · rename_i read
    cases selected
    cases source with
    | var observed => rw [read] at observed; cases observed
    | node observed _ children => rw [read] at observed; cases observed; cases children; rfl
  · cases selected

private theorem sort_expand (env : Environment) (proof : Bool) :
    expand env (loopSortTerm proof) = loopSortTerm proof := by
  cases proof with
  | false => change expand env (.univ 0) = .univ 0; simp only [Term.univ,expand,expandArgs]
  | true => change expand env .prop = .prop; simp only [Term.prop,expand,expandArgs]

private theorem domain_expand (wf : UnifiedProgram.EnvWellFormed env) (family arity count : Nat) (values : List Term) :
    expand env (.node (.ind family arity) (values.map (Term.rename fun i => i+count) ++
      (List.range count).map (fun j => .var (count-1-j)))) =
    .node (.ind family arity) ((expandArgs env values).map (Term.rename fun i => i+count) ++
      (List.range count).map (fun j => .var (count-1-j))) := by
  simp only [expand,EnvironmentDelta.expandArgs_map,List.map_append,List.map_map,Function.comp_def,
    EnvironmentDelta.expand_renaming wf.admissible]

/-- When the subject supplies the declared parameter count, the exact
motive check identifies a data motive of the indicated sort. The displayed
domain contains the original parameter expressions at their new depth. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (onBase : Prefix base state.arena)
    (source : Represents state.arena inferred written) (parameters : RepresentsList state.arena values args)
    (length : values.length = params) (within : params ≤ arity)
    (success : (run normal limit depth state family params arity motive inferred values).result = .ok result)
    (ambient : Prefix (run normal limit depth state family params arity motive inferred values).state.arena final)
    (retained : PairRetained final result.compared) :
    let after := (run normal limit depth state family params arity motive inferred values).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      RawLend.Conv env (expand env written) (dataMotiveType family params arity (expandArgs env args) result.proof) := by
  unfold run at success ambient ⊢
  obtain ⟨root,normalized,normalNext⟩ := Outcome.next_success success
  rw [normalNext] at success ambient ⊢
  obtain ⟨normalKept,normalBack,residual,represented,converted⟩ := normalSound onBase source normalized
  split at success
  · cases success
  · rename_i domain sort accepted
    simp only [accepted] at ambient ⊢
    obtain ⟨expected,expectedOk,expectedNext⟩ := Outcome.next_success success
    rw [expectedNext] at success ambient ⊢
    obtain ⟨compared,comparedOk,comparedNext⟩ := Outcome.next_success success
    rw [comparedNext] at success ambient ⊢
    obtain ⟨level,levelOk,levelNext⟩ := Outcome.next_success success
    rw [levelNext] at success ambient ⊢
    split at success
    · rename_i proof sorted
      simp only [Except.ok.injEq] at success
      subst result
      simp only [sorted] at ambient ⊢
      let exposed := normal state inferred
      let formed := NativeCoreDataMotiveDomain.run limit depth exposed.state family params arity values
      let checked := requireTypes normal limit depth formed.state domain expected motive
      have afterCompare := (normalProgress checked.state sort).kept.trans ambient
      obtain ⟨D,S,domainRep,sortRep,telShape⟩ := telescope_refines represented accepted
      obtain ⟨madeKept,madeBack,expectedRep⟩ := NativeCoreDataMotiveDomain.run_refines
        (parameters.frame normalKept) length within expectedOk
      have throughMade := normalKept.trans madeKept
      obtain ⟨compareKept,compareBack,domainEqual⟩ := requireTypes_refines normalSound (onBase.trans throughMade)
        (domainRep.frame madeKept) expectedRep comparedOk afterCompare retained
      have throughCompare := throughMade.trans compareKept
      obtain ⟨sortKept,sortBack,_,sortNode,sortRelated⟩ := normalSound (onBase.trans throughCompare)
        (sortRep.frame (madeKept.trans compareKept)) levelOk
      have selectedSort := chosenSort_refines sortNode sorted
      have sortEqual : RawLend.Conv env (expand env S) (loopSortTerm proof) := by
        simpa only [selectedSort,sort_expand] using sortRelated.converted
      rw [domain_expand wf] at domainEqual
      have exposedType : RawLend.Conv env (expand env written)
          (u64Telescope (arity-params) (.pi false (expand env D) (expand env S))) := by
        simpa only [telShape,telescope_expand,Term.pi,expand,expandArgs] using converted.converted
      refine ⟨throughCompare.trans sortKept,sortBack ∘ compareBack ∘ madeBack ∘ normalBack,
        exposedType.trans ?_⟩
      exact telescope_convert (.node (.pi false) (.cons domainEqual (.cons sortEqual .nil))) _
    · cases success

/-- Both allowed sorts follow the same domain comparison and preserve
the newly allocated index scope. An erased motive index is rejected
before any domain rows are allocated. -/
theorem data_and_proposition_motives_share_domain_schedule :
    let input : Arena := #[.var 0,.node .u64 [],.var 1,.node (.ind 0 2) [2,0],
      .node (.universe 0) [],.node .prop [],.node (.pi false) [3,4],.node (.pi false) [1,6],
      .node (.pi false) [3,5],.node (.pi false) [1,8],.node (.pi true) [1,6]]
    let normal := NativeCoreGhostLiteralAddition.run [] 0 18 16
    let data := run normal 18 16 ⟨input,0⟩ 0 1 2 7 7 [0]
    let proof := run normal 18 16 ⟨input,0⟩ 0 1 2 9 9 [0]
    let rejected := run normal 18 16 ⟨input,0⟩ 0 1 2 10 10 [0]
    data.state.steps = 18 ∧ proof.state.steps = 18 ∧ data.result.map Motive.proof = .ok false ∧
      proof.result.map Motive.proof = .ok true ∧
      data.state.arena = input ++ #[.var 1,.var 0,.node (.ind 0 2) [11,12]] ∧
      proof.state.arena = data.state.arena ∧ rejected = ⟨⟨input,7⟩,.error (.outsideFragment 10)⟩ := by cbv

end Jihoo.NativeKernel.NativeCoreDataMotiveInference
