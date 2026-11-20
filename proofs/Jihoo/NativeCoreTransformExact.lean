import Jihoo.NativeCoreTransformWire
import Jihoo.NativeCoreUnsignedCancellation

/-! Core.transform visits live arena rows in field order. It keeps a row
whose payload and child references are unchanged, and appends changed rows
after their children. Earlier appends survive rejection in a later child. -/
namespace Jihoo.NativeKernel.NativeCoreTransformExact

open NativeArena NativeTransform
open NativeKernel.Conversion (treeSize)

inductive Error where
  | tick (reason : NativeCoreIdentical.Error)
  | binderLimit (ref : Nat)
  | escapes (ref : Nat)
  | variableLimit (ref : Nat)
  | add (reason : NativeCoreGraph.Error)
  deriving DecidableEq, Repr

structure State where
  arena : Arena
  steps : Nat
  deriving Repr

structure Outcome (α : Type) where
  state : State
  result : Except Error α
  deriving Repr

private def Outcome.next (result : Outcome α) (next : State → α → Outcome β) : Outcome β :=
  match result.result with
  | .error reason => ⟨result.state, .error reason⟩
  | .ok value => next result.state value

inductive Mode where
  | shift (delta : Int)
  | replace (policy : ReplacementMode) (value : Nat)
  deriving Repr

def Mode.cutoff (mode : Mode) (binders : Nat) : Nat :=
  match mode with
  | .shift _ => binders
  | .replace policy _ => policy.target binders

def Mode.expected (mode : Mode) (binders : Nat) (replacement source : Term) : Option Term :=
  match mode with
  | .shift delta => PartialRenaming.shift delta binders source
  | .replace policy _ => some (source.subst (liftSub binders (policy.environment replacement)))

def Mode.Argument (mode : Mode) (arena : Arena) (replacement : Term) : Prop :=
  match mode with
  | .shift _ => True
  | .replace _ value => Represents arena value replacement

private theorem Mode.Argument.frame {mode : Mode} (argument : mode.Argument before term) (kept : Prefix before after) :
    mode.Argument after term := by
  cases mode with
  | shift => exact trivial
  | replace => exact Represents.frame argument kept

private def finish (state : State) (root : Nat) (before after : Node) : Outcome Nat :=
  if before = after then ⟨state, .ok root⟩ else
    match NativeCoreGraph.addNode state.arena after with
    | .error reason => ⟨state, .error (.add reason)⟩
    | .ok (arena, fresh) => ⟨{state with arena := arena}, .ok fresh⟩

private def shiftVariable (state : State) (root index cutoff : Nat) (delta : Int) : Outcome Nat :=
  if index < cutoff then ⟨state, .ok root⟩ else
    let next := (index : Int) + delta
    if next < (cutoff : Int) then ⟨state, .error (.escapes root)⟩
    else if (indexLimit : Int) ≤ next then ⟨state, .error (.variableLimit root)⟩
    else finish state root (.var index) (.var next.toNat)

private def children (visit : State → Nat → Nat → Outcome Nat) (mode : Mode) (op : Op)
    (binders : Nat) : List Nat → Nat → State → Outcome (List Nat)
  | [], _, state => ⟨state, .ok []⟩
  | child :: rest, offset, state =>
      let crossed := op.binders offset
      let inner := binders + crossed
      if crossed ≠ 0 ∧ indexLimit ≤ mode.cutoff inner then ⟨state, .error (.binderLimit child)⟩
      else
        (visit state child inner).next fun afterHead head =>
          (children visit mode op binders rest (offset + 1) afterHead).next fun afterTail tail =>
            ⟨afterTail, .ok (head :: tail)⟩

private def tickFailure (arena : Arena) (steps : Nat) (reason : NativeCoreIdentical.Error) : Outcome Nat :=
  ⟨⟨arena, steps⟩, .error (.tick reason)⟩

/-- The matched-variable branch shifts the original replacement reference
under the crossed binders, with the same live arena and shared counter. -/
def run (limit : Nat) : Nat → State → Nat → Mode → Nat → Outcome Nat
  | 0, state, root, _, _ =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit 0 state.steps root
      match tried.1 with
      | .error reason => tickFailure state.arena tried.2 reason
      | .ok () => tickFailure state.arena tried.2 (.depthLimit root)
  | depth + 1, state, root, mode, binders =>
      let tried := NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root
      match tried.1 with
      | .error reason => tickFailure state.arena tried.2 reason
      | .ok () =>
          let entered := {state with steps := tried.2}
          match state.arena[root]? with
          | none => tickFailure state.arena tried.2 (.invalidReference root)
          | some (.var index) =>
              match mode with
              | .shift delta => shiftVariable entered root index binders delta
              | .replace policy value =>
                  if index = policy.target binders then run limit depth entered value (.shift binders) 0
                  else finish entered root (.var index) (.var (policy.other binders index))
          | some (.node op refs) =>
              let visit := fun state child inner => run limit depth state child mode inner
              (children visit mode op binders refs 0 entered).next fun afterChildren transformed =>
                finish afterChildren root (.node op refs) (.node op transformed)

def shift (limit depth : Nat) (state : State) (root : Nat) (delta : Int64) (cutoff : UInt32) : Outcome Nat :=
  run limit depth state root (.shift delta.toInt) cutoff.toNat

def substitute (limit depth : Nat) (state : State) (body value : Nat) : Outcome Nat :=
  run limit depth state body (.replace .substitute value) 0

def rewrite (limit depth : Nat) (state : State) (body target value : Nat) : Outcome Nat :=
  run limit depth state body (.replace (.rewrite target) value) 0

mutual
  /-- Every source occurrence is visited, and each replacement match also
  visits every occurrence in the argument being shifted. -/
  def work (mode : Mode) (value : Term) (binders : Nat) : Term → Nat
    | .var index =>
        match mode with
        | .shift _ => 1
        | .replace policy _ => if index = policy.target binders then 1 + treeSize value else 1
    | .node op args => 1 + workArgs mode value binders op 0 args
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf; omega

  def workArgs (mode : Mode) (value : Term) (binders : Nat) (op : Op) (offset : Nat) : List Term → Nat
    | [] => 0
    | first :: rest =>
        work mode value (binders + op.binders offset) first +
          workArgs mode value binders op (offset + 1) rest
  termination_by terms => sizeOf terms
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem work_shift (delta : Int) (value term : Term) (cutoff : Nat) :
    work (.shift delta) value cutoff term = treeSize term := by
  induction term using Term.rec (motive_2 := fun terms => ∀ op offset cutoff,
    workArgs (.shift delta) value cutoff op offset terms = (terms.map treeSize).sum) generalizing cutoff with
  | var => simp [work, treeSize]
  | node op terms ih => simp [work, treeSize, ih]
  | nil => simp [workArgs]
  | cons first rest ihFirst ihRest => simp [workArgs, ihFirst, ihRest]

private theorem lift_raiseIndex (cutoff amount n : Nat) :
    liftRenaming n (PartialRenaming.raiseIndex cutoff amount) =
      PartialRenaming.raiseIndex (cutoff + n) amount := by
  induction n with
  | zero => simp [liftRenaming]
  | succ n ih =>
      funext x
      cases x with
      | zero =>
          have below : 0 < cutoff + (n + 1) := by omega
          simp [liftRenaming, Indexed.liftRenaming, PartialRenaming.raiseIndex, below]
      | succ x =>
          by_cases localVar : x < cutoff + n
          · have localSucc : x + 1 < cutoff + (n + 1) := by omega
            simp [liftRenaming, Indexed.liftRenaming, ih, PartialRenaming.raiseIndex, localVar, localSucc]
          · have outerSucc : ¬(x + 1 < cutoff + (n + 1)) := by omega
            simp [liftRenaming, Indexed.liftRenaming, ih, PartialRenaming.raiseIndex, localVar, outerSucc]
            omega

private theorem lift_shiftIndex (delta : Int) (cutoff n : Nat) :
    PartialRenaming.lift n (shiftIndex delta cutoff) = shiftIndex delta (cutoff + n) := by
  by_cases positive : 0 ≤ delta
  · simp only [shiftIndex, positive, ite_true, lift_total, lift_raiseIndex]
  · simp only [shiftIndex, positive, ite_false, PartialRenaming.lift_lowerIndex]

private theorem shift_some_of_index (success : shiftIndex delta cutoff index = some next) :
    PartialRenaming.shift delta cutoff (.var index) = some (.var next) := by
  rw [← shiftIndex_semantics]
  simp [PartialRenaming.rename?, success]

private theorem shift_index_of_widened (index cutoff : Nat) (delta : Int)
    (above : ¬index < cutoff) (low : (cutoff : Int) ≤ (index : Int) + delta) :
    shiftIndex delta cutoff index = some ((index : Int) + delta).toNat := by
  by_cases positive : 0 ≤ delta
  · have count : ((index : Int) + delta).toNat = index + delta.toNat := by omega
    simp [shiftIndex, positive, PartialRenaming.raiseIndex, above, count]
  · have allowed : cutoff + (-delta).toNat ≤ index := by omega
    have count : ((index : Int) + delta).toNat = index - (-delta).toNat := by omega
    simp [shiftIndex, positive, PartialRenaming.lowerIndex, above, allowed, count]

private theorem shift_index_local (below : index < cutoff) :
    shiftIndex delta cutoff index = some index := by
  by_cases positive : 0 ≤ delta <;>
    simp [shiftIndex, positive, PartialRenaming.raiseIndex, PartialRenaming.lowerIndex, below]

private inductive Args (mode : Mode) (replacement : Term) (binders : Nat) (op : Op) :
    Nat → List Term → List Term → Prop where
  | nil : Args mode replacement binders op offset [] []
  | cons : mode.expected (binders + op.binders offset) replacement input = some output →
      Args mode replacement binders op (offset + 1) inputs outputs →
      Args mode replacement binders op offset (input :: inputs) (output :: outputs)

private theorem Args.length (args : Args mode value binders op offset ins outs) :
    outs.length = ins.length := by
  induction args with
  | nil => rfl
  | cons _ _ later => exact congrArg Nat.succ later

private theorem Args.shift (args : Args (.shift delta) value cutoff op offset ins outs) :
    PartialRenaming.renameArgs? op (shiftIndex delta cutoff) offset ins = some outs := by
  induction args with
  | nil => rw [PartialRenaming.renameArgs?]
  | cons first _ rest =>
      simp only [Mode.expected, ← shiftIndex_semantics] at first
      simp [PartialRenaming.renameArgs?, lift_shiftIndex, first, rest]

private theorem Args.replace (args : Args (.replace policy ref) value binders op offset ins outs) :
    substArgs op (liftSub binders (policy.environment value)) offset ins = outs := by
  induction args with
  | nil => rw [substArgs]
  | cons first _ rest =>
      simp only [Mode.expected, Option.some.injEq] at first
      simp only [substArgs, PartialRenaming.liftSub_add, first, rest]

private theorem Args.node (args : Args mode value binders op 0 ins outs) :
    mode.expected binders value (.node op ins) = some (.node op outs) := by
  cases mode with
  | shift delta =>
      simp [Mode.expected, ← shiftIndex_semantics, PartialRenaming.rename?, args.shift]
  | replace policy ref =>
      simp only [Mode.expected, Term.subst, args.replace]

private theorem Outcome.next_success {previous : Outcome α} {next : State → α → Outcome β}
    (success : (previous.next next).result = .ok selected) :
    ∃ value, previous.result = .ok value ∧ previous.next next = next previous.state value := by
  cases previousResult : previous.result with
  | error reason => simp [Outcome.next, previousResult] at success
  | ok value => exact ⟨value, rfl, by simp [Outcome.next, previousResult]⟩

private theorem finish_steps (state : State) (root : Nat) (before after : Node) :
    (finish state root before after).state.steps = state.steps := by
  unfold finish
  split
  · rfl
  · split <;> rfl

private theorem shiftVariable_steps (state : State) (root index cutoff : Nat) (delta : Int) :
    (shiftVariable state root index cutoff delta).state.steps = state.steps := by
  unfold shiftVariable
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · exact finish_steps ..

private theorem tick_steps (charged : NativeCoreUnsignedCancellation.tick arena limit depth initial root = (.ok (), spent)) :
    spent = initial + 1 ∧ spent ≤ limit := by
  by_cases over : limit < initial + 1
  · simp [NativeCoreUnsignedCancellation.tick, over] at charged
  by_cases zero : depth = 0
  · simp [NativeCoreUnsignedCancellation.tick, over, zero] at charged
  by_cases invalid : arena.size ≤ root
  · simp [NativeCoreUnsignedCancellation.tick, over, zero, invalid] at charged
  · simp only [NativeCoreUnsignedCancellation.tick, over, zero, invalid, ite_false, Prod.mk.injEq] at charged
    obtain ⟨_, rfl⟩ := charged
    exact ⟨rfl, Nat.le_of_not_gt over⟩

private theorem known_children (source : RepresentsList arena refs terms) :
    ∀ ref ∈ refs, ref < arena.size := by
  induction source using RepresentsList.rec (motive_1 := fun ref _ _ => ref < arena.size) with
  | var read | node read => exact (Array.getElem?_eq_some_iff.mp read).1
  | nil => simp
  | cons _ _ head tail =>
      intro ref member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail ref member

private theorem represented_length (source : RepresentsList arena refs terms) :
    refs.length = terms.length := by
  induction source using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => rfl
  | cons _ _ _ rest => exact congrArg Nat.succ rest

private theorem finish_refines (read : state.arena[root]? = some before)
    (references : ∀ child ∈ after.references, child < state.arena.size)
    (success : (finish state root before after).result = .ok selected) :
    let result := (finish state root before after).state.arena
    Prefix state.arena result ∧ (Backward state.arena → Backward result) ∧ result[selected]? = some after := by
  by_cases same : before = after
  · simp [finish, same] at success
    subst selected
    simp only [finish, same, ite_true]
    exact ⟨.refl _, id, same ▸ read⟩
  · cases built : NativeCoreGraph.addNode state.arena after with
    | error reason => simp [finish, same, built] at success
    | ok output =>
        obtain ⟨next, fresh⟩ := output
        simp [finish, same, built] at success
        subst selected
        obtain ⟨kept, index, _, _, _, lookup⟩ := NativeCoreGraph.addNode_commits built
        have backward (old : Backward state.arena) : Backward next := by
          apply NativeCoreGraph.addNode_preserves_backward old built
          rw [index]
          exact references
        simp only [finish, same, ite_false, built]
        exact ⟨kept, backward, lookup⟩

structure Refines (mode : Mode) (binders : Nat) (value source : Term) (start : State)
    (outcome : Outcome Nat) (selected : Nat) : Prop where
  kept : Prefix start.arena outcome.state.arena
  backward : Backward start.arena → Backward outcome.state.arena
  meaning : ∃ term, mode.expected binders value source = some term ∧ Represents outcome.state.arena selected term

private theorem shiftVariable_refines (read : state.arena[root]? = some (.var index))
    (success : (shiftVariable state root index cutoff delta).result = .ok selected) :
    Refines (.shift delta) cutoff value (.var index) state (shiftVariable state root index cutoff delta) selected := by
  by_cases localVar : index < cutoff
  · simp [shiftVariable, localVar] at success
    subst selected
    have meaning := shift_some_of_index (delta := delta) (shift_index_local (delta := delta) localVar)
    simpa [shiftVariable, localVar] using
      (show Refines (.shift delta) cutoff value (.var index) state ⟨state, .ok root⟩ root from
        ⟨.refl _, id, .var index, meaning, .var read⟩)
  · by_cases escapes : (index : Int) + delta < (cutoff : Int)
    · simp [shiftVariable, localVar, escapes] at success
    by_cases tooWide : (indexLimit : Int) ≤ (index : Int) + delta
    · simp [shiftVariable, localVar, escapes, tooWide] at success
    · let next := ((index : Int) + delta).toNat
      have branch : shiftVariable state root index cutoff delta = finish state root (.var index) (.var next) := by
        simp [shiftVariable, localVar, escapes, tooWide, next]
      rw [branch] at success ⊢
      obtain ⟨kept, backward, rep⟩ := finish_refines read (after := .var next) (by simp [Node.references]) success
      have meaning : PartialRenaming.shift delta cutoff (.var index) = some (.var next) :=
        shift_some_of_index (shift_index_of_widened index cutoff delta localVar (Int.le_of_not_gt escapes))
      exact ⟨kept, backward, .var next, meaning, .var rep⟩

private theorem children_refines (source : RepresentsList start.arena refs ins)
    (argument : mode.Argument start.arena value)
    (spec : ∀ {state ref inner term result}, Represents state.arena ref term → mode.Argument state.arena value →
      (visit state ref inner).result = .ok result → Refines mode inner value term state (visit state ref inner) result ∧
        (visit state ref inner).state.steps = state.steps + work mode value inner term)
    (success : (children visit mode op binders refs offset start).result = .ok results) :
    let computed := children visit mode op binders refs offset start
    Prefix start.arena computed.state.arena ∧ (Backward start.arena → Backward computed.state.arena) ∧
      computed.state.steps = start.steps + workArgs mode value binders op offset ins ∧
        ∃ outs, Args mode value binders op offset ins outs ∧ RepresentsList computed.state.arena results outs := by
  induction refs generalizing start offset ins results with
  | nil =>
      cases source
      simp [children] at success
      subst results
      exact ⟨.refl _, id, by simp [children, workArgs], [], .nil, .nil⟩
  | cons child refs ih =>
      cases source with
      | @cons _ input _ ins first rest =>
          by_cases overflow : op.binders offset ≠ 0 ∧ indexLimit ≤ mode.cutoff (binders + op.binders offset)
          · simp [children, overflow] at success
          · let inner := binders + op.binders offset
            let head := visit start child inner
            have branch : children visit mode op binders (child :: refs) offset start =
                head.next (fun afterHead headRef =>
                  (children visit mode op binders refs (offset + 1) afterHead).next (fun afterTail tailRefs =>
                    ⟨afterTail, .ok (headRef :: tailRefs)⟩)) := by
              simp [children, overflow, head, inner]
            rw [branch] at success ⊢
            obtain ⟨firstRef, headFound, firstDone⟩ := Outcome.next_success success
            rw [firstDone] at success ⊢
            obtain ⟨restRefs, tailFound, tailDone⟩ := Outcome.next_success success
            rw [tailDone] at success ⊢
            have exactRefs : firstRef :: restRefs = results := by injection success
            subst results
            obtain ⟨firstFacts, headSteps⟩ := spec first argument headFound
            obtain ⟨kept, back, firstTerm, expected, firstRep⟩ := firstFacts
            obtain ⟨frame, preserves, tailSteps, restTerms, expectedRest, restRep⟩ :=
              ih (rest.frame kept) (argument.frame kept) tailFound
            refine ⟨kept.trans frame, fun old => preserves (back old), ?_, firstTerm :: restTerms,
              .cons expected expectedRest, .cons (firstRep.frame frame) restRep⟩
            change (children visit mode op binders refs (offset + 1) head.state).state.steps =
              start.steps + workArgs mode value binders op offset (input :: ins)
            rw [tailSteps]
            change head.state.steps + workArgs mode value binders op (offset + 1) ins = _
            rw [show head.state.steps = start.steps + work mode value inner input from headSteps, workArgs]
            exact Nat.add_assoc ..

/-- Any successful transform across the shared constructor vocabulary agrees
with the independently defined capture-avoiding syntax operation. Changed
rows extend the arena and preserve all backward references. -/
theorem run_refines {mode : Mode}
    (source : Represents state.arena root term) (argument : mode.Argument state.arena value)
    (success : (run limit depth state root mode binders).result = .ok selected) :
    let output := run limit depth state root mode binders
    Refines mode binders value term state output selected ∧
      output.state.steps = state.steps + work mode value binders term := by
  dsimp only
  induction depth generalizing state root term mode binders value selected with
  | zero =>
      by_cases over : limit < state.steps + 1 <;>
        simp [run, NativeCoreUnsignedCancellation.tick, tickFailure, over] at success
  | succ depth ih =>
      rcases charged : NativeCoreUnsignedCancellation.tick state.arena limit (depth + 1) state.steps root with
        ⟨answer, spent⟩
      cases answer with
      | error reason => simp [run, charged, tickFailure] at success
      | ok chargedValue =>
          cases chargedValue
          have counter := (tick_steps charged).1
          let entered := {state with steps := spent}
          cases source with
          | @var _ index read =>
              cases mode with
              | shift delta =>
                  have exact : run limit (depth + 1) state root (.shift delta) binders =
                      shiftVariable entered root index binders delta := by simp [run, charged, read, entered]
                  rw [exact] at success ⊢
                  obtain ⟨kept, preserves, meaning⟩ :=
                    shiftVariable_refines (value := value) (state := entered) read success
                  exact ⟨⟨kept, preserves, meaning⟩, by
                    rw [shiftVariable_steps, work]
                    exact counter⟩
              | replace policy ref =>
                  by_cases matched : index = policy.target binders
                  · have exact : run limit (depth + 1) state root (.replace policy ref) binders =
                        run limit depth entered ref (.shift binders) 0 := by
                      simp [run, charged, read, matched, entered]
                    rw [exact] at success ⊢
                    obtain ⟨⟨kept, preserves, output, expected, represents⟩, shiftWork⟩ :=
                      ih (mode := .shift binders) (value := value) (state := entered) argument trivial success
                    have indices : PartialRenaming.raiseIndex 0 binders = fun x => x + binders := by
                      funext index
                      simp [PartialRenaming.raiseIndex]
                    have formula :
                        (Mode.shift binders).expected 0 value value = some (value.rename (fun x => x + binders)) := by
                      simp [Mode.expected, PartialRenaming.shift, indices]
                    rw [formula] at expected
                    cases expected
                    refine ⟨⟨kept, preserves, _, ?_, represents⟩, ?_⟩
                    · simp only [Mode.expected, Term.subst, replacement_environment_at, matched, ite_true]
                    · rw [shiftWork, work_shift, work, ite_eq_left matched]
                      change spent + treeSize value = state.steps + (1 + treeSize value)
                      omega
                  · let next := policy.other binders index
                    have exact : run limit (depth + 1) state root (.replace policy ref) binders =
                        finish entered root (.var index) (.var next) := by
                      simp [run, charged, read, matched, entered, next]
                    rw [exact] at success ⊢
                    obtain ⟨kept, preserves, represents⟩ :=
                      finish_refines (state := entered) read (after := .var next) (by simp [Node.references]) success
                    refine ⟨⟨kept, preserves, .var next, ?_, .var represents⟩, ?_⟩
                    · simp only [Mode.expected, Term.subst, replacement_environment_at, matched, ite_false, next]
                    · rw [finish_steps, work, ite_eq_right matched]
                      exact counter
          | @node _ op refs terms read arity kids =>
              let visit := fun state ref inner => run limit depth state ref mode inner
              let traversed := children visit mode op binders refs 0 entered
              have branch : run limit (depth + 1) state root mode binders =
                  traversed.next (fun afterChildren transformed =>
                    finish afterChildren root (.node op refs) (.node op transformed)) := by
                simp [run, charged, read, traversed, visit, entered]
              rw [branch] at success ⊢
              obtain ⟨results, found, done⟩ := Outcome.next_success success
              rw [done] at success ⊢
              obtain ⟨kept, preserves, used, outs, expectedArgs, outputArgs⟩ :=
                children_refines (start := entered) kids argument (fun rep arg childRun => ih rep arg childRun) found
              have known : ∀ child ∈ (Node.node op results).references, child < traversed.state.arena.size :=
                known_children outputArgs
              obtain ⟨retained, backward, outputRead⟩ := finish_refines (kept.lookup read) known success
              have outputArity : results.length = op.arity :=
                (represented_length outputArgs).trans
                  (expectedArgs.length.trans ((represented_length kids).symm.trans arity))
              refine ⟨⟨kept.trans retained, fun old => backward (preserves old), .node op outs,
                expectedArgs.node, .node outputRead outputArity (outputArgs.frame retained)⟩, ?_⟩
              rw [finish_steps, work]
              change traversed.state.steps = _
              rw [show traversed.state.steps = spent + workArgs mode value binders op 0 terms from used]
              omega

/-- The graph primitive substitutes at variable zero under each binder and
returns the result of capture-avoiding instantiation. -/
theorem substitute_refines (body : Represents state.arena root term) (argument : Represents state.arena ref value)
    (success : (substitute limit depth state root ref).result = .ok selected) :
    let result := (substitute limit depth state root ref).state.arena
    Prefix state.arena result ∧ (Backward state.arena → Backward result) ∧
      Represents result selected (term.subst (single value)) := by
  obtain ⟨kept, backwards, output, expected, represents⟩ :=
    (run_refines (mode := .replace .substitute ref) (binders := 0) body argument success).1
  simp only [Mode.expected, ReplacementMode.environment, liftSub, Option.some.injEq] at expected
  subst output
  exact ⟨kept, backwards, represents⟩

/-- The rewrite primitive increments the target cutoff along actual binder
edges and does not remove the binder or decrement other references. -/
theorem rewrite_refines (body : Represents state.arena root term) (argument : Represents state.arena ref value)
    (success : (rewrite limit depth state root target ref).result = .ok selected) :
    let result := (rewrite limit depth state root target ref).state.arena
    Prefix state.arena result ∧ (Backward state.arena → Backward result) ∧
      Represents result selected (PartialRenaming.rewrite target value term) := by
  obtain ⟨kept, backwards, output, expected, represents⟩ :=
    (run_refines (mode := .replace (.rewrite target) ref) (binders := 0) body argument success).1
  simp only [Mode.expected, ReplacementMode.environment, liftSub, Option.some.injEq] at expected
  subst output
  exact ⟨kept, backwards, by rw [PartialRenaming.rewrite_eq_subst]; exact represents⟩

/-- The signed native shift evaluates to the checked partial renaming,
including scope removal for negative deltas. -/
theorem shift_refines (source : Represents state.arena root term)
    (success : (shift limit depth state root delta cutoff).result = .ok selected) :
    let result := (shift limit depth state root delta cutoff).state.arena
    Prefix state.arena result ∧ (Backward state.arena → Backward result) ∧
      ∃ output, PartialRenaming.shift delta.toInt cutoff.toNat term = some output ∧ Represents result selected output := by
  obtain ⟨kept, backwards, meaning⟩ :=
    (run_refines (mode := .shift delta.toInt) (binders := cutoff.toNat) (value := term) source trivial success).1
  exact ⟨kept, backwards, meaning⟩

theorem substitute_scoped (body : Represents state.arena root term)
    (argument : Represents state.arena ref value)
    (bodyScope : term.Scoped (scope + 1)) (valueScope : value.Scoped scope)
    (success : (substitute limit depth state root ref).result = .ok selected) :
    let result := (substitute limit depth state root ref).state.arena
    ∃ output, Represents result selected output ∧ output.Scoped scope :=
  ⟨_, (substitute_refines body argument success).2.2, bodyScope.instantiate valueScope⟩

/-- A zero shift reuses every row. Instantiating the same lambda creates
the shifted argument first, then the lambda with a changed child reference. -/
theorem reuse_and_capture_example :
    let arena : Arena := #[.var 0, .var 1, .node .u64 [], .node (.lam false) [2, 1]]
    shift 3 3 ⟨arena, 0⟩ 3 0 0 = ⟨⟨arena, 3⟩, .ok 3⟩ ∧
    substitute 4 3 ⟨arena, 0⟩ 3 0 =
      ⟨⟨(arena.push (.var 1)).push (.node (.lam false) [2, 4]), 4⟩, .ok 5⟩ := by
  exact ⟨rfl, rfl⟩

/-- The second child hits the work limit. The two rows produced by the first
child remain committed and no parent row is added. -/
theorem failure_retains_earlier_child_example :
    let arena : Arena := #[.var 0, .var 1, .node .u64 [], .node (.lam false) [2, 1], .node .eq [3, 0]]
    substitute 5 4 ⟨arena, 0⟩ 4 0 =
      ⟨⟨(arena.push (.var 1)).push (.node (.lam false) [2, 5]), 6⟩, .error (.tick (.stepLimit 0))⟩ :=
  rfl

end Jihoo.NativeKernel.NativeCoreTransformExact
