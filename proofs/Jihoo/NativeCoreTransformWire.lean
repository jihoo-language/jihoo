import Jihoo.NativeCoreGraphWire
import Jihoo.NativeTransformMachine
import Jihoo.NativeReplacementTransform

/-! Follow the edges of Core's original version-6 arena. The observed words
specify both child order and the edges at which `Core.transform` increments
its cutoff. The path model accounts for those increments independently of the
traversal's global step budget, node allocation, and diagnostics. -/
namespace Jihoo.NativeKernel.NativeTransform

open NativeArena NativeCoreGraph GraphCertificates.Canonical

/-- The four constructor arms of `Core.transform_under_binder`, using writer
tags and zero-based positions in the flattened `Core.children` vector. -/
def wireBinder (tag offset : Nat) : Bool :=
  ((tag == 44 || tag == 45) && offset == 1) ||
  ((tag == 52 || tag == 53) && offset == 2)

theorem wireBinder_tag (op : Op) (offset : Nat) :
    wireBinder (NativeSchema.tag op) offset = (op.binders offset == 1) := by
  rcases offset with _ | _ | _ | _ <;> cases op <;> rfl

private theorem ofCode_tag (decoded : NativeSchema.ofCode tag fields = some op) :
    tag = NativeSchema.tag op := by
  -- Isolate tags 0 through 53 and the rejecting high range. Reducing each
  -- payload separately keeps the large schema match out of the proof search.
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first
    | cases decoded <;> rfl
    | rcases fields with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
      all_goals first
        | cases decoded <;> rfl
        | rcases a with _ | _ | _ | _ <;> cases decoded <;> rfl
        | rcases a with _ | _ | _ | _ <;>
            rcases b with _ | _ <;> cases decoded <;> rfl

private theorem wordBinder {words : NodeWords} {op : Op}
    (decoded : words.toNode = some (.node op refs)) (offset : Nat) :
    wireBinder words.tag.toNat offset = (op.binders offset == 1) := by
  unfold NodeWords.toNode at decoded
  split at decoded
  · dsimp only at decoded
    split at decoded <;> cases decoded
  · cases code : NativeSchema.ofCode words.tag.toNat (words.fields.map UInt64.toNat) with
    | none => simp [code] at decoded
    | some found =>
        simp only [code, Option.map_some, Option.some.injEq, Node.node.injEq] at decoded
        rw [ofCode_tag code, decoded.1]
        exact wireBinder_tag op offset

/-- Follow original child ordinals directly through the UInt32 references
passed to the snapshot writer. Return the final node ID and the crossed
binder flags in traversal order. -/
def wirePath (words : List NodeWords) : Nat → List Nat → Option (Nat × List Bool)
  | root, [] => some (root, [])
  | root, offset :: rest => do
      let source ← words[root]?
      let next ← source.children[offset]?
      let (leaf, crossed) ← wirePath words next.toNat rest
      some (leaf, wireBinder source.tag.toNat offset :: crossed)

/-- Select a subtree at the same ordinals in the independent syntax tree. -/
def focus : Term → List Nat → Option (Term × List Bool)
  | term, [] => some (term, [])
  | .var _, _ :: _ => none
  | .node op args, offset :: rest => do
      let child ← args[offset]?
      let (leaf, crossed) ← focus child rest
      some (leaf, (op.binders offset == 1) :: crossed)

private theorem focus_child
    (selected : focus (.node op args) (offset :: path) = some (subterm, crossed)) :
    ∃ child inner, args[offset]? = some child ∧ focus child path = some (subterm, inner) ∧
      crossed = (op.binders offset == 1) :: inner := by
  simp only [focus] at selected
  obtain ⟨child, childAt, selected⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨⟨leaf, inner⟩, focused, selected⟩ := Option.bind_eq_some_iff.mp selected
  simp only [Option.some.injEq, Prod.mk.injEq] at selected
  obtain ⟨rfl, rfl⟩ := selected
  exact ⟨child, inner, childAt, focused, rfl⟩

private theorem word_at {words : List NodeWords} {nodes : List Node} {index : Nat}
    (parsed : words.mapM NodeWords.toNode = some nodes) (lookup : nodes[index]? = some node) :
    ∃ word, words[index]? = some word ∧ word.toNode = some node := by
  induction words generalizing nodes index with
  | nil => simp at parsed; subst nodes; simp at lookup
  | cons word words ih =>
      cases head : word.toNode with
      | none => simp [List.mapM_cons, head] at parsed
      | some first =>
          cases tail : words.mapM NodeWords.toNode with
          | none => simp [List.mapM_cons, head, tail] at parsed
          | some rest =>
              simp only [List.mapM_cons, head, tail, Bind.bind, Option.bind, Pure.pure,
                Option.some.injEq] at parsed
              subst nodes
              cases index with
              | zero =>
                  cases lookup
                  exact ⟨word, rfl, head⟩
              | succ index => exact ih tail lookup

private theorem represented_child {index : Nat} (rep : RepresentsList g refs args)
    (atChild : args[index]? = some child) :
    ∃ ref, refs[index]? = some ref ∧ Represents g ref child := by
  induction rep using RepresentsList.rec (motive_1 := fun _ _ _ => True)
      generalizing index with
  | var | node => trivial
  | nil => simp at atChild
  | @cons first t refs args firstRep restRep _ ih =>
      cases index with
      | zero =>
          cases atChild
          exact ⟨first, rfl, firstRep⟩
      | succ index => exact ih atChild

private theorem wirePath_focus_core
    (aligned : words.mapM NodeWords.toNode = some g.toList)
    (rep : Represents g root term) (selected : focus term path = some (subterm, crossed)) :
    ∃ leaf, wirePath words root path = some (leaf, crossed) ∧ Represents g leaf subterm := by
  induction path generalizing root term subterm crossed with
  | nil =>
      cases selected
      exact ⟨root, rfl, rep⟩
  | cons offset path ih =>
      cases rep with
      | var => simp [focus] at selected
      | @node root op refs args nodeAt _ children =>
          obtain ⟨child, flags, childAt, suffix, rfl⟩ := focus_child selected
          obtain ⟨childRef, refAt, childRep⟩ := represented_child children childAt
          have nodeInList : g.toList[root]? = some (.node op refs) := by simpa using nodeAt
          obtain ⟨word, wordAt, wordNode⟩ := word_at aligned nodeInList
          have refVector : refs = word.children.map UInt32.toNat := NodeWords.toNode_references wordNode
          rw [refVector, List.getElem?_map] at refAt
          obtain ⟨wordRef, wordRefAt, refEq⟩ := Option.map_eq_some_iff.mp refAt
          obtain ⟨leaf, pathAt, leafRep⟩ := ih childRep suffix
          exact ⟨leaf, by simp [wirePath, wordAt, wordRefAt, refEq, pathAt, wordBinder wordNode], leafRep⟩

/-- The exact bytes written for a version-6 snapshot determine the path and
its binder edges, and the selected reference represents the same subtree. -/
theorem wirePath_focus
    (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ rest) =
      some (snapshot, tail))
    (rep : Represents snapshot.arena root term)
    (selected : focus term path = some (subterm, crossed)) :
    ∃ leaf, wirePath words root path = some (leaf, crossed) ∧
      Represents snapshot.arena leaf subterm := by
  rw [parseObservedProgram _ _ _ fits] at parsed
  cases aligned : words.mapM NodeWords.toNode with
  | none => simp [aligned] at parsed
  | some nodes =>
      simp only [aligned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      exact wirePath_focus_core (by simpa using aligned) rep selected

def binderCount : List Bool → Nat
  | [] => 0
  | false :: rest => binderCount rest
  | true :: rest => binderCount rest + 1

private theorem binderCount_cons (op : Op) (offset : Nat) (crossed : List Bool) :
    binderCount ((op.binders offset == 1) :: crossed) = op.binders offset + binderCount crossed := by
  rcases offset with _ | _ | _ | _ <;> cases op
  all_goals first | exact (Nat.zero_add _).symm | exact Nat.add_comm _ _

private theorem liftRenaming_add (outer inner : Nat) (ρ : Nat → Nat) :
    liftRenaming inner (liftRenaming outer ρ) = liftRenaming (outer + inner) ρ := by
  induction inner with
  | zero => rfl
  | succ inner ih => exact congrArg Indexed.liftRenaming ih

private theorem liftPartial_add (outer inner : Nat) (ρ : Nat → Option Nat) :
    PartialRenaming.lift inner (PartialRenaming.lift outer ρ) =
      PartialRenaming.lift (outer + inner) ρ := by
  induction inner with
  | zero => rfl
  | succ inner ih => exact congrArg PartialRenaming.liftOne ih

theorem focus_rename (ρ : Nat → Nat) (selected : focus term path = some (subterm, crossed)) :
    focus (term.rename ρ) path = some (subterm.rename (liftRenaming (binderCount crossed) ρ), crossed) := by
  induction path generalizing term subterm crossed ρ with
  | nil =>
      cases selected
      rfl
  | cons offset path ih =>
      cases term with
      | var => simp [focus] at selected
      | node op args =>
          obtain ⟨child, inner, childAt, atLeaf, rfl⟩ := focus_child selected
          have rest := ih (liftRenaming (op.binders offset) ρ) atLeaf
          simp [Term.rename, focus, renameArgs_get, childAt, rest, binderCount_cons, liftRenaming_add]

theorem focus_subst (σ : Nat → Term) (selected : focus term path = some (subterm, crossed)) :
    focus (term.subst σ) path = some (subterm.subst (liftSub (binderCount crossed) σ), crossed) := by
  induction path generalizing term subterm crossed σ with
  | nil =>
      cases selected
      rfl
  | cons offset path ih =>
      cases term with
      | var => simp [focus] at selected
      | node op args =>
          obtain ⟨child, inner, childAt, atLeaf, rfl⟩ := focus_child selected
          have rest := ih (liftSub (op.binders offset) σ) atLeaf
          simp [Term.subst, focus, substArgs_get, childAt, rest, binderCount_cons, PartialRenaming.liftSub_add]

/-- At a selected variable, native ordinary substitution replaces the
exact cutoff and decrements only variables above the removed binder. -/
theorem focus_substitute_variable (value : Term)
    (selected : focus term path = some (.var index, crossed)) :
    focus (term.subst (single value)) path =
      some ((if index = binderCount crossed then value.rename (fun x => x + binderCount crossed)
        else .var (if binderCount crossed < index then index - 1 else index)), crossed) := by
  rw [focus_subst (single value) selected]
  simp only [Term.subst]
  exact congrArg (fun t : Term => some (t, crossed))
    (replacement_environment_at .substitute value (binderCount crossed) index)

theorem focus_partialRename (ρ : Nat → Option Nat)
    (selected : focus term path = some (subterm, crossed))
    (renamed : PartialRenaming.rename? ρ term = some output) :
    ∃ leaf, focus output path = some (leaf, crossed) ∧
      PartialRenaming.rename? (PartialRenaming.lift (binderCount crossed) ρ) subterm = some leaf := by
  induction path generalizing term subterm crossed ρ output with
  | nil =>
      cases selected
      exact ⟨output, rfl, renamed⟩
  | cons offset path ih =>
      cases term with
      | var => simp [focus] at selected
      | node op args =>
          obtain ⟨child, inner, childAt, atLeaf, rfl⟩ := focus_child selected
          rw [PartialRenaming.rename?] at renamed
          obtain ⟨outArgs, outArgsEq, rfl⟩ := Option.map_eq_some_iff.mp renamed
          have inside : offset < outArgs.length := by
            rw [PartialRenaming.renameArgs?_length outArgsEq]
            exact (List.getElem?_eq_some_iff.mp childAt).1
          have outChild := List.getElem?_eq_getElem inside
          obtain ⟨inputChild, inputAt, transformed⟩ :=
            PartialRenaming.renameArgs?_get outArgsEq outChild
          have same := Option.some.inj (inputAt.symm.trans childAt)
          subst inputChild
          simp only [Nat.zero_add] at transformed
          obtain ⟨leaf, leafAt, leafRenamed⟩ := ih _ atLeaf transformed
          exact ⟨leaf, by simp [focus, outChild, leafAt],
            by simpa only [binderCount_cons, liftPartial_add] using leafRenamed⟩

private theorem liftRaiseIndex (cutoff amount depth : Nat) :
    liftRenaming depth (PartialRenaming.raiseIndex cutoff amount) =
      PartialRenaming.raiseIndex (cutoff + depth) amount := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext x
      simp only [liftRenaming, ih]
      cases x with
      | zero => simp [Indexed.liftRenaming, PartialRenaming.raiseIndex]
      | succ x =>
          have bound : x + 1 < cutoff + (depth + 1) ↔ x < cutoff + depth := by omega
          by_cases before : x < cutoff + depth <;>
            simp [Indexed.liftRenaming, PartialRenaming.raiseIndex, bound, before, Nat.add_right_comm]

theorem lift_shiftIndex (delta : Int) (cutoff depth : Nat) :
    PartialRenaming.lift depth (shiftIndex delta cutoff) = shiftIndex delta (cutoff + depth) := by
  by_cases positive : 0 ≤ delta
  · simp only [shiftIndex, ite_eq_left positive, lift_total, liftRaiseIndex]
  · simp only [shiftIndex, ite_eq_right positive, PartialRenaming.lift_lowerIndex]

theorem focus_shift (selected : focus term path = some (subterm, crossed))
    (shifted : PartialRenaming.shift delta cutoff term = some output) :
    ∃ leaf, focus output path = some (leaf, crossed) ∧
      PartialRenaming.shift delta (cutoff + binderCount crossed) subterm = some leaf := by
  rw [← shiftIndex_semantics] at shifted
  obtain ⟨leaf, leafAt, leafShift⟩ := focus_partialRename _ selected shifted
  rw [lift_shiftIndex, shiftIndex_semantics] at leafShift
  exact ⟨leaf, leafAt, leafShift⟩

/-- Model consecutive calls to `transform_under_binder` on one path. Plain
children carry their parent's cutoff without checking an addition. -/
def stepCutoffs : List Bool → UInt32 → Option UInt32
  | [], cutoff => some cutoff
  | false :: rest, cutoff => stepCutoffs rest cutoff
  | true :: rest, cutoff => do
      let inner ← binderCutoff cutoff
      stepCutoffs rest inner

/-- A path can have arbitrary nonbinding edges even at the maximum cutoff.
Failure occurs exactly when a visited binder overflows that cutoff. -/
theorem stepCutoffs_refines (crossed : List Bool) (cutoff : UInt32) :
    (stepCutoffs crossed cutoff).map UInt32.toNat =
      if cutoff.toNat + binderCount crossed < indexLimit then
        some (cutoff.toNat + binderCount crossed) else none := by
  induction crossed generalizing cutoff with
  | nil =>
      have width : cutoff.toNat < indexLimit := cutoff.toNat_lt
      simp [stepCutoffs, binderCount, width]
  | cons binds crossed ih =>
      cases binds with
      | false => exact ih cutoff
      | true =>
          have step := binderCutoff_refines cutoff
          cases advanced : binderCutoff cutoff with
          | none =>
              simp only [advanced, Option.map_none] at step
              have cannot : ¬cutoff.toNat + 1 < indexLimit := by
                intro within
                rw [ite_eq_left within] at step
                contradiction
              have total : ¬cutoff.toNat + (binderCount crossed + 1) < indexLimit := by omega
              simp [stepCutoffs, advanced, binderCount, total]
          | some inner =>
              simp only [advanced, Option.map_some] at step
              have within : cutoff.toNat + 1 < indexLimit := by
                by_cases fits : cutoff.toNat + 1 < indexLimit
                · exact fits
                · rw [ite_eq_right fits] at step
                  contradiction
              have exactWord : inner.toNat = cutoff.toNat + 1 := by
                simpa only [ite_eq_left within, Option.some.injEq] using step
              simp only [stepCutoffs, binderCount, advanced, Bind.bind, Option.bind]
              have total : cutoff.toNat + 1 + binderCount crossed =
                  cutoff.toNat + (binderCount crossed + 1) := by omega
              rw [ih inner, exactWord, total]
              by_cases fits : cutoff.toNat + (binderCount crossed + 1) < indexLimit <;> simp [fits]

/-- Once the path cutoff has been reached, the actual widened shift and
UInt32 output guard implement the corresponding lifted variable map. -/
theorem shiftVariable_at_path
    (walked : stepCutoffs crossed cutoff = some reached) (index : UInt32) (delta : Int64) :
    (shiftVariable index reached delta).map UInt32.toNat =
      (PartialRenaming.lift (binderCount crossed) (shiftIndex delta.toInt cutoff.toNat) index.toNat).filter
        (fun next => decide (next < indexLimit)) := by
  have cutoffAt := stepCutoffs_refines crossed cutoff
  rw [walked, Option.map_some] at cutoffAt
  split at cutoffAt
  · rw [Option.some.injEq] at cutoffAt
    rw [shiftVariable_refines, cutoffAt, lift_shiftIndex]
  · contradiction

theorem wirePath_cutoff (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ rest) =
      some (snapshot, tail))
    (rep : Represents snapshot.arena root term)
    (selected : focus term path = some (subterm, crossed)) (cutoff : UInt32) :
    ∃ leaf, wirePath words root path = some (leaf, crossed) ∧
      Represents snapshot.arena leaf subterm ∧
      (stepCutoffs crossed cutoff).map UInt32.toNat =
        if cutoff.toNat + binderCount crossed < indexLimit then
          some (cutoff.toNat + binderCount crossed) else none := by
  obtain ⟨leaf, visited, represented⟩ := wirePath_focus fits parsed rep selected
  exact ⟨leaf, visited, represented, stepCutoffs_refines crossed cutoff⟩

end Jihoo.NativeKernel.NativeTransform
