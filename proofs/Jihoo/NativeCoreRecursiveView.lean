import Jihoo.NativeCoreRecursiveCase
import Jihoo.NativeCoreViewShapeAlignment

/-! The joint pure walker handles Borrow, Deref and View. A known View
first visits the original constructor telescope, then builds its native
spine and reenters the same walker on the resulting applications. The
graph model validates the telescope and requires its live flags to agree
with the checked signature before using a raw View equation. -/
namespace Jihoo.NativeKernel.NativeCoreRecursiveView

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress Refines RefinesFor GhostNormalization PostExtension emptyPrefix nodeResult nodeResult_exact
  nodeResult_progress runWithExtension runWithExtension_progress runWithExtension_refines computeNormalization)
open NativeCoreCaseEvaluation (represented_branches)
open NativeCoreElimNormal (represented_ref FamilyRules)
open NativeCoreViewNormal (Shape checkedShape buildSpine buildSpine_refines buildSpine_progress)
open Environment.FamilyIota (viewTerm)

private def loanOp (dereference : Bool) : Op := if dereference then .deref else .borrow

private def unaryRef (expected : Op) : Node → Option Nat
  | .node actual [ref] => if actual = expected then some ref else none
  | _ => none

private def finishLoan (dereference : Bool) (root : Nat) (state : State) (before : List Nat) :
    List Nat → Outcome Nat
  | [ref] =>
      match state.arena[ref]?.bind (unaryRef (loanOp !dereference)) with
      | some original => ⟨state, .ok original⟩
      | none => nodeResult state root (loanOp dereference) before [ref]
  | _ => ⟨state, .error (.outsideFragment root)⟩

private theorem unary_representation (source : Represents arena root term)
    (read : arena[root]?.bind (unaryRef op) = some target) :
    ∃ inner, term = .node op [inner] ∧ Represents arena target inner := by
  cases source with
  | var found => simp [unaryRef, found] at read
  | @node _ actual refs values found arity children =>
      cases children with
      | nil => simp [unaryRef, found] at read
      | cons child tail =>
          cases tail with
          | nil =>
              by_cases same : actual = op
              · subst actual
                simp [unaryRef, found] at read
                subst target
                exact ⟨_, rfl, child⟩
              · simp [unaryRef, found, same] at read
          | cons _ _ => simp [unaryRef, found] at read

private theorem finishLoan_refines (rules : FamilyRules env relation)
    (compute : ∀ {a b}, ACU.Computes a b → relation a b)
    (read : state.arena[root]? = some (.node (loanOp dereference) before))
    (operands : RepresentsList state.arena after terms)
    (size : after.length = (loanOp dereference).arity)
    (success : (finishLoan dereference root state before after).result = .ok selected) :
    RefinesFor relation state (.node (loanOp dereference) terms) (finishLoan dereference root state before after) selected := by
  have unary : after.length = 1 := size.trans (by cases dereference <;> rfl)
  cases operands with
  | nil => cases unary
  | @cons ref arg _ _ operand rest =>
      cases rest with
      | cons => cases unary
      | nil =>
          cases reduced : state.arena[ref]?.bind (unaryRef (loanOp !dereference)) with
          | none =>
              simp only [finishLoan, reduced] at success ⊢
              obtain ⟨kept, backward, held⟩ := nodeResult_exact read (.cons operand .nil) size success
              exact ⟨kept, backward, _, held, rules.same _⟩
          | some result =>
              simp only [finishLoan, reduced, Except.ok.injEq] at success ⊢
              subst selected
              obtain ⟨inner, rfl, original⟩ := unary_representation operand reduced
              have cancellation : ACU.Computes (.node (loanOp dereference) [.node (loanOp !dereference) [inner]]) inner := by
                cases dereference
                · exact .borrowDeref inner
                · exact .derefBorrow inner
              exact ⟨.refl _, id, inner, original, compute cancellation⟩

private theorem finishLoan_progress (dereference : Bool) (root : Nat) (state : State)
    (before after : List Nat) : Progress limit state (finishLoan dereference root state before after) := by
  simp only [finishLoan]
  repeat' first | exact Progress.atState _ _ | exact nodeResult_progress _ _ _ _ _ _ | split

def constructorRoot (roots : List NativeFamilyWire.FamilyRoots) (family constructor : Nat) : Option Nat :=
  roots[family]?.bind fun declaration => declaration.constructors[constructor]?

private theorem decodedMember {f : α → Option β} {inputs : List α} {outputs : List β} {index : Nat}
    (decoded : inputs.mapM f = some outputs)
    (selected : inputs[index]? = some input) : ∃ output, f input = some output := by
  induction index generalizing inputs outputs with
  | zero =>
      cases inputs with
      | nil => contradiction
      | cons head tail =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst input
          cases found : f head with
          | none => simp [List.mapM_cons, found] at decoded
          | some output => exact ⟨output, rfl⟩
  | succ index ih =>
      cases inputs with
      | nil => contradiction
      | cons head tail =>
          cases found : f head with
          | none => simp [List.mapM_cons, found] at decoded
          | some output =>
              cases ready : tail.mapM f with
              | none => simp [List.mapM_cons, found, ready] at decoded
              | some rest => exact ih ready selected

/-- The extra representation check succeeds at every constructor root of
an admitted snapshot, including after append-only normalization. -/
theorem constructorRoot_decodes
    (decoded : NativeFamilyWire.decodeProgram snapshot = some (definitions, declarations))
    (selected : constructorRoot snapshot.families family constructor = some root)
    (extended : Prefix snapshot.arena arena) :
    ∃ term, decode 128 arena root = some term := by
  unfold NativeFamilyWire.decodeProgram at decoded
  split at decoded
  · contradiction
  · obtain ⟨_, _, checkedFamilies⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨_, familiesDecoded, _⟩ := Option.bind_eq_some_iff.mp checkedFamilies
    obtain ⟨familyRow, found, constructorFound⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨familyTerm, checked⟩ := decodedMember familiesDecoded found
    unfold NativeFamilyWire.decodeFamily at checked
    obtain ⟨_, constructors, _⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨term, decodedTerm⟩ := decodedMember constructors constructorFound
    exact ⟨term, decode_frame_exact decodedTerm extended⟩

private def checkedPlan (env : Environment) (family : Nat) (entry : CheckedFamily)
    (signature : Signature) : Option (List ViewFieldPlan) :=
  viewPlan env family (signature.fields.drop entry.declaration.params)

private def runKnown (env : Environment) (visit : State → Nat → Outcome Nat) (state : State)
    (recursion : Bool) (family motive : Nat) (cases : List Nat) (owner branch typeRoot : Nat)
    (entry : CheckedFamily) (signature : Signature) (fields : List Nat) : Outcome (Option Nat) :=
  if (decode 128 state.arena typeRoot).isSome then
    (NativeCoreViewShape.run env family visit state entry.declaration.params typeRoot).next fun scanned shape =>
      if fields.length = entry.declaration.params + shape.length then
        match checkedPlan env family entry signature with
        | some plans =>
            if fields.length = signature.fields.length ∧ entry.declaration.params ≤ signature.fields.length ∧
                shape = checkedShape plans then
              ((buildSpine scanned recursion family motive entry.declaration.params cases branch fields shape).next
                visit).next fun final selected => ⟨final, .ok (some selected)⟩
            else ⟨scanned, .error (.outsideFragment owner)⟩
        | none => ⟨scanned, .error (.outsideFragment owner)⟩
      else ⟨scanned, .ok none⟩
  else ⟨state, .error (.outsideFragment typeRoot)⟩

private def tryOwner (env : Environment) (roots : List NativeFamilyWire.FamilyRoots)
    (visit : State → Nat → Outcome Nat) (state : State) (recursion : Bool) (family motive : Nat)
    (cases : List Nat) (owner : Nat) : Outcome (Option Nat) :=
  match state.arena[owner]? with
  | none | some (.node .strict _) => ⟨state, .error (.outsideFragment owner)⟩
  | some (.node (.con actual constructor _) fields) =>
      if actual = family then
        match env.families[family]?, cases[constructor]? with
        | some entry, some branch =>
            if entry.boxed ∧ cases.length = entry.signatures.length then
              match entry.signatures[constructor]?, constructorRoot roots family constructor with
              | some signature, some typeRoot =>
                  runKnown env visit state recursion family motive cases owner branch typeRoot entry signature fields
              | _, _ => ⟨state, .error (.outsideFragment owner)⟩
            else ⟨state, .ok none⟩
        | _, _ => ⟨state, .ok none⟩
      else ⟨state, .ok none⟩
  | some _ => ⟨state, .ok none⟩

private def tryView (env : Environment) (roots : List NativeFamilyWire.FamilyRoots)
    (visit : State → Nat → Outcome Nat) (state : State) (recursion : Bool) (family motive : Nat)
    (cases : List Nat) (scrutinee : Nat) : Outcome (Option Nat) :=
  match state.arena[scrutinee]?.bind (unaryRef .borrow) with
  | some owner => tryOwner env roots visit state recursion family motive cases owner
  | none => ⟨state, .ok none⟩

private def finishView (env : Environment) (roots : List NativeFamilyWire.FamilyRoots)
    (visit : State → Nat → Outcome Nat) (root : Nat) (state : State) (recursion : Bool)
    (family count : Nat) (before : List Nat) : List Nat → Outcome Nat
  | motive :: operands =>
      match operands[count]? with
      | some scrutinee =>
          (tryView env roots visit state recursion family motive (operands.take count) scrutinee).next
            fun next selected =>
              match selected with
              | some ref => ⟨next, .ok ref⟩
              | none => nodeResult next root (.view recursion family count) before (motive :: operands)
      | none => ⟨state, .error (.outsideFragment root)⟩
  | [] => ⟨state, .error (.outsideFragment root)⟩

def extension (env : Environment) (roots : List NativeFamilyWire.FamilyRoots) : PostExtension where
  accepts
    | .borrow | .deref | .view .. | .caseOf .. | .elim .. => true
    | _ => false
  finish visit limit depth root state op before after :=
    match op with
    | .borrow => finishLoan false root state before after
    | .deref => finishLoan true root state before after
    | .view recursion family count => finishView env roots visit root state recursion family count before after
    | _ => (NativeCoreRecursiveCase.extension env).finish visit limit depth root state op before after

def run (env : Environment) (roots : List NativeFamilyWire.FamilyRoots) (limit depth : Nat)
    (state : State) (root : Nat) : Outcome Nat :=
  runWithExtension (extension env roots) limit depth state root

private theorem runKnown_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (runKnown env visit state recursion family motive cases owner branch typeRoot entry signature fields) := by
  unfold runKnown
  split
  · apply (NativeCoreViewShape.run_progress metered state entry.declaration.params typeRoot (family := family) (env := env)).next
    intro shape
    repeat' first
      | exact Progress.atState _ _
      | exact ((buildSpine_progress _ _ _ _ _ _ _ _ _).next (fun ref => metered _ ref)).next
          (fun _ => Progress.atState _ _)
      | split
  · exact Progress.atState _ _

private theorem tryOwner_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (tryOwner env roots visit state recursion family motive cases owner) := by
  simp only [tryOwner]
  repeat' first | exact Progress.atState _ _ | exact runKnown_progress metered | split

private theorem tryView_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (tryView env roots visit state recursion family motive cases scrutinee) := by
  simp only [tryView]
  split
  · exact tryOwner_progress metered
  · exact Progress.atState _ _

private theorem finishView_progress (metered : ∀ state ref, Progress limit state (visit state ref)) :
    Progress limit state (finishView env roots visit root state recursion family count before after) := by
  simp only [finishView]
  repeat' first
    | exact Progress.atState _ _
    | exact (tryView_progress metered).next (fun chosen => by
        cases chosen
        · exact nodeResult_progress _ _ _ _ _ _
        · exact Progress.atState _ _)
    | split

theorem extension_metered (env : Environment) (roots : List NativeFamilyWire.FamilyRoots) :
    (extension env roots).Metered := by
  intro visit limit depth root state op before after accepted metered
  cases op <;> try contradiction
  case borrow => exact finishLoan_progress false root state before after
  case deref => exact finishLoan_progress true root state before after
  case view recursion family count => exact finishView_progress metered
  case elim family count =>
    exact NativeCoreRecursiveCase.extension_metered env
      (op := .elim family count) (depth := depth) (before := before) rfl metered
  case caseOf family count =>
    exact NativeCoreRecursiveCase.extension_metered env
      (op := .caseOf family count) (depth := depth) (before := before) rfl metered

private structure ViewRefines (relation : Term → Term → Prop) (before after : Arena) (input : Term)
    (selected : Option Nat) : Prop where
  kept : Prefix before after
  backward : Backward before → Backward after
  value : match selected with
    | none => True
    | some ref => ∃ output, Represents after ref output ∧
        relation input output

private theorem declined (state : State)
    (found : (.ok none : Except NativeCorePureComputationNormal.Error (Option Nat)) = .ok selected) :
    ViewRefines relation state.arena state.arena source selected := by
  cases found
  exact ⟨.refl _, id, trivial⟩

private theorem runKnown_refines (rules : FamilyRules env relation) (onBase : Prefix base state.arena)
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
    (signatureRead : entry.signatures[constructor]? = some signature)
    (branchRead : caseRefs[constructor]? = some branchRef) (count : caseRefs.length = entry.signatures.length)
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (fieldsRep : RepresentsList state.arena fieldRefs fields)
    (success : (runKnown env visit state recursion family motiveRef caseRefs owner branchRef
      typeRoot entry signature fieldRefs).result = .ok selected) :
    ViewRefines relation state.arena
      (runKnown env visit state recursion family motiveRef caseRefs owner branchRef typeRoot entry signature fieldRefs).state.arena
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor fields.length) fields))) selected := by
  unfold runKnown at success ⊢
  cases decoded : decode 128 state.arena typeRoot with
  | none => simp [decoded] at success
  | some declaration =>
      simp only [decoded, Option.isSome_some, ite_true] at success ⊢
      obtain ⟨shape, scanned, procedure⟩ := Outcome.next_success success
      rw [procedure] at success ⊢
      have sourceRep : Represents state.arena typeRoot declaration := decode_sound decoded
      obtain ⟨kept, backward⟩ := NativeCoreViewShape.run_framesFrom onBase visitor sourceRep scanned
      by_cases nativeSize : fieldRefs.length = entry.declaration.params + shape.length
      · simp only [ite_eq_left nativeSize] at success ⊢
        cases planned : checkedPlan env family entry signature with
        | none => simp [planned] at success
        | some plans =>
            simp only [planned] at success ⊢
            by_cases aligned : fieldRefs.length = signature.fields.length ∧
                entry.declaration.params ≤ signature.fields.length ∧ shape = checkedShape plans
            · rw [ite_eq_left aligned] at success ⊢
              obtain ⟨outputRef, foundResult, done⟩ := Outcome.next_success success
              rw [done] at success ⊢
              obtain ⟨spine, foundSpine, visited⟩ := Outcome.next_success foundResult
              rw [visited] at foundResult ⊢
              have same : some outputRef = selected := Except.ok.inj success
              subst selected
              obtain ⟨fieldCount, parameters, shapeEq⟩ := aligned
              subst shape
              obtain ⟨branch, branchFound, branchRep⟩ := represented_ref caseRep branchRead
              obtain ⟨spineKept, spineBackward, _, spineRep⟩ := buildSpine_refines
                (motiveRep.frame kept) (caseRep.frame kept) (branchRep.frame kept) (fieldsRep.frame kept)
                (plans := plans) foundSpine
              obtain ⟨later, laterBackward, residual, residualRep, normalized⟩ := visitor (onBase.trans (kept.trans spineKept)) spineRep foundResult
              have arms := NativeCoreIdentical.represented_length caseRep
              have values := NativeCoreIdentical.represented_length fieldsRep
              have native : FamilyIota.Root env
                  (viewTerm recursion family motive cases (.borrow (.node (.con family constructor fields.length) fields)))
                  (FamilyIota.viewBody recursion family entry.declaration.params motive branch cases fields plans) :=
                .view found boxed signatureRead branchFound (arms.symm.trans count) (values.symm.trans fieldCount)
                  parameters planned
              exact ⟨kept.trans (spineKept.trans later),
                fun old => laterBackward (spineBackward (backward old)), residual, residualRep,
                rules.trans (rules.contract native) normalized⟩
            · simp [aligned] at success
      · simp only [ite_eq_right nativeSize, Except.ok.injEq] at success ⊢
        subst selected
        exact ⟨kept, backward, trivial⟩

private theorem tryOwner_refines (rules : FamilyRules env relation) (onBase : Prefix base state.arena)
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (ownerRep : Represents state.arena owner ownerTerm)
    (success : (tryOwner env roots visit state recursion family motiveRef caseRefs owner).result = .ok selected) :
    ViewRefines relation state.arena (tryOwner env roots visit state recursion family motiveRef caseRefs owner).state.arena
      (viewTerm recursion family motive cases (.borrow ownerTerm)) selected := by
  cases ownerRep with
  | var read =>
      simp only [tryOwner, read] at success ⊢
      exact declined state success
  | @node _ op fieldRefs fields read arity represented =>
      cases op
      all_goals try solve
        | simp only [tryOwner, read] at success ⊢
          exact declined state success
        | simp [tryOwner, read] at success
      case con actual constructor width =>
        by_cases same : actual = family
        · subst actual
          simp only [tryOwner, read, ite_true] at success ⊢
          cases found : env.families[family]? with
          | none =>
              simp only [found] at success
              exact declined state success
          | some entry =>
              cases branchRead : caseRefs[constructor]? with
              | none =>
                  simp only [found, branchRead] at success
                  exact declined state success
              | some branch =>
                  simp only [found, branchRead] at success ⊢
                  by_cases enabled : entry.boxed = true ∧ caseRefs.length = entry.signatures.length
                  · rw [ite_eq_left enabled] at success ⊢
                    cases signatureRead : entry.signatures[constructor]? with
                    | none => simp [signatureRead] at success
                    | some signature =>
                        cases typeRead : constructorRoot roots family constructor with
                        | none => simp [signatureRead, typeRead] at success
                        | some typeRoot =>
                            have sameWidth : width = fields.length :=
                              arity.symm.trans (NativeCoreIdentical.represented_length represented)
                            subst width
                            simp only [signatureRead, typeRead] at success ⊢
                            exact runKnown_refines rules onBase visitor found enabled.1 signatureRead branchRead enabled.2
                              motiveRep caseRep represented success
                  · rw [ite_eq_right enabled] at success ⊢
                    exact declined state success
        · simp only [tryOwner, read, ite_eq_right same] at success ⊢
          exact declined state success

private theorem tryView_refines (rules : FamilyRules env relation) (onBase : Prefix base state.arena)
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (motiveRep : Represents state.arena motiveRef motive) (caseRep : RepresentsList state.arena caseRefs cases)
    (scrutineeRep : Represents state.arena scrutinee value)
    (success : (tryView env roots visit state recursion family motiveRef caseRefs scrutinee).result = .ok selected) :
    ViewRefines relation state.arena (tryView env roots visit state recursion family motiveRef caseRefs scrutinee).state.arena
      (viewTerm recursion family motive cases value) selected := by
  cases read : state.arena[scrutinee]?.bind (unaryRef .borrow) with
  | none =>
      simp only [tryView, read] at success ⊢
      exact declined state success
  | some owner =>
      obtain ⟨ownerTerm, rfl, ownerRep⟩ := unary_representation scrutineeRep read
      simp only [tryView, read] at success ⊢
      exact tryOwner_refines rules onBase visitor motiveRep caseRep ownerRep success

private theorem finishView_refines (rules : FamilyRules env relation) (onBase : Prefix base state.arena)
    (visitor : ∀ {state ref term selected}, Prefix base state.arena → Represents state.arena ref term →
      (visit state ref).result = .ok selected → RefinesFor relation state term (visit state ref) selected)
    (read : state.arena[root]? = some (.node (.view recursion family count) before))
    (operands : RepresentsList state.arena after terms) (size : after.length = count + 2)
    (success : (finishView env roots visit root state recursion family count before after).result = .ok selected) :
    RefinesFor relation state (.node (.view recursion family count) terms)
      (finishView env roots visit root state recursion family count before after) selected := by
  cases operands with
  | nil => cases size
  | @cons motiveRef motive _ _ motiveRep rest =>
      obtain ⟨caseRefs, scrutRef, arms, value, rfl, rfl, width, caseRep, valueRep⟩ :=
        represented_branches rest (Nat.succ.inj size)
      subst count
      have lookup : (caseRefs ++ [scrutRef])[caseRefs.length]? = some scrutRef := by simp
      simp only [finishView, lookup, List.take_left] at success ⊢
      obtain ⟨chosen, found, done⟩ := Outcome.next_success success
      rw [done] at success ⊢
      obtain ⟨kept, backward, valueResult⟩ := tryView_refines rules onBase visitor motiveRep caseRep valueRep found
      cases chosen with
      | some selectedRef =>
          cases success
          obtain ⟨residual, represented, normalized⟩ := valueResult
          have count := NativeCoreIdentical.represented_length caseRep
          exact ⟨kept, backward, residual, represented, by simpa only [viewTerm, ← count] using normalized⟩
      | none =>
          obtain ⟨preserved, checked, represented⟩ :=
            nodeResult_exact (kept.lookup read) ((RepresentsList.cons motiveRep rest).frame kept)
              size success
          exact ⟨kept.trans preserved, fun old => checked (backward old), _, represented, rules.same _⟩

theorem extension_soundFrom (rules : FamilyRules env relation)
    (compute : ∀ {a b}, ACU.Computes a b → relation a b) :
    (extension env roots).SoundFrom base relation := by
  constructor
  · intro op accepted
    cases op <;> try contradiction
    all_goals
      refine ⟨?_, rfl⟩
      intro equal
      cases equal
  · intro visit limit depth root state op before after terms selected accepted onBase read represented size visitor success
    cases op <;> try contradiction
    case borrow => exact finishLoan_refines rules compute (dereference := false) read represented size success
    case deref => exact finishLoan_refines rules compute (dereference := true) read represented size success
    case view recursion family count => exact finishView_refines rules onBase visitor read represented size success
    case elim family count =>
      exact (NativeCoreRecursiveCase.extension_soundFrom (base := base) rules).2
        (limit := limit) (depth := depth) rfl onBase read represented size visitor success
    case caseOf family count =>
      exact (NativeCoreRecursiveCase.extension_soundFrom (base := base) rules).2
        (limit := limit) (depth := depth) rfl onBase read represented size visitor success

theorem extension_sound (history : ScopedProgram.History definitions declarations env) :
    (extension env roots).Sound env := by
  have proof : (extension env roots).SoundFrom #[] (GhostNormalization env) :=
    extension_soundFrom (FamilyRules.ghost history) (computeNormalization history.wellFormed)
  refine ⟨proof.1, ?_⟩
  intro visit limit depth root state op before after terms selected accepted read represented size visitor success
  exact proof.2 accepted (emptyPrefix _) read represented size (fun _ rep done => visitor rep done) success

theorem run_progress (env : Environment) (roots : List NativeFamilyWire.FamilyRoots)
    (limit depth : Nat) (state : State) (root : Nat) : Progress limit state (run env roots limit depth state root) :=
  runWithExtension_progress (extension_metered env roots) limit depth state root

theorem run_refines (history : LoanTyping.MixedProgram.History definitions declarations env)
    (source : Represents state.arena root term)
    (success : (run env roots limit depth state root).result = .ok selected) :
    Refines env state term (run env roots limit depth state root) selected :=
  runWithExtension_refines history.wellFormed (extension_sound (ScopedProgram.History.ofLoanMixed history)) source success

open NativeProgramWire

/-- The actual admitted snapshot supplies the declaration roots for shape
visits as well as the type of the stored definition being normalized. -/
theorem admitted_program_preserves
    (accepted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes = true) :
    ∃ (snapshot : NativeFamilyWire.Snapshot) (definitions : List Definitions.Definition)
      (familyTerms : List NativeFamilyWire.FamilyTerms) (env : Environment),
      NativeFamilyWire.encodeSnapshot snapshot = bytes ∧
      LoanTyping.MixedProgram.History definitions (familyTerms.map NativeLoanMixedAdmission.declaration) env ∧
      ∀ {index limit depth initial selected : Nat} {row : Roots},
        snapshot.definitions[index]? = some row →
        (run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot).result = .ok selected →
        let output := run env snapshot.families limit depth ⟨snapshot.arena, initial⟩ row.valueRoot
        ∃ (entry : GlobalDeclaration) (residual : Term), env.globals[index]? = some entry ∧
          Prefix snapshot.arena output.state.arena ∧ Backward output.state.arena ∧
          Represents output.state.arena selected residual ∧
          LoanTyping.HasType env [] [] true (EnvironmentDelta.expand env residual) entry.type := by
  obtain ⟨snapshot, definitions, families, env, exactBytes, _, backward, represented, _, history, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound accepted
  refine ⟨snapshot, definitions, families, env, exactBytes, history, ?_⟩
  intro index limit depth initial selected row found success
  obtain ⟨entry, raw, read, source, typed⟩ := NativeCoreGlobalNormal.checked_definition_at represented history found
  obtain ⟨kept, preserves, residual, residualRep, change⟩ := run_refines history source.2 success
  exact ⟨entry, residual, read, kept, preserves backward, residualRep, change.expanded.typed typed⟩

namespace Examples

private def box : Term := .node (.ind 0 0) []
private def family : FamilyDeclaration := ⟨true, 0, 0, [box, .pi false box box], 0⟩
private def leafSignature : Signature := ⟨[], []⟩
private def branchSignature : Signature := ⟨[⟨false, box, some []⟩], []⟩
private def base : Term := .natural 7
private def branch : Term := .lam false (.ref box) (.lam false .u64 (.var 0))
private def leaf : Term := .node (.con 0 0 0) []
private def parent (child : Term) : Term := .node (.con 0 1 1) [child]
private def sourceView : Term := viewTerm true 0 .u64 [base, branch] (.borrow (parent (parent leaf)))
private def source : Term := .eq sourceView base
private def env : Environment := ⟨#[⟨.prop, source⟩], #[⟨family, [leafSignature, branchSignature], true⟩]⟩

private def snapshot : NativeFamilyWire.Snapshot where
  definitions := [⟨14, 13⟩]
  families := [⟨true, 0, 0, 0, [1, 12]⟩]
  arena := #[.node .u64 [], .node (.ind 0 0) [], .node .ref [1], .var 0,
    .node (.lam false) [0, 3], .node (.lam false) [2, 4], .node (.natural 7) [],
    .node (.con 0 0 0) [], .node (.con 0 1 1) [7], .node (.con 0 1 1) [8],
    .node .borrow [9], .node (.view true 0 2) [0, 6, 5, 10], .node (.pi false) [1, 1],
    .node .eq [11, 6], .node .prop []]

private def emitted : Array Node := #[.node .borrow [8], .node .app [5, 15], .node .borrow [8],
  .node (.view true 0 2) [0, 6, 5, 17], .node .app [16, 18],
  .node .borrow [7], .node .app [5, 20], .node .borrow [7],
  .node (.view true 0 2) [0, 6, 5, 22], .node .app [21, 23], .node .eq [6, 6]]

/-- The actual checker admits a proposition whose operand is a recursive
View. Both generated hypotheses reenter the same graph driver and the leaf
word returns through the selected branches to the enclosing equality. -/
theorem admitted_recursive_view_reaches_leaf :
    NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true ∧
    run env snapshot.families 512 64 ⟨snapshot.arena, 0⟩ 13 =
      ⟨⟨snapshot.arena ++ emitted, 80⟩, .ok 25⟩ ∧
    LoanTyping.HasType env [] [] true (.eq base base) .prop := by
  have admitted : NativeLoanMixedAdmission.checkBytes 64 128 (NativeFamilyWire.encodeSnapshot snapshot) = true := by
    rw [NativeLoanMixedAdmission.checkBytes_encode]
    cbv
  have installed : LoanTyping.MixedProgram.checkProgram 64 128 [⟨.prop, source⟩] [family] = some env := by cbv
  have history := LoanTyping.MixedProgram.checkProgram_sound installed
  have typed := (history.global_typing (index := 0) (declaration := ⟨.prop, source⟩) rfl).choose_spec.2
  have sourceRep : Represents snapshot.arena 13 source := decode_sound (fuel := 14) rfl
  have computed : run env snapshot.families 512 64 ⟨snapshot.arena, 0⟩ 13 =
      ⟨⟨snapshot.arena ++ emitted, 80⟩, .ok 25⟩ := by cbv
  obtain ⟨_, _, residual, represented, changes⟩ := run_refines history sourceRep (congrArg Outcome.result computed)
  rw [computed] at represented
  have expected : Represents (snapshot.arena ++ emitted) 25 (.eq base base) := decode_sound (fuel := 4) rfl
  have preserved := changes.raw.typed typed
  rw [represented.unique expected] at preserved
  exact ⟨admitted, computed, preserved⟩

end Examples

end Jihoo.NativeKernel.NativeCoreRecursiveView
