import Jihoo.NativeCoreGhostBinderCheck
import Jihoo.NativeCoreGhostBackMotive
import Jihoo.NativeCoreDependentLendCallbacks
import Jihoo.NativeLoanFunctionInversion
import Jihoo.NativeCoreCodeLendGates
import Jihoo.NativeCoreCodeLeaseLookup
import Jihoo.NativeCoreBufferRelease
import Jihoo.NativeLoanGhostPromotion

/-! Ghost Lend checks the original callbacks in the generic branch.
Its dependent branch checks the specialized reader and the continuation
that restores the original owner. Both keep their exact native order. -/
namespace Jihoo.NativeKernel.NativeCoreGhostLendInference

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit InferSound Inferred Refines PairRetained RetainedComparisons next_progress
  requireTypes requireTypes_progress requireTypes_refines)
open NativeCoreGhostBinderCheck (inferBinder inferBinder_progress inferBinder_refines)
open NativeCoreGhostReferenceTypes (BoxedFamilies requireOwned requireOwned_progress requireOwned_refines)
open NativeCoreGhostBackMotive (exposeProduct product_progress product_refines)
open NativeCoreGhostSort (DataFamilies)
open NativeCoreCaseStrict (append append_progress append_refines)
open EnvironmentDelta (expand expandArgs)

private def reject (state : State) (root : Nat) : Outcome α := ⟨state,.error (.outsideFragment root)⟩

private def shift (limit depth : Nat) (state : State) (root : Nat) (amount : Int) : Outcome Nat :=
  let shifted := NativeCoreTransformExact.run limit depth state root (.shift amount) 0
  ⟨shifted.state,shifted.result.mapError .substitution⟩

private def outlived (isData : Nat → Bool) (arena : Arena) (root : Nat) : Bool :=
  match arena[root]? with
  | some (.node .u64 _) | some (.node .i64 _) | some (.node .refine _)
  | some (.node .array _) | some (.node .buffer _) | some (.node (.back _) _) => true
  | some (.node (.ind family _) _) => isData family
  | _ => false

private def readerType (normal : Visit) (isData : Nat → Bool) (state : State) (type reader : Nat) : Outcome Nat :=
  (normal state type).next fun exposed root =>
    if outlived isData exposed.arena root then ⟨exposed,.ok root⟩ else reject exposed reader

private def compare (normal : Visit) (limit depth : Nat) (state : State) (actual expected atRoot : Nat) :
    Outcome (Nat × Nat) := requireTypes normal limit depth state actual expected atRoot

private def lowerResult (normal : Visit) (limit depth : Nat) (state : State) (root : Nat) (amount : Int) : Outcome Nat :=
  (normal state root).next fun exposed result => shift limit depth exposed result amount

private def dependent (infer : Infer) (normal : Visit) (isData : Nat → Bool) (limit depth : Nat) (state : State)
    (owner ownerType borrow reader continuation : Nat) (callbacks : NativeCoreDependentLendCallbacks.Prepared) :
    Outcome Inferred :=
  (inferBinder infer normal isData state callbacks.domain false).next fun afterDomain domain =>
    (compare normal limit depth afterDomain callbacks.domain borrow reader).next fun afterReadDomain readDomain =>
      (infer afterReadDomain callbacks.reader).next fun inferred readType =>
        (readerType normal isData inferred readType.typeRoot reader).next fun accepted value =>
          match NativeCoreDependentLendCallbacks.select accepted.arena owner reader continuation with
          | none => reject accepted continuation
          | some written =>
            (shift limit depth accepted ownerType 1).next fun shifted again =>
              (inferBinder infer normal isData shifted written.first false).next fun checkedFirst first =>
                (compare normal limit depth checkedFirst written.first value continuation).next fun firstMatch valuePair =>
                  (compare normal limit depth firstMatch written.again again continuation).next fun checked resumeOwner =>
                    (infer checked callbacks.continuation).next fun resumed afterType =>
                      (exposeProduct normal resumed afterType.typeRoot continuation).next fun exposed product =>
                        (lowerResult normal limit depth exposed product.2 (-1)).next fun after root =>
                          ⟨after,.ok ⟨root,domain.compared ++ ([readDomain] ++ (readType.compared ++
                            (first.compared ++ ([valuePair,resumeOwner] ++ afterType.compared))))⟩⟩

private def continuationType (normal : Visit) (state : State) (type continuation : Nat) : Outcome (Nat × Nat × Nat) :=
  (exposeProduct normal state type continuation).next fun after first =>
    match after.arena[first.2]? with
    | some (.node (.pi false) [owner,result]) => ⟨after,.ok (first.1,owner,result)⟩
    | _ => reject after continuation

private def generic (infer : Infer) (normal : Visit) (isData : Nat → Bool) (limit depth : Nat) (state : State)
    (ownerType borrow reader continuation : Nat) : Outcome Inferred :=
  (infer state reader).next fun inferred readType =>
    (exposeProduct normal inferred readType.typeRoot reader).next fun exposed product =>
      (compare normal limit depth exposed product.1 borrow reader).next fun afterReadDomain readDomain =>
        (shift limit depth afterReadDomain product.2 (-1)).next fun lowered outside =>
          (readerType normal isData lowered outside reader).next fun accepted value =>
            (infer accepted continuation).next fun continued afterType =>
              (continuationType normal continued afterType.typeRoot continuation).next fun after head =>
                (shift limit depth after ownerType 1).next fun shifted again =>
                  (compare normal limit depth shifted head.1 value continuation).next fun matched valuePair =>
                    (compare normal limit depth matched head.2.1 again continuation).next fun checked resumeOwner =>
                      (lowerResult normal limit depth checked head.2.2 (-2)).next fun final result =>
                        ⟨final,.ok ⟨result,readType.compared ++ ([readDomain] ++ (afterType.compared ++ [valuePair,resumeOwner]))⟩⟩

def run (infer : Infer) (normal : Visit) (isData isBoxed : Nat → Bool) (limit depth : Nat)
    (state : State) (owner reader continuation : Nat) : Outcome Inferred :=
  (infer state owner).next fun inferred ownerType =>
    (requireOwned normal isBoxed inferred ownerType.typeRoot owner).next fun owns _ =>
      (append owns .ref [ownerType.typeRoot]).next fun withBorrow borrow =>
        (NativeCoreDependentLendCallbacks.run limit depth withBorrow owner reader continuation).next fun prepared shape =>
          let rest := match shape with
            | some callbacks => dependent infer normal isData limit depth prepared owner ownerType.typeRoot borrow reader continuation callbacks
            | none => generic infer normal isData limit depth prepared ownerType.typeRoot borrow reader continuation
          rest.next fun after result => ⟨after,.ok ⟨result.typeRoot,ownerType.compared ++ result.compared⟩⟩

private theorem shift_ok (success : (shift limit depth state root amount).result = .ok selected) :
    (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result = .ok selected := by
  unfold shift at success
  cases found : (NativeCoreTransformExact.run limit depth state root (.shift amount) 0).result <;>
    simp only [found,Except.mapError,reduceCtorEq,Except.ok.injEq] at success ⊢
  exact success

private theorem shift_progress : Progress limit state (shift limit depth state root amount) := by
  have progress := NativeCoreTransformExact.run_progress limit depth state root (.shift amount) 0
  exact ⟨progress.kept,progress.monotone,progress.bounded,fun room _ success => progress.accepted room _ (shift_ok success)⟩

private theorem readerType_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (readerType normal isData state type reader) := by
  unfold readerType
  apply (normalizes _ _).next
  intro root
  split <;> exact Progress.atState _ _

private theorem lowerResult_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (lowerResult normal limit depth state root amount) :=
  (normalizes _ _).next fun _ => shift_progress

private theorem compare_progress (normalizes : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) : Progress limit state (compare normal limit depth state actual expected atRoot) :=
  requireTypes_progress (fun current root _ => normalizes current root) room

private theorem dependent_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (dependent infer normal isData limit depth state owner ownerType borrow reader continuation callbacks) := by
  unfold dependent
  apply next_progress (inferBinder_progress infers normalizes room) room
  intro _ _ binderRoom
  apply next_progress (compare_progress normalizes binderRoom) binderRoom
  intro _ _ readerRoom
  apply next_progress (infers _ _ readerRoom) readerRoom
  intro _ _ inferredRoom
  apply next_progress (readerType_progress normalizes) inferredRoom
  intro _ _ readRoom
  split
  · exact Progress.atState _ _
  · apply next_progress shift_progress readRoom
    intro _ _ shiftRoom
    apply next_progress (inferBinder_progress infers normalizes shiftRoom) shiftRoom
    intro _ _ firstRoom
    apply next_progress (compare_progress normalizes firstRoom) firstRoom
    intro _ _ comparisonRoom
    apply next_progress (compare_progress normalizes comparisonRoom) comparisonRoom
    intro _ _ continuationRoom
    apply next_progress (infers _ _ continuationRoom) continuationRoom
    intro _ _ _
    exact (product_progress normalizes).next (fun _ =>
      (lowerResult_progress normalizes).next (fun _ => Progress.atState _ _))

private theorem continuationType_progress (normalizes : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (continuationType normal state type continuation) := by
  unfold continuationType
  exact (product_progress normalizes).next (fun _ => by split <;> exact Progress.atState _ _)

private theorem generic_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (generic infer normal isData limit depth state ownerType borrow reader continuation) := by
  unfold generic
  apply next_progress (infers _ _ room) room
  intro _ _ readRoom
  apply next_progress (product_progress normalizes) readRoom
  intro _ _ domainRoom
  apply next_progress (compare_progress normalizes domainRoom) domainRoom
  intro _ _ compareRoom
  apply next_progress shift_progress compareRoom
  intro _ _ shiftedRoom
  apply next_progress (readerType_progress normalizes) shiftedRoom
  intro _ _ afterReader
  apply next_progress (infers _ _ afterReader) afterReader
  intro _ _ continuationRoom
  apply next_progress (continuationType_progress normalizes) continuationRoom
  intro _ _ codomainRoom
  apply next_progress shift_progress codomainRoom
  intro _ _ shiftedOwner
  apply next_progress (compare_progress normalizes shiftedOwner) shiftedOwner
  intro _ _ matchedValue
  apply next_progress (compare_progress normalizes matchedValue) matchedValue
  intro _ _ _
  exact (lowerResult_progress normalizes).next (fun _ => Progress.atState _ _)

theorem run_progress
    (infers : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalizes : ∀ state root, Progress limit state (normal state root)) (room : state.steps ≤ limit) :
    Progress limit state (run infer normal isData isBoxed limit depth state owner reader continuation) := by
  unfold run
  apply next_progress (infers _ _ room) room
  intro _ _ typedRoom
  apply next_progress (requireOwned_progress normalizes) typedRoom
  intro _ _ ownedRoom
  apply next_progress (append_progress _ _ _) ownedRoom
  intro _ _ referenceRoom
  apply next_progress NativeCoreDependentLendCallbacks.run_progress referenceRoom
  intro shape _ ready
  cases shape with
  | none => exact (generic_progress infers normalizes ready).next (fun _ => Progress.atState _ _)
  | some callbacks => exact (dependent_progress infers normalizes ready).next (fun _ => Progress.atState _ _)

private theorem outlived_sound (metadata : DataFamilies env isData)
    (represented : Represents arena root term) (accepted : outlived isData arena root = true) :
    Lending.outlivedHead env (expand env term) = true := by
  unfold outlived at accepted
  cases represented with
  | var read => simp only [read,reduceCtorEq] at accepted
  | @node _ op refs terms read arity children =>
    simp only [read] at accepted
    cases op
    case u64 | i64 | refine | array | buffer | back =>
      have length := (NativeCoreIdentical.represented_length children).symm.trans arity
      first
      | have empty : terms.length = 0 := length
        rw [List.length_eq_zero_iff.mp empty]
        simp [expand,expandArgs,Lending.outlivedHead]
      | have one : terms.length = 1 := length
        rcases terms with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> simp at one
        simp only [expand,expandArgs,Lending.outlivedHead]
      | have two : terms.length = 2 := length
        rcases terms with _ | ⟨_,_ | ⟨_,_ | ⟨_,_⟩⟩⟩ <;> simp at two
        simp only [expand,expandArgs,Lending.outlivedHead]
    case ind family count =>
      obtain ⟨entry,found,data⟩ := metadata family accepted
      simp only [expand,Lending.outlivedHead,found,Option.any_some,data]
    all_goals cases accepted

private theorem readerType_refines (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena type T)
    (success : (readerType normal isData state type reader).result = .ok selected) :
    let after := (readerType normal isData state type reader).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ A, Represents after selected A ∧ RawLend.Conv env (expand env T) (expand env A) ∧
        LoanTyping.Outlived env (expand env A) := by
  unfold readerType at success ⊢
  obtain ⟨root,normalOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  split at success
  · rename_i accepted
    cases success
    simp only [ite_eq_left accepted]
    obtain ⟨kept,backward,ranged,represented,normalized⟩ := normalSound onBase source normalOk
    exact ⟨kept,backward,ranged,represented,normalized.converted,
      _,.refl _,outlived_sound metadata represented accepted⟩
  · cases success

private theorem shift_refines
    (source : Represents state.arena root written)
    (success : (shift limit depth state root amount).result = .ok selected) :
    let after := (shift limit depth state root amount).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ residual, Represents after selected residual ∧ PartialRenaming.shift amount 0 written = some residual := by
  obtain ⟨kept,backward,residual,meaning,represented⟩ := (NativeCoreTransformExact.run_refines
    (mode := .shift amount) (binders := 0) (value := written) source trivial (shift_ok success)).1
  exact ⟨kept,backward,residual,represented,meaning⟩

private theorem scoped_renaming (amount : Nat) : PartialRenaming.raiseIndex 0 amount = fun index => index+amount := by
  funext index
  simp [PartialRenaming.raiseIndex]

private theorem expanded_lowering (wf : UnifiedProgram.EnvWellFormed env)
    (negative : amount < 0) (lowered : PartialRenaming.shift amount 0 original = some outside) :
    PartialRenaming.shift amount 0 (expand env original) = some (expand env outside) := by
  have rename := PartialRenaming.shift_negative_reweakens negative lowered
  rw [← rename,EnvironmentDelta.expand_renaming wf.admissible,PartialRenaming.shift_negative negative,
    scoped_renaming]
  exact Environment.lower_raised (expand env outside) (-amount).toNat

private theorem raise_owner_refines
    (source : Represents state.arena root written)
    (success : (shift limit depth state root 1).result = .ok selected) :
    let after := (shift limit depth state root 1).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ Represents after selected (written.rename Nat.succ) := by
  obtain ⟨kept,backward,residual,represented,meaning⟩ := shift_refines source success
  rw [PartialRenaming.shift_nonnegative (by decide : (0 : Int) ≤ 1),scoped_renaming] at meaning
  cases meaning
  exact ⟨kept,backward,represented⟩

private theorem lowerResult_refines (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena root written)
    (negative : amount < 0)
    (success : (lowerResult normal limit depth state root amount).result = .ok selected) :
    let after := (lowerResult normal limit depth state root amount).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ normalType outside, Represents after selected outside ∧ RawLend.Conv env (expand env written) normalType ∧
        PartialRenaming.shift amount 0 normalType = some (expand env outside) := by
  unfold lowerResult at success ⊢
  obtain ⟨result,normalOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨normalKept,normalBack,normalType,represented,converted⟩ := normalSound onBase source normalOk
  obtain ⟨lowerKept,lowerBack,outside,held,lowered⟩ := shift_refines represented success
  exact ⟨normalKept.trans lowerKept,lowerBack ∘ normalBack,expand env normalType,outside,held,
    converted.converted,expanded_lowering wf negative lowered⟩

private theorem continuationType_refines (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (source : Represents state.arena type written)
    (success : (continuationType normal state type continuation).result = .ok triple) :
    let after := (continuationType normal state type continuation).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ first again result, Represents after triple.1 first ∧ Represents after triple.2.1 again ∧
        Represents after triple.2.2 result ∧
          RawLend.Conv env (expand env written) (.pi false (expand env first) (.pi false (expand env again) (expand env result))) := by
  unfold continuationType at success ⊢
  obtain ⟨pair,productOk,next⟩ := Outcome.next_success success
  rw [next] at success ⊢
  obtain ⟨kept,backward,first,remaining,firstRep,innerRep,converted⟩ := product_refines normalSound onBase source productOk
  split at success
  · rename_i owner result read
    cases success
    cases innerRep with
    | var found => rw [read] at found; cases found
    | node found _ children =>
      rw [read] at found
      cases found
      cases children with
      | cons ownerRep rest =>
        cases rest with
        | cons resultRep tail =>
          cases tail
          exact ⟨kept,backward,_,_,_,firstRep,ownerRep,resultRep,
            by simpa only [Term.pi,expand,expandArgs] using converted⟩
  · cases success

private theorem generic_result_weakening (type result : Term) :
    (.pi false type (result.rename Nat.succ) : Term).rename Nat.succ =
      .pi false (type.rename Nat.succ) (result.rename (fun i => i+2)) := by
  simp only [Term.pi,Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_comp]
  rfl

private theorem generic_refines (wf : UnifiedProgram.EnvWellFormed env) (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena ownerType T) (borrowRep : Represents state.arena borrow (.ref T))
    (readerRep : Represents state.arena reader readerTerm) (contRep : Represents state.arena continuation contTerm)
    (ownerTyped : LoanTyping.HasType env [] ctx true (expand env ownerTerm) (expand env T))
    (owned : LoanTyping.Owned env (expand env T))
    (success : (generic infer normal isData limit depth state ownerType borrow reader continuation).result = .ok answer)
    (ambient : Prefix (generic infer normal isData limit depth state ownerType borrow reader continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.lend ownerTerm readerTerm contTerm)
      (generic infer normal isData limit depth state ownerType borrow reader continuation) answer := by
  unfold generic at success ambient ⊢
  obtain ⟨readType,readOk,readNext⟩ := Outcome.next_success success
  rw [readNext] at success ambient ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ambient ⊢
  obtain ⟨readDomain,readDomainOk,readDomainNext⟩ := Outcome.next_success success
  rw [readDomainNext] at success ambient ⊢
  obtain ⟨outside,outsideOk,outsideNext⟩ := Outcome.next_success success
  rw [outsideNext] at success ambient ⊢
  obtain ⟨value,valueOk,valueNext⟩ := Outcome.next_success success
  rw [valueNext] at success ambient ⊢
  obtain ⟨continuationResult,contOk,contNext⟩ := Outcome.next_success success
  rw [contNext] at success ambient ⊢
  obtain ⟨head,headOk,headNext⟩ := Outcome.next_success success
  rw [headNext] at success ambient ⊢
  obtain ⟨raised,raisedOk,raisedNext⟩ := Outcome.next_success success
  rw [raisedNext] at success ambient ⊢
  obtain ⟨valuePair,valuePairOk,valuePairNext⟩ := Outcome.next_success success
  rw [valuePairNext] at success ambient ⊢
  obtain ⟨ownerPair,ownerPairOk,ownerPairNext⟩ := Outcome.next_success success
  rw [ownerPairNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let readRun := infer state reader
  let productRun := exposeProduct normal readRun.state readType.typeRoot reader
  let domainRun := compare normal limit depth productRun.state product.1 borrow reader
  let outsideRun := shift limit depth domainRun.state product.2 (-1)
  let valueRun := readerType normal isData outsideRun.state outside reader
  let resumeRun := infer valueRun.state continuation
  let headRun := continuationType normal resumeRun.state continuationResult.typeRoot continuation
  let raisedRun := shift limit depth headRun.state ownerType 1
  let valueCompare := compare normal limit depth raisedRun.state head.1 value continuation
  let ownerCompare := compare normal limit depth valueCompare.state head.2.1 raised continuation
  have readCost := inferProgress state reader room
  have readRoom := readCost.accepted room readType readOk
  have productCost := product_progress (state := readRun.state) (type := readType.typeRoot) (motive := reader) normalProgress
  have productRoom := productCost.accepted readRoom product productOk
  have domainCost := compare_progress (state := productRun.state) (depth := depth) (actual := product.1)
    (expected := borrow) (atRoot := reader) normalProgress productRoom
  have domainRoom := domainCost.accepted productRoom readDomain readDomainOk
  have outsideCost := shift_progress (limit := limit) (depth := depth) (state := domainRun.state) (root := product.2) (amount := -1)
  have outsideRoom := outsideCost.accepted domainRoom outside outsideOk
  have valueCost := readerType_progress (limit := limit) (isData := isData) (state := outsideRun.state)
    (type := outside) (reader := reader) normalProgress
  have valueRoom := valueCost.accepted outsideRoom value valueOk
  have resumeCost := inferProgress valueRun.state continuation valueRoom
  have resumeRoom := resumeCost.accepted valueRoom continuationResult contOk
  have headCost := continuationType_progress (limit := limit) (state := resumeRun.state)
    (type := continuationResult.typeRoot) (continuation := continuation) normalProgress
  have headRoom := headCost.accepted resumeRoom head headOk
  have raiseCost := shift_progress (limit := limit) (depth := depth) (state := headRun.state)
    (root := ownerType) (amount := 1)
  have raiseRoom := raiseCost.accepted headRoom raised raisedOk
  have valueCompareCost := compare_progress (state := raisedRun.state) (depth := depth) (actual := head.1)
    (expected := value) (atRoot := continuation) normalProgress raiseRoom
  have valueCompareRoom := valueCompareCost.accepted raiseRoom valuePair valuePairOk
  have ownerCompareCost := compare_progress (state := valueCompare.state) (depth := depth) (actual := head.2.1)
    (expected := raised) (atRoot := continuation) normalProgress valueCompareRoom
  have finalCost := lowerResult_progress (limit := limit) (depth := depth) (state := ownerCompare.state)
    (root := head.2.2) (amount := -2) normalProgress
  have afterOwner := finalCost.kept.trans ambient
  have afterValueComparison := ownerCompareCost.kept.trans afterOwner
  have afterRaise := valueCompareCost.kept.trans afterValueComparison
  have afterHead := raiseCost.kept.trans afterRaise
  have afterResume := headCost.kept.trans afterHead
  have afterValue := resumeCost.kept.trans afterResume
  have afterOutside := valueCost.kept.trans afterValue
  have afterDomain := outsideCost.kept.trans afterOutside
  have afterProduct := domainCost.kept.trans afterDomain
  have afterRead := productCost.kept.trans afterProduct
  obtain ⟨readKept,readBack,_,rawRead,readTyped⟩ := inferSound onBase room readerRep readOk afterRead
    (fun pair member => retained pair (by simp [member]))
  obtain ⟨productKept,productBack,readerAnnotation,_,domainRep,readResultRep,readConverted⟩ := product_refines normalSound
    (onBase.trans readKept) rawRead productOk
  have throughProduct := readKept.trans productKept
  obtain ⟨domainKept,domainBack,readerDomain⟩ := requireTypes_refines normalSound (onBase.trans throughProduct)
    domainRep (borrowRep.frame throughProduct) readDomainOk afterDomain (retained readDomain (by simp))
  have throughDomain := throughProduct.trans domainKept
  obtain ⟨outsideKept,outsideBack,_,outsideRep,loweredRead⟩ := shift_refines
    (readResultRep.frame domainKept) outsideOk
  have throughOutside := throughDomain.trans outsideKept
  obtain ⟨valueKept,valueBack,A,valueRep,valueConverted,outlives⟩ := readerType_refines metadata normalSound
    (onBase.trans throughOutside) outsideRep valueOk
  have throughValue := throughOutside.trans valueKept
  obtain ⟨resumeKept,resumeBack,_,rawResume,resumeTyped⟩ := inferSound (onBase.trans throughValue) valueRoom
    (contRep.frame throughValue) contOk afterResume (fun pair member => retained pair (by simp [member]))
  have throughResume := throughValue.trans resumeKept
  obtain ⟨headKept,headBack,_,againAnnotation,_,firstRep,againRep,resultRep,resumeConverted⟩ :=
    continuationType_refines normalSound (onBase.trans throughResume) rawResume headOk
  have throughHead := throughResume.trans headKept
  obtain ⟨raiseKept,raiseBack,raisedRep⟩ := raise_owner_refines (ownerRep.frame throughHead) raisedOk
  have throughRaise := throughHead.trans raiseKept
  have valueBefore := resumeKept.trans (headKept.trans raiseKept)
  obtain ⟨valuePairKept,valuePairBack,firstConverted⟩ := requireTypes_refines normalSound (onBase.trans throughRaise)
    (firstRep.frame raiseKept) (valueRep.frame valueBefore) valuePairOk afterValueComparison (retained valuePair (by simp))
  have throughValuePair := throughRaise.trans valuePairKept
  obtain ⟨ownerPairKept,ownerPairBack,againConverted⟩ := requireTypes_refines normalSound (onBase.trans throughValuePair)
    (againRep.frame (raiseKept.trans valuePairKept)) (raisedRep.frame valuePairKept)
    ownerPairOk afterOwner (retained ownerPair (by simp))
  have throughOwner := throughValuePair.trans ownerPairKept
  obtain ⟨resultKept,resultBack,normalResult,R,finalRep,resultConverted,loweredResult⟩ := lowerResult_refines wf normalSound
    (onBase.trans throughOwner) (resultRep.frame (raiseKept.trans (valuePairKept.trans ownerPairKept)))
    (by decide : (-2 : Int) < 0) resultOk
  have readRenamed := PartialRenaming.shift_negative_reweakens (by decide : (-1 : Int) < 0)
    (expanded_lowering wf (by decide : (-1 : Int) < 0) loweredRead)
  rw [scoped_renaming] at readRenamed
  have readerDomainConverted : RawLend.Conv env (expand env readerAnnotation) (.ref (expand env T)) := by
    simpa only [Term.ref,expand,expandArgs] using readerDomain
  have readerCodomain := readRenamed ▸ (valueConverted.renaming Nat.succ wf.closed)
  have readerCheck := readTyped.convert (readConverted.trans
    (.node (.pi false) (.cons readerDomainConverted (.cons readerCodomain .nil))))
  have again : RawLend.Conv env (expand env againAnnotation) ((expand env T).rename Nat.succ) := by
    simpa only [EnvironmentDelta.expand_renaming wf.admissible] using againConverted
  have resultRenamed := load_result_reweakens loweredResult
  have resultAligned := resultRenamed ▸ resultConverted
  have resumeCheck := resumeTyped.convert (resumeConverted.trans (.node (.pi false) (.cons firstConverted
    (.cons (.node (.pi false) (.cons again (.cons resultAligned .nil))) .nil))))
  change LoanTyping.HasType env [] ctx true (expand env contTerm)
    (.pi false (expand env A) (.pi false ((expand env T).rename Nat.succ) ((expand env R).rename (fun i => i+2)))) at resumeCheck
  rw [← generic_result_weakening] at resumeCheck
  refine ⟨throughOwner.trans resultKept,resultBack ∘ ownerPairBack ∘ valuePairBack ∘ raiseBack ∘ headBack ∘
    resumeBack ∘ valueBack ∘ outsideBack ∘ domainBack ∘ productBack ∘ readBack,R,finalRep,?_⟩
  simpa only [Term.lend,expand,expandArgs] using
    LoanTyping.HasType.lendGeneric ownerTyped owned outlives readerCheck resumeCheck (.inl rfl)

/-- When the source callbacks select the generic branch, completed native
inference constructs a Loan64 Lend derivation at the returned outer type. -/
theorem run_generic_refines (wf : UnifiedProgram.EnvWellFormed env)
    (data : DataFamilies env isData) (boxed : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena owner x) (readerRep : Represents state.arena reader f)
    (contRep : Represents state.arena continuation g)
    (ordinary : NativeCoreDependentLendCallbacks.select state.arena owner reader continuation = none)
    (success : (run infer normal isData isBoxed limit depth state owner reader continuation).result = .ok answer)
    (ambient : Prefix (run infer normal isData isBoxed limit depth state owner reader continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.lend x f g) (run infer normal isData isBoxed limit depth state owner reader continuation) answer := by
  unfold run at success ambient ⊢
  obtain ⟨ownerResult,ownerOk,ownerNext⟩ := Outcome.next_success success
  rw [ownerNext] at success ambient ⊢
  obtain ⟨_,ownedOk,ownedNext⟩ := Outcome.next_success success
  rw [ownedNext] at success ambient ⊢
  obtain ⟨borrow,borrowOk,borrowNext⟩ := Outcome.next_success success
  rw [borrowNext] at success ambient ⊢
  let checkedOwner := infer state owner
  let checkedOwned := requireOwned normal isBoxed checkedOwner.state ownerResult.typeRoot owner
  let builtBorrow := append checkedOwned.state .ref [ownerResult.typeRoot]
  have ownerCost := inferProgress state owner room
  have ownedRoom := ownerCost.accepted room ownerResult ownerOk
  have ownedCost := requireOwned_progress (state := checkedOwner.state) (isBoxed := isBoxed)
    (root := ownerResult.typeRoot) (rejected := owner) normalProgress
  have borrowRoom := ownedCost.accepted ownedRoom () ownedOk
  have borrowCost := append_progress (limit := limit) checkedOwned.state .ref [ownerResult.typeRoot]
  have startRoom := borrowCost.accepted borrowRoom borrow borrowOk
  have kept := ownerCost.kept.trans (ownedCost.kept.trans borrowCost.kept)
  have selected : NativeCoreDependentLendCallbacks.select builtBorrow.state.arena owner reader continuation = none :=
    (NativeCoreDependentLendCallbacks.select_frame ownerRep readerRep contRep kept).trans ordinary
  rw [NativeCoreDependentLendCallbacks.run_none selected] at success ambient ⊢
  simp only [Outcome.next] at success ambient ⊢
  cases last : (generic infer normal isData limit depth builtBorrow.state ownerResult.typeRoot borrow reader continuation).result with
  | error reason => simp only [last,reduceCtorEq] at success
  | ok accepted =>
    simp only [last,Except.ok.injEq] at success ambient ⊢
    subst answer
    have genericCost := generic_progress (state := builtBorrow.state) (isData := isData)
      (depth := depth) (ownerType := ownerResult.typeRoot) (borrow := borrow) (reader := reader)
      (continuation := continuation) inferProgress normalProgress startRoom
    have afterBorrow := genericCost.kept.trans ambient
    obtain ⟨ownerKept,ownerBack,_,ownerTypeRep,typed⟩ := inferSound onBase room ownerRep ownerOk
      (ownedCost.kept.trans (borrowCost.kept.trans afterBorrow))
      (fun pair member => retained pair (List.mem_append_left _ member))
    obtain ⟨ownedKept,ownedBack,owns⟩ := requireOwned_refines boxed normalSound
      (onBase.trans ownerKept) ownerTypeRep ownedOk
    obtain ⟨borrowKept,borrowBack,borrowRep⟩ := append_refines (.cons (ownerTypeRep.frame ownedKept) .nil) rfl borrowOk
    obtain ⟨done,doneBack,inferred⟩ := generic_refines wf data normalSound normalProgress inferSound inferProgress
      (onBase.trans kept) startRoom (ownerTypeRep.frame (ownedKept.trans borrowKept)) borrowRep
      (readerRep.frame kept) (contRep.frame kept) typed owns last ambient
      (fun pair member => retained pair (List.mem_append_right _ member))
    exact ⟨kept.trans done,doneBack ∘ borrowBack ∘ ownedBack ∘ ownerBack,inferred⟩

private theorem expand_read (wf : UnifiedProgram.EnvWellFormed env) (index : Nat) (body : Term) :
    expand env (Lending.read (.var index) body) = Lending.read (.var index) (expand env body) := by
  unfold Lending.read
  rw [EnvironmentDelta.expand_substitution wf.admissible]
  congr 1
  funext slot
  cases slot <;> simp only [single,Term.borrow,expand,expandArgs]

/-- The native dependent CODE reader is checked after its written
domain is formed and compared to the inferred reference of the owner. -/
def runScopedReader (inferAnnotation : Infer) (inferCode : List NativeCoreCodeLeaseLookup.Snapshot → Infer)
    (normal : Visit) (isData : Nat → Bool) (limit depth width : Nat) (state : State)
    (snapshots : List NativeCoreCodeLeaseLookup.Snapshot) (owner borrow reader : Nat)
    (callbacks : NativeCoreDependentLendCallbacks.Prepared) : Outcome Inferred :=
  (inferBinder inferAnnotation normal isData state callbacks.domain false).next fun afterDomain binder =>
    (compare normal limit depth afterDomain callbacks.domain borrow reader).next fun afterMatch matched =>
      (inferCode (⟨width,owner⟩ :: snapshots) afterMatch callbacks.reader).next fun afterBody checked =>
        (readerType normal isData afterBody checked.typeRoot reader).next fun after result =>
          ⟨after,.ok ⟨result,binder.compared ++ matched :: checked.compared⟩⟩

theorem runScopedReader_progress
    (annotationProgress : ∀ state root, state.steps ≤ limit →
      Progress limit state (inferAnnotation state root))
    (codeProgress : ∀ saved state root, state.steps ≤ limit →
      Progress limit state (inferCode saved state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runScopedReader inferAnnotation inferCode normal isData limit depth width state
      snapshots owner borrow reader callbacks) := by
  unfold runScopedReader
  apply next_progress (inferBinder_progress annotationProgress normalProgress room) room
  intro _ _ binderRoom
  apply next_progress (compare_progress normalProgress binderRoom) binderRoom
  intro _ _ bodyRoom
  apply next_progress (codeProgress _ _ _ bodyRoom) bodyRoom
  intro _ _ _
  exact (readerType_progress normalProgress).next fun _ => Progress.atState _ _

/-- The checked callback runs at the original context width with a new
snapshot for the represented owner. Its result is normalized to an
outlived representation while the written reader type is preserved. -/
theorem runScopedReader_refines
    (wf : UnifiedProgram.EnvWellFormed env) (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (annotationSound : InferSound env base ctx limit inferAnnotation)
    (annotationProgress : ∀ state root, state.steps ≤ limit →
      Progress limit state (inferAnnotation state root))
    (codeSound : ∀ {arena}, Prefix base arena →
      NativeCoreCodeLeaseLookup.FramesRep arena (⟨ctx.length,owner⟩ :: snapshots)
        (Loans.enter ctx.length index loans) →
      NativeCoreBufferRelease.ModeSound env (Loans.enter ctx.length index loans) arena ctx limit false
        (inferCode (⟨ctx.length,owner⟩ :: snapshots)))
    (codeProgress : ∀ saved state root, state.steps ≤ limit →
      Progress limit state (inferCode saved state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (frames : NativeCoreCodeLeaseLookup.FramesRep state.arena snapshots loans)
    (ownerRep : Represents state.arena owner (.var index))
    (borrowRep : Represents state.arena borrow (.ref T))
    (domainRep : Represents state.arena callbacks.domain domain)
    (readerRep : Represents state.arena callbacks.reader (Lending.read (.var index) readBody))
    (success : (runScopedReader inferAnnotation inferCode normal isData limit depth ctx.length state
      snapshots owner borrow reader callbacks).result = .ok answer)
    (ambient : Prefix (runScopedReader inferAnnotation inferCode normal isData limit depth ctx.length state
      snapshots owner borrow reader callbacks).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (runScopedReader inferAnnotation inferCode normal isData limit depth ctx.length state
      snapshots owner borrow reader callbacks).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ sort type, Represents after answer.typeRoot type ∧
        LoanTyping.Binder env loans ctx false (expand env domain) sort ∧
        RawLend.Conv env (expand env domain) (.ref (expand env T)) ∧
        LoanTyping.HasType env (Loans.enter ctx.length index loans) ctx false
          (Lending.read (.var index) (expand env readBody)) (expand env type) ∧
        LoanTyping.Outlived env (expand env type) := by
  unfold runScopedReader at success ambient ⊢
  obtain ⟨binder,binderOk,binderNext⟩ := Outcome.next_success success
  rw [binderNext] at success ambient ⊢
  obtain ⟨matched,matchedOk,matchedNext⟩ := Outcome.next_success success
  rw [matchedNext] at success ambient ⊢
  obtain ⟨checked,checkedOk,checkedNext⟩ := Outcome.next_success success
  rw [checkedNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let bound := inferBinder inferAnnotation normal isData state callbacks.domain false
  let matching := compare normal limit depth bound.state callbacks.domain borrow reader
  let saved := (⟨ctx.length,owner⟩ : NativeCoreCodeLeaseLookup.Snapshot) :: snapshots
  let evaluated := inferCode saved matching.state callbacks.reader
  have binderProgress := inferBinder_progress (state := state) (domain := callbacks.domain) (erased := false)
    (isData := isData) annotationProgress normalProgress room
  have binderRoom := binderProgress.accepted room binder binderOk
  have matchingProgress := compare_progress (state := bound.state) (depth := depth)
    (actual := callbacks.domain) (expected := borrow) (atRoot := reader) normalProgress binderRoom
  have matchingRoom := matchingProgress.accepted binderRoom matched matchedOk
  have readingProgress := codeProgress saved matching.state callbacks.reader matchingRoom
  have outlivingProgress := readerType_progress (limit := limit) (isData := isData) (state := evaluated.state)
    (type := checked.typeRoot) (reader := reader) normalProgress
  have finalAfterBody := outlivingProgress.kept.trans ambient
  have finalAfterMatch := readingProgress.kept.trans finalAfterBody
  obtain ⟨boundKept,boundBack,typedDomain⟩ := inferBinder_refines metadata normalSound normalProgress
    annotationSound annotationProgress onBase room domainRep binderOk (matchingProgress.kept.trans finalAfterMatch)
    (fun pair member => retained pair (List.mem_append_left _ member))
  obtain ⟨matchKept,matchBack,converted⟩ := requireTypes_refines normalSound (onBase.trans boundKept)
    (domainRep.frame boundKept) (borrowRep.frame boundKept) matchedOk finalAfterMatch
    (retained matched (by simp))
  have throughMatch := boundKept.trans matchKept
  have savedFrames := (frames.frame throughMatch).enter (current := ctx.length) (ownerRep.frame throughMatch)
  obtain ⟨bodyKept,bodyBack,_,bodyType,typedRead⟩ := codeSound (onBase.trans throughMatch) savedFrames
    (.refl _) matchingRoom (readerRep.frame throughMatch) checkedOk finalAfterBody
    (fun pair member => retained pair (List.mem_append_right _ (List.mem_cons_of_mem _ member)))
  have throughBody := throughMatch.trans bodyKept
  obtain ⟨resultKept,resultBack,ty,represented,valueConversion,outlived⟩ := readerType_refines metadata normalSound
    (onBase.trans throughBody) bodyType resultOk
  rw [expand_read wf] at typedRead
  refine ⟨throughBody.trans resultKept,resultBack ∘ bodyBack ∘ matchBack ∘ boundBack,
    binder.sort,ty,represented,?_,?_,typedRead.convert valueConversion,outlived⟩
  · cases typedDomain with
    | intro typed allowed => exact .intro (typed.ghost loans) allowed
  · simpa only [Term.ref,expand,expandArgs] using converted

private def scopedReturn (gate : State → Nat → Nat → Outcome Unit) (normal : Visit) (limit depth : Nat) (state : State)
    (slot restored continuation type : Nat) : Outcome Nat :=
  (exposeProduct normal state type continuation).next fun exposed product =>
    (NativeCoreCodeLendGates.ownerOnce limit depth slot exposed restored).next fun used _ =>
      (lowerResult normal limit depth used product.2 (-1)).next fun lowered result =>
        (gate lowered result continuation).next fun after _ =>
          ⟨after,.ok result⟩

/-- The final native head check retains the lowered root after the
product, returned-owner and lexical escape checks. -/
def runScopedReturn (normal : Visit) (limit depth : Nat) (state : State)
    (slot restored continuation type : Nat) : Outcome Nat :=
  scopedReturn (NativeCoreCodeLendGates.checkResult normal) normal limit depth state slot restored continuation type

def runCanonicalReturn (normal : Visit) (limit depth : Nat) (state : State)
    (slot restored continuation type : Nat) : Outcome Nat :=
  scopedReturn (NativeCoreCodeLendGates.checkCanonical normal) normal limit depth state slot restored continuation type

private theorem scopedReturn_progress
    (gateProgress : ∀ state root atRoot, Progress limit state (gate state root atRoot))
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (scopedReturn gate normal limit depth state slot restored continuation type) := by
  unfold scopedReturn
  apply (product_progress normalProgress).next
  intro product
  apply NativeCoreCodeLendGates.ownerOnce_progress.next
  intro _
  apply (lowerResult_progress normalProgress).next
  intro output
  exact (gateProgress _ _ _).next
    (fun _ => Progress.atState _ _)

theorem runScopedReturn_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (runScopedReturn normal limit depth state slot restored continuation type) :=
  scopedReturn_progress (fun _ _ _ => NativeCoreCodeLendGates.checkResult_progress normalProgress) normalProgress

theorem runCanonicalReturn_progress
    (normalProgress : ∀ state root, Progress limit state (normal state root)) :
    Progress limit state (runCanonicalReturn normal limit depth state slot restored continuation type) :=
  scopedReturn_progress (fun _ _ _ => NativeCoreCodeLendGates.checkCanonical_progress normalProgress) normalProgress

private theorem scopedReturn_refines {postcondition : Term → Prop}
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (gateSound : ∀ {current root term}, Prefix base current.arena → Represents current.arena root term →
      (gate current root continuation).result = .ok () →
      Prefix current.arena (gate current root continuation).state.arena ∧
        (Backward current.arena → Backward (gate current root continuation).state.arena) ∧ postcondition term)
    (onBase : Prefix base state.arena) (typeRep : Represents state.arena type annotation)
    (bodyRep : Represents state.arena body written)
    (lambdaRead : state.arena[restored]? = some (.node (.lam erased) [domain,body]))
    (success : (scopedReturn gate normal limit depth state slot restored continuation type).result = .ok answer) :
    let after := (scopedReturn gate normal limit depth state slot restored continuation type).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ first codomain normalized result control, Represents after answer result ∧
        RawLend.Conv env (expand env annotation) (.pi false (expand env first) (expand env codomain)) ∧
        RawLend.Conv env (expand env codomain) normalized ∧
        PartialRenaming.shift (-1) 0 normalized = some (expand env result) ∧
        NativeCoreCodeUses.Projects written control ∧ control.demand (slot+1) = some 1 ∧
        postcondition result := by
  unfold scopedReturn at success ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ⊢
  obtain ⟨⟨⟩,single,singleNext⟩ := Outcome.next_success success
  rw [singleNext] at success ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ⊢
  obtain ⟨⟨⟩,gateOk,gateNext⟩ := Outcome.next_success success
  rw [gateNext] at success ⊢
  cases success
  let exposed := exposeProduct normal state type continuation
  let used := NativeCoreCodeLendGates.ownerOnce limit depth slot exposed.state restored
  let lowered := lowerResult normal limit depth used.state product.2 (-1)
  obtain ⟨productKept,productBack,first,codomain,_,codomainRep,typed⟩ :=
    product_refines normalSound onBase typeRep productOk
  obtain ⟨same,control,projected,once⟩ :=
    NativeCoreCodeLendGates.openedOwnerOnce_refines (bodyRep.frame productKept)
      (productKept.lookup lambdaRead) single
  have usedKept : Prefix exposed.state.arena used.state.arena := same.symm ▸ .refl _
  have usedBack : Backward exposed.state.arena → Backward used.state.arena := fun h => same.symm ▸ h
  have beforeLower := productKept.trans usedKept
  obtain ⟨lowerKept,lowerBack,normalized,result,represented,converted,shifted⟩ :=
    lowerResult_refines wf normalSound (onBase.trans beforeLower) (codomainRep.frame usedKept)
      (by decide : (-1 : Int) < 0) resultOk
  have beforeGate := beforeLower.trans lowerKept
  obtain ⟨gateKept,gateBack,post⟩ := gateSound (onBase.trans beforeGate) represented gateOk
  exact ⟨beforeGate.trans gateKept,gateBack ∘ lowerBack ∘ usedBack ∘ productBack,
    first,codomain,normalized,result,control,represented.frame gateKept,
    typed,converted,shifted,projected,once,post⟩

/-- The exact continuation checks retain the body type plus the owner's
one-use observation. The lowered result and its final observed head
remain connected by native conversion. -/
theorem runScopedReturn_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (typeRep : Represents state.arena type annotation)
    (bodyRep : Represents state.arena body written)
    (lambdaRead : state.arena[restored]? = some (.node (.lam erased) [domain,body]))
    (success : (runScopedReturn normal limit depth state slot restored continuation type).result = .ok answer) :
    let after := (runScopedReturn normal limit depth state slot restored continuation type).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ first codomain normalized result observed control, Represents after answer result ∧
        RawLend.Conv env (expand env annotation) (.pi false (expand env first) (expand env codomain)) ∧
        RawLend.Conv env (expand env codomain) normalized ∧
        PartialRenaming.shift (-1) 0 normalized = some (expand env result) ∧
        RawLend.Conv env (expand env result) (expand env observed) ∧
        (∀ erased D B, observed ≠ Term.pi erased D B) ∧
        NativeCoreCodeUses.Projects written control ∧ control.demand (slot+1) = some 1 := by
  obtain ⟨kept,backward,first,codomain,normalized,result,control,represented,product,converted,shifted,
    projected,once,observed,observation,nonPi⟩ := scopedReturn_refines
      (postcondition := fun term => ∃ observed,
        RawLend.Conv env (expand env term) (expand env observed) ∧ ∀ erased D B, observed ≠ Term.pi erased D B)
      wf normalSound (gate := NativeCoreCodeLendGates.checkResult normal)
      (fun onBase source accepted => by
        obtain ⟨kept,backward,_,observed,_,_,converted,nonPi⟩ :=
          NativeCoreCodeLendGates.checkResult_refines normalSound onBase source accepted
        exact ⟨kept,backward,observed,converted,nonPi⟩) onBase typeRep bodyRep lambdaRead success
  exact ⟨kept,backward,first,codomain,normalized,result,observed,control,represented,
    product,converted,shifted,observation,nonPi,projected,once⟩

/-- The canonical branch supplies the positive continuation policy at
the exact original lowered type. -/
theorem runCanonicalReturn_refines
    (wf : UnifiedProgram.EnvWellFormed env)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (typeRep : Represents state.arena type annotation)
    (bodyRep : Represents state.arena body written)
    (lambdaRead : state.arena[restored]? = some (.node (.lam erased) [domain,body]))
    (success : (runCanonicalReturn normal limit depth state slot restored continuation type).result = .ok answer) :
    let after := (runCanonicalReturn normal limit depth state slot restored continuation type).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ first codomain normalized result control, Represents after answer result ∧
        RawLend.Conv env (expand env annotation) (.pi false (expand env first) (expand env codomain)) ∧
        RawLend.Conv env (expand env codomain) normalized ∧
        PartialRenaming.shift (-1) 0 normalized = some (expand env result) ∧
        NativeCoreCodeUses.Projects written control ∧ control.demand (slot+1) = some 1 ∧
        LoanTyping.continuationAllowed env false (expand env result) :=
  scopedReturn_refines wf normalSound
    (NativeCoreCodeLendGates.checkCanonical_policy normalSound) onBase typeRep bodyRep lambdaRead success

/-- Acceptance of a canonical continuation follows the same native
schedule and returns the same original graph root. -/
theorem runCanonicalReturn_native
    (success : (runCanonicalReturn normal limit depth state slot restored continuation type).result = .ok answer) :
    runCanonicalReturn normal limit depth state slot restored continuation type =
      runScopedReturn normal limit depth state slot restored continuation type := by
  unfold runCanonicalReturn scopedReturn at success ⊢
  unfold runScopedReturn scopedReturn
  obtain ⟨product,productOk,next⟩ := Outcome.next_success success
  rw [next] at success
  obtain ⟨⟨⟩,ownerOk,ownerNext⟩ := Outcome.next_success success
  rw [ownerNext] at success
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success
  obtain ⟨⟨⟩,accepted,_⟩ := Outcome.next_success success
  simp only [Outcome.next,productOk,ownerOk,resultOk,NativeCoreCodeLendGates.checkCanonical_native accepted]

private theorem expand_restore (wf : UnifiedProgram.EnvWellFormed env) (index : Nat) (first body : Term) :
    expand env (Lending.restore (.var index) first body) = Lending.restore (.var index) (expand env first) (expand env body) := by
  simp only [Lending.restore,Term.lam,expand,expandArgs]
  have substitution : (fun x => expand env (single ((Term.var index).rename Nat.succ) x)) =
      single ((Term.var index).rename Nat.succ) := by
    funext slot
    cases slot <;> simp only [single,Term.rename,expand]
  rw [EnvironmentDelta.expand_substitution wf.admissible,substitution]

private def resumeCode (inferAnnotation infer : Infer) (normal : Visit) (isData : Nat → Bool)
    (limit depth : Nat) (state : State) (slot ownerType continuation : Nat)
    (written : NativeCoreDependentLendCallbacks.Callbacks) (restored : Nat) (readerResultRoot : Nat) : Outcome Inferred :=
  (shift limit depth state ownerType 1).next fun shifted again =>
    (inferBinder inferAnnotation normal isData shifted written.first false).next fun checkedFirst first =>
      (compare normal limit depth checkedFirst written.first readerResultRoot continuation).next fun firstMatch valuePair =>
        (compare normal limit depth firstMatch written.again again continuation).next fun checked ownerPair =>
          (infer checked restored).next fun resumed resumeType =>
            (runCanonicalReturn normal limit depth resumed slot restored continuation resumeType.typeRoot).next fun finished result =>
              ⟨finished,.ok ⟨result,first.compared ++ ([valuePair,ownerPair] ++ resumeType.compared)⟩⟩

private def afterScopedReader (inferAnnotation infer : Infer) (normal : Visit) (isData : Nat → Bool)
    (limit depth : Nat) (state : State) (owner ownerType reader continuation restored readerResultRoot : Nat) :
    Outcome Inferred :=
  match NativeCoreDependentLendCallbacks.select state.arena owner reader continuation, state.arena[owner]? with
  | some written,some (.var slot) =>
      resumeCode inferAnnotation infer normal isData limit depth state slot ownerType continuation written restored readerResultRoot
  | _,_ => reject state continuation

/-- The selected native CODE path checks the owner once, specializes the
two written callbacks and uses the new snapshot only in the reader. -/
def runDependentCode (inferAnnotation : Infer) (inferCode : List NativeCoreCodeLeaseLookup.Snapshot → Infer)
    (normal : Visit) (isData isBoxed : Nat → Bool) (limit depth width : Nat) (state : State)
    (snapshots : List NativeCoreCodeLeaseLookup.Snapshot) (owner reader continuation : Nat) : Outcome Inferred :=
  let infer := inferCode snapshots
  (infer state owner).next fun inferred ownerType =>
    (requireOwned normal isBoxed inferred ownerType.typeRoot owner).next fun owns _ =>
      (append owns .ref [ownerType.typeRoot]).next fun withBorrow borrow =>
        (NativeCoreDependentLendCallbacks.run limit depth withBorrow owner reader continuation).next fun prepared shape =>
          match shape with
          | none => reject prepared continuation
          | some callbacks =>
              (runScopedReader inferAnnotation inferCode normal isData limit depth width prepared snapshots owner
                borrow reader callbacks).next fun closed readType =>
                  (afterScopedReader inferAnnotation infer normal isData limit depth closed owner
                    ownerType.typeRoot reader continuation callbacks.continuation readType.typeRoot).next fun after result =>
                      ⟨after,.ok ⟨result.typeRoot,ownerType.compared ++ (readType.compared ++ result.compared)⟩⟩

private theorem resumeCode_progress
    (annotationProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferAnnotation state root))
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (resumeCode inferAnnotation infer normal isData limit depth state slot ownerType continuation
      written restored readerResultRoot) := by
  unfold resumeCode
  apply next_progress shift_progress room
  intro _ _ shiftedRoom
  apply next_progress (inferBinder_progress annotationProgress normalProgress shiftedRoom) shiftedRoom
  intro _ _ binderRoom
  apply next_progress (compare_progress normalProgress binderRoom) binderRoom
  intro _ _ firstRoom
  apply next_progress (compare_progress normalProgress firstRoom) firstRoom
  intro _ _ resumeRoom
  apply next_progress (inferProgress _ _ resumeRoom) resumeRoom
  intro _ _ _
  exact (runCanonicalReturn_progress normalProgress).next (fun _ => Progress.atState _ _)

private theorem afterScopedReader_progress
    (annotationProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferAnnotation state root))
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (afterScopedReader inferAnnotation infer normal isData limit depth state owner ownerType
      reader continuation restored readerResultRoot) := by
  unfold afterScopedReader
  split
  · exact resumeCode_progress annotationProgress inferProgress normalProgress room
  · exact Progress.atState _ _

theorem runDependentCode_progress
    (annotationProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferAnnotation state root))
    (codeProgress : ∀ snapshots state root, state.steps ≤ limit → Progress limit state (inferCode snapshots state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (runDependentCode inferAnnotation inferCode normal isData isBoxed limit depth width
      state snapshots owner reader continuation) := by
  unfold runDependentCode
  apply next_progress (codeProgress _ _ _ room) room
  intro _ _ ownerRoom
  apply next_progress (requireOwned_progress normalProgress) ownerRoom
  intro _ _ ownedRoom
  apply next_progress (append_progress _ _ _) ownedRoom
  intro _ _ borrowedRoom
  apply next_progress NativeCoreDependentLendCallbacks.run_progress borrowedRoom
  intro prepared _ selectedRoom
  cases prepared with
  | none => exact Progress.atState _ _
  | some callbacks =>
    apply next_progress (runScopedReader_progress annotationProgress codeProgress normalProgress selectedRoom) selectedRoom
    intro _ _ closedRoom
    exact (afterScopedReader_progress annotationProgress (codeProgress _) normalProgress closedRoom).next
      (fun _ => Progress.atState _ _)

private theorem restored_lambda_read
    (represented : Represents arena root (Lending.restore (.var index) first body)) :
    ∃ domain bodyRoot, arena[root]? = some (.node (.lam false) [domain,bodyRoot]) ∧
      Represents arena bodyRoot (body.subst (single ((Term.var index).rename Nat.succ))) := by
  change Represents arena root (.node (.lam false) [first, body.subst (single ((Term.var index).rename Nat.succ))]) at represented
  cases represented with
  | node read _ children =>
    cases children with
    | cons _ tail =>
      cases tail with
      | cons bodyRep rest =>
        cases rest
        exact ⟨_,_,read,bodyRep⟩

private theorem resumeCode_refines
    (wf : UnifiedProgram.EnvWellFormed env) (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (annotationSound : InferSound env base ctx limit inferAnnotation)
    (annotationProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferAnnotation state root))
    (inferSound : NativeCoreBufferRelease.ModeSound env loans base ctx limit false infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerTypeRep : Represents state.arena ownerType T)
    (readerTypeRep : Represents state.arena readerResultRoot A)
    (firstRep : Represents state.arena written.first first)
    (againRep : Represents state.arena written.again again)
    (restoredRep : Represents state.arena restored (Lending.restore (.var index) first body))
    (success : (resumeCode inferAnnotation infer normal isData limit depth state index ownerType continuation
      written restored readerResultRoot).result = .ok answer)
    (ambient : Prefix (resumeCode inferAnnotation infer normal isData limit depth state index ownerType continuation
      written restored readerResultRoot).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (resumeCode inferAnnotation infer normal isData limit depth state index ownerType continuation
      written restored readerResultRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type codomain normalized, Represents after answer.typeRoot type ∧
        RawLend.Conv env (expand env first) (expand env A) ∧
        RawLend.Conv env (expand env again) ((expand env T).rename Nat.succ) ∧
        LoanTyping.HasType env loans ctx false (Lending.restore (.var index) (expand env first) (expand env body))
          (.pi false (expand env first) (expand env codomain)) ∧
        RawLend.Conv env (expand env codomain) normalized ∧
        PartialRenaming.shift (-1) 0 normalized = some (expand env type) ∧
        LoanTyping.continuationAllowed env false (expand env type) := by
  unfold resumeCode at success ambient ⊢
  obtain ⟨raised,raisedOk,raisedNext⟩ := Outcome.next_success success
  rw [raisedNext] at success ambient ⊢
  obtain ⟨firstBinder,firstOk,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ambient ⊢
  obtain ⟨valuePair,valuePairOk,valuePairNext⟩ := Outcome.next_success success
  rw [valuePairNext] at success ambient ⊢
  obtain ⟨ownerPair,ownerPairOk,ownerPairNext⟩ := Outcome.next_success success
  rw [ownerPairNext] at success ambient ⊢
  obtain ⟨resume,resumeOk,resumeNext⟩ := Outcome.next_success success
  rw [resumeNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let raisedRun := shift limit depth state ownerType 1
  let firstCheck := inferBinder inferAnnotation normal isData raisedRun.state written.first false
  let compareValue := compare normal limit depth firstCheck.state written.first readerResultRoot continuation
  let compareOwner := compare normal limit depth compareValue.state written.again raised continuation
  let resumeRun := infer compareOwner.state restored
  have raiseCost := shift_progress (limit := limit) (depth := depth) (state := state)
    (root := ownerType) (amount := 1)
  have raiseRoom := raiseCost.accepted room raised raisedOk
  have firstCost := inferBinder_progress (state := raisedRun.state) (isData := isData) (domain := written.first) (erased := false)
    annotationProgress normalProgress raiseRoom
  have firstRoom := firstCost.accepted raiseRoom firstBinder firstOk
  have valueCost := compare_progress (state := firstCheck.state) (depth := depth) (actual := written.first)
    (expected := readerResultRoot) (atRoot := continuation) normalProgress firstRoom
  have valueRoom := valueCost.accepted firstRoom valuePair valuePairOk
  have ownerCost := compare_progress (state := compareValue.state) (depth := depth) (actual := written.again)
    (expected := raised) (atRoot := continuation) normalProgress valueRoom
  have resumeRoom := ownerCost.accepted valueRoom ownerPair ownerPairOk
  have resumeCost := inferProgress compareOwner.state restored resumeRoom
  have finishCost := runCanonicalReturn_progress (state := resumeRun.state) (type := resume.typeRoot)
    (slot := index) (restored := restored) (continuation := continuation) (depth := depth) normalProgress
  have afterResume := finishCost.kept.trans ambient
  have afterOwner := resumeCost.kept.trans afterResume
  have afterValue := ownerCost.kept.trans afterOwner
  have afterFirst := valueCost.kept.trans afterValue
  obtain ⟨raiseKept,raiseBack,raisedTypeRep⟩ := raise_owner_refines ownerTypeRep raisedOk
  obtain ⟨firstKept,firstBack,_⟩ := inferBinder_refines metadata normalSound normalProgress annotationSound annotationProgress
    (onBase.trans raiseKept) raiseRoom (firstRep.frame raiseKept) firstOk afterFirst
    (fun pair member => retained pair (List.mem_append_left _ member))
  have throughFirst := raiseKept.trans firstKept
  obtain ⟨valueKept,valueBack,firstConverted⟩ := requireTypes_refines normalSound
    (onBase.trans throughFirst) (firstRep.frame throughFirst) (readerTypeRep.frame throughFirst)
    valuePairOk afterValue (retained valuePair (by simp))
  have throughValue := throughFirst.trans valueKept
  obtain ⟨ownerKept,ownerBack,againConverted⟩ := requireTypes_refines normalSound
    (onBase.trans throughValue) (againRep.frame throughValue) (raisedTypeRep.frame (firstKept.trans valueKept))
    ownerPairOk afterOwner (retained ownerPair (by simp))
  have throughOwner := throughValue.trans ownerKept
  obtain ⟨resumeKept,resumeBack,resumedType,outputType,typedResume⟩ := inferSound
    (onBase.trans throughOwner) resumeRoom (restoredRep.frame throughOwner) resumeOk afterResume
    (fun pair member => retained pair (by simp [member]))
  have throughResume := throughOwner.trans resumeKept
  obtain ⟨_,_,lambdaRead,bodyRep⟩ := restored_lambda_read (restoredRep.frame throughResume)
  obtain ⟨resultKept,resultBack,foundFirst,codomain,normalized,output,_,represented,converted,bodyConverted,
    lowered,_,_,allowed⟩ :=
      runCanonicalReturn_refines wf normalSound (onBase.trans throughResume) outputType bodyRep lambdaRead resultOk
  have againAligned : RawLend.Conv env (expand env again) ((expand env T).rename Nat.succ) := by
    simpa only [EnvironmentDelta.expand_renaming wf.admissible] using againConverted
  rw [expand_restore wf] at typedResume
  have typedLambda : LoanTyping.HasType env loans ctx false
      (.lam false (expand env first) ((expand env body).subst (single ((Term.var index).rename Nat.succ))))
      (expand env resumedType) := by simpa only [Lending.restore] using typedResume
  obtain ⟨_,_,_,_,lambdaPi⟩ := typedLambda.lamView
  have foundFirstConverted := ((lambdaPi.trans converted).pi_injective wf.admissible).2.1
  have alignedProduct : RawLend.Conv env (.pi false (expand env foundFirst) (expand env codomain))
      (.pi false (expand env first) (expand env codomain)) :=
    .node _ (.cons foundFirstConverted.symm (.cons (.refl _) .nil))
  exact ⟨throughResume.trans resultKept,resultBack ∘ resumeBack ∘ ownerBack ∘ valueBack ∘ firstBack ∘ raiseBack,
    output,codomain,normalized,represented,firstConverted,againAligned,
    typedResume.convert (converted.trans alignedProduct),bodyConverted,lowered,allowed⟩

/-- A successful dependent CODE check reconstructs the written source
callbacks. The reader runs under the owner snapshot and the continuation
uses the original loan stack. The result keeps the original lowered type. -/
theorem runDependentCode_refines
    (wf : UnifiedProgram.EnvWellFormed env) (metadata : DataFamilies env isData)
    (boxed : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (annotationSound : InferSound env base ctx limit inferAnnotation)
    (annotationProgress : ∀ state root, state.steps ≤ limit → Progress limit state (inferAnnotation state root))
    (codeSound : ∀ {arena saved active}, Prefix base arena →
      NativeCoreCodeLeaseLookup.FramesRep arena saved active →
      NativeCoreBufferRelease.ModeSound env active arena ctx limit false (inferCode saved))
    (codeProgress : ∀ snapshots state root, state.steps ≤ limit → Progress limit state (inferCode snapshots state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (frames : NativeCoreCodeLeaseLookup.FramesRep state.arena snapshots loans)
    (ownerRep : Represents state.arena owner x) (readerRep : Represents state.arena reader f)
    (continuationRep : Represents state.arena continuation g)
    (success : (runDependentCode inferAnnotation inferCode normal isData isBoxed limit depth ctx.length state
      snapshots owner reader continuation).result = .ok answer)
    (ambient : Prefix (runDependentCode inferAnnotation inferCode normal isData isBoxed limit depth ctx.length state
      snapshots owner reader continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (runDependentCode inferAnnotation inferCode normal isData isBoxed limit depth ctx.length state
      snapshots owner reader continuation).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ type, Represents after answer.typeRoot type ∧
        LoanTyping.HasType env loans ctx false (expand env (.lend x f g)) (expand env type) := by
  unfold runDependentCode at success ambient ⊢
  obtain ⟨inferred,inferredOk,inferredNext⟩ := Outcome.next_success success
  rw [inferredNext] at success ambient ⊢
  obtain ⟨ownedType,ownedOk,ownedNext⟩ := Outcome.next_success success
  rw [ownedNext] at success ambient ⊢
  obtain ⟨borrow,borrowOk,borrowNext⟩ := Outcome.next_success success
  rw [borrowNext] at success ambient ⊢
  obtain ⟨shape,preparedOk,preparedNext⟩ := Outcome.next_success success
  rw [preparedNext] at success ambient ⊢
  cases shape with
  | none => cases success
  | some callbacks =>
    dsimp only at success ambient ⊢
    obtain ⟨readType,readOk,readNext⟩ := Outcome.next_success success
    rw [readNext] at success ambient ⊢
    obtain ⟨resume,resumeOk,resumeNext⟩ := Outcome.next_success success
    rw [resumeNext] at success ambient ⊢
    simp only [Except.ok.injEq] at success
    subst answer
    let visited := inferCode snapshots state owner
    let owns := requireOwned normal isBoxed visited.state inferred.typeRoot owner
    let referenced := append owns.state .ref [inferred.typeRoot]
    let prepared := NativeCoreDependentLendCallbacks.run limit depth referenced.state owner reader continuation
    let reading := runScopedReader inferAnnotation inferCode normal isData limit depth ctx.length prepared.state snapshots
      owner borrow reader callbacks
    have ownerCost := codeProgress snapshots state owner room
    have ownerRoom := ownerCost.accepted room inferred inferredOk
    have ownedCost := requireOwned_progress (state := visited.state) (root := inferred.typeRoot) (rejected := owner)
      (isBoxed := isBoxed) normalProgress
    have ownedRoom := ownedCost.accepted ownerRoom ownedType ownedOk
    have borrowCost := append_progress (limit := limit) owns.state .ref [inferred.typeRoot]
    have borrowRoom := borrowCost.accepted ownedRoom borrow borrowOk
    have preparedCost := NativeCoreDependentLendCallbacks.run_progress (limit := limit) (depth := depth)
      (state := referenced.state) (owner := owner) (reader := reader) (continuation := continuation)
    have preparedRoom := preparedCost.accepted borrowRoom (some callbacks) preparedOk
    have readCost := runScopedReader_progress (state := prepared.state) (width := ctx.length) (depth := depth) (isData := isData)
      (snapshots := snapshots) (owner := owner) (borrow := borrow) (reader := reader) (callbacks := callbacks)
      annotationProgress codeProgress normalProgress preparedRoom
    have readRoom := readCost.accepted preparedRoom readType readOk
    have resumeCost := afterScopedReader_progress (state := reading.state) (depth := depth) (isData := isData)
      (owner := owner) (ownerType := inferred.typeRoot) (reader := reader) (continuation := continuation)
      (restored := callbacks.continuation) (readerResultRoot := readType.typeRoot)
      annotationProgress (codeProgress snapshots) normalProgress readRoom
    have afterRead := resumeCost.kept.trans ambient
    have afterPrepare := readCost.kept.trans afterRead
    have afterBorrow := preparedCost.kept.trans afterPrepare
    have afterOwned := borrowCost.kept.trans afterBorrow
    have afterOwner := ownedCost.kept.trans afterOwned
    have localCode : NativeCoreBufferRelease.ModeSound env loans state.arena ctx limit false (inferCode snapshots) :=
      codeSound onBase frames
    obtain ⟨ownerKept,ownerBack,T,typeRep,typedOwner⟩ := localCode (.refl _) room ownerRep inferredOk afterOwner
      (fun pair member => retained pair (List.mem_append_left _ member))
    obtain ⟨ownedKept,ownedBack,owned⟩ := requireOwned_refines boxed normalSound
      (onBase.trans ownerKept) typeRep ownedOk
    have throughOwned := ownerKept.trans ownedKept
    obtain ⟨borrowKept,borrowBack,borrowRep⟩ := append_refines (.cons (typeRep.frame ownedKept) .nil) rfl borrowOk
    have throughBorrow := throughOwned.trans borrowKept
    obtain ⟨preparedKept,preparedBack,written,index,domain,readBody,first,again,body,selected,
      ownerShape,readerShape,continuationShape,domainRep,readRep,restoredRep,firstRep,againRep⟩ :=
      NativeCoreDependentLendCallbacks.run_selected_refines
        (ownerRep.frame throughBorrow) (readerRep.frame throughBorrow) (continuationRep.frame throughBorrow) preparedOk
    subst x
    subst f
    subst g
    have throughPrepare := throughBorrow.trans preparedKept
    obtain ⟨readerKept,readerBack,sort,A,readerTypeRep,formed,readDomain,typedRead,outlived⟩ :=
      runScopedReader_refines wf metadata normalSound normalProgress annotationSound annotationProgress
        codeSound codeProgress (onBase.trans throughPrepare) preparedRoom (frames.frame throughPrepare)
        (ownerRep.frame throughPrepare) (borrowRep.frame preparedKept) domainRep readRep readOk afterRead
        (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_left _ member)))
    have throughReader := throughPrepare.trans readerKept
    have laterSelection := (NativeCoreDependentLendCallbacks.select_frame
      (ownerRep.frame throughBorrow) (readerRep.frame throughBorrow) (continuationRep.frame throughBorrow)
      (preparedKept.trans readerKept)).trans selected
    have ownerRead : state.arena[owner]? = some (.var index) := by
      cases ownerRep with
      | var read => exact read
    have closedRead := throughReader.lookup ownerRead
    simp only [afterScopedReader,laterSelection,closedRead] at resumeOk ambient ⊢
    have normalLocal : VisitsFrom state.arena (ExpandedNormalization env) normal := by
      intro _ _ _ _ later represented accepted
      exact normalSound (onBase.trans later) represented accepted
    have annotationLocal : InferSound env state.arena ctx limit inferAnnotation := by
      intro _ _ _ _ _ later cost represented accepted kept tape
      exact annotationSound (onBase.trans later) cost represented accepted kept tape
    obtain ⟨returnKept,returnBack,output,codomain,normalized,outputRep,firstConverted,againConverted,
      typedRestore,converted,lowered,allowed⟩ := resumeCode_refines wf metadata normalLocal normalProgress
        annotationLocal annotationProgress localCode (codeProgress snapshots) throughReader readRoom
        (typeRep.frame (ownedKept.trans (borrowKept.trans (preparedKept.trans readerKept))))
        readerTypeRep (firstRep.frame readerKept) (againRep.frame readerKept) (restoredRep.frame readerKept)
        resumeOk ambient (fun pair member => retained pair (List.mem_append_right _ (List.mem_append_right _ member)))
    have sourceOwner : LoanTyping.HasType env loans ctx false (.var index) (expand env T) := by
      simpa only [expand] using typedOwner
    refine ⟨throughReader.trans returnKept,returnBack ∘ readerBack ∘ preparedBack ∘ borrowBack ∘ ownedBack ∘ ownerBack,
      output,outputRep,?_⟩
    simpa only [Term.lend,Term.lam,expand,expandArgs] using LoanTyping.HasType.lendDependentCode sourceOwner owned
      formed readDomain typedRead outlived firstConverted againConverted typedRestore converted lowered allowed

private theorem dependent_refines (wf : UnifiedProgram.EnvWellFormed env) (metadata : DataFamilies env isData)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena owner (.var index))
    (readerRep : Represents state.arena reader (.lam false domain readBody))
    (contRep : Represents state.arena continuation (.lam false first (.lam false again resumeBody)))
    (ownerTypeRep : Represents state.arena ownerType T) (borrowRep : Represents state.arena borrow (.ref T))
    (typedOwner : LoanTyping.HasType env [] ctx true (.var index) (expand env T))
    (owned : LoanTyping.Owned env (expand env T))
    (selected : NativeCoreDependentLendCallbacks.select state.arena owner reader continuation = some written)
    (domainRep : Represents state.arena callbacks.domain domain)
    (readRep : Represents state.arena callbacks.reader (Lending.read (.var index) readBody))
    (restRep : Represents state.arena callbacks.continuation (Lending.restore (.var index) first resumeBody))
    (firstRep : Represents state.arena written.first first) (againRep : Represents state.arena written.again again)
    (success : (dependent infer normal isData limit depth state owner ownerType borrow reader continuation callbacks).result = .ok answer)
    (ambient : Prefix (dependent infer normal isData limit depth state owner ownerType borrow reader continuation callbacks).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.lend (.var index) (.lam false domain readBody) (.lam false first (.lam false again resumeBody)))
      (dependent infer normal isData limit depth state owner ownerType borrow reader continuation callbacks) answer := by
  unfold dependent at success ambient ⊢
  obtain ⟨binder,binderOk,binderNext⟩ := Outcome.next_success success
  rw [binderNext] at success ambient ⊢
  obtain ⟨readDomain,domainOk,domainNext⟩ := Outcome.next_success success
  rw [domainNext] at success ambient ⊢
  obtain ⟨readType,readOk,readNext⟩ := Outcome.next_success success
  rw [readNext] at success ambient ⊢
  obtain ⟨value,valueOk,valueNext⟩ := Outcome.next_success success
  rw [valueNext] at success ambient ⊢
  let checkedBinder := inferBinder infer normal isData state callbacks.domain false
  let checkedDomain := compare normal limit depth checkedBinder.state callbacks.domain borrow reader
  let readRun := infer checkedDomain.state callbacks.reader
  let checkedValue := readerType normal isData readRun.state readType.typeRoot reader
  have binderCost := inferBinder_progress (state := state) (isData := isData) (domain := callbacks.domain) (erased := false)
    inferProgress normalProgress room
  have binderRoom := binderCost.accepted room binder binderOk
  have domainCost := compare_progress (state := checkedBinder.state) (depth := depth) (actual := callbacks.domain)
    (expected := borrow) (atRoot := reader) normalProgress binderRoom
  have domainRoom := domainCost.accepted binderRoom readDomain domainOk
  have readCost := inferProgress checkedDomain.state callbacks.reader domainRoom
  have readRoom := readCost.accepted domainRoom readType readOk
  have valueCost := readerType_progress (limit := limit) (isData := isData) (state := readRun.state)
    (type := readType.typeRoot) (reader := reader) normalProgress
  have valueRoom := valueCost.accepted readRoom value valueOk
  have toValue := binderCost.kept.trans (domainCost.kept.trans (readCost.kept.trans valueCost.kept))
  have currentSelection : NativeCoreDependentLendCallbacks.select checkedValue.state.arena owner reader continuation = some written :=
    (NativeCoreDependentLendCallbacks.select_frame ownerRep readerRep contRep toValue).trans selected
  rw [currentSelection] at success ambient ⊢
  dsimp only at success ambient ⊢
  obtain ⟨raised,raisedOk,raisedNext⟩ := Outcome.next_success success
  rw [raisedNext] at success ambient ⊢
  obtain ⟨firstBinder,firstOk,firstNext⟩ := Outcome.next_success success
  rw [firstNext] at success ambient ⊢
  obtain ⟨valuePair,valuePairOk,valuePairNext⟩ := Outcome.next_success success
  rw [valuePairNext] at success ambient ⊢
  obtain ⟨ownerPair,ownerPairOk,ownerPairNext⟩ := Outcome.next_success success
  rw [ownerPairNext] at success ambient ⊢
  obtain ⟨resume,resumeOk,resumeNext⟩ := Outcome.next_success success
  rw [resumeNext] at success ambient ⊢
  obtain ⟨product,productOk,productNext⟩ := Outcome.next_success success
  rw [productNext] at success ambient ⊢
  obtain ⟨result,resultOk,resultNext⟩ := Outcome.next_success success
  rw [resultNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let raisedRun := shift limit depth checkedValue.state ownerType 1
  let firstCheck := inferBinder infer normal isData raisedRun.state written.first false
  let compareValue := compare normal limit depth firstCheck.state written.first value continuation
  let compareOwner := compare normal limit depth compareValue.state written.again raised continuation
  let resumeRun := infer compareOwner.state callbacks.continuation
  let productRun := exposeProduct normal resumeRun.state resume.typeRoot continuation
  have raiseCost := shift_progress (limit := limit) (depth := depth) (state := checkedValue.state)
    (root := ownerType) (amount := 1)
  have raiseRoom := raiseCost.accepted valueRoom raised raisedOk
  have firstCost := inferBinder_progress (state := raisedRun.state) (isData := isData) (domain := written.first) (erased := false)
    inferProgress normalProgress raiseRoom
  have firstRoom := firstCost.accepted raiseRoom firstBinder firstOk
  have valueCompareCost := compare_progress (state := firstCheck.state) (depth := depth) (actual := written.first)
    (expected := value) (atRoot := continuation) normalProgress firstRoom
  have pairRoom := valueCompareCost.accepted firstRoom valuePair valuePairOk
  have ownerCompareCost := compare_progress (state := compareValue.state) (depth := depth) (actual := written.again)
    (expected := raised) (atRoot := continuation) normalProgress pairRoom
  have resumeRoom := ownerCompareCost.accepted pairRoom ownerPair ownerPairOk
  have resumeCost := inferProgress compareOwner.state callbacks.continuation resumeRoom
  have productCost := product_progress (state := resumeRun.state) (type := resume.typeRoot) (motive := continuation)
    normalProgress
  have loweredCost := lowerResult_progress (limit := limit) (depth := depth)
    (state := productRun.state) (root := product.2) (amount := -1) normalProgress
  have afterProduct := loweredCost.kept.trans ambient
  have afterResume := productCost.kept.trans afterProduct
  have afterOwner := resumeCost.kept.trans afterResume
  have afterValueComparison := ownerCompareCost.kept.trans afterOwner
  have afterFirst := valueCompareCost.kept.trans afterValueComparison
  have afterRaise := firstCost.kept.trans afterFirst
  have afterValue := raiseCost.kept.trans afterRaise
  have afterRead := valueCost.kept.trans afterValue
  have afterDomain := readCost.kept.trans afterRead
  have afterBinder := domainCost.kept.trans afterDomain
  obtain ⟨binderKept,binderBack,typedBinder⟩ := inferBinder_refines metadata normalSound normalProgress
    inferSound inferProgress onBase room domainRep binderOk afterBinder (fun pair member => retained pair (by simp [member]))
  obtain ⟨domainKept,domainBack,rawDomain⟩ := requireTypes_refines normalSound (onBase.trans binderKept)
    (domainRep.frame binderKept) (borrowRep.frame binderKept) domainOk afterDomain (retained readDomain (by simp))
  have throughDomain := binderKept.trans domainKept
  obtain ⟨readKept,readBack,_,readTypeRep,typedRead⟩ := inferSound (onBase.trans throughDomain) domainRoom
    (readRep.frame throughDomain) readOk afterRead (fun pair member => retained pair (by simp [member]))
  have throughRead := throughDomain.trans readKept
  obtain ⟨valueKept,valueBack,_,valueRep,readConverted,outlives⟩ := readerType_refines metadata normalSound
    (onBase.trans throughRead) readTypeRep valueOk
  have throughValue := throughRead.trans valueKept
  obtain ⟨raiseKept,raiseBack,raisedTypeRep⟩ := raise_owner_refines (ownerTypeRep.frame throughValue) raisedOk
  have throughRaise := throughValue.trans raiseKept
  obtain ⟨firstKept,firstBack,_⟩ := inferBinder_refines metadata normalSound normalProgress inferSound inferProgress
    (onBase.trans throughRaise) raiseRoom (firstRep.frame throughRaise) firstOk afterFirst
    (fun pair member => retained pair (by simp [member]))
  have throughFirst := throughRaise.trans firstKept
  obtain ⟨valuePairKept,valuePairBack,firstConverted⟩ := requireTypes_refines normalSound
    (onBase.trans throughFirst) (firstRep.frame throughFirst) (valueRep.frame (raiseKept.trans firstKept))
    valuePairOk afterValueComparison (retained valuePair (by simp))
  have throughValuePair := throughFirst.trans valuePairKept
  obtain ⟨ownerPairKept,ownerPairBack,againConverted⟩ := requireTypes_refines normalSound
    (onBase.trans throughValuePair) (againRep.frame throughValuePair) (raisedTypeRep.frame (firstKept.trans valuePairKept))
    ownerPairOk afterOwner (retained ownerPair (by simp))
  have throughOwner := throughValuePair.trans ownerPairKept
  obtain ⟨resumeKept,resumeBack,resumedType,resumeTypeRep,typedResume⟩ := inferSound
    (onBase.trans throughOwner) resumeRoom (restRep.frame throughOwner) resumeOk afterResume
    (fun pair member => retained pair (by simp [member]))
  have throughResume := throughOwner.trans resumeKept
  obtain ⟨productKept,productBack,foundFirst,foundBody,_,bodyTypeRep,productConverted⟩ :=
    product_refines normalSound (onBase.trans throughResume) resumeTypeRep productOk
  have throughProduct := throughResume.trans productKept
  obtain ⟨resultKept,resultBack,_,R,output,resultConverted,lowered⟩ := lowerResult_refines wf normalSound
    (onBase.trans throughProduct) bodyTypeRep (by decide : (-1 : Int) < 0) resultOk
  have domainConverted : RawLend.Conv env (expand env domain) (.ref (expand env T)) := by
    simpa only [Term.ref,expand,expandArgs] using rawDomain
  have againAligned : RawLend.Conv env (expand env again) ((expand env T).rename Nat.succ) := by
    simpa only [EnvironmentDelta.expand_renaming wf.admissible] using againConverted
  rw [expand_read wf] at typedRead
  rw [expand_restore wf] at typedResume
  have typedLambda : LoanTyping.HasType env [] ctx true
      (.lam false (expand env first) ((expand env resumeBody).subst (single ((Term.var index).rename Nat.succ))))
      (expand env resumedType) := by simpa only [Lending.restore] using typedResume
  obtain ⟨_,_,_,_,lambdaPi⟩ := typedLambda.lamView
  have foundFirstConverted := ((lambdaPi.trans productConverted).pi_injective wf.admissible).2.1
  have alignedProduct : RawLend.Conv env (.pi false (expand env foundFirst) (expand env foundBody))
      (.pi false (expand env first) (expand env foundBody)) :=
    .node _ (.cons foundFirstConverted.symm (.cons (.refl _) .nil))
  have restored := typedResume.convert (productConverted.trans alignedProduct)
  refine ⟨throughProduct.trans resultKept,resultBack ∘ productBack ∘ resumeBack ∘ ownerPairBack ∘ valuePairBack ∘
    firstBack ∘ raiseBack ∘ valueBack ∘ readBack ∘ domainBack ∘ binderBack,R,output,?_⟩
  simpa only [Term.lend,Term.lam,expand,expandArgs] using LoanTyping.HasType.lendDependentGhost typedOwner owned
    typedBinder domainConverted (typedRead.convert readConverted) outlives firstConverted againAligned restored
    resultConverted lowered

/-- Both executable branches reconstruct the source ghost lending judgment
from the original input and the checks on the real shared graph. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (data : DataFamilies env isData) (boxed : BoxedFamilies env isBoxed)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (inferSound : InferSound env base ctx limit infer)
    (inferProgress : ∀ state root, state.steps ≤ limit → Progress limit state (infer state root))
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (ownerRep : Represents state.arena owner x) (readerRep : Represents state.arena reader f)
    (contRep : Represents state.arena continuation g)
    (success : (run infer normal isData isBoxed limit depth state owner reader continuation).result = .ok answer)
    (ambient : Prefix (run infer normal isData isBoxed limit depth state owner reader continuation).state.arena final)
    (retained : RetainedComparisons final answer) :
    Refines env state.arena ctx (.lend x f g) (run infer normal isData isBoxed limit depth state owner reader continuation) answer := by
  cases original : NativeCoreDependentLendCallbacks.select state.arena owner reader continuation with
  | none =>
    exact run_generic_refines wf data boxed normalSound normalProgress inferSound inferProgress
      onBase room ownerRep readerRep contRep original success ambient retained
  | some selected =>
    unfold run at success ambient ⊢
    obtain ⟨ownerResult,ownerOk,ownerNext⟩ := Outcome.next_success success
    rw [ownerNext] at success ambient ⊢
    obtain ⟨_,ownedOk,ownedNext⟩ := Outcome.next_success success
    rw [ownedNext] at success ambient ⊢
    obtain ⟨borrow,borrowOk,borrowNext⟩ := Outcome.next_success success
    rw [borrowNext] at success ambient ⊢
    obtain ⟨shape,preparedOk,preparedNext⟩ := Outcome.next_success success
    rw [preparedNext] at success ambient ⊢
    let checkedOwner := infer state owner
    let checkedOwned := requireOwned normal isBoxed checkedOwner.state ownerResult.typeRoot owner
    let builtBorrow := append checkedOwned.state .ref [ownerResult.typeRoot]
    let prepared := NativeCoreDependentLendCallbacks.run limit depth builtBorrow.state owner reader continuation
    have ownerCost := inferProgress state owner room
    have ownedRoom := ownerCost.accepted room ownerResult ownerOk
    have ownedCost := requireOwned_progress (state := checkedOwner.state) (isBoxed := isBoxed)
      (root := ownerResult.typeRoot) (rejected := owner) normalProgress
    have borrowRoom := ownedCost.accepted ownedRoom () ownedOk
    have borrowCost := append_progress (limit := limit) checkedOwned.state .ref [ownerResult.typeRoot]
    have startRoom := borrowCost.accepted borrowRoom borrow borrowOk
    have kept := ownerCost.kept.trans (ownedCost.kept.trans borrowCost.kept)
    have beforeSelection : NativeCoreDependentLendCallbacks.select builtBorrow.state.arena owner reader continuation = some selected :=
      (NativeCoreDependentLendCallbacks.select_frame ownerRep readerRep contRep kept).trans original
    cases shape with
    | none =>
      unfold NativeCoreDependentLendCallbacks.run at preparedOk
      rw [beforeSelection] at preparedOk
      dsimp only at preparedOk
      obtain ⟨callback,callbackOk,next⟩ := Outcome.next_success preparedOk
      rw [next] at preparedOk
      cases preparedOk
    | some callbacks =>
      dsimp only at success ambient ⊢
      obtain ⟨checked,checkedOk,checkedNext⟩ := Outcome.next_success success
      rw [checkedNext] at success ambient ⊢
      simp only [Except.ok.injEq] at success
      subst answer
      have prepareCost := NativeCoreDependentLendCallbacks.run_progress (limit := limit) (depth := depth)
        (state := builtBorrow.state) (owner := owner) (reader := reader) (continuation := continuation)
      have afterPrepareRoom := prepareCost.accepted startRoom (some callbacks) preparedOk
      have bodyCost := dependent_progress (state := prepared.state) (isData := isData) (depth := depth)
        (owner := owner) (ownerType := ownerResult.typeRoot) (borrow := borrow) (reader := reader)
        (continuation := continuation) (callbacks := callbacks) inferProgress normalProgress afterPrepareRoom
      have afterPrepare := bodyCost.kept.trans ambient
      have afterBorrow := prepareCost.kept.trans afterPrepare
      obtain ⟨ownerKept,ownerBack,_,ownerTypeRep,typed⟩ := inferSound onBase room ownerRep ownerOk
        (ownedCost.kept.trans (borrowCost.kept.trans afterBorrow))
        (fun pair member => retained pair (List.mem_append_left _ member))
      obtain ⟨ownedKept,ownedBack,owns⟩ := requireOwned_refines boxed normalSound
        (onBase.trans ownerKept) ownerTypeRep ownedOk
      obtain ⟨borrowKept,borrowBack,borrowRep⟩ := append_refines (.cons (ownerTypeRep.frame ownedKept) .nil) rfl borrowOk
      obtain ⟨prepareKept,prepareBack,written,index,domain,read,first,again,resume,writtenAt,rfl,rfl,rfl,
        domainRep,readRep,restRep,firstRep,againRep⟩ := NativeCoreDependentLendCallbacks.run_selected_refines
          (ownerRep.frame kept) (readerRep.frame kept) (contRep.frame kept) preparedOk
      have preparedKept := kept.trans prepareKept
      have current := (NativeCoreDependentLendCallbacks.select_frame (ownerRep.frame kept) (readerRep.frame kept)
        (contRep.frame kept) prepareKept).trans writtenAt
      obtain ⟨done,doneBack,inferred⟩ := dependent_refines wf data normalSound normalProgress inferSound inferProgress
        (onBase.trans preparedKept) afterPrepareRoom (ownerRep.frame preparedKept) (readerRep.frame preparedKept)
        (contRep.frame preparedKept) (ownerTypeRep.frame (ownedKept.trans (borrowKept.trans prepareKept)))
        (borrowRep.frame prepareKept) (by simpa only [expand] using typed) owns current domainRep readRep restRep
        firstRep againRep checkedOk ambient (fun pair member => retained pair (List.mem_append_right _ member))
      exact ⟨preparedKept.trans done,doneBack ∘ prepareBack ∘ borrowBack ∘ ownedBack ∘ ownerBack,inferred⟩

end Jihoo.NativeKernel.NativeCoreGhostLendInference
