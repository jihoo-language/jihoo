import Jihoo.NativeBindingMachineLoanTyping
import Jihoo.NativeLoanLendInputs

/-! Original-type provenance for actual explicit Lend callback entry. The
specialized source rule types the substituted reader and final continuation,
not arbitrary raw macro applications. Runtime bindings still retain their
original bodies and actual values; these theorems derive ghost origin typing
from the input Lend derivation, without post-value typing certificates. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- Closing a real reader binder agrees with the specialized source read. -/
theorem reader_entry_origin (code : Code) (owner domain body : Term) (token : Nat) :
    (enter false domain body code.context code.origins code.values
      (.borrow (owner.subst code.origins)) (some (.reference token))).origin =
      (Lending.read owner body).subst code.origins := by
  rw [Lending.read_subst]
  simp only [Code.origin,enter,Lending.read,subst_lift_consValues]

/-- The actual result-origin saved for the continuation is the activated
reader body, including computed closures' exact captures. -/
theorem reader_activation_origin (domain body : Term) (context : Context)
    (origins : Nat → Term) (captured : List (Option Value))
    (token object : Nat) (name : Option Nat) (ownerOrigin readerOrigin : Term)
    (continuation : Code) (stack : List Frame) :
    let bodyCode := enter false domain body context origins captured
      (.borrow ownerOrigin) (some (.reference token))
    returnAction (.closure false domain body context origins captured)
      (.lendReader token object name ownerOrigin readerOrigin continuation :: stack) =
      some (.control (.evaluate bodyCode)
        (.lendFinish token object name ownerOrigin bodyCode.origin continuation :: stack)
        (some (false,body,.borrow ownerOrigin))) := rfl

/-- This covers both generic and specialized Lend source rules. The actual
reader body origin is well typed even when no arbitrary-argument callback
derivation is available. Its runtime reference points to the existing token;
heap liveness follows separately from the all-prefix inventory. -/
theorem typed_explicit_reader_origin
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) (token : Nat) :
    ∃ valueType : Term,
      LoanTyping.HasType env [] [] true
        (enter false domain readerBody code.context code.origins code.values
          (.borrow (owner.subst code.origins)) (some (.reference token))).origin
        (valueType.subst code.origins) ∧ LoanTyping.Outlived env valueType := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨ownerType,valueType,ownerTyped,owned,readerTyped,outlived⟩ :=
    source.explicitLendInputs history.wellFormed
  refine ⟨valueType,?_,outlived⟩
  rw [reader_entry_origin]
  exact readerTyped.ghostSubstitution history.wellFormed closing

/-- The actual two continuation binders close to the source-specialized
finish, with distinct owner and reader-result runtime slots. -/
theorem continuation_entry_origin (code : Code) (owner value first again body : Term)
    (object : Nat) (result : Value) :
    (enter false again body (⟨first,false⟩ :: code.context)
      (consValues (value.subst code.origins) code.origins) (some result :: code.values)
      (owner.subst code.origins) (some (.owner object))).origin =
      (Lending.finish owner body value).subst code.origins := by
  simp only [Code.origin,enter,Lending.finish,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero =>
      simp only [consValues,single,Term.subst_rename]
      congr 1
      funext x
      simp only [Term.subst]
  | succ index =>
      cases index <;> simp [consValues,single,Term.subst]

/-- Original requested ghost type at the concrete final continuation body.
This derives provenance from the input typing; it does not certify arbitrary
runtime results as inhabiting that type. -/
theorem typed_explicit_continuation_origin
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) (object : Nat) (result : Value) :
    LoanTyping.HasType env [] [] true
      (enter false again body (⟨first,false⟩ :: code.context)
        (consValues ((Lending.read owner readerBody).subst code.origins) code.origins)
        (some result :: code.values) (owner.subst code.origins) (some (.owner object))).origin type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  have endpoint := source.explicitLendFinish history.wellFormed
    owner domain readerBody first again body shape
  rw [continuation_entry_origin]
  exact (endpoint.ghostSubstitution history.wellFormed closing).convert converted

/-- Both actual continuation activations retain the distinct runtime result
and original owner. No macro application is used as their saved origin. -/
theorem continuation_activations (code : Code) (first again body ownerOrigin resultOrigin : Term)
    (object : Nat) (result : Value) (stack : List Frame) :
    returnAction (.closure false first (.lam false again body) code.context code.origins code.values)
      (.lendContinuation object ownerOrigin resultOrigin result :: stack) =
      some (.control
        (.evaluate (enter false first (.lam false again body) code.context code.origins code.values resultOrigin (some result)))
        (.lendOwnerArgument object ownerOrigin :: stack) (some (false,.lam false again body,resultOrigin))) ∧
    returnAction (.closure false again body (⟨first,false⟩ :: code.context)
      (consValues resultOrigin code.origins) (some result :: code.values))
      (.lendOwnerArgument object ownerOrigin :: stack) =
      some (.control
        (.evaluate (enter false again body (⟨first,false⟩ :: code.context)
          (consValues resultOrigin code.origins) (some result :: code.values) ownerOrigin (some (.owner object))))
        stack (some (false,body,ownerOrigin))) := ⟨rfl,rfl⟩

theorem ReaderPresent.same_frames (present : ReaderPresent key object before)
    (same : readerFrames before = readerFrames after) : ReaderPresent key object after := by
  obtain ⟨frame,member,token,descriptor⟩ := present
  have stored : (token,object,some key) ∈ readerFrames before :=
    List.mem_filterMap.mpr ⟨frame,member,descriptor⟩
  rw [same] at stored
  obtain ⟨next,member,descriptor⟩ := List.mem_filterMap.mp stored
  exact ⟨next,member,token,descriptor⟩

theorem LoanSlots.same_frames (slots : LoanSlots code loans before)
    (same : readerFrames before = readerFrames after) : LoanSlots code loans after := by
  intro index permission
  obtain ⟨object,stored,present⟩ := slots index permission
  exact ⟨object,stored,present.same_frames same⟩

/-- Actual named reader entry preserves all outer permissions and installs
its new permission below the reference binder. This combines runtime owner
slots, lexical depths and concrete reader frames; no Borrow guard is assumed. -/
theorem named_reader_body_slots (code : Code)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (domain body : Term) (token : Nat) (readerOrigin : Term) (continuation : Code) :
    let bodyCode := enter false domain body code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
    LoanSlots bodyCode (Loans.enter code.context.length owner loans)
      (.lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) bodyCode.origin continuation :: stack) := by
  have readerSlots := slots.begin_reader stored token
    ((Term.var owner).subst code.origins) readerOrigin continuation
  have bodySlots := readerSlots.enter (Loans.entered_enter entered) false domain body
    (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
  exact bodySlots.same_frames rfl

/-- At a real reachable named-reader activation, the complete source Lend
judgment supplies reader-origin typing, binding preserves all named-owner
permissions, and the actual prefix supplies lease and owner liveness. No
successful-step, close-guard or output-value typing oracle is supplied. -/
theorem reachable_named_reader_activation (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (sourceShape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (slots : LoanSlots code loans rest) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (controlShape : (run fuel (initial term)).state.control =
      .returned (.closure false domain readerBody code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerOrigin continuation :: rest) :
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
    let afterStack := .lendFinish token object (some (code.context.length-owner))
      ((Term.var owner).subst code.origins) bodyCode.origin continuation :: rest
    ∃ valueType : Term,
      LoanTyping.HasType env [] [] true bodyCode.origin (valueType.subst code.origins) ∧
      LoanSlots bodyCode (Loans.enter code.context.length owner loans) afterStack ∧
      (run fuel (initial term)).state.heap.heap.lease token = some object ∧
      (run fuel (initial term)).state.heap.heap.live object = true ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,afterStack⟩,
          some (.activate false readerBody (.borrow ((Term.var owner).subst code.origins)))) := by
  obtain ⟨valueType,originTyped,outlived⟩ := typed_explicit_reader_origin history typed sourceShape token
  have readers := initial_run_readers_live term fuel
  rw [stackShape] at readers
  have leased := readers _ List.mem_cons_self token object (some (code.context.length-owner)) rfl
  refine ⟨valueType,originTyped,named_reader_body_slots code slots entered stored domain readerBody
    token readerOrigin continuation,leased,(initial_run_heap_valid term fuel).leased token object leased |>.2,?_⟩
  simp only [step,action,controlShape,stackShape,reader_activation_origin,Option.map_some,execute]

/-- The actual final owner-binding transition receives the original source
Lend result type. Only input typing and concrete control/closure shapes are
premises; no typing of the observed output is requested. -/
theorem reachable_explicit_continuation_activation (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (sourceShape : code.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (controlShape : (run fuel (initial term)).state.control =
      .returned (.closure false again body (⟨first,false⟩ :: code.context)
        (consValues ((Lending.read owner readerBody).subst code.origins) code.origins)
        (some result :: code.values)))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendOwnerArgument object (owner.subst code.origins) :: rest) :
    let bodyCode := enter false again body (⟨first,false⟩ :: code.context)
      (consValues ((Lending.read owner readerBody).subst code.origins) code.origins)
      (some result :: code.values) (owner.subst code.origins) (some (.owner object))
    LoanTyping.HasType env [] [] true bodyCode.origin type ∧
      step (run fuel (initial term)).state = some
        (⟨(run fuel (initial term)).state.heap,.evaluate bodyCode,rest⟩,
          some (.activate false body (owner.subst code.origins))) := by
  refine ⟨typed_explicit_continuation_origin history typed sourceShape object result,?_⟩
  simp only [step,action,controlShape,stackShape,returnAction,applyValue,Option.map_some,execute]

end Jihoo.NativeKernel.Environment.BindingMachine
