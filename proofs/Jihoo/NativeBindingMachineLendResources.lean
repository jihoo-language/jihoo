import Jihoo.NativeBindingMachineLendOrigins
import Jihoo.NativeLoanQuantityOrigins

namespace Jihoo.NativeKernel.Environment.LoanTyping

private def FreeTail (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Term → Prop
  | .free _ rest,type => HasType env loans ctx mode rest type
  | _,_ => True

private theorem free_tail_convert (view : FreeTail env loans ctx mode term first)
    (converted : Conversion.Conv env first second) : FreeTail env loans ctx mode term second := by
  fun_cases FreeTail env loans ctx mode term first <;> simp only [FreeTail] at view ⊢
  exact view.convert converted

/-- Inversion of the complete judgment, retaining arbitrary result conversion. -/
theorem HasType.free_tail (typed : HasType env loans ctx mode (.free owner rest) type) :
    HasType env loans ctx mode rest type := by
  have general : ∀ {term type}, HasType env loans ctx mode term type →
      FreeTail env loans ctx mode term type := by
    intro term type source
    apply HasType.rec (t := source)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack context ghost expression result _ => FreeTail env stack context ghost expression result)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | assumption | skip
    case dataElim => split <;> trivial
    case convert original converted ih => exact free_tail_convert ih converted
  exact general typed

end Jihoo.NativeKernel.Environment.LoanTyping

/-! The dependent resource check identifies the returned owner with its old
name. Actual continuation code retains both bindings. This bridge constructs
the close/activation transitions, transports every old loan permission through
the two retained binders, and interprets both owner aliases as the same heap
identity. Heap guards are derived from the exact reachable reader inventory.
General source/control/resource preservation through arbitrary bodies remains
a separate obligation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

def ObjectReader (object : Nat) (stack : List Frame) : Prop :=
  ∃ frame ∈ stack, ∃ token name, frame.reader? = some (token,object,name)

theorem ReaderInventory.borrowed_iff
    (inventory : ReaderInventory heap (readerFrames stack)) :
    (∃ token, heap.heap.lease token = some object) ↔ ObjectReader object stack := by
  constructor
  · rintro ⟨token,leased⟩
    obtain ⟨name,member⟩ := inventory.covered token object leased
    obtain ⟨frame,member,descriptor⟩ := List.mem_filterMap.mp member
    exact ⟨frame,member,token,name,descriptor⟩
  · rintro ⟨frame,member,token,name,descriptor⟩
    exact ⟨token,inventory.live _ (List.mem_filterMap.mpr ⟨frame,member,descriptor⟩)⟩

theorem ReaderInventory.free_guard_iff (valid : SizedBufferHeap.Valid heap)
    (inventory : ReaderInventory heap (readerFrames stack)) :
    freeGuard heap object = true ↔ ¬ ObjectReader object stack := by
  constructor
  · intro guarded present
    obtain ⟨token,leased⟩ := inventory.borrowed_iff.mpr present
    exact freeGuard_unborrowed valid guarded token leased
  · intro absent
    apply List.all_eq_true.mpr
    intro token member
    apply decide_eq_true
    intro leased
    exact absent (inventory.borrowed_iff.mp ⟨token,leased⟩)

/-- The actual body has owner/result/old-captures slots. The checked restored
body has result/old-captures slots and opens slot zero as the old owner. -/
def restoredContinuation (code : Code) (first again body ownerOrigin resultOrigin : Term)
    (object : Nat) (result : Value) : Code :=
  enter false again body (⟨first,false⟩ :: code.context)
    (consValues resultOrigin code.origins) (some result :: code.values)
    ownerOrigin (some (.owner object))

theorem restored_continuation_slots (code : Code)
    (stored : code.values[owner]? = some (some (.owner object)))
    (first again body resultOrigin : Term) (result : Value) :
    ∀ index,
      (restoredContinuation code first again body ((Term.var owner).subst code.origins)
        resultOrigin object result).values[index]? =
      (some result :: code.values)[Jihoo.Quantity.openOwner (owner+1) index]? := by
  intro index
  cases index with
  | zero => simpa only [restoredContinuation,enter,Jihoo.Quantity.openOwner,
      List.getElem?_cons_zero,List.getElem?_cons_succ] using stored.symm
  | succ index => rfl

theorem restored_continuation_origins (code : Code) (first again body resultOrigin : Term)
    (object : Nat) (result : Value) :
    (restoredContinuation code first again body ((Term.var owner).subst code.origins)
      resultOrigin object result).origin =
      (body.subst (single ((Term.var owner).rename Nat.succ))).subst
        (consValues resultOrigin code.origins) := by
  simp only [restoredContinuation,Code.origin,enter,Term.subst_comp]
  congr 1
  funext index
  cases index with
  | zero => simp only [single,Term.rename,Term.subst,consValues]
  | succ index => simp only [consValues,single,Term.subst]

theorem restored_continuation_loans (code : Code)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (first again body ownerOrigin resultOrigin : Term) (object : Nat) (result : Value) :
    LoanSlots (restoredContinuation code first again body ownerOrigin resultOrigin object result) loans stack := by
  have once := slots.enter entered false first (.lam false again body) resultOrigin (some result)
  have deeper : Loans.Entered (code.context.length+1) loans := by
    intro frame member
    have := entered frame member
    omega
  exact once.enter deeper false again body ownerOrigin (some (.owner object))

private theorem close_activate_five_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object)
    (first again body ownerOrigin resultOrigin : Term) (result : Value) (name : Option Nat)
    (stack : List Frame) :
    run 5 ⟨heap,.returned result,
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      ⟨⟨SizedBufferHeap.close heap token,
        .evaluate (restoredContinuation code first again body ownerOrigin resultOrigin object result),stack⟩,
        [.heap (.close token),.activate false (.lam false again body) resultOrigin,
          .activate false body ownerOrigin],5⟩ := by
  simp only [run,step,action,returnAction,execute,leased,↓reduceIte,evaluateAction,
    Code.child,applyValue,enter,restoredContinuation,Option.map_some]
  rfl

/-- A real reader return installs both aliases, discharges its lease before
either continuation activation, preserves outer permissions and retains the
original result type. Source typing and resource evidence come from the same
Loan64 code/context; no callback/output/success oracle is assumed. -/
theorem reachable_checked_lend_handoff (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (stored : code.values[owner]? = some (some (.owner object)))
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (returned : (run fuel (initial term)).state.control = .returned result)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        ((Lending.read (.var owner) readerBody).subst code.origins)
        (code.child (.lam false first (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let bodyCode := restoredContinuation code first again body ((Term.var owner).subst code.origins)
      ((Lending.read (.var owner) readerBody).subst code.origins) object result
    run 5 (run fuel (initial term)).state =
      ⟨⟨SizedBufferHeap.close heap token,.evaluate bodyCode,stack⟩,
        [.heap (.close token),
          .activate false (.lam false again body) ((Lending.read (.var owner) readerBody).subst code.origins),
          .activate false body ((Term.var owner).subst code.origins)],5⟩ ∧
      LoanTyping.HasType env [] [] true bodyCode.origin type ∧
      LoanSlots bodyCode loans stack ∧
      (∀ index, bodyCode.values[index]? =
        (some result :: code.values)[Jihoo.Quantity.openOwner (owner+1) index]?) ∧
      (SizedBufferHeap.close heap token).heap.live object = true ∧
      (freeGuard (SizedBufferHeap.close heap token) object = true ↔ ¬ ObjectReader object stack) ∧
      ∃ reader mode rest,
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans)
          code.context (Lending.read (.var owner) readerBody) = some reader ∧
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
          (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode rest).demand owner = some 1 ∧
        control = .seq reader (.scope mode rest) := by
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  have remaining := inventory.finish.2
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned result,
        .lendFinish token object name ((Term.var owner).subst code.origins)
          ((Lending.read (.var owner) readerBody).subst code.origins)
          (code.child (.lam false first (.lam false again body))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨?_,typed_explicit_continuation_origin history typed shape object result,
    restored_continuation_loans code slots entered _ _ _ _ _ _ _,
    restored_continuation_slots code stored _ _ _ _ _,live,
    remaining.free_guard_iff valid,?_⟩
  · rw [stateShape]
    exact close_activate_five_steps _ _ leased _ _ _ _ _ _ _ _
  · rw [shape] at checked
    obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
      formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
      readZero,restOne,same⟩ := LoanTyping.ResourceQuantity.dependent_project_contract checked
    exact ⟨reader,mode,rest,readProjected,restProjected,readZero,restOne,same⟩

set_option linter.unusedSimpArgs false in
private theorem close_activate_free_eight_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object) (live : heap.heap.live object = true)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selected : index = 0 ∨ index = owner+2)
    (first again tail ownerOrigin resultOrigin : Term) (result : Value) (name : Option Nat)
    (stack : List Frame) :
    let body := Term.free (.var index) tail
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object result
    let closed := SizedBufferHeap.close heap token
    run 8 ⟨heap,.returned result,
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      if freeGuard closed object then
        ⟨⟨SizedBufferHeap.release closed object,.evaluate (bodyCode.child tail),stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin,.heap (.free object)],8⟩
      else
        ⟨⟨closed,.fault .borrowedOwner,stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin],8⟩ := by
  have aliasStored : (some (.owner object) :: some result :: code.values)[index]? =
      some (some (.owner object)) := by
    rcases selected with rfl | rfl
    · rfl
    · simpa only [Nat.add_assoc,List.getElem?_cons_succ] using stored
  dsimp only
  simp only [run,step,action,returnAction,execute,leased,↓reduceIte,evaluateAction,
    Code.child,applyValue,enter,restoredContinuation,Option.map_some,aliasStored,
    SizedBufferHeap.close,live]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- Both the returned-owner slot and the old captured name execute the same
physical Free. The active reader supplies liveness; the reachable inventory
decides whether an outer reader still prevents release. Neither a live-owner
nor a free-guard/success certificate is an input. -/
theorem reachable_lend_owner_free (term : Term) (fuel : Nat) (code : Code)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selected : index = 0 ∨ index = owner+2)
    (returned : (run fuel (initial term)).state.control = .returned result)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again (.free (.var index) tail)))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let body := Term.free (.var index) tail
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object result
    (¬ ObjectReader object stack →
      run 8 (run fuel (initial term)).state =
        ⟨⟨SizedBufferHeap.release closed object,.evaluate (bodyCode.child tail),stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin,.heap (.free object)],8⟩) ∧
    (ObjectReader object stack →
      run 8 (run fuel (initial term)).state =
        ⟨⟨closed,.fault .borrowedOwner,stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin],8⟩) := by
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  have remaining := inventory.finish.2
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  have guard := remaining.free_guard_iff (object := object) valid
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned result,
        .lendFinish token object name ownerOrigin resultOrigin
          (code.child (.lam false first (.lam false again (.free (.var index) tail)))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := close_activate_free_eight_steps (run fuel (initial term)).state.heap code
    leased live stored selected first again tail ownerOrigin resultOrigin result name stack
  dsimp only at executed
  rw [← stateShape] at executed
  constructor
  · intro absent
    simpa only [guard.mpr absent,↓reduceIte] using executed
  · intro present
    have rejected : freeGuard (SizedBufferHeap.close (run fuel (initial term)).state.heap token) object = false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      exact guard.mp accepted present
    simpa only [rejected,Bool.false_eq_true,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine

namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Expose the actual recursive resource visit after a physical owner use;
the tail is not supplied with a safety or demand certificate. -/
theorem projectRaw_free_variable
    (checked : projectRaw (fuel+2) env loans ctx (.free (.var owner) tail) = some control) :
    ∃ binding rest,
      lookup ctx owner = some binding ∧ binding.erased = false ∧
      projectRaw (fuel+1) env loans ctx tail = some rest ∧
      control = .seq (.use owner) (.seq rest .pure) := by
  simp only [projectRaw,Op.arity,runtimeFields,erasedNode,fields,fetch,
    List.length_cons,List.length_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    bind,Option.bind,Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      simp only [selected] at checked
      cases erased : binding.erased with
      | true => simp [erased] at checked
      | false =>
          cases projected : projectRaw (fuel+1) env loans ctx tail with
          | none => simp [erased,projected] at checked
          | some rest =>
              simp [erased,projected] at checked
              exact ⟨binding,rest,rfl,erased,rfl,checked.symm⟩

/-- Opening the two retained owner aliases is checked before demand analysis.
Once that use is consumed, the source continuation has zero residual demand
for the original owner on every abstract resource prefix. Associating arbitrary
tail-machine executions with those prefixes remains a fundamental obligation. -/
theorem checked_lend_free_tail_zero
    (selected : index = 0 ∨ index = owner+2)
    (checked : project (fuel+3) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false first (.lam false again (.free (.var index) tail)))) = some control) :
    ∃ rest,
      projectRaw (fuel+1) env loans (⟨first,false⟩ :: ctx)
        (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      rest.demand (owner+1) = some 0 ∧
      (∀ events, Prefix rest events → events.count (owner+1) = 0) := by
  obtain ⟨outside,sort,resultType,reader,mode,rest,originalScope,readScope,restScope,
    formed,controlScoped,sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,
    readZero,restOne,same⟩ := dependent_project_contract checked
  have ownerMapping : (Term.var index).subst (single ((Term.var owner).rename Nat.succ)) =
      .var (owner+1) := by
    rcases selected with rfl | rfl
    · exact restored_returned_owner
    · exact restored_original_owner
  rw [subst_free] at restProjected
  rw [ownerMapping] at restProjected
  obtain ⟨binding,tailControl,found,relevant,tailProjected,rfl⟩ := projectRaw_free_variable restProjected
  have residual : tailControl.demand (owner+1) = some 0 := by
    have ownerOne := Jihoo.Quantity.scopes_outer (modes := [mode]) restOne
    simp only [List.length_cons,List.length_nil] at ownerOne
    rw [Control.demand,Control.demand,ite_eq_left rfl] at ownerOne
    change ((tailControl.demand (owner+1)).bind (fun n => some (n+0))).bind
      (fun n => some (1+n)) = some 1 at ownerOne
    cases demand : tailControl.demand (owner+1) with
    | none => simp [demand] at ownerOne
    | some count =>
        simp only [demand,Option.bind_some,Option.some.injEq] at ownerOne
        have zero : count = 0 := by omega
        exact congrArg some zero
  refine ⟨tailControl,tailProjected,residual,?_⟩
  intro events run
  have bound := run.count_le residual
  omega

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- One actual checked Lend supplies the original ghost result type and zero
residual ownership demand. Its real reader-return prefix constructs the close,
both retained bindings and the physical Free (or an outer-reader conflict).
Excluding that conflict from general admitted source execution remains open. -/
theorem reachable_checked_lend_free (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again (.free (.var index) tail))))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+3) env loans code.context code.term = some control)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selected : index = 0 ∨ index = owner+2)
    (returned : (run fuel (initial term)).state.control = .returned result)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        ((Lending.read (.var owner) readerBody).subst code.origins)
        (code.child (.lam false first (.lam false again (.free (.var index) tail)))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let body := Term.free (.var index) tail
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (Lending.read (.var owner) readerBody).subst code.origins
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object result
    LoanTyping.HasType env [] [] true (bodyCode.child tail).origin type ∧
      (∃ rest,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨first,false⟩ :: code.context)
          (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        rest.demand (owner+1) = some 0 ∧
        (∀ events, Jihoo.Quantity.Prefix rest events → events.count (owner+1) = 0)) ∧
      (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
      run 8 (run fuel (initial term)).state =
        if freeGuard closed object then
          ⟨⟨SizedBufferHeap.release closed object,.evaluate (bodyCode.child tail),stack⟩,
            [.heap (.close token),.activate false (.lam false again body) resultOrigin,
              .activate false body ownerOrigin,.heap (.free object)],8⟩
        else
          ⟨⟨closed,.fault .borrowedOwner,stack⟩,
            [.heap (.close token),.activate false (.lam false again body) resultOrigin,
              .activate false body ownerOrigin],8⟩ := by
  have original := typed_explicit_continuation_origin history typed shape object result
  change LoanTyping.HasType env [] [] true
    ((Term.free (.var index) tail).subst
      (consValues ((Term.var owner).subst code.origins)
        (consValues ((Lending.read (.var owner) readerBody).subst code.origins) code.origins))) type at original
  rw [subst_free] at original
  have residual := LoanTyping.ResourceQuantity.checked_lend_free_tail_zero selected (shape ▸ checked)
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  have remaining := inventory.finish.2
  have valid := SizedBufferHeap.step_valid (initial_run_heap_valid term fuel) (.close leased)
  refine ⟨original.free_tail,residual,remaining.free_guard_iff valid,?_⟩
  have executed := close_activate_free_eight_steps (run fuel (initial term)).state.heap code
    leased live stored selected first again tail ((Term.var owner).subst code.origins)
    ((Lending.read (.var owner) readerBody).subst code.origins) result name stack
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned result,
        .lendFinish token object name ((Term.var owner).subst code.origins)
          ((Lending.read (.var owner) readerBody).subst code.origins)
          (code.child (.lam false first (.lam false again (.free (.var index) tail)))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  dsimp only at executed
  rw [← stateShape] at executed
  exact executed

end Jihoo.NativeKernel.Environment.BindingMachine
