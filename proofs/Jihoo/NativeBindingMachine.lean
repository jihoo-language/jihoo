import Jihoo.NativeCallStorePermissions
import Jihoo.SizedBufferHeap

/-! A binding-retaining native-tree CBV machine. Closures capture original
code and environments; runtime arguments are evaluated once and inserted as
values, while erased arguments retain only source provenance. The explicit
fragment covers U64 addition, signed I64 arithmetic, conditionals, Strict and
buffer Alloc/Free.
Unsupported syntax and invalid operations report faults. This is a source
machine and abstract allocator model, not native evaluator refinement or a
whole-kernel progress theorem. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

inductive Value where
  | natural (value : Nat)
  | integer (value : Int)
  | typeCode (source : Term)
  | owner (object : Nat)
  | closure (erased : Bool) (domain body : Term) (context : Context)
      (origins : Nat → Term) (captured : List (Option Value))

structure Code where
  term : Term
  context : Context
  origins : Nat → Term
  values : List (Option Value)

def Code.initial (term : Term) : Code := ⟨term,[],Term.var,[]⟩
def Code.child (code : Code) (term : Term) : Code := { code with term := term }
def Code.origin (code : Code) : Term := code.term.subst code.origins

inductive Fault where
  | unsupported
  | missingVariable
  | erasedVariable
  | wrongValue
  | literalRange
  | arithmeticOverflow
  | allocationOverflow
  | deadOwner
  | borrowedOwner
  deriving DecidableEq, Repr

inductive Control where
  | evaluate (code : Code)
  | returned (value : Value)
  | fault (reason : Fault)

inductive Frame where
  | function (argument : Code)
  | argument (function : Value) (origin : Term)
  | strict (rest : Code)
  | addLeft (right : Code)
  | addRight (left : Nat)
  | arithmeticLeft (op : Arith) (right : Code)
  | arithmeticRight (op : Arith) (left : Int)
  | allocateCount (fill : Code)
  | allocateFill (count : Nat)
  | free (rest : Code)
  | branchLeft (equal : Bool) (second yes no : Code) (first : Term)
  | branchRight (equal : Bool) (first : Nat) (yes no : Code) (firstOrigin secondOrigin : Term)

inductive Event where
  | heap (event : SizedBufferHeap.Event)
  | activate (erased : Bool) (body argumentOrigin : Term)

structure State where
  heap : SizedBufferHeap.State
  control : Control
  stack : List Frame

def initial (term : Term) (heap : SizedBufferHeap.State := SizedBufferHeap.empty) : State :=
  ⟨heap,.evaluate (.initial term),[]⟩

/-- This constructor performs the actual source binding update. The code body
and captured context are retained; the argument expression is not substituted. -/
def enter (erased : Bool) (domain body : Term) (context : Context)
    (origins : Nat → Term) (captured : List (Option Value))
    (argumentOrigin : Term) (argument : Option Value) : Code :=
  ⟨body,⟨domain,erased⟩ :: context,consValues argumentOrigin origins,argument :: captured⟩

inductive Action where
  | control (next : Control) (stack : List Frame) (activation : Option (Bool × Term × Term) := none)
  | allocate (count : Nat) (fill : Int) (stack : List Frame)
  | free (object : Nat) (rest : Code) (stack : List Frame)

def fault (reason : Fault) (stack : List Frame) : Action := .control (.fault reason) stack

def applyValue (function : Value) (argumentOrigin : Term) (argument : Option Value)
    (stack : List Frame) : Action :=
  match function with
  | .closure erased domain body context origins captured =>
      .control (.evaluate (enter erased domain body context origins captured argumentOrigin argument))
        stack (some (erased,body,argumentOrigin))
  | _ => fault .wrongValue stack

def branchCode (equal : Bool) (yes : Code) (firstOrigin secondOrigin : Term) : Code :=
  let domain := if equal then Term.eq firstOrigin secondOrigin else Term.lt firstOrigin secondOrigin
  let evidence := if equal then Term.refl (firstOrigin.subst yes.origins)
    else Term.decide (firstOrigin.subst yes.origins) (secondOrigin.subst yes.origins)
  ⟨yes.term,⟨domain,true⟩ :: yes.context,consValues evidence yes.origins,none :: yes.values⟩

def returnAction (value : Value) : List Frame → Option Action
  | [] => none
  | frame :: stack => some <| match frame,value with
      | .function argument,.closure true domain body context origins captured =>
          applyValue (.closure true domain body context origins captured) argument.origin none stack
      | .function argument,function@(.closure false _ _ _ _ _) =>
          .control (.evaluate argument) (.argument function argument.origin :: stack)
      | .function _,_ => fault .wrongValue stack
      | .argument function origin,value => applyValue function origin (some value) stack
      | .strict rest,_ => .control (.evaluate rest) stack
      | .addLeft right,.natural left => .control (.evaluate right) (.addRight left :: stack)
      | .addRight left,.natural right =>
          if left + right < 2^64 then .control (.returned (.natural (left + right))) stack
          else fault .arithmeticOverflow stack
      | .arithmeticLeft op right,.integer left =>
          .control (.evaluate right) (.arithmeticRight op left :: stack)
      | .arithmeticRight op left,.integer right =>
          let result := ValueReduction.arithmetic op left right
          if ValueReduction.signed64 result then .control (.returned (.integer result)) stack
          else fault .arithmeticOverflow stack
      | .allocateCount fill,.natural count => .control (.evaluate fill) (.allocateFill count :: stack)
      | .allocateFill count,.integer fill => .allocate count fill stack
      | .free rest,.owner object => .free object rest stack
      | .branchLeft equal second yes no first,.natural left =>
          .control (.evaluate second) (.branchRight equal left yes no first second.term :: stack)
      | .branchRight equal left yes no firstOrigin secondOrigin,.natural right =>
          if (if equal then left == right else left < right) then
            .control (.evaluate (branchCode equal yes firstOrigin secondOrigin)) stack
          else .control (.evaluate no) stack
      | _,_ => fault .wrongValue stack

def evaluateAction (code : Code) (stack : List Frame) : Action :=
  match code.term with
  | .var index => match code.values[index]? with
      | none => fault .missingVariable stack
      | some none => fault .erasedVariable stack
      | some (some value) => .control (.returned value) stack
  | .natural value =>
      if value < 2^64 then .control (.returned (.natural value)) stack else fault .literalRange stack
  | .integer value =>
      if ValueReduction.signed64 value then .control (.returned (.integer value)) stack else fault .literalRange stack
  | .lam erased domain body =>
      .control (.returned (.closure erased domain body code.context code.origins code.values)) stack
  | .app function argument => .control (.evaluate (code.child function)) (.function (code.child argument) :: stack)
  | .strict first rest => .control (.evaluate (code.child first)) (.strict (code.child rest) :: stack)
  | .uadd left right => .control (.evaluate (code.child left)) (.addLeft (code.child right) :: stack)
  | .arith op left right => .control (.evaluate (code.child left)) (.arithmeticLeft op (code.child right) :: stack)
  | .alloc count fill => .control (.evaluate (code.child count)) (.allocateCount (code.child fill) :: stack)
  | .free owner rest => .control (.evaluate (code.child owner)) (.free (code.child rest) :: stack)
  | .ifLt left right yes no => .control (.evaluate (code.child left))
      (.branchLeft false (code.child right) (code.child yes) (code.child no) left :: stack)
  | .ifEq left right yes no => .control (.evaluate (code.child left))
      (.branchLeft true (code.child right) (code.child yes) (code.child no) left :: stack)
  | .univ _ | .prop | .u64 | .i64 | .array _ | .pi _ _ _ | .buffer _ |
      .ref _ | .back _ _ _ | .refine _ | .lt _ _ | .eq _ _ =>
      .control (.returned (.typeCode code.origin)) stack
  | _ => fault .unsupported stack

def action (state : State) : Option Action :=
  match state.control with
  | .evaluate code => some (evaluateAction code state.stack)
  | .returned value => returnAction value state.stack
  | .fault _ => none

def freeGuard (heap : SizedBufferHeap.State) (object : Nat) : Bool :=
  (List.range heap.heap.nextLease).all (fun token => decide (heap.heap.lease token ≠ some object))

def encodeInteger (value : Int) : Nat := (value + 2^63).toNat
def decodeInteger (value : Nat) : Int := (value : Int) - 2^63

/-- Every action has a result, including explicit faults. Allocation is the
existing abstract successful-allocation model with an explicit byte-overflow
guard; this definition does not assume a host malloc call succeeds. -/
def execute (heap : SizedBufferHeap.State) : Action → State × Option Event
  | .control control stack activation =>
      (⟨heap,control,stack⟩,activation.map (fun event => .activate event.1 event.2.1 event.2.2))
  | .allocate count fill stack =>
      if count * 8 + 8 < 2^64 then
        (⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
          some (.heap (.alloc heap.heap.nextObject count (encodeInteger fill))))
      else (⟨heap,.fault .allocationOverflow,stack⟩,none)
  | .free object rest stack =>
      if heap.heap.live object then
        if freeGuard heap object then
          (⟨SizedBufferHeap.release heap object,.evaluate rest,stack⟩,some (.heap (.free object)))
        else (⟨heap,.fault .borrowedOwner,stack⟩,none)
      else (⟨heap,.fault .deadOwner,stack⟩,none)

def step (state : State) : Option (State × Option Event) :=
  (action state).map (execute state.heap)

def eventHeap : Option Event → List SizedBufferHeap.Event
  | some (.heap event) => [event]
  | _ => []

def eventsHeap (events : List Event) : List SizedBufferHeap.Event :=
  events.filterMap fun | .heap event => some event | .activate _ _ _ => none

structure Result where
  state : State
  events : List Event
  steps : Nat

def run : Nat → State → Result
  | 0,state => ⟨state,[],0⟩
  | fuel + 1,state => match step state with
      | none => ⟨state,[],0⟩
      | some (next,event) =>
          let result := run fuel next
          ⟨result.state,event.toList ++ result.events,result.steps + 1⟩

inductive Status where
  | done
  | fault (reason : Fault)
  | fuel
  deriving DecidableEq, Repr

def status (result : Result) : Status :=
  match result.state.control,result.state.stack with
  | .returned _,[] => .done
  | .fault reason,_ => .fault reason
  | _,_ => .fuel

inductive Observation where
  | natural (value : Nat)
  | integer (value : Int)
  | owner (object : Nat)
  | closure
  | typeCode
  | fault (reason : Fault)
  | fuel
  deriving DecidableEq, Repr

def observe (result : Result) : Observation :=
  match result.state.control,result.state.stack with
  | .returned (.natural value),[] => .natural value
  | .returned (.integer value),[] => .integer value
  | .returned (.owner object),[] => .owner object
  | .returned (.closure _ _ _ _ _ _),[] => .closure
  | .returned (.typeCode _),[] => .typeCode
  | .fault reason,_ => .fault reason
  | _,_ => .fuel

def activationBodies (events : List Event) : List Term :=
  events.filterMap fun | .activate _ body _ => some body | _ => none

def activationOrigins (events : List Event) : List Term :=
  events.filterMap fun | .activate _ _ argument => some argument | _ => none

end Jihoo.NativeKernel.Environment.BindingMachine
