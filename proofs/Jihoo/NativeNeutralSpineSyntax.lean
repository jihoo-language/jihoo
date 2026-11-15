import Jihoo.NativeTyping

/-! Shared free-head spine syntax, independent of the active conversion alias. -/
namespace Jihoo.NativeKernel

def neutralSpine (head : Nat) : List Term → Term
  | [] => .var head
  | argument :: rest => .app (neutralSpine head rest) argument

end Jihoo.NativeKernel
