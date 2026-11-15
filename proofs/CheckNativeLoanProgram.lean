import Jihoo.NativeLoanGlobalInput
import Jihoo.TypingInput

/-! Bounded IO adapter for sequential loan-aware global typing. The pure
acceptance theorem is in NativeLoanGlobalInput; quantities remain separate. -/
open Jihoo.NativeKernel Jihoo.GraphCertificates

private def preflight (bytes : ByteArray) : Bool := (do
  let (version, cursor) ← TypingInput.scanNat bytes 0
  if version != 6 then none else do
    let (definitions, cursor) ← TypingInput.scanNat bytes cursor
    if definitions > 1024 then none else do
      let cursor ← TypingInput.scanFields bytes cursor (2 * definitions)
      let (families, cursor) ← TypingInput.scanNat bytes cursor
      if families != 0 then none else do
        let (nodes, cursor) ← TypingInput.scanNat bytes cursor
        if nodes > 4096 then none else do
          let mut cursor := cursor
          for _ in [:nodes] do
            cursor ← TypingInput.scanFields bytes cursor 1
            cursor ← TypingInput.scanVector bytes cursor 4
            cursor ← TypingInput.scanVector bytes cursor 4096
          if cursor = bytes.size then some () else none).isSome

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText] := args | throw (IO.userError "expected typing fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid loan program shape or bounds")
    let some env := NativeLoanGlobalInput.checkBytes fuel bytes |
      throw (IO.userError "native loan program typing rejects")
    IO.println s!"exact native loan program typing accepted: {env.globals.size} declarations"
    return 0
  catch error =>
    IO.eprintln s!"native loan program typing rejected: {error}"
    return 1
