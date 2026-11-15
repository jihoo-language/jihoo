import Jihoo.NativeLoanTypingInput
import Jihoo.TypingInput

/-! Bounded loan typing for one canonical version-6 declaration without families.
This is a typing entry point; resource/heap admission remains separate. -/
open Jihoo.NativeKernel Jihoo.GraphCertificates

private def preflight (bytes : ByteArray) : Bool := (do
  let (version, cursor) ← TypingInput.scanNat bytes 0
  if version != 6 then none else do
    let (definitions, cursor) ← TypingInput.scanNat bytes cursor
    if definitions != 1 then none else do
      let cursor ← TypingInput.scanFields bytes cursor (2 * definitions)
      let (families, cursor) ← TypingInput.scanNat bytes cursor
      if families != 0 then none else do
        let mut cursor := cursor
        let mut constructors := 0
        for _ in [:families] do
          cursor ← TypingInput.scanFields bytes cursor 4
          let (count, next) ← TypingInput.scanNat bytes cursor
          constructors := constructors + count
          if constructors > 4096 then none else do
            cursor ← TypingInput.scanFields bytes next count
        let (nodes, nodeStart) ← TypingInput.scanNat bytes cursor
        if nodes > 4096 then none else do
          let mut nodeCursor := nodeStart
          for _ in [:nodes] do
            nodeCursor ← TypingInput.scanFields bytes nodeCursor 1
            nodeCursor ← TypingInput.scanVector bytes nodeCursor 4
            nodeCursor ← TypingInput.scanVector bytes nodeCursor 4096
          if nodeCursor = bytes.size then some () else none).isSome

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText] := args | throw (IO.userError "expected typing fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid family program shape or bounds")
    unless NativeLoanTypingInput.checkBytes fuel bytes do
      throw (IO.userError "native loan typing rejects")
    IO.println "exact native loan typing accepted"
    return 0
  catch error =>
    IO.eprintln s!"native loan typing rejected: {error}"
    return 1
