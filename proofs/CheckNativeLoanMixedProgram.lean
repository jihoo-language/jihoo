import Jihoo.NativeLoanMixedAdmission
import Jihoo.NativeLoanPureMixedAdmission
import Jihoo.TypingInput

/-! Bounded IO adapter for canonical version-6 mixed declarations. -/
open Jihoo.NativeKernel Jihoo.GraphCertificates

private def preflight (bytes : ByteArray) : Bool := (do
  let (version, cursor) ← TypingInput.scanNat bytes 0
  if version != 6 then none else do
    let (definitions, cursor) ← TypingInput.scanNat bytes cursor
    if definitions > 1024 then none else do
      let cursor ← TypingInput.scanFields bytes cursor (2 * definitions)
      let (families, cursor) ← TypingInput.scanNat bytes cursor
      if families > 1024 then none else do
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
    let (fuelText, quantityText, pureMode) ← match args with
      | [fuelText, quantityText] => pure (fuelText, quantityText, false)
      | [fuelText, quantityText, "--pure"] => pure (fuelText, quantityText, true)
      | _ => throw (IO.userError "expected typing and quantity fuel with optional --pure")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    let some quantityFuel := quantityText.toNat? | throw (IO.userError "invalid quantity fuel")
    if fuel > 128 || quantityFuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid family program shape or bounds")
    if pureMode then
      unless (Environment.LoanTyping.PureMixedAdmission.checkBytes ⟨fuel, quantityFuel, fuel, 8192⟩ bytes).isSome do
        throw (IO.userError "native pure mixed admission rejects")
      IO.println "exact native pure mixed program accepted"
    else
      unless NativeLoanMixedAdmission.checkBytes fuel quantityFuel bytes do
        throw (IO.userError "native loan mixed admission rejects")
      IO.println "exact native loan mixed program accepted"
    return 0
  catch error =>
    IO.eprintln s!"native loan mixed program rejected: {error}"
    return 1
