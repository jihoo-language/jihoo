import Jihoo.NativeWire
import Jihoo.NativePartialRenaming
import Jihoo.TypingInput

/-! Differential adapter for retained actual Core.shift/substitute/rewrite
observations. The expected tree transformations are the mechanized definitions,
not an independent Python reimplementation. IO/source association is trusted. -/
open Jihoo.NativeKernel NativeArena NativeWire

private def snapshot (text : String) : IO Snapshot := do
  let some s := decodeSnapshot text.toUTF8 | throw (IO.userError "invalid canonical arena")
  unless graphValid s.arena do throw (IO.userError "invalid complete graph")
  return s

private def decoded (s : Snapshot) (root : Nat) : IO Term := do
  let some t := decode 128 s.arena root | throw (IO.userError "invalid selected root")
  return t

private def boundedVariableShift (delta : Int) (body : Term) : Option Term :=
  (PartialRenaming.shift delta 0 body).filter fun
    | .var index => decide (index < 2 ^ 32)
    | _ => false

private def checkLine (line : String) : IO Unit := do
  let [countText, name, mode, status, beforeText, afterText] := line.splitOn "\t" |
    throw (IO.userError "invalid transform observation shape")
  let some count := countText.toNat? | throw (IO.userError "invalid vector count")
  unless count = 0 ∨ count = 1 ∨ count = 3 do throw (IO.userError "unexpected vector count")
  let before ← snapshot beforeText
  let after ← snapshot afterText
  unless before.termRoot = after.termRoot do throw (IO.userError "original root changed")
  unless before.arena.toList = after.arena.toList.take before.arena.size do
    throw (IO.userError "native operation changed existing arena entries")
  let body ← decoded before before.termRoot
  let value ← decoded before before.typeRoot
  let expected ← match mode with
    | "shift-up" => pure (PartialRenaming.shift 2 0 body)
    | "shift-down" => pure (PartialRenaming.shift (-1) 0 body)
    | "shift-u32-max" | "shift-u32-wrap" => pure (boundedVariableShift 1 body)
    | "shift-i64-max" => pure (boundedVariableShift (2 ^ 63 - 1) body)
    | "shift-i64-min" => pure (boundedVariableShift (-(2 ^ 63)) body)
    | "shift-cutoff-wrap" => do
        let .node (.lam _) [_, _] := body | throw (IO.userError "invalid cutoff-overflow fixture")
        pure none
    | "substitute" => pure (some (body.subst (single value)))
    | "rewrite" => pure (some (PartialRenaming.rewrite 0 value body))
    | _ => throw (IO.userError "unknown native operation")
  if status = "1" then
    let result ← decoded after after.typeRoot
    unless expected = some result do throw (IO.userError s!"{name}/{count}/{mode}: result differs")
  else if status = "0" then
    unless expected = none do throw (IO.userError s!"{name}/{count}/{mode}: unexpected rejection")
  else throw (IO.userError "invalid result status")

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid observation text")
    let lines := (text.splitOn "\n").filter (· != "")
    unless lines.length = 665 do throw (IO.userError "incomplete transform observations")
    for line in lines do checkLine line
    IO.println "native transforms: 665 actual Core operations matched (including five machine boundaries)"
    return 0
  catch error =>
    IO.eprintln s!"native transform correspondence rejected: {error}"
    return 1
