import Ziku.Parser
import Ziku.Translate

open Ziku
open Ziku.Translate

def testTranslate (input : String) : IO Unit := do
  match parseExprString input.trim with
  | .ok expr =>
    match translate expr with
    | .ok producer =>
      IO.println s!"Input: {input}"
      IO.println s!"IR: {producer}"
      IO.println ""
    | .error e =>
      IO.println s!"Translation error: {e}"
  | .error e =>
    IO.println s!"Parse error: {e}"

def main : IO UInt32 := do
  IO.println "=== Translation Tests ==="
  IO.println ""

  -- Test literal
  testTranslate "42"

  -- Test variable
  testTranslate "x"

  -- Test binary operation
  testTranslate "1 + 2"

  -- Test lambda
  testTranslate "\\x => x"

  -- Test application
  testTranslate "f(x)"

  -- Test let
  testTranslate "let x = 1 in x + 1"

  -- Test if
  testTranslate "if true then 1 else 0"

  -- Test label
  testTranslate "label result { 42 }"

  -- Test label with goto
  testTranslate "label result { if true then goto(42, result) else 0 }"

  -- Test undefined label (should error)
  IO.println "Testing undefined label (should error):"
  testTranslate "goto(42, undefined)"

  return 0
