import Ziku.IR.Eval

open Ziku.IR

-- Test case structure for string truncation
structure TestCase where
  name : String
  input : String
  maxLen : Nat
  expected : String

def runTest (tc : TestCase) : IO Bool := do
  let result := truncate tc.input tc.maxLen
  let passed := result == tc.expected
  IO.println s!"Test: {tc.name}"
  IO.println s!"  Input: {repr tc.input} (length: {tc.input.length})"
  IO.println s!"  Max length: {tc.maxLen}"
  IO.println s!"  Expected: {repr tc.expected}"
  IO.println s!"  Actual: {repr result}"
  IO.println s!"  Status: {if passed then "✓ PASS" else "✗ FAIL"}"
  IO.println ""
  return passed

def tests : List TestCase := [
  -- Test 1: Short string (no truncation needed)
  { name := "Short string"
    input := "hello"
    maxLen := 80
    expected := "hello"
  },

  -- Test 2: Empty string
  { name := "Empty string"
    input := ""
    maxLen := 80
    expected := ""
  },

  -- Test 3: Exact boundary (exactly maxLen)
  { name := "Exact boundary"
    input := "12345678"
    maxLen := 8
    expected := "12345678"
  },

  -- Test 4: Just over boundary
  { name := "Just over boundary"
    input := "123456789"
    maxLen := 8
    expected := "12345..."
  },

  -- Test 5: Much longer string
  { name := "Much longer string"
    input := "hello world this is a very long string that needs truncation"
    maxLen := 20
    expected := "hello world this ..."
  },

  -- Test 6: Very short maxLen
  { name := "Very short maxLen"
    input := "hello"
    maxLen := 3
    expected := "..."
  },

  -- Test 7: maxLen less than 3 (edge case)
  { name := "maxLen = 2"
    input := "hello"
    maxLen := 2
    expected := "..."  -- Should still show "..." even though maxLen < 3
  },

  -- Test 8: Single character with maxLen 1
  { name := "Single char, maxLen 1"
    input := "a"
    maxLen := 1
    expected := "a"
  },

  -- Test 9: Unicode string
  { name := "Unicode string"
    input := "こんにちは世界"
    maxLen := 10
    expected := "こんにちは世界"
  },

  -- Test 10: Long unicode string
  { name := "Long unicode string"
    input := "これは非常に長い日本語の文字列です"
    maxLen := 15
    expected := "これは非常に長い日本語の..."
  },

  -- Test 11: Default maxLen (80)
  { name := "Default maxLen"
    input := String.ofList (List.replicate 100 'a')  -- 100 'a's
    maxLen := 80
    expected := String.ofList (List.replicate 77 'a') ++ "..."
  }
]

def main : IO UInt32 := do
  IO.println "=== Generic String Truncation Tests ==="
  IO.println ""

  let mut allPassed := true
  for test in tests do
    let passed ← runTest test
    allPassed := allPassed && passed

  IO.println "=== Summary ==="
  if allPassed then
    IO.println s!"All {tests.length} tests passed ✓"
    return 0
  else
    IO.println "Some tests failed ✗"
    return 1
