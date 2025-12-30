import Ziku.IR.Eval
import Ziku.IR.Syntax
import Ziku.Syntax

open Ziku
open Ziku.IR

-- Helper to create a SourcePos for testing
def testPos : SourcePos := default

-- Helper to create integer literal
def intLit (n : Int) : Producer := Producer.lit testPos (Ziku.Lit.int n)

-- Helper to create string for field value (simulating a long value)
def longValue : Producer :=
  Producer.lit testPos (Ziku.Lit.int 1234567890123456789012345678901234567890)

-- Helper to create a very long string value
def veryLongStringValue : Producer :=
  Producer.lit testPos (Ziku.Lit.string "This is a very long string value that will definitely exceed the eighty character limit for truncation")

-- Helper to check if a string contains a substring
def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Test case structure
structure TestCase where
  name : String
  producer : Producer
  expectedContains : List String
  maxLen : Nat := 80

def runTest (tc : TestCase) : IO Bool := do
  let result := truncateRecord tc.producer tc.maxLen
  let allMatch := tc.expectedContains.all (stringContains result)
  IO.println s!"Test: {tc.name}"
  IO.println s!"  Result: {result}"
  IO.println s!"  Expected to contain: {tc.expectedContains}"
  IO.println s!"  Length: {result.length}"
  IO.println s!"  Status: {if allMatch then "✓ PASS" else "✗ FAIL"}"
  IO.println ""
  return allMatch

def tests : List TestCase := [
  -- Test 1: Empty record
  { name := "Empty record"
    producer := Producer.record testPos []
    expectedContains := ["{ }"]
  },

  -- Test 2: Short record (should not truncate)
  { name := "Short record (no truncation)"
    producer := Producer.record testPos [
      ("x", intLit 1),
      ("y", intLit 2)
    ]
    expectedContains := ["{ x = 1, y = 2 }"]
  },

  -- Test 3: Long record with many fields (should truncate)
  { name := "Long record with many fields"
    producer := Producer.record testPos [
      ("field1", intLit 1),
      ("field2", intLit 2),
      ("field3", intLit 3),
      ("field4", intLit 4),
      ("field5", intLit 5),
      ("field6", intLit 6),
      ("field7", intLit 7),
      ("field8", intLit 8),
      ("field9", intLit 9),
      ("field10", intLit 10)
    ]
    expectedContains := [", ... }"]
  },

  -- Test 4: First field is very long
  { name := "First field is very long"
    producer := Producer.record testPos [
      ("very_long_field_name_that_exceeds_limit", longValue),
      ("y", intLit 2)
    ]
    expectedContains := ["{ very_long_field_name_that_exceeds_limit =", "... }"]
  },

  -- Test 5: Multiple fields, truncates at second field
  { name := "Truncate at second field"
    producer := Producer.record testPos [
      ("short", intLit 1),
      ("very_long_field_with_long_value", longValue)
    ]
    expectedContains := [", ... }"]
    maxLen := 30
  },

  -- Test 6: Non-record type (should not truncate)
  { name := "Non-record type (integer)"
    producer := intLit 42
    expectedContains := ["42"]
  },

  -- Test 7: Single field that fits
  { name := "Single short field"
    producer := Producer.record testPos [("x", intLit 1)]
    expectedContains := ["{ x = 1 }"]
  },

  -- Test 8: Single field that's too long
  { name := "Single long field exceeds limit"
    producer := Producer.record testPos [
      ("very_long_field_name_that_definitely_exceeds_the_eighty_character_limit", longValue)
    ]
    expectedContains := ["{ ", "... }"]
  },

  -- Test 9: Short field name but very long value
  { name := "Short name, long value"
    producer := Producer.record testPos [
      ("x", veryLongStringValue),
      ("y", intLit 2)
    ]
    expectedContains := [", ... }"]
  }
]

def main : IO UInt32 := do
  IO.println "=== Record Truncation Tests ==="
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
