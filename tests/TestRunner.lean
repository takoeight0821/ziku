/-
Master test runner that executes all test suites:
- Truncate tests (unit tests for string truncation)
- Golden tests (integration tests for parser, type inference, IR evaluation)
-/

import Ziku.Parser
import Ziku.Infer
import Ziku.Elaborate
import Ziku.Translate
import Ziku.IR.Eval
import Ziku.Backend.Scheme

-- ============================================================================
-- Truncate Tests (from TruncateTest.lean)
-- ============================================================================

structure TruncateTestCase where
  name : String
  input : String
  maxLen : Nat
  expected : String

def runTruncateTest (tc : TruncateTestCase) : IO Bool := do
  let result := Ziku.IR.truncate tc.input tc.maxLen
  let passed := result == tc.expected
  IO.println s!"  Testing {tc.name}... {if passed then "✓" else "✗"}"
  if !passed then
    IO.println s!"    Expected: {repr tc.expected}"
    IO.println s!"    Actual:   {repr result}"
  return passed

def truncateTests : List TruncateTestCase := [
  { name := "Short string"
    input := "hello"
    maxLen := 80
    expected := "hello"
  },
  { name := "Empty string"
    input := ""
    maxLen := 80
    expected := ""
  },
  { name := "Exact boundary"
    input := "12345678"
    maxLen := 8
    expected := "12345678"
  },
  { name := "Just over boundary"
    input := "123456789"
    maxLen := 8
    expected := "12345..."
  },
  { name := "Much longer string"
    input := "hello world this is a very long string that needs truncation"
    maxLen := 20
    expected := "hello world this ..."
  },
  { name := "Very short maxLen"
    input := "hello"
    maxLen := 3
    expected := "..."
  },
  { name := "maxLen = 2"
    input := "hello"
    maxLen := 2
    expected := "..."
  },
  { name := "Single char, maxLen 1"
    input := "a"
    maxLen := 1
    expected := "a"
  },
  { name := "Unicode string"
    input := "こんにちは世界"
    maxLen := 10
    expected := "こんにちは世界"
  },
  { name := "Long unicode string"
    input := "これは非常に長い日本語の文字列です"
    maxLen := 15
    expected := "これは非常に長い日本語の..."
  },
  { name := "Default maxLen"
    input := String.ofList (List.replicate 100 'a')
    maxLen := 80
    expected := String.ofList (List.replicate 77 'a') ++ "..."
  }
]

def runTruncateTests : IO (Nat × Nat) := do
  IO.println "\n=== truncate tests ==="
  let mut passed := 0
  let mut failed := 0
  for test in truncateTests do
    let ok ← runTruncateTest test
    if ok then
      passed := passed + 1
    else
      failed := failed + 1
  pure (passed, failed)

-- ============================================================================
-- Golden Tests (from GoldenTest.lean)
-- ============================================================================

inductive TestResult where
  | pass : TestResult
  | fail : String → String → TestResult
  | error : String → TestResult
  deriving Repr

structure TestCase where
  name : String
  inputPath : String
  goldenPath : String
  testType : String
  expectError : Bool

def readFileOrEmpty (path : String) : IO String := do
  try
    IO.FS.readFile path
  catch _ =>
    pure ""

def discoverTests (dir : System.FilePath) : IO (List String) := do
  try
    let entries ← dir.readDir
    let zikuFiles := entries.filterMap fun entry =>
      let name := entry.fileName
      if name.endsWith ".ziku" then
        some (name.dropRight 5)
      else
        none
    pure (zikuFiles.toList.mergeSort (· < ·))
  catch _ =>
    pure []

structure TestOutput where
  output : String
  isError : Bool
  deriving Repr

def runParserTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr => .ok { output := toString expr, isError := false }
  | .error e => .ok { output := e, isError := true }

def runInferTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.runInfer expr with
    | .ok (ty, _) => .ok { output := toString ty, isError := false }
    | .error e => .ok { output := toString e, isError := true }
  | .error e => .error e

def runIREvalTest (input : String) : IO (Except String TestOutput) := do
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translateToStatement elaborated with
      | .ok stmt =>
        let result ← Ziku.IR.eval stmt
        match result with
        | .value p _ => return .ok { output := Ziku.IR.truncate p.toString, isError := false }
        | .stuck s env =>
          let val := env.lookup "evalList"
          return .error s!"Stuck: {s}\nEnv keys: {env.keys}\nevalList: {repr val}"
        | .error msg => return .ok { output := s!"Error: {msg}", isError := true }
      | .error e => return .ok { output := s!"Translation error: {e}", isError := true }
    | .error e => return .ok { output := s!"Elaboration error: {e}", isError := true }
  | .error e => return .error e

def runTranslateTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer => .ok { output := producer.toString, isError := false }
      | .error e => .ok { output := s!"Translation error: {e}", isError := true }
    | .error e => .ok { output := s!"Elaboration error: {e}", isError := true }
  | .error e => .error e

def generateScheme (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer =>
        .ok (Ziku.Backend.Scheme.compileProducer producer)
      | .error e => .error s!"Translation error: {e}"
    | .error e => .error s!"Elaboration error: {e}"
  | .error e => .error e

def runSchemeCodegenTest (input : String) : Except String TestOutput :=
  match generateScheme input with
  | .ok code => .ok { output := code, isError := false }
  | .error e => .ok { output := s!"Compilation error: {e}", isError := true }

def runSchemeTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  match generateScheme input with
  | .error e =>
    pure (TestResult.error s!"Compilation error: {e}")
  | .ok schemeCode =>
    let tempFile := s!"/tmp/ziku_test_{tc.name}.ss"
    IO.FS.writeFile tempFile schemeCode

    let result ← IO.Process.output {
      cmd := "scheme"
      args := #["--script", tempFile]
    }

    let actual := result.stdout.trim

    if result.exitCode != 0 then
      pure (TestResult.error s!"Scheme error: {result.stderr.trim}")
    else if golden.isEmpty then
      IO.FS.writeFile tc.goldenPath actual
      IO.println s!"  Created golden file: {tc.goldenPath}"
      pure TestResult.pass
    else if actual == golden.trim then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trim actual)

def runIREvalFull (input : String) : IO (Except String TestOutput) := do
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translateToStatement elaborated with
      | .ok stmt =>
        let result ← Ziku.IR.eval stmt
        match result with
        | .value p _ => return .ok { output := p.toString, isError := false }
        | .stuck s env =>
          let val := env.lookup "evalList"
          return .error s!"Stuck: {s}\nEnv keys: {env.keys}\nevalList: {repr val}"
        | .error msg => return .ok { output := s!"Error: {msg}", isError := true }
      | .error e => return .ok { output := s!"Translation error: {e}", isError := true }
    | .error e => return .ok { output := s!"Elaboration error: {e}", isError := true }
  | .error e => return .error e

def runConsistencyTest (name : String) (inputPath : String) : IO TestResult := do
  let input ← IO.FS.readFile inputPath

  let irResult ← runIREvalFull input
  match irResult with
  | .error e =>
    pure (TestResult.error s!"IR eval parse error: {e}")
  | .ok irOutput =>
    match generateScheme input with
    | .error e =>
      pure (TestResult.error s!"Scheme compilation error: {e}")
    | .ok schemeCode =>
      let tempFile := s!"/tmp/ziku_consistency_{name}.ss"
      IO.FS.writeFile tempFile schemeCode

      let result ← IO.Process.output {
        cmd := "scheme"
        args := #["--script", tempFile]
      }

      if result.exitCode != 0 then
        pure (TestResult.error s!"Scheme error: {result.stderr.trim}")
      else
        let schemeOutput := result.stdout.trim
        if irOutput.output.trim == schemeOutput then
          pure TestResult.pass
        else
          let irDisplay := Ziku.IR.truncate irOutput.output.trim
          pure (TestResult.fail s!"IR eval: {irDisplay}" s!"Scheme: {Ziku.IR.truncate schemeOutput}")

def runTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  let result : Except String TestOutput ← match tc.testType with
    | "infer" => pure (runInferTest input)
    | "ir-eval" => runIREvalTest input
    | "translate" => pure (runTranslateTest input)
    | "scheme-codegen" => pure (runSchemeCodegenTest input)
    | _ => pure (runParserTest input)

  match result with
  | .error e =>
    pure (TestResult.error s!"Parse error: {e}")
  | .ok testOutput =>
    if tc.expectError && !testOutput.isError then
      pure (TestResult.error s!"Expected error but got success: {testOutput.output}")
    else if !tc.expectError && testOutput.isError then
      pure (TestResult.error s!"Expected success but got error: {testOutput.output}")
    else if golden.isEmpty then
      IO.FS.writeFile tc.goldenPath testOutput.output
      IO.println s!"  Created golden file: {tc.goldenPath}"
      pure TestResult.pass
    else if testOutput.output.trim == golden.trim then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trim testOutput.output.trim)

def runSubCategory (category : String) (subdir : String) (testType : String) (expectError : Bool) : IO (Nat × Nat) := do
  let dir := System.FilePath.mk s!"tests/golden/{category}/{subdir}"
  let tests ← discoverTests dir

  let mut passed := 0
  let mut failed := 0

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{dir}/{baseName}.ziku"
      goldenPath := s!"{dir}/{baseName}.golden"
      testType := testType
      expectError := expectError
    }

    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    let result ← runTest tc
    match result with
    | .pass =>
      IO.println s!"✓"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"✗"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"✗ {msg}"
      failed := failed + 1

  pure (passed, failed)

def runCategory (category : String) (testType : String) : IO (Nat × Nat) := do
  IO.println s!"\n=== {category} tests ==="

  IO.println s!"  --- success ---"
  let (successPassed, successFailed) ← runSubCategory category "success" testType false

  IO.println s!"  --- error ---"
  let (errorPassed, errorFailed) ← runSubCategory category "error" testType true

  pure (successPassed + errorPassed, successFailed + errorFailed)

def runSchemeOnlyCategory : IO (Nat × Nat) := do
  let dir := System.FilePath.mk "tests/golden/scheme/success"
  let tests ← discoverTests dir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== scheme-only tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{dir}/{baseName}.ziku"
      goldenPath := s!"{dir}/{baseName}.golden"
      testType := "scheme"
      expectError := false
    }

    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    let result ← runSchemeTest tc
    match result with
    | .pass =>
      IO.println s!"✓"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"✗"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"✗ {msg}"
      failed := failed + 1

  pure (passed, failed)

def runConsistencyCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== consistency tests (IR eval vs Scheme) ==="

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    let result ← runConsistencyTest baseName inputPath
    match result with
    | .pass =>
      IO.println s!"✓"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"✗"
      IO.println s!"    {expected}"
      IO.println s!"    {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"✗ {msg}"
      failed := failed + 1

  pure (passed, failed)

def runEmitTranslateCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== emit-translate tests ==="

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    let input ← IO.FS.readFile inputPath
    let result := runTranslateTest input
    match result with
    | .ok output =>
      if output.isError then
        IO.println s!"✗ {output.output}"
        failed := failed + 1
      else
        IO.println s!"✓"
        passed := passed + 1
    | .error e =>
      IO.println s!"✗ {e}"
      failed := failed + 1

  pure (passed, failed)

def runEmitSchemeCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== emit-scheme tests ==="

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    let input ← IO.FS.readFile inputPath
    let result := runSchemeCodegenTest input
    match result with
    | .ok output =>
      if output.isError then
        IO.println s!"✗ {output.output}"
        failed := failed + 1
      else
        IO.println s!"✓"
        passed := passed + 1
    | .error e =>
      IO.println s!"✗ {e}"
      failed := failed + 1

  pure (passed, failed)

def runIOTest (baseName : String) (inputPath : String) (goldenPath : String) (stdinInputPath : Option String) : IO TestResult := do
  let golden ← readFileOrEmpty goldenPath
  
  let args := #["exe", "ziku", "--eval", inputPath]
  
  -- If there is an .input file, we use it as stdin. 
  -- Currently we can't easily pipe stdin to lake exe without using a shell or fancier IO process API.
  -- But IO.Process.spawn/output doesn't support setting stdin content directly as string or file.
  -- However, we can use "sh -c 'echo ... | lake ...'" or simply assume `lake` is available in PATH?
  -- Wait, `lake exe ziku` builds and runs.
  -- Let's try to run the binary directly if possible, or use a shell wrapper.
  -- Simpler: write a temporary script.
  
  let stdinContent ← match stdinInputPath with
    | some p => IO.FS.readFile p
    | none => pure ""

  -- Workaround for feeding stdin: use sh
  -- Be careful with escaping.
  -- Ideally we would use IO.Process.spawn with Stdio.piped and write to stdin.
  -- But IO.Process.output doesn't expose that.
  -- We can use child.stdin.putStr ...
  
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := args
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  
  let (stdin, child) ← child.takeStdin
  stdin.putStr stdinContent
  stdin.flush
  -- Close stdin to signal EOF (drop happens automatically when variable goes out of scope?)
  -- In Lean, resources are managed by reference counting / GC or explicit close?
  -- Explicitly relying on scope/GC for stdin closure might be tricky.
  -- But IO.Handle doesn't have explicit close in API easily accessible?
  -- Actually, `takeStdin` gives `IO.FS.Stream`.
  -- Let's ignore explicit close for now (maybe flush is enough?) or verify if `ziku` waits for EOF. `readLine` waits for newline.

  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated

  let exitCode ← child.wait
  let actualStdOut ← IO.ofExcept stdout.get
  let actualStdErr ← IO.ofExcept stderr.get
  
  let actual := actualStdOut.trim
  
  if exitCode != 0 then
    pure (TestResult.error s!"Runtime error: {actualStdErr.trim}")
  else if golden.isEmpty then
    IO.FS.writeFile goldenPath actual
    IO.println s!"  Created golden file: {goldenPath}"
    pure TestResult.pass
  else if actual == golden.trim then
    pure TestResult.pass
  else
    pure (TestResult.fail golden.trim actual)

def runIOTestCategory : IO (Nat × Nat) := do
  let dir := System.FilePath.mk "tests/golden/io/success"
  let tests ← discoverTests dir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== io tests ==="

  for baseName in tests do
    let inputPath := s!"{dir}/{baseName}.ziku"
    let goldenPath := s!"{dir}/{baseName}.golden"
    let inputFilePath := s!"{dir}/{baseName}.input"
    let stdinInputPath := if (← System.FilePath.pathExists inputFilePath) then some inputFilePath else none

    IO.print s!"  Testing {baseName}... "
    (← IO.getStdout).flush
    
    let result ← runIOTest baseName inputPath goldenPath stdinInputPath
    match result with
    | .pass =>
      IO.println s!"✓"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"✗"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"✗ {msg}"
      failed := failed + 1

  pure (passed, failed)

-- ============================================================================
-- Main: Run all test suites
-- ============================================================================

def main : IO UInt32 := do
  IO.println "Running all tests..."

  -- Truncate tests (unit tests)
  let (truncatePassed, truncateFailed) ← runTruncateTests

  -- Golden tests (integration tests)
  let (parserPassed, parserFailed) ← runCategory "parser" "parser"
  let (inferPassed, inferFailed) ← runCategory "infer" "infer"
  let (irEvalPassed, irEvalFailed) ← runCategory "ir-eval" "ir-eval"
  let (emitTranslatePassed, emitTranslateFailed) ← runEmitTranslateCategory
  let (emitSchemePassed, emitSchemeFailed) ← runEmitSchemeCategory
  let (schemeOnlyPassed, schemeOnlyFailed) ← runSchemeOnlyCategory
  let (consistencyPassed, consistencyFailed) ← runConsistencyCategory
  let (ioPassed, ioFailed) ← runIOTestCategory

  let totalPassed := truncatePassed + parserPassed + inferPassed + irEvalPassed +
                     emitTranslatePassed + emitSchemePassed + schemeOnlyPassed + consistencyPassed + ioPassed
  let totalFailed := truncateFailed + parserFailed + inferFailed + irEvalFailed +
                     emitTranslateFailed + emitSchemeFailed + schemeOnlyFailed + consistencyFailed + ioFailed

  IO.println s!"\n=== Summary ==="
  IO.println s!"Truncate tests: {truncatePassed} passed, {truncateFailed} failed"
  IO.println s!"Golden tests: {totalPassed - truncatePassed} passed, {totalFailed - truncateFailed} failed"
  IO.println s!"Total: {totalPassed} passed, {totalFailed} failed"

  if totalFailed > 0 then
    pure 1
  else
    IO.println "All tests passed!"
    pure 0
