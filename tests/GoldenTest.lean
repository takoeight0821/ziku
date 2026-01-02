import Ziku.Parser
import Ziku.Infer
import Ziku.Elaborate
import Ziku.Translate
import Ziku.IR.Eval
import Ziku.Backend.Scheme

/-- Result of a single test case -/
inductive TestResult where
  | pass : TestResult
  | fail : String → String → TestResult  -- expected, actual
  | error : String → TestResult
  deriving Repr

/-- A test case with input file and expected output -/
structure TestCase where
  name : String
  inputPath : String
  goldenPath : String
  testType : String  -- "parser", "infer", or "ir-eval"
  expectError : Bool -- true if this test should produce an error

/-- Read file contents, return empty string if file doesn't exist -/
def readFileOrEmpty (path : String) : IO String := do
  try
    IO.FS.readFile path
  catch _ =>
    pure ""

/-- Discover test files in a directory by scanning for .ziku files -/
def discoverTests (dir : System.FilePath) : IO (List String) := do
  try
    let entries ← dir.readDir
    let zikuFiles := entries.filterMap fun entry =>
      let name := entry.fileName
      if name.endsWith ".ziku" then
        some (name.dropRight 5)  -- Remove ".ziku" extension
      else
        none
    pure (zikuFiles.toList.mergeSort (· < ·))  -- Sort for deterministic order
  catch _ =>
    pure []  -- Return empty list if directory doesn't exist

/-- Result of running a test: (output, isError) -/
structure TestOutput where
  output : String
  isError : Bool
  deriving Repr

/-- Run a parser test -/
def runParserTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr => .ok { output := toString expr, isError := false }
  | .error e => .ok { output := e, isError := true }  -- Parse errors are test output for error tests


/-- Run a type inference test -/
def runInferTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.runInfer expr with
    | .ok (ty, _) => .ok { output := toString ty, isError := false }
    | .error e => .ok { output := toString e, isError := true }
  | .error e => .error e

/-- Run an IR evaluation test (parse → elaborate → translate → focus → IR eval) -/
def runIREvalTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translateToStatement elaborated with
      | .ok stmt =>
        let result := Ziku.IR.eval stmt
        match result with
        | .value p => .ok { output := Ziku.IR.truncate p.toString, isError := false }
        | .stuck s => .error s!"Stuck: {s}"
        | .error msg => .ok { output := s!"Error: {msg}", isError := true }
      | .error e => .ok { output := s!"Translation error: {e}", isError := true }
    | .error e => .ok { output := s!"Elaboration error: {e}", isError := true }
  | .error e => .error e

/-- Run an IR translation test (parse → elaborate → translate → show IR) -/
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

/-- Generate Scheme code (parse → elaborate → translate → compile to Scheme) -/
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

/-- Run a Scheme codegen test (compile to Scheme, compare generated code) -/
def runSchemeCodegenTest (input : String) : Except String TestOutput :=
  match generateScheme input with
  | .ok code => .ok { output := code, isError := false }
  | .error e => .ok { output := s!"Compilation error: {e}", isError := true }

/-- Run a Scheme test (compile to Scheme, run with chez, compare output) -/
def runSchemeTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  match generateScheme input with
  | .error e =>
    pure (TestResult.error s!"Compilation error: {e}")
  | .ok schemeCode =>
    -- Write scheme code to temp file
    let tempFile := s!"/tmp/ziku_test_{tc.name}.ss"
    IO.FS.writeFile tempFile schemeCode

    -- Run with scheme interpreter
    let result ← IO.Process.output {
      cmd := "scheme"
      args := #["--script", tempFile]
    }

    let actual := result.stdout.trim

    if result.exitCode != 0 then
      pure (TestResult.error s!"Scheme error: {result.stderr.trim}")
    else if golden.isEmpty then
      -- No golden file yet, create it
      IO.FS.writeFile tc.goldenPath actual
      IO.println s!"  Created golden file: {tc.goldenPath}"
      pure TestResult.pass
    else if actual == golden.trim then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trim actual)

/-- Run a consistency check: compare IR eval result with Scheme backend result -/
def runConsistencyTest (name : String) (inputPath : String) : IO TestResult := do
  let input ← IO.FS.readFile inputPath

  -- Get IR eval result
  let irResult := runIREvalTest input
  match irResult with
  | .error e =>
    pure (TestResult.error s!"IR eval parse error: {e}")
  | .ok irOutput =>
    -- Get Scheme result
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
        -- Compare outputs
        if irOutput.output.trim == schemeOutput then
          pure TestResult.pass
        else
          pure (TestResult.fail s!"IR eval: {irOutput.output.trim}" s!"Scheme: {schemeOutput}")

/-- Run a single test case -/
def runTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  let result := match tc.testType with
    | "infer" => runInferTest input
    | "ir-eval" => runIREvalTest input
    | "translate" => runTranslateTest input
    | "scheme-codegen" => runSchemeCodegenTest input
    | _ => runParserTest input

  match result with
  | .error e =>
    -- Parse error - do not create golden file, fail the test
    pure (TestResult.error s!"Parse error: {e}")
  | .ok testOutput =>
    -- Check if error expectation matches
    if tc.expectError && !testOutput.isError then
      pure (TestResult.error s!"Expected error but got success: {testOutput.output}")
    else if !tc.expectError && testOutput.isError then
      pure (TestResult.error s!"Expected success but got error: {testOutput.output}")
    else if golden.isEmpty then
      -- No golden file yet, create it
      IO.FS.writeFile tc.goldenPath testOutput.output
      IO.println s!"  Created golden file: {tc.goldenPath}"
      pure TestResult.pass
    else if testOutput.output.trim == golden.trim then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trim testOutput.output.trim)

/-- Run tests in a subdirectory (success or error) -/
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

    let result ← runTest tc
    match result with
    | .pass =>
      IO.println s!"  ✓ {baseName}"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"  ✗ {baseName}"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {baseName}: {msg}"
      failed := failed + 1

  pure (passed, failed)

/-- Run all tests in a category (both success and error subdirectories) -/
def runCategory (category : String) (testType : String) : IO (Nat × Nat) := do
  IO.println s!"\n=== {category} tests ==="

  IO.println s!"  --- success ---"
  let (successPassed, successFailed) ← runSubCategory category "success" testType false

  IO.println s!"  --- error ---"
  let (errorPassed, errorFailed) ← runSubCategory category "error" testType true

  pure (successPassed + errorPassed, successFailed + errorFailed)

/-- Run all scheme tests (uses ir-eval/success source files but compiles to Scheme) -/
def runSchemeCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"  -- Use ir-eval success source files
  let goldenDir := "tests/golden/scheme"   -- But scheme-specific golden files
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== scheme tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{sourceDir}/{baseName}.ziku"
      goldenPath := s!"{goldenDir}/{baseName}.golden"
      testType := "scheme"
      expectError := false
    }

    let result ← runSchemeTest tc
    match result with
    | .pass =>
      IO.println s!"  ✓ {baseName}"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"  ✗ {baseName}"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {baseName}: {msg}"
      failed := failed + 1

  pure (passed, failed)

/-- Run consistency tests: verify Scheme backend produces same results as IR eval -/
def runConsistencyCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== consistency tests (IR eval vs Scheme) ==="

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    let result ← runConsistencyTest baseName inputPath
    match result with
    | .pass =>
      IO.println s!"  ✓ {baseName}"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"  ✗ {baseName}"
      IO.println s!"    {expected}"
      IO.println s!"    {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {baseName}: {msg}"
      failed := failed + 1

  pure (passed, failed)

/-- Run translate tests: verify IR translation output -/
def runTranslateCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let goldenDir := "tests/golden/translate"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== translate tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{sourceDir}/{baseName}.ziku"
      goldenPath := s!"{goldenDir}/{baseName}.golden"
      testType := "translate"
      expectError := false
    }

    let result ← runTest tc
    match result with
    | .pass =>
      IO.println s!"  ✓ {baseName}"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"  ✗ {baseName}"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {baseName}: {msg}"
      failed := failed + 1

  pure (passed, failed)

/-- Run scheme-codegen tests: verify Scheme code generation output -/
def runSchemeCodegenCategory : IO (Nat × Nat) := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let goldenDir := "tests/golden/scheme-codegen"
  let tests ← discoverTests sourceDir

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== scheme-codegen tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{sourceDir}/{baseName}.ziku"
      goldenPath := s!"{goldenDir}/{baseName}.golden"
      testType := "scheme-codegen"
      expectError := false
    }

    let result ← runTest tc
    match result with
    | .pass =>
      IO.println s!"  ✓ {baseName}"
      passed := passed + 1
    | .fail expected actual =>
      IO.println s!"  ✗ {baseName}"
      IO.println s!"    Expected: {expected}"
      IO.println s!"    Actual:   {actual}"
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {baseName}: {msg}"
      failed := failed + 1

  pure (passed, failed)

def main : IO UInt32 := do
  IO.println "Running golden tests..."

  let (parserPassed, parserFailed) ← runCategory "parser" "parser"
  let (inferPassed, inferFailed) ← runCategory "infer" "infer"
  let (irEvalPassed, irEvalFailed) ← runCategory "ir-eval" "ir-eval"
  let (translatePassed, translateFailed) ← runTranslateCategory
  let (schemeCodegenPassed, schemeCodegenFailed) ← runSchemeCodegenCategory
  let (schemePassed, schemeFailed) ← runSchemeCategory
  let (consistencyPassed, consistencyFailed) ← runConsistencyCategory

  let totalPassed := parserPassed + inferPassed + irEvalPassed + translatePassed + schemeCodegenPassed + schemePassed + consistencyPassed
  let totalFailed := parserFailed + inferFailed + irEvalFailed + translateFailed + schemeCodegenFailed + schemeFailed + consistencyFailed

  IO.println s!"\n=== Summary ==="
  IO.println s!"Passed: {totalPassed}"
  IO.println s!"Failed: {totalFailed}"

  if totalFailed > 0 then
    pure 1
  else
    IO.println "All tests passed!"
    pure 0
