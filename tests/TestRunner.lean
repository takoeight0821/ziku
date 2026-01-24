/- Master test runner that executes all test suites:
- Truncate tests (unit tests for string truncation)
- Golden tests (integration tests for parser, type inference, IR evaluation)
- Big-Step unit tests (incremental verification of the new interpreter)
- Consistency tests (Small-step vs Big-step vs Scheme)
-/

import Ziku.Parser
import Ziku.Infer
import Ziku.Elaborate
import Ziku.Translate
import Ziku.IR.Eval
import Ziku.IR.BigStepEval
import Ziku.Backend.Scheme
import tests.BigStepEvalTest

set_option linter.missingDocs false

-- ============================================================================
-- Truncate Tests (from TruncateTest.lean)
-- ============================================================================

structure TruncateTestCase where
  name : String
  input : String
  maxLen : Nat
  expected : String

def runTruncateTest (tc : TruncateTestCase) : IO Bool :=
  do
    let result := Ziku.IR.truncate tc.input tc.maxLen
    let passed := result == tc.expected
    IO.println s!"  Testing {tc.name}... {if passed then "✓" else "✗"}"
    if !passed then
      IO.println s!"    Expected: {repr tc.expected}"
      IO.println s!"    Actual:   {repr result}"
    return passed

def truncateTests : List TruncateTestCase :=
  [
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

def runTruncateTests : IO (Nat × Nat) :=
  do
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
-- Golden Tests Infrastructure
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

def readFileOrEmpty (path : String) : IO String :=
  try
    IO.FS.readFile path
  catch _ =>
    pure ""

def discoverTests (dir : System.FilePath) : IO (List String) :=
  try
    let entries ← dir.readDir
    let zikuFiles := entries.filterMap fun entry =>
      let name := entry.fileName
      if name.endsWith ".ziku" then
        some (name.dropEnd 5).toString
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
  match Ziku.parseProgram input.trimAscii.toString with
  | .ok decls => .ok { output := toString decls, isError := false }
  | .error progErr =>
    match Ziku.parseExprString input.trimAscii.toString with 
    | .ok expr => .ok { output := toString expr, isError := false }
    | .error exprErr =>
      let trimmed := input.trimAscii.toString
      if trimmed.startsWith "data" || trimmed.startsWith "codata" || trimmed.startsWith "def" ||
         trimmed.startsWith "module" || trimmed.startsWith "import" || trimmed.startsWith "infix" ||
         trimmed.startsWith "@" then
        .ok { output := progErr, isError := true }
      else
        .ok { output := exprErr, isError := true }

def runInferTest (input : String) : Except String TestOutput :=
  match Ziku.parseExprString input.trimAscii.toString with 
  | .ok expr =>
    match Ziku.runInfer expr with
    | .ok (ty, _) => .ok { output := toString ty, isError := false }
    | .error e => .ok { output := toString e, isError := true }
  | .error e => .error e

def runIREvalTest (input : String) : IO (Except String TestOutput) :=
  do
    match Ziku.parseExprString input.trimAscii.toString with 
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
  match Ziku.parseExprString input.trimAscii.toString with 
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer => .ok { output := producer.toString, isError := false }
      | .error e => .ok { output := s!"Translation error: {e}", isError := true }
    | .error e => .ok { output := s!"Elaboration error: {e}", isError := true }
  | .error e => .error e

def generateScheme (input : String) : Except String String :=
  match Ziku.parseExprString input.trimAscii.toString with 
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

def runSchemeTest (tc : TestCase) : IO TestResult :=
  do
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

      let actual := result.stdout.trimAscii.toString

      if result.exitCode != 0 then
        pure (TestResult.error s!"Scheme error: {result.stderr.trimAscii.toString}")
      else if golden.isEmpty then
        IO.FS.writeFile tc.goldenPath actual
        IO.println s!"  Created golden file: {tc.goldenPath}"
        pure TestResult.pass
      else if actual == golden.trimAscii.toString then
        pure TestResult.pass
      else
        pure (TestResult.fail golden.trimAscii.toString actual)

-- ============================================================================
-- Evaluator Full Execution Helpers
-- ============================================================================

def runIREvalFull (input : String) : IO (Except String TestOutput) := do

  match Ziku.parseExprString input.trimAscii.toString with

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



def runBigStepEvalFull (input : String) : IO (Except String TestOutput) := do

  match Ziku.parseExprString input.trimAscii.toString with

  | .ok expr =>

    match Ziku.elaborateAll expr with

    | .ok elaborated =>

      match Ziku.Translate.translateToStatement elaborated with

      | .ok stmt =>

        let result ← Ziku.IR.BigStepEval.eval stmt

        match result with

        | .value v => return .ok { output := toString v, isError := false }

        | .error msg => return .ok { output := s!"Error: {msg}", isError := true }

      | .error e => return .ok { output := s!"Translation error: {e}", isError := true }

    | .error e => return .ok { output := s!"Elaboration error: {e}", isError := true }

  | .error e => return .error e



def runBigStepEvalTest (input : String) : IO (Except String TestOutput) := do

  match ← runBigStepEvalFull input with

  | .ok output => return .ok { output with output := Ziku.IR.truncate output.output }

  | .error e => return .error e



-- ============================================================================

-- Consistency Tests

-- ============================================================================



def runConsistencyTest (name : String) (inputPath : String) : IO TestResult :=
  do
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
          pure (TestResult.error s!"Scheme error: {result.stderr.trimAscii.toString}")
        else
          let schemeOutput := result.stdout.trimAscii.toString
          if irOutput.output.trimAscii.toString == schemeOutput then
            pure TestResult.pass
          else
            let irDisplay := Ziku.IR.truncate irOutput.output.trimAscii.toString
            pure (TestResult.fail s!"IR eval: {irDisplay}" s!"Scheme: {Ziku.IR.truncate schemeOutput}")

def runBigStepConsistencyTest (_name : String) (inputPath : String) : IO TestResult :=
  do
    let input ← IO.FS.readFile inputPath

    let smallStepResult ← runIREvalFull input
    match smallStepResult with
    | .error e =>
      pure (TestResult.error s!"Small-step parse error: {e}")
    | .ok smallStepOutput =>
      let bigStepResult ← runBigStepEvalFull input
      match bigStepResult with
      | .error e =>
        pure (TestResult.error s!"Big-step parse error: {e}")
      | .ok bigStepOutput =>
        if smallStepOutput.output.trimAscii.toString == bigStepOutput.output.trimAscii.toString then
          pure TestResult.pass
        else
          let smallDisplay := Ziku.IR.truncate smallStepOutput.output.trimAscii.toString
          let bigDisplay := Ziku.IR.truncate bigStepOutput.output.trimAscii.toString
          pure (TestResult.fail s!"Small-step: {smallDisplay}" s!"Big-step: {bigDisplay}")

-- ============================================================================
-- Generic Test Execution
-- ============================================================================

def runTest (tc : TestCase) : IO TestResult :=
  do

  let input ← IO.FS.readFile tc.inputPath

  let golden ← readFileOrEmpty tc.goldenPath



    let result : Except String TestOutput ← match tc.testType with



      | "infer" => pure (runInferTest input)



      | "ir-eval" => runIREvalTest input



      | "ir-eval-big-step" => runBigStepEvalTest input



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
      else if testOutput.output.trimAscii.toString == golden.trimAscii.toString then
        pure TestResult.pass
      else
        pure (TestResult.fail golden.trimAscii.toString testOutput.output.trimAscii.toString)

def runSubCategory (category : String) (subdir : String) (testType : String) (expectError : Bool) : IO (Nat × Nat) :=
  do
    let dir := System.FilePath.mk s!"tests/golden/{category}/{subdir}"
    let tests ← discoverTests dir

    let mut passed := 0
    let mut failed := 0

    for baseName in tests do
      let tc : TestCase :=
        { name := baseName
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

def runCategory (category : String) (testType : String) : IO (Nat × Nat) :=
  do
    IO.println s!"\n=== {category} tests ==="

    IO.println s!"  --- success ---"
    let (successPassed, successFailed) ← runSubCategory category "success" testType false

    IO.println s!"  --- error ---"
    let (errorPassed, errorFailed) ← runSubCategory category "error" testType true

    pure (successPassed + errorPassed, successFailed + errorFailed)

def runSchemeOnlyCategory : IO (Nat × Nat) :=
  do
    let dir := System.FilePath.mk "tests/golden/scheme/success"
    let tests ← discoverTests dir

    let mut passed := 0
    let mut failed := 0

    IO.println s!"\n=== scheme-only tests ==="

    for baseName in tests do
      let tc : TestCase :=
        { name := baseName
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

def runConsistencyCategory : IO (Nat × Nat) :=
  do
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

def runBigStepConsistencyCategory : IO (Nat × Nat) :=
  do
    let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
    let tests ← discoverTests sourceDir

    let mut passed := 0
    let mut failed := 0

    IO.println "\n=== consistency tests (Small-step vs Big-step) ==="

    for baseName in tests do
      if baseName.endsWith ".slow" then continue
      let inputPath := s!"{sourceDir}/{baseName}.ziku"
      IO.print s!"  Testing {baseName}... "
      (← IO.getStdout).flush
      let result ← runBigStepConsistencyTest baseName inputPath
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

def runEmitTranslateCategory : IO (Nat × Nat) :=
  do
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

def runEmitSchemeCategory : IO (Nat × Nat) :=
  do
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

def runIOTest (_baseName : String) (inputPath : String) (goldenPath : String) (stdinInputPath : Option String) : IO TestResult :=
  do
    let golden ← readFileOrEmpty goldenPath
    
    let args := #["exe", "ziku", "--eval", inputPath]
    
    let stdinContent ← match stdinInputPath with
      | some p => IO.FS.readFile p
      | none => pure ""

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

    let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated

    let exitCode ← child.wait
    let actualStdOut ← IO.ofExcept stdout.get
    let actualStdErr ← IO.ofExcept stderr.get
    
    let actual := actualStdOut.trimAscii.toString
    
    if exitCode != 0 then
      pure (TestResult.error s!"Runtime error: {actualStdErr.trimAscii.toString}")
    else if golden.isEmpty then
      IO.FS.writeFile goldenPath actual
      IO.println s!"  Created golden file: {goldenPath}"
      pure TestResult.pass
    else if actual == golden.trimAscii.toString then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trimAscii.toString actual)

def runIOTestCategory : IO (Nat × Nat) :=
  do
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



-- All available test categories
def allCategories : List String :=
  ["truncate", "big-step", "parser", "infer", "ir-eval", "ir-eval-big-step",
   "emit-translate", "emit-scheme", "scheme-only", "consistency",
   "big-step-consistency", "io"]

-- Run a single category and return (passed, failed)
def runCategoryByName (cat : String) : IO (Nat × Nat) := do
  match cat with
  | "truncate" => runTruncateTests
  | "big-step" => BigStepEvalTest.runTests
  | "parser" => runCategory "parser" "parser"
  | "infer" => runCategory "infer" "infer"
  | "ir-eval" => runCategory "ir-eval" "ir-eval"
  | "ir-eval-big-step" => runCategory "ir-eval" "ir-eval-big-step"
  | "emit-translate" => runEmitTranslateCategory
  | "emit-scheme" => runEmitSchemeCategory
  | "scheme-only" => runSchemeOnlyCategory
  | "consistency" => runConsistencyCategory
  | "big-step-consistency" => runBigStepConsistencyCategory
  | "io" => runIOTestCategory
  | _ => do
    IO.println s!"Unknown category: {cat}"
    IO.println s!"Available categories: {allCategories}"
    pure (0, 0)

-- Write test results to a JSON file
def writeJsonReport (reportPath : String) (passed failed : Nat) (categories : List String) : IO Unit := do
  let json := s!"\{\"passed\": {passed}, \"failed\": {failed}, \"categories\": [{", ".intercalate (categories.map (fun c => s!"\"{c}\""))}]}"
  IO.FS.writeFile reportPath json

-- Parse command line arguments
-- Returns (categories to run, optional report path)
def parseArgs (args : List String) : List String × Option String :=
  let rec go (args : List String) (cats : List String) (report : Option String) : List String × Option String :=
    match args with
    | [] => (cats.reverse, report)
    | "--report" :: path :: rest => go rest cats (some path)
    | "--help" :: _ => (["--help"], none)
    | cat :: rest => go rest (cat :: cats) report
  go args [] none

def main (args : List String) : IO UInt32 := do
  let (categories, reportPath) := parseArgs args

  -- Handle --help
  if categories == ["--help"] then
    IO.println "Usage: lake test [-- [OPTIONS] [CATEGORIES...]]"
    IO.println ""
    IO.println "OPTIONS:"
    IO.println "  --report PATH    Write JSON results to PATH"
    IO.println "  --help           Show this help"
    IO.println ""
    IO.println "CATEGORIES:"
    for cat in allCategories do
      IO.println s!"  {cat}"
    IO.println ""
    IO.println "EXAMPLES:"
    IO.println "  lake test                        # Run all tests"
    IO.println "  lake test -- parser              # Run parser tests only"
    IO.println "  lake test -- parser infer        # Run parser and infer tests"
    IO.println "  lake test -- --report out.json   # Run all tests with JSON report"
    return 0

  -- Determine which categories to run
  let categoriesToRun := if categories.isEmpty then allCategories else categories

  IO.println s!"Running tests: {categoriesToRun}"

  -- Run each category and collect results
  let mut totalPassed := 0
  let mut totalFailed := 0
  let mut results : List (String × Nat × Nat) := []

  for cat in categoriesToRun do
    let (passed, failed) ← runCategoryByName cat
    totalPassed := totalPassed + passed
    totalFailed := totalFailed + failed
    results := results ++ [(cat, passed, failed)]

  -- Print summary
  IO.println s!"\n=== Summary ==="
  for (cat, passed, failed) in results do
    IO.println s!"{cat}: {passed} passed, {failed} failed"
  IO.println s!"Total: {totalPassed} passed, {totalFailed} failed"

  -- Write JSON report if requested
  if let some path := reportPath then
    writeJsonReport path totalPassed totalFailed categoriesToRun
    IO.println s!"Report written to: {path}"

  if totalFailed > 0 then
    return 1
  else
    IO.println "All tests passed!"
    return 0
