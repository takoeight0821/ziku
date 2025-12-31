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
  testType : String  -- "parser" or "eval"

/-- Read file contents, return empty string if file doesn't exist -/
def readFileOrEmpty (path : String) : IO String := do
  try
    IO.FS.readFile path
  catch _ =>
    pure ""

/-- Run a parser test -/
def runParserTest (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr => .ok (toString expr)
  | .error e => .error e


/-- Run a type inference test -/
def runInferTest (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.runInfer expr with
    | .ok (ty, _) => .ok (toString ty)
    | .error e => .ok (toString e)
  | .error e => .error e

/-- Run an IR evaluation test (parse → elaborate → translate → IR eval) -/
def runIREvalTest (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer =>
        let dummyPos : Ziku.SourcePos := { line := 0, col := 0 }
        let stmt := Ziku.IR.Statement.cut dummyPos producer (Ziku.IR.Consumer.covar dummyPos "halt")
        let result := Ziku.IR.eval stmt
        match result with
        | .value p => .ok (Ziku.IR.truncate p.toString)
        | .stuck s => .error s!"Stuck: {s}"
        | .error msg => .ok s!"Error: {msg}"
      | .error e => .ok s!"Translation error: {e}"
    | .error e => .ok s!"Elaboration error: {e}"
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
        if irOutput.trim == schemeOutput then
          pure TestResult.pass
        else
          pure (TestResult.fail s!"IR eval: {irOutput.trim}" s!"Scheme: {schemeOutput}")

/-- Run a single test case -/
def runTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  let result := match tc.testType with
    | "infer" => runInferTest input
    | "ir-eval" => runIREvalTest input
    | _ => runParserTest input

  match result with
  | .error e =>
    -- Parse error - do not create golden file, fail the test
    pure (TestResult.error s!"Parse error: {e}")
  | .ok actual =>
    if golden.isEmpty then
      -- No golden file yet, create it
      IO.FS.writeFile tc.goldenPath actual
      IO.println s!"  Created golden file: {tc.goldenPath}"
      pure TestResult.pass
    else if actual.trim == golden.trim then
      pure TestResult.pass
    else
      pure (TestResult.fail golden.trim actual.trim)

/-- List of parser test cases -/
def parserTests : List String :=
  ["arithmetic", "precedence", "comparison", "let", "lambda",
   "if", "nested_let", "application", "unary", "record", "field_access",
   "match", "letRec", "logical", "codata", "multiParamLambda",
   "codataMultiline", "stringLiteral", "charLiteral", "floatLiteral",
   "boolLiteral", "unitLiteral", "pipeOperator", "pipeChain", "concatOperator",
   "concatStrings", "notEqual", "lessEqual", "greaterEqual", "lessThan",
   "greaterThan", "equality", "codataSingleClause", "codataNestedAccessor",
   "codataCallable", "codataCallableNested", "codataMixedAccessors",
   "codataTripleNested", "codataNewlineSeparated", "codataConsumerSyntax",
   "applicationParens", "applicationComma", "applicationMixed",
   "applicationMethod", "recordSingleField", "recordNested", "recordMultiline",
   "recordComplexValues", "recordEmpty", "matchWildcard", "matchLiteral",
  "matchNestedPattern", "matchConstructorNoArgs", "matchSingleCase",
   "typeAnnotation", "typeAnnotationLambda",
   "muAbstraction", "muAbstractionAscii", "muAbstractionSimple", "muUnicode",
   "fieldAccessChain", "fieldAccessDeep", "lambdaNested", "lambdaComplexBody",
   "lambdaThreeParams", "letWithAnnotation", "letRecWithAnnotation",
   "negativeNumber", "parenthesesOnly", "parenthesesNested",
   "expressionMixedOperators", "divisionByZero", "variableSnakeCase",
   "variableCamelCase", "operatorNoSpaces", "operatorExtraSpaces",
   "cutSimple", "cutExpression", "hash", "labelSimple", "labelNested", "gotoSimple", "labelGoto",
   "app_field_precedence", "labelInLet", "nestedCodata", "lambdaInRecord"]


/-- List of type inference test cases -/
def inferTests : List String :=
  ["literal_int", "literal_bool", "literal_string", "literal_unit",
   "binary_arithmetic", "binary_comparison", "binary_logical",
   "unary_neg", "unary_not",
   "lambda_simple", "lambda_multi_param", "lambda_nested",
   "application_simple", "application_curried",
   "let_simple", "let_polymorphic",
   "let_rec_factorial", "let_rec_mutual",
   "if_then_else", "type_annotation",
   "match_var_pattern", "match_literal_pattern", "match_bool_scrutinee", "match_annotated_pattern",
   "record_simple", "record_field_access", "record_let_binding", "record_nested",
   "pipe_operator",
   "codata_field", "codata_callable", "codata_multi_param", "codata_nested",
   "label_simple", "label_goto", "label_nested", "label_function", "label_let",
   "label_early_return", "label_match",
   "unbound_variable", "type_mismatch",
   "if_branch_mismatch", "function_arg_mismatch", "too_many_args",
   "codata_field_type", "higher_order_function", "compose_functions"]

/-- List of IR evaluation test cases -/
def irEvalTests : List String :=
  ["literal", "binop_add", "binop_comparison", "if_simple", "if_comparison",
   "let_simple", "let_nested", "let_computation", "let_chain",
   "label_simple", "label_goto", "label_goto_nested",
   "label_immediate_exit", "label_conditional_exit", "label_early_exit", "label_nested_goto",
   "lambda_square", "lambda_nonvalue_args", "lambda_higher_order", "lambda_curried", "lambda_compose",
   "codata_simple", "codata_chain", "letrec_simple",
   "letrec_codata_simple", "letrec_codata_tail", "letrec_codata_lambda", "letrec_codata_lambda_tail",
   "let_record_access", "letrec_codata_minimal",
   "fib_codata", "record_nested", "codata_closure", "sum_to_n",
   "church_zero", "label_loop", "codata_counter", "letrec_mutual_record"]

/-- List of Scheme backend test cases -/
def schemeTests : List String :=
  ["literal", "binop_add", "binop_comparison", "if_simple", "if_comparison",
   "let_simple", "let_nested", "let_computation", "let_chain",
   "label_simple", "label_goto", "label_goto_nested",
   "label_immediate_exit", "label_conditional_exit", "label_early_exit", "label_nested_goto",
   "lambda_square", "lambda_curried", "lambda_compose", "lambda_nonvalue_args", "lambda_higher_order",
   "codata_simple", "codata_chain", "letrec_simple",
   "letrec_codata_simple", "letrec_codata_tail", "letrec_codata_lambda", "letrec_codata_lambda_tail",
   "letrec_codata_minimal",
   "let_record_access", "record_nested", "codata_closure",
   "sum_to_n", "label_loop",
   "fib_codata", "codata_counter", "church_zero", "letrec_mutual_record"]

/-- Run all tests in a category -/
def runCategory (category : String) (tests : List String) (testType : String) : IO (Nat × Nat) := do
  let dir := s!"tests/golden/{category}"

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== {category} tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{dir}/{baseName}.ziku"
      goldenPath := s!"{dir}/{baseName}.golden"
      testType := testType
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

/-- Run all scheme tests (uses ir-eval source files but compiles to Scheme) -/
def runSchemeCategory (tests : List String) : IO (Nat × Nat) := do
  let sourceDir := "tests/golden/ir-eval"  -- Use ir-eval source files
  let goldenDir := "tests/golden/scheme"   -- But scheme-specific golden files

  let mut passed := 0
  let mut failed := 0

  IO.println s!"\n=== scheme tests ==="

  for baseName in tests do
    let tc : TestCase := {
      name := baseName
      inputPath := s!"{sourceDir}/{baseName}.ziku"
      goldenPath := s!"{goldenDir}/{baseName}.golden"
      testType := "scheme"
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
def runConsistencyCategory (tests : List String) : IO (Nat × Nat) := do
  let sourceDir := "tests/golden/ir-eval"

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

def main : IO UInt32 := do
  IO.println "Running golden tests..."

  let (parserPassed, parserFailed) ← runCategory "parser" parserTests "parser"
  let (inferPassed, inferFailed) ← runCategory "infer" inferTests "infer"
  let (irEvalPassed, irEvalFailed) ← runCategory "ir-eval" irEvalTests "ir-eval"
  let (schemePassed, schemeFailed) ← runSchemeCategory schemeTests
  let (consistencyPassed, consistencyFailed) ← runConsistencyCategory schemeTests

  let totalPassed := parserPassed + inferPassed + irEvalPassed + schemePassed + consistencyPassed
  let totalFailed := parserFailed + inferFailed + irEvalFailed + schemeFailed + consistencyFailed

  IO.println s!"\n=== Summary ==="
  IO.println s!"Passed: {totalPassed}"
  IO.println s!"Failed: {totalFailed}"

  if totalFailed > 0 then
    pure 1
  else
    IO.println "All tests passed!"
    pure 0
