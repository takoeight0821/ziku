import Ziku.Parser
import Ziku.Eval
import Ziku.Infer

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

/-- Run an eval test -/
def runEvalTest (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.eval {} expr with
    | some v => .ok (toString v)
    | none => .ok "Evaluation error"
  | .error e => .error e

/-- Run a type inference test -/
def runInferTest (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.runInfer expr with
    | .ok (ty, _) => .ok (toString ty)
    | .error e => .ok (toString e)
  | .error e => .error e

/-- Run a single test case -/
def runTest (tc : TestCase) : IO TestResult := do
  let input ← IO.FS.readFile tc.inputPath
  let golden ← readFileOrEmpty tc.goldenPath

  let result := match tc.testType with
    | "eval" => runEvalTest input
    | "infer" => runInferTest input
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
   "match", "letRec", "logical", "codata", "multiParamLambda", "hash",
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
   "cutSimple", "cutExpression"]

/-- List of eval test cases -/
def evalTests : List String :=
  ["arithmetic", "let", "if"]

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
   "unbound_variable", "type_mismatch"]

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

def main : IO UInt32 := do
  IO.println "Running golden tests..."

  let (parserPassed, parserFailed) ← runCategory "parser" parserTests "parser"
  let (evalPassed, evalFailed) ← runCategory "eval" evalTests "eval"
  let (inferPassed, inferFailed) ← runCategory "infer" inferTests "infer"

  let totalPassed := parserPassed + evalPassed + inferPassed
  let totalFailed := parserFailed + evalFailed + inferFailed

  IO.println s!"\n=== Summary ==="
  IO.println s!"Passed: {totalPassed}"
  IO.println s!"Failed: {totalFailed}"

  if totalFailed > 0 then
    pure 1
  else
    IO.println "All tests passed!"
    pure 0
