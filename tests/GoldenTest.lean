import Ziku.Parser
import Ziku.Infer
import Ziku.Elaborate
import Ziku.Translate
import Ziku.IR.Eval

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
   "cutSimple", "cutExpression", "hash", "labelSimple", "labelNested", "gotoSimple", "labelGoto"]


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
   "unbound_variable", "type_mismatch"]

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
   "fib_codata"]

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
  let (inferPassed, inferFailed) ← runCategory "infer" inferTests "infer"
  let (irEvalPassed, irEvalFailed) ← runCategory "ir-eval" irEvalTests "ir-eval"

  let totalPassed := parserPassed + inferPassed + irEvalPassed
  let totalFailed := parserFailed + inferFailed + irEvalFailed

  IO.println s!"\n=== Summary ==="
  IO.println s!"Passed: {totalPassed}"
  IO.println s!"Failed: {totalFailed}"

  if totalFailed > 0 then
    pure 1
  else
    IO.println "All tests passed!"
    pure 0
