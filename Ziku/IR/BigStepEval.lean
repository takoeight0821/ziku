import Ziku.Syntax
import Ziku.IR.Syntax

namespace Ziku.IR.BigStepEval

/-!
# Big-Step Interpreter for λμμ̃-calculus IR

A fast big-step interpreter optimized for execution speed.

## Design Choices
- **Direct recursive evaluation**: No state machine overhead
- **Separate Value type**: Eliminates repeated `isValue` checks
- **No fuel**: Uses `partial def` for maximum speed
-/

open Ziku (SourcePos Ident BinOp Builtin Lit synthesizedPos)

/-! ## Runtime Value Types -/

mutual
  /-- Runtime values produced by evaluation. -/
  inductive Value where
    | lit : Lit → Value
    | closure : Producer → Env → Value          -- cocase body with captured env
    | record : List (String × Value) → Value
    | dataCon : String → List Value → Value

  /-- Environment entries. -/
  inductive EnvValue where
    | val : Value → EnvValue
    | covarClosure : Consumer → Env → EnvValue
    | continuation : EnvValue -- Marker for a jump target (continuation)

  /-- Evaluation environment. -/
  inductive Env where
    | mk : List (Ident × EnvValue) → Env
end

namespace Env
  def empty : Env := .mk []

  def lookup (env : Env) (x : Ident) : Option EnvValue :=
    match env with
    | .mk bindings => bindings.find? (·.1 == x) |>.map (·.2)

  def insert (env : Env) (x : Ident) (v : EnvValue) : Env :=
    match env with
    | .mk bindings => .mk ((x, v) :: bindings)

  def insertVal (env : Env) (x : Ident) (v : Value) : Env :=
    env.insert x (.val v)

  def insertCovar (env : Env) (α : Ident) (c : Consumer) (env' : Env) : Env :=
    env.insert α (.covarClosure c env')
    
  def insertContinuation (env : Env) (α : Ident) : Env :=
    env.insert α .continuation
end Env

/-! ## Evaluation Errors -/

inductive EvalError where
  | divisionByZero : SourcePos → EvalError
  | binOpTypeMismatch : SourcePos → BinOp → String → String → EvalError
  | unsupportedBinOp : SourcePos → BinOp → Lit → Lit → EvalError
  | builtinArgTypeMismatch : SourcePos → Builtin → Nat → EvalError
  | stringIndexOutOfBounds : SourcePos → String → Int → EvalError
  | stringToIntFailed : SourcePos → String → EvalError
  | invalidUnicodeCodePoint : SourcePos → Int → EvalError
  | builtinWrongArity : SourcePos → Builtin → Nat → Nat → EvalError
  | unboundVariable : SourcePos → Ident → EvalError
  | unboundCovariable : SourcePos → Ident → EvalError
  | patternMatchFailed : SourcePos → String → EvalError
  | caseNotFound : SourcePos → String → List String → EvalError
  | destructorNotFound : SourcePos → String → List String → EvalError
  | callNotSupported : SourcePos → EvalError
  deriving Repr, Inhabited

def truncate (s : String) (maxLen : Nat := 80) : String :=
  if s.length <= maxLen then s else if maxLen < 3 then "..." else (s.take (maxLen - 3)).toString ++ "..."

def EvalError.toString : EvalError → String
  | .divisionByZero pos => s!"Division by zero at {pos}"
  | .binOpTypeMismatch pos op s1 s2 => s!"Binary operation type mismatch at {pos}: {op} on {s1} and {s2}"
  | .unsupportedBinOp pos op l1 l2 => s!"Unsupported binary operation at {pos}: {op} on {l1} and {l2}"
  | .builtinArgTypeMismatch pos b n => s!"Builtin argument type mismatch at {pos}: {b} with {n} args"
  | .stringIndexOutOfBounds pos s i => s!"String index out of bounds at {pos}: index {i} in string of length {s.length}"
  | .stringToIntFailed pos s => s!"Failed to convert string to int at {pos}: \"{truncate s 20}\""
  | .invalidUnicodeCodePoint pos n => s!"Invalid Unicode code point at {pos}: {n}"
  | .builtinWrongArity pos b got expected => s!"Builtin {b} expects {expected} args, got {got} at {pos}"
  | .unboundVariable pos x => s!"Unbound variable at {pos}: {x}"
  | .unboundCovariable pos α => s!"Unbound covariable at {pos}: {α}"
  | .patternMatchFailed pos msg => s!"Pattern match failed at {pos}: {msg}"
  | .caseNotFound pos conName branches => s!"Case not found at {pos}: constructor '{conName}' not in branches {branches}"
  | .destructorNotFound pos d branches => s!"Destructor not found at {pos}: '{d}' not in {branches}"
  | .callNotSupported pos => s!"Call statements are not supported in evaluation at {pos}"

instance : ToString EvalError := ⟨EvalError.toString⟩

/-! ## Evaluation Result -/

-- Internal result type that supports non-local jumps
inductive Result where
  | ok : Value → Result
  | error : EvalError → Result
  | jump : Ident → Value → Result
  deriving Inhabited

inductive EvalResult where
  | value : Value → EvalResult
  | error : EvalError → EvalResult
  deriving Inhabited

/-! ## Value Conversion -/

partial def Value.toProducer : Value → Producer
  | .lit l => .lit synthesizedPos l
  | .dataCon con args => .dataCon synthesizedPos con (args.map Value.toProducer)
  | .record fields => .record synthesizedPos (fields.map fun (n, v) => (n, v.toProducer))
  | .closure p _ => p

instance : ToString Value where
  toString v := s!"{v.toProducer}"

def EvalResult.toString : EvalResult → String
  | .value v => s!"{v}"
  | .error e => s!"Error: {e}"

instance : ToString EvalResult := ⟨EvalResult.toString⟩

/-! ## Binary Operation Evaluation -/

def evalBinOp (pos : SourcePos) (op : BinOp) (v1 v2 : Value) : Except EvalError Value :=
  match v1, v2 with
  | .lit (.int n1), .lit (.int n2) =>
    match op with
    | .add => .ok (.lit (.int (n1 + n2)))
    | .sub => .ok (.lit (.int (n1 - n2)))
    | .mul => .ok (.lit (.int (n1 * n2)))
    | .div => if n2 == 0 then .error (.divisionByZero pos) else .ok (.lit (.int (n1 / n2)))
    | .eq => .ok (.lit (.bool (n1 == n2)))
    | .ne => .ok (.lit (.bool (n1 != n2)))
    | .lt => .ok (.lit (.bool (n1 < n2)))
    | .le => .ok (.lit (.bool (n1 <= n2)))
    | .gt => .ok (.lit (.bool (n1 > n2)))
    | .ge => .ok (.lit (.bool (n1 >= n2)))
    | _ => .error (.unsupportedBinOp pos op (.int n1) (.int n2))
  | .lit (.bool b1), .lit (.bool b2) =>
    match op with
    | .and => .ok (.lit (.bool (b1 && b2)))
    | .or => .ok (.lit (.bool (b1 || b2)))
    | _ => .error (.unsupportedBinOp pos op (.bool b1) (.bool b2))
  | .lit (.string s1), .lit (.string s2) =>
    match op with
    | .concat => .ok (.lit (.string (s1 ++ s2)))
    | .eq => .ok (.lit (.bool (s1 == s2)))
    | .ne => .ok (.lit (.bool (s1 != s2)))
    | _ => .error (.unsupportedBinOp pos op (.string s1) (.string s2))
  | .lit (.char c1), .lit (.char c2) =>
    match op with
    | .eq => .ok (.lit (.bool (c1 == c2)))
    | .ne => .ok (.lit (.bool (c1 != c2)))
    | _ => .error (.unsupportedBinOp pos op (.char c1) (.char c2))
  | _, _ => .error (.binOpTypeMismatch pos op (toString v1) (toString v2))

/-! ## Builtin Evaluation -/

def evalBuiltin (pos : SourcePos) (b : Builtin) (args : List Value) : IO (Except EvalError Value) :=
  match b, args with
  | .strLen, [.lit (.string s)] =>
    return .ok (.lit (.int s.length))
  | .strAt, [.lit (.string s), .lit (.int i)] =>
    return if i < 0 then .error (.stringIndexOutOfBounds pos s i) else
      match s.toList[i.toNat]? with
      | some c => .ok (.lit (.char c))
      | none => .error (.stringIndexOutOfBounds pos s i)
  | .strSub, [.lit (.string s), .lit (.int start), .lit (.int len)] =>
    return if start < 0 || len < 0 || start.toNat > s.length
      then .error (.stringIndexOutOfBounds pos s start)
      else .ok (.lit (.string (s.drop start.toNat |>.take len.toNat |>.toString)))
  | .strToInt, [.lit (.string s)] =>
    return match s.toInt? with
    | some n => .ok (.lit (.int n))
    | none => .error (.stringToIntFailed pos s)
  | .intToStr, [.lit (.int n)] =>
    return .ok (.lit (.string (toString n)))
  | .runeToStr, [.lit (.char c)] =>
    return .ok (.lit (.string (String.singleton c)))
  | .intToRune, [.lit (.int n)] =>
    return if n < 0 || n > 0x10FFFF
      then .error (.invalidUnicodeCodePoint pos n)
      else .ok (.lit (.char (Char.ofNat n.toNat)))
  | .runeToInt, [.lit (.char c)] =>
    return .ok (.lit (.int c.toNat))
  | .readLine, [.lit (.string prompt)] => do
    IO.print prompt
    let input ← IO.getStdin >>= (·.getLine)
    return .ok (.lit (.string input.trimAsciiEnd.toString))
  | .println, [.lit (.string s)] => do
    IO.println s
    return .ok (.lit .unit)
  | _, _ =>
    let expected := match b with
      | .strLen | .strToInt | .intToStr | .runeToStr | .intToRune | .runeToInt | .println | .readLine => 1
      | .strAt => 2
      | .strSub => 3
    return if args.length != expected
      then .error (.builtinWrongArity pos b args.length expected)
      else .error (.builtinArgTypeMismatch pos b args.length)

/-! ## Core Big-Step Evaluator -/

mutual
  /-- Evaluate a producer to a value. -/
  partial def evalProducer (p : Producer) (env : Env) : IO Result := do
    match p with
    | .var pos x =>
      match env.lookup x with
      | some (.val v) => return .ok v
      | some (.covarClosure _ _) => return .error (.unboundVariable pos x)
      | some .continuation => return .error (.unboundVariable pos x) -- Shouldn't happen for var
      | none => return .error (.unboundVariable pos x)
    | .lit _ l => return .ok (.lit l)
    | .mu _ α s =>
      -- μα.s: evaluate s with α bound as continuation
      -- If s returns jump to α, catch it and return value.
      -- If s returns other jump, propagate it.
      -- If s returns value, it fell through (e.g. to halt), return it.
      let res ← evalStatement s (env.insertContinuation α)
      match res with
      | .jump β v => if α == β then return .ok v else return .jump β v
      | _ => return res
    | .cocase _ _ =>
      -- Cocase is a value (closure)
      return .ok (.closure p env)
    | .record _ fields => do
      -- Evaluate all fields
      let mut result : List (String × Value) := []
      for (name, prod) in fields do
        match ← evalProducer prod env with
        | .ok v => result := result ++ [(name, v)]
        | .jump β v => return .jump β v
        | .error e => return .error e
      return .ok (.record result)
    | .fix pos x body => do
      -- Create recursive binding: extend env with x bound to fix itself
      let recEnv := env.insert x (.val (.closure (.fix pos x body) env))
      evalProducer body recEnv
    | .dataCon _ con args => do
      -- Evaluate all arguments
      let mut result : List Value := []
      for arg in args do
        match ← evalProducer arg env with
        | .ok v => result := result ++ [v]
        | .jump β v => return .jump β v
        | .error e => return .error e
      return .ok (.dataCon con result)

  /-- Apply a consumer to a value. -/
  partial def applyConsumer (v : Value) (c : Consumer) (env : Env) : IO Result := do
    match c with
    | .covar pos α =>
      if α == "halt" then return .ok v
      else match env.lookup α with
        | some (.covarClosure c' env') => applyConsumer v c' env'
        | some .continuation => return .jump α v
        | _ => return .error (.unboundCovariable pos α)
    | .muTilde _ x s =>
      -- Bind value to x and evaluate statement
      evalStatement s (env.insertVal x v)
    | .case pos branches =>
      -- Match constructor
      match v with
      | .dataCon conName args =>
        let branchNames := branches.map (·.1)
        match branches.find? (fun (k, _, _) => k == conName) with
        | some (_, vars, body) =>
          if vars.length != args.length then
            return .error (.patternMatchFailed pos s!"arity mismatch: {conName}")
          else
            -- Bind arguments to variables
            let env' := vars.zip args |>.foldl (fun e (x, v) => e.insertVal x v) env
            evalStatement body env'
        | none =>
          -- Try wildcard
          match branches.find? (fun (k, _, _) => k == "_wild") with
          | some (_, _, body) => evalStatement body env
          | none =>
            -- Try variable pattern
            match branches.find? (fun (k, _, _) => k == "_var") with
            | some (_, [x], body) => evalStatement body (env.insertVal x v)
            | _ => return .error (.caseNotFound pos conName branchNames)
      | .lit l =>
        -- Literal case matching
        let litConName := match l with
          | .int n => s!"_lit_int_{n}"
          | .bool b => s!"_lit_bool_{b}"
          | .string s => s!"_lit_string_{s}"
          | .char c => s!"_lit_rune_{c.val}"
          | .float f => s!"_lit_float_{f}"
          | .unit => "_lit_unit"
        let branchNames := branches.map (·.1)
        match branches.find? (fun (k, _, _) => k == litConName) with
        | some (_, _, body) => evalStatement body env
        | none =>
          match branches.find? (fun (k, _, _) => k == "_wild") with
          | some (_, _, body) => evalStatement body env
          | none =>
            match branches.find? (fun (k, _, _) => k == "_var") with
            | some (_, [x], body) => evalStatement body (env.insertVal x v)
            | _ => return .error (.caseNotFound pos litConName branchNames)
      | _ => return .error (.patternMatchFailed pos "cannot case on closure/record")
    | .destructor pos d args cont =>
      match v with
      | .closure (.fix _ x body) fixEnv =>
        -- Unfold the fix: evaluate body with x bound to the fix itself
        let recEnv := fixEnv.insert x (.val v)
        match ← evalProducer body recEnv with
        | .ok unfolded => applyConsumer unfolded c env
        | .jump β v => return .jump β v
        | .error e => return .error e
      | .closure (.cocase _ branches) closureEnv =>
        -- Look up destructor branch
        let branchNames := branches.map (·.1)
        match branches.find? (fun (d', _, _) => d' == d) with
        | some (_, vars, body) =>
          if vars.length != args.length + 1 then
            return .error (.patternMatchFailed pos s!"destructor arity mismatch: {d}")
          else
            -- Evaluate arguments
            let mut argVals : List Value := []
            for arg in args do
              match ← evalProducer arg env with
              | .ok argVal => argVals := argVals ++ [argVal]
              | .jump β v => return .jump β v
              | .error e => return .error e
            -- Bind arguments and continuation
            let contCovar := vars.getLast!
            let argVars := vars.dropLast
            let env' := argVars.zip argVals |>.foldl (fun e (x, v) => e.insertVal x v) closureEnv
            let env'' := env'.insertCovar contCovar cont env
            evalStatement body env''
        | none => return .error (.destructorNotFound pos d branchNames)
      | .record fields =>
        -- Record field access
        if !args.isEmpty then
          return .error (.patternMatchFailed pos "record field access takes no arguments")
        else
          let fieldNames := fields.map (·.1)
          match fields.find? (fun (f, _) => f == d) with
          | some (_, fieldVal) => applyConsumer fieldVal cont env
          | none => return .error (.destructorNotFound pos d fieldNames)
      | _ => return .error (.patternMatchFailed pos "cannot destruct non-closure/non-record")

  /-- Evaluate a statement to a value. -/
  partial def evalStatement (s : Statement) (env : Env) : IO Result := do
    match s with
    | .cut _ p c => do
      match ← evalProducer p env with
      | .ok v => applyConsumer v c env
      | .jump β v => return .jump β v
      | .error e => return .error e
    | .binOp pos op p1 p2 c => do
      match ← evalProducer p1 env with
      | .error e => return .error e
      | .jump β v => return .jump β v
      | .ok v1 =>
        match ← evalProducer p2 env with
        | .error e => return .error e
        | .jump β v => return .jump β v
        | .ok v2 =>
          match evalBinOp pos op v1 v2 with
          | .error e => return .error e
          | .ok result => applyConsumer result c env
    | .ifz pos cond s1 s2 => do
      match ← evalProducer cond env with
      | .error e => return .error e
      | .jump β v => return .jump β v
      | .ok v =>
        match v with
        | .lit (.bool true) => evalStatement s1 env
        | .lit (.bool false) => evalStatement s2 env
        | .lit (.int n) => if n == 0 then evalStatement s1 env else evalStatement s2 env
        | _ => return .error (.patternMatchFailed pos "ifz expects bool or int")
    | .builtin pos b ps c => do
      -- Evaluate all arguments
      let mut args : List Value := []
      for p in ps do
        match ← evalProducer p env with
        | .ok v => args := args ++ [v]
        | .jump β v => return .jump β v
        | .error e => return .error e
      match ← evalBuiltin pos b args with
      | .ok result => applyConsumer result c env
      | .error e => return .error e
    | .call pos _ _ _ => return .error (.callNotSupported pos)
end

/-! ## Entry Point -/

def eval (s : Statement) : IO EvalResult := do
  match ← evalStatement s .empty with
  | .ok v => return .value v
  | .jump _ v => return .value v -- Top-level jump (e.g. to halt) treated as value
  | .error e => return .error e

end Ziku.IR.BigStepEval
