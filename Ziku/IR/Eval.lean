import Ziku.Syntax
import Ziku.IR.Syntax

namespace Ziku.IR

/-!
# Sequent Calculus IR Evaluator

Implements evaluation for the λμμ̃-calculus IR based on "Grokking the Sequent Calculus" (ICFP 2024).

## Reduction Rules

```
⟨μα.s | c̄⟩    ⊲  s[c̄/α]     (μ-reduction)
⟨v̄ | μ̃x.s⟩    ⊲  s[v̄/x]     (μ̃-reduction, v is value)
```

This evaluator uses an environment-based approach with closures to handle bindings efficiently.
It also uses substitution for "simple" values (like literals) to avoid unnecessary lookups.
-/

open Ziku (SourcePos Ident BinOp Builtin Lit)

mutual
  /-- Values stored in the environment.
  In an environment-based λμμ̃-evaluator, we store closures (code + environment). -/
  inductive EnvValue where
    | closure (p : Producer) (env : Env)
    | covarClosure (c : Consumer) (env : Env)
    deriving Repr

  /-- Evaluation environment mapping identifiers to values. -/
  inductive Env where
    | mk (bindings : List (Ident × EnvValue))
    deriving Repr
end

namespace Env
  def empty : Env := .mk []

  def lookup (env : Env) (x : Ident) : Option EnvValue :=
    match env with
    | .mk bindings => bindings.find? (·.1 == x) |>.map (·.2)

  def extend (env : Env) (x : Ident) (v : EnvValue) : Env :=
    match env with
    | .mk bindings => .mk ((x, v) :: bindings)

  def keys (env : Env) : List Ident :=
    match env with
    | .mk bindings => bindings.map (·.1)
end Env

-- Substitution: replace variable x with producer p in statement
mutual
partial def Producer.substVar (x : Ident) (p : Producer) : Producer → Producer
  | .var pos y => if y == x then p else .var pos y
  | .lit pos l => .lit pos l
  | .mu pos α s => .mu pos α (Statement.substVar x p s)
  | .cocase pos branches =>
    .cocase pos (branches.map fun (d, vars, s) =>
      if vars.contains x then (d, vars, s)
      else (d, vars, Statement.substVar x p s))
  | .record pos fields =>
    .record pos (fields.map fun (n, prod) => (n, Producer.substVar x p prod))
  | .fix pos y body =>
    if y == x then .fix pos y body
    else .fix pos y (Producer.substVar x p body)
  | .dataCon pos con args =>
    .dataCon pos con (args.map (Producer.substVar x p))

partial def Consumer.substVar (x : Ident) (p : Producer) : Consumer → Consumer
  | .covar pos α => .covar pos α
  | .muTilde pos y s =>
    if y == x then .muTilde pos y s
    else .muTilde pos y (Statement.substVar x p s)
  | .case pos branches =>
    .case pos (branches.map fun (k, vars, s) =>
      if vars.contains x then (k, vars, s)
      else (k, vars, Statement.substVar x p s))
  | .destructor pos d ps c =>
    .destructor pos d (ps.map (Producer.substVar x p)) (Consumer.substVar x p c)

partial def Statement.substVar (x : Ident) (p : Producer) : Statement → Statement
  | .cut pos prod cons => .cut pos (Producer.substVar x p prod) (Consumer.substVar x p cons)
  | .binOp pos op p1 p2 cons => .binOp pos op (Producer.substVar x p p1) (Producer.substVar x p p2) (Consumer.substVar x p cons)
  | .ifz pos cond s1 s2 => .ifz pos (Producer.substVar x p cond) (Statement.substVar x p s1) (Statement.substVar x p s2)
  | .call pos f ps cs => .call pos f (ps.map (Producer.substVar x p)) (cs.map (Consumer.substVar x p))
  | .builtin pos b ps cons => .builtin pos b (ps.map (Producer.substVar x p)) (Consumer.substVar x p cons)
end

-- Substitution: replace covariable α with consumer c in statement
mutual
partial def Producer.substCovar (α : Ident) (c : Consumer) : Producer → Producer
  | .var pos x => .var pos x
  | .lit pos l => .lit pos l
  | .mu pos β s =>
    if β == α then .mu pos β s
    else .mu pos β (Statement.substCovar α c s)
  | .cocase pos branches =>
    .cocase pos (branches.map fun (d, vars, s) =>
      if vars.contains α then (d, vars, s)
      else (d, vars, Statement.substCovar α c s))
  | .record pos fields =>
    .record pos (fields.map fun (n, prod) => (n, Producer.substCovar α c prod))
  | .fix pos y body => .fix pos y (Producer.substCovar α c body)
  | .dataCon pos con args => .dataCon pos con (args.map (Producer.substCovar α c))

partial def Consumer.substCovar (α : Ident) (c : Consumer) : Consumer → Consumer
  | .covar pos β => if β == α then c else .covar pos β
  | .muTilde pos x s => .muTilde pos x (Statement.substCovar α c s)
  | .case pos branches =>
    .case pos (branches.map fun (k, vars, s) =>
      if vars.contains α then (k, vars, s)
      else (k, vars, Statement.substCovar α c s))
  | .destructor pos d ps c' =>
    .destructor pos d (ps.map (Producer.substCovar α c)) (Consumer.substCovar α c c')

partial def Statement.substCovar (α : Ident) (c : Consumer) : Statement → Statement
  | .cut pos prod cons => .cut pos (Producer.substCovar α c prod) (Consumer.substCovar α c cons)
  | .binOp pos op p1 p2 cons => .binOp pos op (Producer.substCovar α c p1) (Producer.substCovar α c p2) (Consumer.substCovar α c cons)
  | .ifz pos cond s1 s2 => .ifz pos (Producer.substCovar α c cond) (Statement.substCovar α c s1) (Statement.substCovar α c s2)
  | .call pos f ps cs => .call pos f (ps.map (Producer.substCovar α c)) (cs.map (Consumer.substCovar α c))
  | .builtin pos b ps cons => .builtin pos b (ps.map (Producer.substCovar α c)) (Consumer.substCovar α c cons)
end

-- Evaluation errors (all variants include SourcePos for error reporting)
inductive EvalError where
  -- BinOp関連
  | divisionByZero : SourcePos → EvalError
  | binOpTypeMismatch : SourcePos → BinOp → Producer → Producer → EvalError
  | unsupportedBinOp : SourcePos → BinOp → Lit → Lit → EvalError
  -- Builtin関連
  | builtinArgTypeMismatch : SourcePos → Builtin → List Producer → EvalError
  | builtinUnresolvedVar : SourcePos → Ident → EvalError
  | stringIndexOutOfBounds : SourcePos → String → Int → EvalError
  | stringToIntFailed : SourcePos → String → EvalError
  | invalidUnicodeCodePoint : SourcePos → Int → EvalError
  | builtinWrongArity : SourcePos → Builtin → Nat → Nat → EvalError
  -- 評価関連
  | unboundVariable : SourcePos → Ident → EvalError
  | unboundCovariable : SourcePos → Ident → EvalError
  | patternMatchFailed : SourcePos → Producer → Consumer → EvalError
  | caseNotFound : SourcePos → String → List String → EvalError
  | destructorNotFound : SourcePos → String → List String → EvalError
  | callNotSupported : SourcePos → EvalError
  deriving Repr, Inhabited

-- Evaluation result
inductive EvalResult where
  | value : Producer → Env → EvalResult
  | stuck : Statement → Env → EvalResult
  | error : EvalError → EvalResult
  deriving Repr, Inhabited

-- Producers that are terminal values
partial def Producer.isTerminal : Producer → Bool
  | .var _ _ => false
  | .lit _ _ => true
  | .mu _ _ _ => false
  | .cocase _ _ => true
  | .record _ _ => true
  | .fix _ _ _ => false
  | .dataCon _ _ args => args.all Producer.isTerminal

def Producer.isValue := Producer.isTerminal

-- Simple values that don't need an environment
partial def Producer.isSimpleValue : Producer → Bool
  | .lit _ _ => true
  | .dataCon _ _ args => args.all Producer.isSimpleValue
  | _ => false

-- Simple consumers that don't need an environment
def Consumer.isSimpleConsumer : Consumer → Bool
  | .covar _ "halt" => true
  | _ => false

-- Helper: evaluate binary operation
def evalBinOp (pos : SourcePos) (op : BinOp) (p1 p2 : Producer) : Except EvalError Producer :=
  match p1, p2 with
  | .lit lpos (.int n1), .lit _ (.int n2) =>
    match op with
    | .add => .ok (.lit lpos (.int (n1 + n2)))
    | .sub => .ok (.lit lpos (.int (n1 - n2)))
    | .mul => .ok (.lit lpos (.int (n1 * n2)))
    | .div => if n2 == 0 then .error (.divisionByZero pos) else .ok (.lit lpos (.int (n1 / n2)))
    | .eq => .ok (.lit lpos (.bool (n1 == n2)))
    | .ne => .ok (.lit lpos (.bool (n1 != n2)))
    | .lt => .ok (.lit lpos (.bool (n1 < n2)))
    | .le => .ok (.lit lpos (.bool (n1 <= n2)))
    | .gt => .ok (.lit lpos (.bool (n1 > n2)))
    | .ge => .ok (.lit lpos (.bool (n1 >= n2)))
    | _ => .error (.unsupportedBinOp pos op (.int n1) (.int n2))
  | .lit lpos (.bool b1), .lit _ (.bool b2) =>
    match op with
    | .and => .ok (.lit lpos (.bool (b1 && b2)))
    | .or => .ok (.lit lpos (.bool (b1 || b2)))
    | _ => .error (.unsupportedBinOp pos op (.bool b1) (.bool b2))
  | .lit lpos (.string s1), .lit _ (.string s2) =>
    match op with
    | .concat => .ok (.lit lpos (.string (s1 ++ s2)))
    | .eq => .ok (.lit lpos (.bool (s1 == s2)))
    | .ne => .ok (.lit lpos (.bool (s1 != s2)))
    | _ => .error (.unsupportedBinOp pos op (.string s1) (.string s2))
  | .lit lpos (.char c1), .lit _ (.char c2) =>
    match op with
    | .eq => .ok (.lit lpos (.bool (c1 == c2)))
    | .ne => .ok (.lit lpos (.bool (c1 != c2)))
    | _ => .error (.unsupportedBinOp pos op (.char c1) (.char c2))
  | _, _ => .error (.binOpTypeMismatch pos op p1 p2)

-- Helper: evaluate built-in function
partial def evalBuiltin (pos : SourcePos) (b : Builtin) (args : List Producer) (env : Env) : Except EvalError Producer :=
  let rec resolve (p : Producer) (env : Env) : Except EvalError Producer :=
    match p with
    | .lit _ _ => .ok p
    | .var vpos x =>
      match env.lookup x with
      | some (.closure p' env') => resolve p' env'
      | _ => .error (.builtinUnresolvedVar vpos x)
    | _ => .error (.builtinArgTypeMismatch pos b [p])

  match b, args with
  | .strLen, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.string s)) => .ok (Producer.lit pos (Lit.int s.length))
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .strAt, [p1, p2] =>
    match resolve p1 env, resolve p2 env with
    | .ok (Producer.lit _ (Lit.string s)), .ok (Producer.lit _ (Lit.int i)) =>
      if i < 0 then .error (.stringIndexOutOfBounds pos s i) else
        match s.toList[i.toNat]? with
        | some c => .ok (Producer.lit pos (Lit.char c))
        | none => .error (.stringIndexOutOfBounds pos s i)
    | .error e, _ => .error e
    | _, .error e => .error e
    | _, _ => .error (.builtinArgTypeMismatch pos b args)
  | .strSub, [p1, p2, p3] =>
    match resolve p1 env, resolve p2 env, resolve p3 env with
    | .ok (Producer.lit _ (Lit.string s)), .ok (Producer.lit _ (Lit.int start)), .ok (Producer.lit _ (Lit.int len)) =>
      if start < 0 || len < 0 || start.toNat > s.length
      then .error (.stringIndexOutOfBounds pos s start)
      else .ok (Producer.lit pos (Lit.string (s.drop start.toNat |>.take len.toNat)))
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
    | _, _, _ => .error (.builtinArgTypeMismatch pos b args)
  | .strToInt, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.string s)) =>
      match s.toInt? with
      | some n => .ok (Producer.lit pos (Lit.int n))
      | none => .error (.stringToIntFailed pos s)
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .intToStr, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.int n)) => .ok (Producer.lit pos (Lit.string (toString n)))
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .runeToStr, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.char c)) => .ok (Producer.lit pos (Lit.string (String.singleton c)))
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .intToRune, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.int n)) =>
      if n < 0 || n > 0x10FFFF
      then .error (.invalidUnicodeCodePoint pos n)
      else .ok (Producer.lit pos (Lit.char (Char.ofNat n.toNat)))
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .runeToInt, [p] =>
    match resolve p env with
    | .ok (Producer.lit _ (Lit.char c)) => .ok (Producer.lit pos (Lit.int c.toNat))
    | .ok _ => .error (.builtinArgTypeMismatch pos b args)
    | .error e => .error e
  | .readLine, [_] => .error (.callNotSupported pos) -- IO not supported in interpreter
  | .println, [_] => .error (.callNotSupported pos) -- IO not supported in interpreter
  | _, _ => .error (.builtinWrongArity pos b args.length (match b with
    | .strLen | .strToInt | .intToStr | .runeToStr | .intToRune | .runeToInt | .println | .readLine => 1
    | .strAt => 2
    | .strSub => 3))

inductive State where
  | cut (p : Producer) (env_p : Env) (c : Consumer) (env_c : Env)
  | stmt (s : Statement) (env : Env)
  deriving Repr

-- Returns .ok none for halt, .ok (some state') for next step, .error e for errors
partial def stateStep : State → Except EvalError (Option State)
  | .stmt (.cut _ p c) env => .ok (some (.cut p env c env))
  | .stmt (.binOp pos op p1 p2 c) env =>
    if !p1.isValue then
      .ok (some (.cut p1 env (.muTilde p1.pos "_binop_l" (.binOp pos op (.var p1.pos "_binop_l") p2 c)) env))
    else if !p2.isValue then
      .ok (some (.cut p2 env (.muTilde p2.pos "_binop_r" (.binOp pos op p1 (.var p2.pos "_binop_r") c)) env))
    else
      match evalBinOp pos op p1 p2 with
      | .ok result => .ok (some (.cut result .empty c env))
      | .error e => .error e
  | .stmt (.ifz pos cond s1 s2) env =>
    if !cond.isValue then
      .ok (some (.cut cond env (.muTilde cond.pos "_ifz_cond" (.ifz pos (.var cond.pos "_ifz_cond") s1 s2)) env))
    else
      match cond with
      | .lit _ (.bool true) => .ok (some (.stmt s1 env))
      | .lit _ (.bool false) => .ok (some (.stmt s2 env))
      | .lit _ (.int n) => if n == 0 then .ok (some (.stmt s1 env)) else .ok (some (.stmt s2 env))
      | _ => .error (.patternMatchFailed pos cond (.muTilde cond.pos "_ifz" (.ifz pos cond s1 s2)))
  | .stmt (.builtin pos b ps c) env =>
    match evalBuiltin pos b ps env with
    | .ok result => .ok (some (.cut result .empty c env))
    | .error e => .error e
  | .stmt (.call pos _ _ _) _ => .error (.callNotSupported pos)
  | .cut p env_p c env_c =>
    match p, c with
    -- Producer-side reductions (highest priority)
    | .mu _ α s, _ =>
      if c.isSimpleConsumer then .ok (some (.stmt (s.substCovar α c) env_p))
      else .ok (some (.stmt s (env_p.extend α (.covarClosure c env_c))))
    | .fix _ x body, _ => .ok (some (.cut body (env_p.extend x (.closure p env_p)) c env_c))
    | .var vpos x, _ =>
      match env_p.lookup x with
      | some (.closure p' env') => .ok (some (.cut p' env' c env_c))
      | _ => .error (.unboundVariable vpos x)
    | .dataCon dPos conName args, _ =>
      if !p.isValue then
        match args.findIdx? (fun arg => !arg.isValue) with
        | some idx =>
          let arg := args[idx]!
          let freshName := s!"_dataCon_arg{idx}"
          let args' := args.set idx (.var arg.pos freshName)
          let env_cont := env_p.extend "_original_c" (.covarClosure c env_c)
          let s_cont := Statement.cut dPos (.dataCon dPos conName args') (Consumer.covar dPos "_original_c")
          .ok (some (.cut arg env_p (Consumer.muTilde arg.pos freshName s_cont) env_cont))
        | none => .error (.patternMatchFailed dPos p c)
      else
        -- p is a value, fall through to consumer-side matches
        match c with
        | .muTilde _ x s =>
          if p.isSimpleValue then .ok (some (.stmt (s.substVar x p) env_c))
          else .ok (some (.stmt s (env_c.extend x (.closure p env_p))))
        | .covar cpos α =>
          if α == "halt" then .ok none
          else match env_c.lookup α with
          | some (.covarClosure c' env') => .ok (some (.cut p env_p c' env'))
          | _ => .error (.unboundCovariable cpos α)
        | .case cpos branches =>
          let branchNames := branches.map (·.1)
          match branches.find? (fun (k, _, _) => k == conName) with
          | some (_, vars, body) =>
            if vars.length != args.length then .error (.patternMatchFailed dPos p c) else
              let env' := vars.zip args |>.foldl (fun e (x, v) => e.extend x (.closure v env_p)) env_c
              .ok (some (.stmt body env'))
          | none =>
            match branches.find? (fun (k, _, _) => k == "_wild") with
            | some (_, _, body) => .ok (some (.stmt body env_c))
            | none =>
              match branches.find? (fun (k, _, _) => k == "_var") with
              | some (_, [x], body) => .ok (some (.stmt body (env_c.extend x (.closure p env_p))))
              | _ => .error (.caseNotFound cpos conName branchNames)
        | .destructor dpos _ _ _ => .error (.patternMatchFailed dpos p c)
    -- Consumer-side reductions (lower priority)
    | _, .muTilde mpos x s =>
      if p.isSimpleValue then .ok (some (.stmt (s.substVar x p) env_c))
      else if p.isValue then .ok (some (.stmt s (env_c.extend x (.closure p env_p))))
      else .error (.patternMatchFailed mpos p c)
    | _, .covar cpos α =>
      if α == "halt" then .ok none
      else match env_c.lookup α with
      | some (.covarClosure c' env') => .ok (some (.cut p env_p c' env'))
      | _ => .error (.unboundCovariable cpos α)
    -- Destructor application
    | .cocase _ branches, .destructor dpos d args cont =>
      let branchNames := branches.map (·.1)
      match branches.find? (fun (d', _, _) => d' == d) with
      | some (_, vars, body) =>
        if vars.length != args.length + 1 then .error (.patternMatchFailed dpos p c) else
          let contCovar := vars.getLast!
          let argVars := vars.dropLast
          let env' := argVars.zip args |>.foldl (fun e (x, p') => e.extend x (.closure p' env_c)) env_p
          let env'' := env'.extend contCovar (.covarClosure cont env_c)
          .ok (some (.stmt body env''))
      | none => .error (.destructorNotFound dpos d branchNames)
    -- Record field access
    | .record _ fields, .destructor dpos fieldName [] cont =>
      let fieldNames := fields.map (·.1)
      match fields.find? (fun (f, _) => f == fieldName) with
      | some (_, value) => .ok (some (.cut value env_p cont env_c))
      | none => .error (.destructorNotFound dpos fieldName fieldNames)
    -- Literal + case
    | .lit _ l, .case cpos branches =>
      let litConName := match l with
        | .int n => s!"_lit_int_{n}" | .bool b => s!"_lit_bool_{b}" | .string s => s!"_lit_string_{s}"
        | .char c => s!"_lit_rune_{c.val}" | .float f => s!"_lit_float_{f}" | .unit => "_lit_unit"
      let branchNames := branches.map (·.1)
      match branches.find? (fun (k, _, _) => k == litConName) with
      | some (_, _, body) => .ok (some (.stmt body env_c))
      | none =>
        match branches.find? (fun (k, _, _) => k == "_wild") with
        | some (_, _, body) => .ok (some (.stmt body env_c))
        | none =>
          match branches.find? (fun (k, _, _) => k == "_var") with
          | some (_, [x], body) => .ok (some (.stmt body (env_c.extend x (.closure p env_p))))
          | _ => .error (.caseNotFound cpos litConName branchNames)
    | _, _ => .error (.patternMatchFailed p.pos p c)

partial def evalWithFuel (fuel : Nat) (state : State) : EvalResult :=
  if fuel == 0 then
    match state with | .stmt s env => .stuck s env | .cut p env_p c _ => .stuck (.cut p.pos p c) env_p
  else
    match stateStep state with
    | .ok (some state') => evalWithFuel (fuel - 1) state'
    | .ok none =>
      -- Normal termination (halt)
      match state with
      | .cut p env_p (.covar _ "halt") _ =>
        match p with
        | .var vpos x =>
          match env_p.lookup x with
          | some (.closure p' env') => evalWithFuel fuel (.cut p' env' (.covar p.pos "halt") .empty)
          | _ => .error (.unboundVariable vpos x)
        | _ => if p.isValue then .value p env_p else .stuck (.cut p.pos p (.covar p.pos "halt")) env_p
      | .stmt s env => .stuck s env
      | .cut p env_p c _ => .stuck (.cut p.pos p c) env_p
    | .error e => .error e

def defaultFuel : Nat := 100000
def eval (s : Statement) : EvalResult := evalWithFuel defaultFuel (.stmt s .empty)

def truncate (s : String) (maxLen : Nat := 80) : String :=
  if s.length <= maxLen then s else if maxLen < 3 then "..." else s.take (maxLen - 3) ++ "..."

def EvalError.toString : EvalError → String
  | .divisionByZero pos => s!"Division by zero at {pos}"
  | .binOpTypeMismatch pos op p1 p2 => s!"Binary operation type mismatch at {pos}: {op} on {truncate p1.toString} and {truncate p2.toString}"
  | .unsupportedBinOp pos op l1 l2 => s!"Unsupported binary operation at {pos}: {op} on {l1} and {l2}"
  | .builtinArgTypeMismatch pos b args => s!"Builtin argument type mismatch at {pos}: {b} with {args.length} args"
  | .builtinUnresolvedVar pos x => s!"Builtin could not resolve variable at {pos}: {x}"
  | .stringIndexOutOfBounds pos s i => s!"String index out of bounds at {pos}: index {i} in string of length {s.length}"
  | .stringToIntFailed pos s => s!"Failed to convert string to int at {pos}: \"{truncate s}\""
  | .invalidUnicodeCodePoint pos n => s!"Invalid Unicode code point at {pos}: {n}"
  | .builtinWrongArity pos b got expected => s!"Builtin {b} expects {expected} args, got {got} at {pos}"
  | .unboundVariable pos x => s!"Unbound variable at {pos}: {x}"
  | .unboundCovariable pos α => s!"Unbound covariable at {pos}: {α}"
  | .patternMatchFailed pos p c => s!"Pattern match failed at {pos}: {truncate p.toString} against {truncate c.toString}"
  | .caseNotFound pos conName branches => s!"Case not found at {pos}: constructor '{conName}' not in branches {branches}"
  | .destructorNotFound pos d branches => s!"Destructor not found at {pos}: '{d}' not in {branches}"
  | .callNotSupported pos => s!"Call statements are not supported in evaluation at {pos}"

instance : ToString EvalError := ⟨EvalError.toString⟩

def EvalResult.toString : EvalResult → String
  | .value p _ => s!"Value: {truncate p.toString}"
  | .stuck s _ => s!"Stuck: {s}"
  | .error e => s!"Error: {e}"

instance : ToString EvalResult := ⟨EvalResult.toString⟩

end Ziku.IR
