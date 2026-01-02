import Ziku.Syntax
import Ziku.IR.Syntax

namespace Ziku.Backend.Scheme

open Ziku (Ident BinOp Lit)
open Ziku.IR (Producer Consumer Statement)

/-!
# Scheme Code Generator

Translates Ziku's sequent calculus IR (λμμ̃-calculus) to Chez Scheme code.

## Translation Strategy

The λμμ̃-calculus maps naturally to continuation-passing style:

| IR Construct | Scheme Translation |
|--------------|-------------------|
| `var x` | `x` |
| `lit n` | `n` / `#t` / `#f` / `"str"` |
| `μα.s` | `(lambda (α) <s>)` |
| `μ̃x.s` | `(lambda (x) <s>)` |
| `covar α` | `α` |
| `⟨p \| c⟩` | `(<c> <p>)` |
| `cocase {ap(x;α)=>s}` | `(lambda (x) (lambda (α) <s>))` |
| `destructor ap(p;c)` | Creates a consumer that applies function |
| `record {f=v,...}` | `(list (cons 'f <v>) ...)` |
| `fix x.p` | `(letrec ((x (lambda () <p>))) (x))` with delayed evaluation |
| `binOp op p1 p2 c` | `(<c> (<op> <p1> <p2>))` |
| `ifz p s1 s2` | `(if <p> <s1> <s2>)` |
-/

-- Mangle identifier to be valid Scheme identifier
def mangleIdent (id : Ident) : String :=
  -- Replace problematic characters
  id.replace "-" "_dash_"
    |>.replace "'" "_prime_"
    |>.replace "?" "_q_"
    |>.replace "!" "_bang_"
    |>.replace "#" "_hash_"
    |>.replace "α" "alpha"
    |>.replace "β" "beta"
    |>.replace "γ" "gamma"

-- Translate literal to Scheme
def translateLit : Lit → String
  | .int n => toString n
  | .float f => toString f
  | .string s => s!"\"{s}\""
  | .char c => s!"#\\{c}"
  | .bool true => "#t"
  | .bool false => "#f"
  | .unit => "'()"

-- Translate binary operator to Scheme
def translateBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "quotient"
  | .eq => "="
  | .ne => "(lambda (a b) (not (= a b)))"
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .and => "(lambda (a b) (and a b))"
  | .or => "(lambda (a b) (or a b))"
  | .concat => "string-append"
  | .pipe => "(lambda (x f) (f x))"

-- Check if binary operator needs wrapping (is not a simple procedure)
def binOpNeedsWrap : BinOp → Bool
  | .ne => true
  | .and => true
  | .or => true
  | .pipe => true
  | _ => false

-- State monad for generating unique variable names
abbrev GenM := StateM Nat

-- Generate a fresh unique variable name
-- Uses prefix "%" which is invalid in Ziku identifiers but valid in Scheme
def freshVar (pfx : String := "g") : GenM String := do
  let n ← get
  set (n + 1)
  pure s!"%{pfx}{n}"

-- Forward declarations for mutual recursion
mutual

partial def translateProducerM : Producer → GenM String
  | .var _ x => pure (mangleIdent x)
  | .lit _ l => pure (translateLit l)
  | .mu _ α s => do
    -- μα.s is a computation that produces a value when given a continuation
    -- We tag it with 'ziku-thunk to distinguish from regular lambdas (cocase)
    let alphaName := mangleIdent α
    let sCode ← translateStatementM s
    pure s!"(vector 'ziku-thunk (lambda ({alphaName}) {sCode}))"
  | .cocase _ branches => do
    -- cocase { D(x̄; α) ⇒ s, ... }
    -- Translate to nested lambdas for each destructor
    -- For function application: cocase { ap(x; α) ⇒ s } becomes (lambda (x) (lambda (α) s))
    match branches with
    | [(d, vars, body)] =>
      -- Single branch case (most common for functions)
      if d == "ap" then
        -- Function: λx.body where vars = [x, α]
        match vars with
        | [x, α] =>
          let xName := mangleIdent x
          let alphaName := mangleIdent α
          let bodyCode ← translateStatementM body
          pure s!"(lambda ({xName}) (lambda ({alphaName}) {bodyCode}))"
        | _ =>
          -- Multiple args: λx₁...λxₙ.body
          let (argVars, contVar) := (vars.dropLast, vars.getLast!)
          let argNames := argVars.map mangleIdent
          let contName := mangleIdent contVar
          let bodyCode ← translateStatementM body
          let lambdas := argNames.foldr (fun arg acc => s!"(lambda ({arg}) {acc})")
            s!"(lambda ({contName}) {bodyCode})"
          pure lambdas
      else
        -- Record-like destructor
        let (argVars, contVar) := (vars.dropLast, vars.getLast!)
        let argNames := argVars.map mangleIdent
        let contName := mangleIdent contVar
        let allArgs := String.intercalate " " (argNames ++ [contName])
        let bodyCode ← translateStatementM body
        pure s!"(lambda ({allArgs}) {bodyCode})"
    | _ =>
      -- Multiple branches: create a dispatch table
      -- This is for codata with multiple destructors
      let branchCodes ← branches.mapM fun (d, vars, body) => do
        let dName := mangleIdent d
        let (argVars, contVar) := (vars.dropLast, vars.getLast!)
        let argNames := argVars.map mangleIdent
        let contName := mangleIdent contVar
        let argsStr := String.intercalate " " argNames
        let bodyCode ← translateStatementM body
        pure s!"(({dName} {argsStr} {contName}) {bodyCode})"
      pure s!"(case-lambda {String.intercalate " " branchCodes})"
  | .record _ fields => do
    -- Record as association list: ((f1 . v1) (f2 . v2) ...)
    let fieldCodes ← fields.mapM fun (name, value) => do
      let valueCode ← translateProducerM value
      pure s!"(cons '{mangleIdent name} {valueCode})"
    pure s!"(list {String.intercalate " " fieldCodes})"
  | .fix _ x body => do
    -- Fixpoint using letrec
    -- For cocase (lambdas), letrec works directly
    -- For records, we use a tagged dispatch function to distinguish from CPS functions
    let xName := mangleIdent x
    match body with
    | .cocase _ _ =>
      -- Lambda-like: can use letrec directly since it's already lazy
      let bodyCode ← translateProducerM body
      pure s!"(letrec (({xName} {bodyCode})) {xName})"
    | .record _ fields =>
      -- Record with potential recursive reference: use tagged dispatch function
      -- The vector #(ziku-dispatch <func>) distinguishes this from CPS functions
      let fieldCases ← fields.mapM fun (name, value) => do
        let valueCode ← translateProducerM value
        pure s!"(({mangleIdent name}) {valueCode})"
      pure s!"(letrec (({xName} (vector 'ziku-dispatch (lambda (%field) (case %field {String.intercalate " " fieldCases}))))) {xName})"
    | _ =>
      -- Other: simple letrec
      let bodyCode ← translateProducerM body
      pure s!"(letrec (({xName} {bodyCode})) {xName})"
  | .dataCon _ con args => do
    -- Data constructor as tagged list: (list 'K v1 v2 ...)
    let conName := mangleIdent con
    let argCodes ← args.mapM translateProducerM
    let argsStr := String.intercalate " " argCodes
    if args.isEmpty then
      pure s!"(list '{conName})"
    else
      pure s!"(list '{conName} {argsStr})"

partial def translateConsumerM : Consumer → GenM String
  | .covar _ α => pure (mangleIdent α)
  | .muTilde _ x s => do
    let xName := mangleIdent x
    let sCode ← translateStatementM s
    pure s!"(lambda ({xName}) {sCode})"
  | .case _ branches => do
    -- case { K(x̄) ⇒ s, ... }
    -- Pattern matching on tagged data (list 'K v1 v2 ...)
    -- Generate: (lambda (%v) (let ((%tag (car %v))) (cond ((eq? %tag 'K1) (let ((x1 (list-ref %v 1)) ...) body1)) ...)))
    let branchCodes ← branches.mapM fun (k, vars, body) => do
      let kName := mangleIdent k
      let varNames := vars.map mangleIdent
      -- Generate let bindings for extracting values from the list
      let indices := List.range varNames.length
      let bindings := indices.zip varNames |>.map fun (i, name) =>
        s!"({name} (list-ref %v {i + 1}))"
      let bindingsStr := String.intercalate " " bindings
      let bodyCode ← translateStatementM body
      if vars.isEmpty then
        pure s!"((eq? %tag '{kName}) {bodyCode})"
      else
        pure s!"((eq? %tag '{kName}) (let ({bindingsStr}) {bodyCode}))"
    pure s!"(lambda (%v) (let ((%tag (car %v))) (cond {String.intercalate " " branchCodes})))"
  | .destructor _ d args cont => do
    -- D(p̄; c) - apply destructor with arguments and continuation
    -- For "ap" (function application): ((fn arg) cont)
    --   A function is (lambda (x) (lambda (k) body)), so:
    --   Apply to arg: (fn arg) => (lambda (k) body[arg/x])
    --   Apply to cont: ((fn arg) cont) => body[arg/x, cont/k]
    -- For field access: get field value, then apply cont
    -- NOTE: We use freshVar to generate unique variable names to avoid capture
    if d == "ap" then
      -- Function application
      -- A function is (lambda (x) (lambda (k) body))
      -- (fn arg) => (lambda (k) body[arg/x])
      -- ((fn arg) cont) => body[arg/x, cont/k]
      -- IMPORTANT: If arg is a μ (translated as thunk), we need to evaluate it first
      --   by calling it with a continuation that does the actual application
      match args with
      | [arg] =>
        let contCode ← translateConsumerM cont
        match arg with
        | .mu _ α s =>
          -- arg is μα.s: evaluate it first, then apply
          -- Note: we inline the μ body here instead of going through the thunk wrapper
          let fnVar ← freshVar "fn"
          let vVar ← freshVar "v"
          let alphaName := mangleIdent α
          let sCode ← translateStatementM s
          pure s!"(lambda ({fnVar}) ((lambda ({alphaName}) {sCode}) (lambda ({vVar}) (({fnVar} {vVar}) {contCode}))))"
        | _ =>
          -- arg is a value (might be a thunk if it's a variable holding a μ)
          let fnVar ← freshVar "fn"
          let argCode ← translateProducerM arg
          -- Check at runtime if arg is a thunk and unwrap it
          pure s!"(lambda ({fnVar}) (let ((%arg {argCode})) (if (and (vector? %arg) (eq? (vector-ref %arg 0) 'ziku-thunk)) ((vector-ref %arg 1) (lambda (%v) (({fnVar} %v) {contCode}))) (({fnVar} %arg) {contCode}))))"
      | _ =>
        -- Multiple arguments: for now, assume all are values
        -- TODO: handle thunks in multiple args
        let fnVar ← freshVar "fn"
        let argCodes ← args.mapM translateProducerM
        let contCode ← translateConsumerM cont
        let applied := argCodes.foldl (fun acc arg => s!"({acc} {arg})") fnVar
        pure s!"(lambda ({fnVar}) ({applied} {contCode}))"
    else
      -- Field access
      -- Record can be either:
      -- 1. Association list: ((f1 . v1) (f2 . v2) ...) - use assq
      -- 2. Tagged dispatch function (from fix): #(ziku-dispatch <func>)
      -- Field values can be:
      -- - Tagged thunk #(ziku-thunk <func>): call with continuation
      -- - Regular value (including lambdas from cocase): pass to continuation
      let dName := mangleIdent d
      let contCode ← translateConsumerM cont
      if args.isEmpty then
        -- Simple field access: get field value
        -- If it's a thunk, unwrap and call with continuation
        -- Otherwise pass to continuation
        pure s!"(lambda (%rec) (let* ((%is-dispatch (and (vector? %rec) (eq? (vector-ref %rec 0) 'ziku-dispatch))) (%v (cond (%is-dispatch ((vector-ref %rec 1) '{dName})) ((procedure? %rec) (%rec '{dName})) (else (cdr (assq '{dName} %rec)))))) (if (and (vector? %v) (eq? (vector-ref %v 0) 'ziku-thunk)) ((vector-ref %v 1) {contCode}) ({contCode} %v))))"
      else
        -- Field with arguments (method call): get field, apply to args, pass to continuation
        let argCodes ← args.mapM translateProducerM
        let argsCode := String.intercalate " " argCodes
        pure s!"(lambda (%rec) (let* ((%is-dispatch (and (vector? %rec) (eq? (vector-ref %rec 0) 'ziku-dispatch))) (%v (cond (%is-dispatch ((vector-ref %rec 1) '{dName})) ((procedure? %rec) (%rec '{dName})) (else (cdr (assq '{dName} %rec)))))) ({contCode} (%v {argsCode}))))"

partial def translateStatementM : Statement → GenM String
  | .cut _ p c => do
    -- ⟨p | c⟩ - apply cut (interaction between producer and consumer)
    -- Key reduction rules:
    -- ⟨μα.s | c⟩ ⊲ s[c/α]  (μ-reduction)
    -- ⟨v | μ̃x.s⟩ ⊲ s[v/x]  (μ̃-reduction)
    match p with
    | .mu _ α s =>
      -- μ-reduction: substitute c for α in s
      -- Note: we don't wrap in vector here since we're doing compile-time substitution
      let alphaName := mangleIdent α
      let cCode ← translateConsumerM c
      let sCode ← translateStatementM s
      pure s!"(let (({alphaName} {cCode})) {sCode})"
    | _ =>
      match c with
      | .muTilde _ x s =>
        -- μ̃-reduction: substitute p for x in s
        let xName := mangleIdent x
        let pCode ← translateProducerM p
        let sCode ← translateStatementM s
        pure s!"(let (({xName} {pCode})) {sCode})"
      | _ =>
        -- General case: (c p)
        -- If p is translated as a thunk #(ziku-thunk <func>), unwrap and call with c
        let pCode ← translateProducerM p
        let cCode ← translateConsumerM c
        pure s!"(let ((%p {pCode})) (if (and (vector? %p) (eq? (vector-ref %p 0) 'ziku-thunk)) ((vector-ref %p 1) {cCode}) ({cCode} %p)))"
  | .binOp _ op p1 p2 c => do
    -- ⊙(p₁, p₂; c) → (c (op p1 p2))
    -- If p1 or p2 is a μ, we need to evaluate it first
    let cCode ← translateConsumerM c
    let opCode := translateBinOp op
    let opCall := if binOpNeedsWrap op then s!"(({opCode})" else s!"({opCode}"
    match p1, p2 with
    | .mu _ α1 s1, .mu _ α2 s2 =>
      -- Both operands need evaluation
      let a1 := mangleIdent α1
      let a2 := mangleIdent α2
      let s1Code ← translateStatementM s1
      let s2Code ← translateStatementM s2
      pure s!"((lambda ({a1}) {s1Code}) (lambda (%v1) ((lambda ({a2}) {s2Code}) (lambda (%v2) ({cCode} {opCall} %v1 %v2))))))"
    | .mu _ α1 s1, _ =>
      -- Only p1 needs evaluation
      let a1 := mangleIdent α1
      let s1Code ← translateStatementM s1
      let p2Code ← translateProducerM p2
      pure s!"((lambda ({a1}) {s1Code}) (lambda (%v1) ({cCode} {opCall} %v1 {p2Code}))))"
    | _, .mu _ α2 s2 =>
      -- Only p2 needs evaluation
      let p1Code ← translateProducerM p1
      let a2 := mangleIdent α2
      let s2Code ← translateStatementM s2
      pure s!"((lambda ({a2}) {s2Code}) (lambda (%v2) ({cCode} {opCall} {p1Code} %v2))))"
    | _, _ =>
      -- Both are values
      let p1Code ← translateProducerM p1
      let p2Code ← translateProducerM p2
      pure s!"({cCode} {opCall} {p1Code} {p2Code}))"
  | .ifz _ cond s1 s2 => do
    -- ifz(p, s₁, s₂) → (if p s1 s2)
    -- If cond is a μ-abstraction, we need to evaluate it first to get the boolean value
    let s1Code ← translateStatementM s1
    let s2Code ← translateStatementM s2
    match cond with
    | .mu _ α s =>
      -- cond is μα.s: evaluate it and use result as condition
      let alphaName := mangleIdent α
      let sCode ← translateStatementM s
      pure s!"((lambda ({alphaName}) {sCode}) (lambda (%cond) (if %cond {s1Code} {s2Code})))"
    | _ =>
      let condCode ← translateProducerM cond
      pure s!"(if {condCode} {s1Code} {s2Code})"
  | .call _ f args conts => do
    -- f(p̄; c̄) → (f arg1 arg2 ... cont1 cont2 ...)
    let fName := mangleIdent f
    let argCodes ← args.mapM translateProducerM
    let contCodes ← conts.mapM translateConsumerM
    let allArgs := String.intercalate " " (argCodes ++ contCodes)
    pure s!"({fName} {allArgs})"

end

-- Non-monadic wrappers for external use
def translateProducer (p : Producer) : String :=
  (translateProducerM p).run' 0

def translateConsumer (c : Consumer) : String :=
  (translateConsumerM c).run' 0

def translateStatement (s : Statement) : String :=
  (translateStatementM s).run' 0

-- Scheme runtime support (inlined in output)
def schemeRuntime : String :=
";; Ziku Runtime Support
;; Generated by Ziku Scheme Backend

;; Pretty print result
(define (ziku-print-result v)
  (cond
    ((boolean? v) (display (if v \"true\" \"false\")))
    ((null? v) (display \"()\"))
    ((pair? v)
     (if (and (pair? (car v)) (symbol? (caar v)))
         ;; Record
         (begin
           (display \"{ \")
           (let loop ((fields v))
             (unless (null? fields)
               (display (caar fields))
               (display \" = \")
               (ziku-print-result (cdar fields))
               (unless (null? (cdr fields))
                 (display \", \"))
               (loop (cdr fields))))
           (display \" }\"))
         ;; Regular pair/list
         (begin
           (display \"(\")
           (ziku-print-result (car v))
           (display \" . \")
           (ziku-print-result (cdr v))
           (display \")\"))))
    ((procedure? v) (display \"<function>\"))
    (else (display v)))
  (newline))

"

-- Generate complete Scheme program
def compile (s : Statement) : String :=
  let mainBody := translateStatement s
  schemeRuntime ++
";; Main program
(define (ziku-main halt)
  " ++ mainBody ++ ")

;; Run with result printer
(ziku-main ziku-print-result)
"

-- Compile a producer (wrapped with halt continuation)
def compileProducer (p : Producer) : String :=
  let stmt := Statement.cut { line := 0, col := 0 } p (Consumer.covar { line := 0, col := 0 } "halt")
  compile stmt

end Ziku.Backend.Scheme
