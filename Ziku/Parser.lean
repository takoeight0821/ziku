import Ziku.Syntax
import Ziku.Lexer

namespace Ziku

/-!
# Ziku Parser

This module implements a recursive descent parser for the Ziku programming language.
The parser uses the token stream from the lexer to build an AST.
-/

-- Parser state
structure ParseState where
  tokens : List PosToken
  deriving Repr

def ParseState.peek? (s : ParseState) : Option PosToken :=
  s.tokens.head?

def ParseState.peekToken? (s : ParseState) : Option Token :=
  s.tokens.head?.map (·.token)

def ParseState.peekN (s : ParseState) (n : Nat) : Option PosToken :=
  s.tokens[n]?

def ParseState.advance (s : ParseState) : ParseState :=
  { s with tokens := s.tokens.drop 1 }

def ParseState.eof (s : ParseState) : Bool :=
  match s.peekToken? with
  | some .eof => true
  | _ => false

def ParseState.currentPos (s : ParseState) : SourcePos :=
  match s.peek? with
  | some tok => tok.pos
  | none => { line := 0, col := 0 }

abbrev Parser α := ParseState → Except String (α × ParseState)

-- Parser combinators
def Parser.pure (a : α) : Parser α := fun s => .ok (a, s)

def Parser.fail (msg : String) : Parser α := fun s =>
  let pos := s.currentPos
  .error s!"{msg} at {pos.line}:{pos.col}"

def Parser.bind (p : Parser α) (f : α → Parser β) : Parser β := fun s =>
  match p s with
  | .ok (a, s') => f a s'
  | .error msg => .error msg

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

instance : MonadExcept String Parser where
  throw := Parser.fail
  tryCatch p handler s :=
    match p s with
    | .ok res => .ok res
    | .error msg => handler msg s

-- Expect a specific token
def expect (expected : Token) : Parser Unit := fun s =>
  match s.peekToken? with
  | some tok =>
    if tok == expected then .ok ((), s.advance)
    else .error s!"expected {expected} but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error s!"expected {expected} but found EOF"

-- Expect and return identifier
def expectIdent : Parser Ident := fun s =>
  match s.peekToken? with
  | some (.ident id) => .ok (id, s.advance)
  | some tok => .error s!"expected identifier but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected identifier but found EOF"

-- Expect constructor identifier
def expectConId : Parser Ident := fun s =>
  match s.peekToken? with
  | some (.conId id) => .ok (id, s.advance)
  | some tok => .error s!"expected constructor identifier but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected constructor identifier but found EOF"

-- Try to match a token, return true if matched
def tryToken (tok : Token) : Parser Bool := fun s =>
  match s.peekToken? with
  | some t => if t == tok then .ok (true, s.advance) else .ok (false, s)
  | none => .ok (false, s)

-- Optional parser
def optional (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

-- Many parser (zero or more)
partial def many (p : Parser α) : Parser (List α) := fun s =>
  match p s with
  | .ok (a, s') =>
    match many p s' with
    | .ok (as, s'') => .ok (a :: as, s'')
    | .error _ => .ok ([a], s')
  | .error _ => .ok ([], s)

-- Many1 parser (one or more)
partial def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  return first :: rest

-- Separated by (sep-separated list)
partial def sepBy (p : Parser α) (sep : Parser β) : Parser (List α) := fun s =>
  match p s with
  | .ok (first, s') =>
    let rec loop (acc : List α) (st : ParseState) : List α × ParseState :=
      match sep st with
      | .ok (_, st') =>
        match p st' with
        | .ok (a, st'') => loop (a :: acc) st''
        | .error _ => (acc, st)
      | .error _ => (acc, st)
    let (rest, s'') := loop [first] s'
    .ok (rest.reverse, s'')
  | .error _ => .ok ([], s)

-- Separated by (at least one)
def seqRight (x : Parser α) (y : Parser β) : Parser β := do
  let _ ← x
  y

def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (seqRight sep p)
  return first :: rest

-- Forward declarations (using mutual recursion)
mutual
  -- Parse a type
  partial def parseType : Parser Ty := parseArrowType

  -- Parse arrow type (right associative)
  partial def parseArrowType : Parser Ty := fun s =>
    let pos := s.currentPos
    match parseAppType s with
    | .ok (left, s') =>
      match tryToken .arrow s' with
      | .ok (hasArrow, s'') =>
        if hasArrow then
          match parseArrowType s'' with
          | .ok (right, s''') => .ok (Ty.arrow pos left right, s''')
          | .error msg => .error msg
        else
          .ok (left, s'')
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse type application
  partial def parseAppType : Parser Ty := fun s =>
    let pos := s.currentPos
    match parseAtomType s with
    | .ok (base, s') =>
      match many parseAtomType s' with
      | .ok (args, s'') => .ok (args.foldl (Ty.app pos) base, s'')
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse atomic type
  partial def parseAtomType : Parser Ty := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some (.ident id) => .ok (.var pos id, s.advance)
    | some (.conId id) => .ok (.con pos id, s.advance)
    | some .kForall =>
      let s := s.advance
      match parseTypeVars s with
      | .ok (vars, s') =>
        match expect .dot s' with
        | .ok (_, s'') =>
          match parseType s'' with
          | .ok (ty, s''') =>
            let result := vars.foldr (fun v acc => Ty.forall_ pos v acc) ty
            .ok (result, s''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | some .lparen =>
      let s := s.advance
      match parseType s with
      | .ok (ty, s') =>
        match expect .rparen s' with
        | .ok (_, s'') => .ok (ty, s'')
        | .error msg => .error msg
      | .error msg => .error msg
    | some .lbrace =>
      -- Record type: { x : ty, ... }
      let s := s.advance
      match parseRecordTypeFields s with
      | .ok (fields, s') =>
        match expect .rbrace s' with
        | .ok (_, s'') => .ok (.record pos fields, s'')
        | .error msg => .error msg
      | .error msg => .error msg
    | some tok => .error s!"expected type but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
    | none => .error "expected type but found EOF"

  partial def parseTypeVars : Parser (List Ident) := many1 expectIdent

  partial def parseRecordTypeFields : Parser (List (Ident × Ty)) :=
    sepBy parseRecordTypeField (expect .comma)

  partial def parseRecordTypeField : Parser (Ident × Ty) := do
    let name ← expectIdent
    expect .colon
    let ty ← parseType
    return (name, ty)

  -- Parse pattern
  partial def parsePattern : Parser Pat := parsePatternAtom

  partial def parsePatternAtom : Parser Pat := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some (.ident id) => .ok (.var pos id, s.advance)
    | some (.conId id) =>
      -- Constructor pattern, possibly with arguments
      let s := s.advance
      match many parsePatternAtom s with
      | .ok (args, s') => .ok (.con pos id args, s')
      | .error msg => .error msg
    | some (.int n) => .ok (.lit pos (.int n), s.advance)
    | some (.string str) => .ok (.lit pos (.string str), s.advance)
    | some (.char c) => .ok (.lit pos (.char c), s.advance)
    | some .kTrue => .ok (.lit pos (.bool true), s.advance)
    | some .kFalse => .ok (.lit pos (.bool false), s.advance)
    | some .underscore => .ok (.wild pos, s.advance)
    | some .lparen =>
      let s := s.advance
      match parsePattern s with
      | .ok (p, s') =>
        match s'.peekToken? with
        | some .colon =>
          -- Annotated pattern
          let s' := s'.advance
          match parseType s' with
          | .ok (ty, s'') =>
            match expect .rparen s'' with
            | .ok (_, s''') => .ok (.ann pos p ty, s''')
            | .error msg => .error msg
          | .error msg => .error msg
        | some .rparen => .ok (.paren pos p, s'.advance)
        | some tok => .error s!"expected ')' or ':' but found {tok}"
        | none => .error "unexpected EOF in pattern"
      | .error msg => .error msg
    | some tok => .error s!"expected pattern but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
    | none => .error "expected pattern but found EOF"

  -- Parse copattern accessor
  partial def parseAccessor : Parser Accessor := fun s =>
    match s.peekToken? with
    | some .dot =>
      let s := s.advance
      match s.peekToken? with
      | some (.ident id) => .ok (.field id, s.advance)
      | some tok => .error s!"expected field name after '.' but found {tok}"
      | none => .error "expected field name after '.'"
    | some .lparen =>
      let s := s.advance
      match s.peekToken? with
      | some (.ident id) =>
        let s := s.advance
        match expect .rparen s with
        | .ok (_, s') => .ok (.apply id, s')
        | .error msg => .error msg
      | some tok => .error s!"expected identifier in copattern application but found {tok}"
      | none => .error "expected identifier in copattern application"
    | some tok => .error s!"expected '.' or '(' but found {tok}"
    | none => .error "expected accessor"

  -- Parse copattern (after #)
  partial def parseCopattern : Parser Copattern := many parseAccessor

  -- Parse expression
  partial def parseExpr : Parser Expr := parsePipeExpr

  -- Pipe operator (lowest precedence, left associative)
  partial def parsePipeExpr : Parser Expr := do
    let left ← parseOrExpr
    parsePipeRest left

  partial def parsePipeRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .pipeGt =>
      let s := s.advance
      match parseOrExpr s with
      | .ok (right, s') =>
        parsePipeRest (Expr.binOp pos .pipe left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Or expression
  partial def parseOrExpr : Parser Expr := do
    let left ← parseAndExpr
    parseOrRest left

  partial def parseOrRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .pipeOr =>
      let s := s.advance
      match parseAndExpr s with
      | .ok (right, s') =>
        parseOrRest (Expr.binOp pos .or left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- And expression
  partial def parseAndExpr : Parser Expr := do
    let left ← parseCompareExpr
    parseAndRest left

  partial def parseAndRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .ampAmp =>
      let s := s.advance
      match parseCompareExpr s with
      | .ok (right, s') =>
        parseAndRest (Expr.binOp pos .and left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Comparison expression
  partial def parseCompareExpr : Parser Expr := do
    let left ← parseConcatExpr
    parseCompareRest left

  partial def parseCompareRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .eqEq =>
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .eq left right, s')
      | .error msg => .error msg
    | some .neq =>
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .ne left right, s')
      | .error msg => .error msg
    | some .langle =>
      -- Check it's not part of something else
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .lt left right, s')
      | .error msg => .error msg
    | some .le =>
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .le left right, s')
      | .error msg => .error msg
    | some .rangle =>
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .gt left right, s')
      | .error msg => .error msg
    | some .ge =>
      let s := s.advance
      match parseConcatExpr s with
      | .ok (right, s') => .ok (Expr.binOp pos .ge left right, s')
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Concat expression (right associative)
  partial def parseConcatExpr : Parser Expr := do
    let left ← parseAddExpr
    parseConcatRest left

  partial def parseConcatRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .plusPlus =>
      let s := s.advance
      match parseConcatExpr s with  -- Right associative
      | .ok (right, s') => .ok (Expr.binOp pos .concat left right, s')
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Additive expression
  partial def parseAddExpr : Parser Expr := do
    let left ← parseMulExpr
    parseAddRest left

  partial def parseAddRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .plus =>
      let s := s.advance
      match parseMulExpr s with
      | .ok (right, s') =>
        parseAddRest (Expr.binOp pos .add left right) s'
      | .error msg => .error msg
    | some .minus =>
      let s := s.advance
      match parseMulExpr s with
      | .ok (right, s') =>
        parseAddRest (Expr.binOp pos .sub left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Multiplicative expression
  partial def parseMulExpr : Parser Expr := do
    let left ← parseUnaryExpr
    parseMulRest left

  partial def parseMulRest (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .star =>
      let s := s.advance
      match parseUnaryExpr s with
      | .ok (right, s') =>
        parseMulRest (Expr.binOp pos .mul left right) s'
      | .error msg => .error msg
    | some .slash =>
      let s := s.advance
      match parseUnaryExpr s with
      | .ok (right, s') =>
        parseMulRest (Expr.binOp pos .div left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  -- Unary expression
  partial def parseUnaryExpr : Parser Expr := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some .minus =>
      let s := s.advance
      match parseUnaryExpr s with
      | .ok (e, s') => .ok (Expr.unaryOp pos .neg e, s')
      | .error msg => .error msg
    | some .kNot =>
      let s := s.advance
      match parseUnaryExpr s with
      | .ok (e, s') => .ok (Expr.unaryOp pos .not e, s')
      | .error msg => .error msg
    | _ => parseAppExpr s

  -- Application and field access expression (same precedence, left-to-right)
  -- This unified parser handles both `f x y` and `f.x.y` with correct associativity
  -- so that `f x .y` parses as `(f x).y` not `f (x.y)`
  partial def parseAppExpr : Parser Expr := do
    let base ← parseAtomExpr
    parsePostfixRest base

  -- Unified postfix parser: handles both field access and application left-to-right
  partial def parsePostfixRest (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken?, s.peekN 1 with
    -- Field access: .field (check this FIRST for left-to-right associativity)
    | some .dot, some ptok =>
      match ptok.token with
      | .ident field =>
        let s := s.advance.advance
        parsePostfixRest (Expr.field pos base field) s
      | _ =>
        -- Dot not followed by identifier - try application
        parsePostfixApp base s
    -- Parenthesized application: f(x) or f(x, y)
    | some .lparen, _ =>
      let s := s.advance
      match sepBy parseExpr (expect .comma) s with
      | .ok (args, s') =>
        match expect .rparen s' with
        | .ok (_, s'') =>
          -- Apply arguments as curried: f(x, y) becomes (f x) y
          let result := args.foldl (Expr.app pos) base
          parsePostfixRest result s''
        | .error msg => .error msg
      | .error msg => .error msg
    -- Other tokens - try space-separated application
    | _, _ => parsePostfixApp base s

  -- Try space-separated application (used when no field access or paren found)
  partial def parsePostfixApp (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken? with
    | some .hash =>
      -- Don't consume # followed by . or ( as application argument
      -- since it likely starts a new codata clause
      match s.peekN 1 with
      | some ptok =>
        if ptok.token == .dot || ptok.token == .lparen then
          .ok (base, s)
        else
          -- Bare # can be an argument
          match parseAtomExpr s with
          | .ok (arg, s') => parsePostfixRest (Expr.app pos base arg) s'
          | .error _ => .ok (base, s)
      | none => .ok (base, s)
    | _ =>
      -- Try space-separated application with atom only (no field access)
      match parseAtomExpr s with
      | .ok (arg, s') =>
        parsePostfixRest (Expr.app pos base arg) s'
      | .error _ => .ok (base, s)

  -- Keep parseFieldExpr for backward compatibility (used by other parts of parser)
  partial def parseFieldExpr : Parser Expr := do
    let base ← parseAtomExpr
    parseFieldRest base

  partial def parseFieldRest (base : Expr) : Parser Expr := fun s =>
    match s.peekToken?, s.peekN 1 with
    | some .dot, some ptok =>
      let pos := base.pos
      match ptok.token with
      | .ident field =>
        let s := s.advance.advance
        parseFieldRest (Expr.field pos base field) s
      | _ => .ok (base, s)
    | _, _ => .ok (base, s)

  -- Atomic expression
  partial def parseAtomExpr : Parser Expr := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    -- Literals
    | some (.int n) => .ok (Expr.lit pos (.int n), s.advance)
    | some (.float f) => .ok (Expr.lit pos (.float f), s.advance)
    | some (.string str) => .ok (Expr.lit pos (.string str), s.advance)
    | some (.char c) => .ok (Expr.lit pos (.char c), s.advance)
    | some .kTrue => .ok (Expr.lit pos (.bool true), s.advance)
    | some .kFalse => .ok (Expr.lit pos (.bool false), s.advance)
    -- Hash (self-reference) for codata
    | some .hash => .ok (Expr.hash pos, s.advance)
    -- Variable or constructor
    | some (.ident id) => .ok (Expr.var pos id, s.advance)
    | some (.conId id) => .ok (Expr.var pos id, s.advance)
    -- Lambda
    | some .backslash => parseLambda s
    -- Let
    | some .kLet => parseLet s
    -- Match
    | some .kMatch => parseMatch s
    -- If
    | some .kIf => parseIf s
    -- Cut
    | some .kCut => parseCut s
    -- Mu
    | some .kMu => parseMu s
    -- Label
    | some .kLabel => parseLabel s
    -- Goto
    | some .kGoto => parseGoto s
    -- Parenthesized or unit
    | some .lparen =>
      let s := s.advance
      match s.peekToken? with
      | some .rparen => .ok (Expr.lit pos .unit, s.advance)
      | _ =>
        match parseExpr s with
        | .ok (e, s') =>
          match s'.peekToken? with
          | some .colon =>
            -- Type annotation
            let s' := s'.advance
            match parseType s' with
            | .ok (ty, s'') =>
              match expect .rparen s'' with
              | .ok (_, s''') => .ok (Expr.ann pos e ty, s''')
              | .error msg => .error msg
            | .error msg => .error msg
          | some .rparen => .ok (e, s'.advance)
          | some tok => .error s!"expected ')' or ':' but found {tok}"
          | none => .error "unexpected EOF"
        | .error msg => .error msg
    -- Codata block or record
    | some .lbrace => parseBraceExpr s
    | some tok => .error s!"expected expression but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
    | none => .error "expected expression but found EOF"

  -- Parse lambda: \x, y => e (desugared to \x => \y => e)
  partial def parseLambda : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip \
    match sepBy1 expectIdent (expect .comma) s with
    | .ok (params, s') =>
      match expect .fatArrow s' with
      | .ok (_, s'') =>
        match parseExpr s'' with
        | .ok (body, s''') =>
          -- Desugar multi-param lambda to nested single-param lambdas
          let result := params.foldr (fun param acc => Expr.lam pos param acc) body
          .ok (result, s''')
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse let: let x = e in body or let rec f = e in body
  partial def parseLet : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'let'
    match s.peekToken? with
    | some .kRec =>
      let s := s.advance
      match expectIdent s with
      | .ok (name, s') =>
        let (tyOpt, s') := match s'.peekToken? with
          | some .colon =>
            match parseType s'.advance with
            | .ok (ty, s'') => (some ty, s'')
            | .error _ => (none, s')
          | _ => (none, s')
        match expect .eq s' with
        | .ok (_, s'') =>
          match parseExpr s'' with
          | .ok (value, s''') =>
            match expect .kIn s''' with
            | .ok (_, s'''') =>
              match parseExpr s'''' with
              | .ok (body, s''''') => .ok (Expr.letRec pos name tyOpt value body, s''''')
              | .error msg => .error msg
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | _ =>
      match expectIdent s with
      | .ok (name, s') =>
        let (tyOpt, s') := match s'.peekToken? with
          | some .colon =>
            match parseType s'.advance with
            | .ok (ty, s'') => (some ty, s'')
            | .error _ => (none, s')
          | _ => (none, s')
        match expect .eq s' with
        | .ok (_, s'') =>
          match parseExpr s'' with
          | .ok (value, s''') =>
            match expect .kIn s''' with
            | .ok (_, s'''') =>
              match parseExpr s'''' with
              | .ok (body, s''''') => .ok (Expr.let_ pos name tyOpt value body, s''''')
              | .error msg => .error msg
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg

  -- Parse match: match e with | p => e end
  partial def parseMatch : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'match'
    match parseExpr s with
    | .ok (scrutinee, s') =>
      match expect .kWith s' with
      | .ok (_, s'') =>
        match parseMatchCases s'' with
        | .ok (cases, s''') =>
          match expect .kEnd s''' with
          | .ok (_, s'''') => .ok (Expr.match_ pos scrutinee cases, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseMatchCases : Parser (List (Pat × Expr)) := many1 parseMatchCase

  partial def parseMatchCase : Parser (Pat × Expr) := fun s =>
    match expect .pipe s with
    | .ok (_, s') =>
      match parsePattern s' with
      | .ok (pat, s'') =>
        match expect .fatArrow s'' with
        | .ok (_, s''') =>
          match parseExpr s''' with
          | .ok (body, s'''') => .ok ((pat, body), s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse if: if c then t else f
  partial def parseIf : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'if'
    match parseExpr s with
    | .ok (cond, s') =>
      match expect .kThen s' with
      | .ok (_, s'') =>
        match parseExpr s'' with
        | .ok (thenBranch, s''') =>
          match expect .kElse s''' with
          | .ok (_, s'''') =>
            match parseExpr s'''' with
            | .ok (elseBranch, s''''') => .ok (Expr.if_ pos cond thenBranch elseBranch, s''''')
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse mu: μk => e or mu k => e
  partial def parseMu : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'μ' or 'mu'
    match expectIdent s with
    | .ok (name, s') =>
      match expect .fatArrow s' with
      | .ok (_, s'') =>
        match parseExpr s'' with
        | .ok (body, s''') => .ok (Expr.mu pos name body, s''')
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse label: label name { body }
  partial def parseLabel : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'label'
    match expectIdent s with
    | .ok (name, s') =>
      match expect .lbrace s' with
      | .ok (_, s'') =>
        match parseExpr s'' with
        | .ok (body, s''') =>
          match expect .rbrace s''' with
          | .ok (_, s'''') => .ok (Expr.label pos name body, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse goto: goto(expr, name)
  partial def parseGoto : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'goto'
    match expect .lparen s with
    | .ok (_, s') =>
      match parseExpr s' with
      | .ok (value, s'') =>
        match expect .comma s'' with
        | .ok (_, s''') =>
          match expectIdent s''' with
          | .ok (name, s'''') =>
            match expect .rparen s'''' with
            | .ok (_, s''''') => .ok (Expr.goto pos value name, s''''')
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse brace expression: codata block { #.f => e } or record { x = 1 }
  partial def parseBraceExpr : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip '{'
    match s.peekToken? with
    | some .hash =>
      -- Codata block
      match parseCodataBlock s with
      | .ok (clauses, s') =>
        match expect .rbrace s' with
        | .ok (_, s'') => .ok (Expr.codata pos clauses, s'')
        | .error msg => .error msg
      | .error msg => .error msg
    | some .pipe =>
      -- Consumer block: { | p => e | ... }
      match parseCodataBlock s with
      | .ok (clauses, s') =>
        match expect .rbrace s' with
        | .ok (_, s'') => .ok (Expr.codata pos clauses, s'')
        | .error msg => .error msg
      | .error msg => .error msg
    | some (.ident _) =>
      -- Could be record or codata with patterns
      -- Check if next is '=' (record) or '#' (codata)
      match s.peekN 1 with
      | some ptok =>
        if ptok.token == .eq then
          -- Record
          match parseRecordFields s with
          | .ok (fields, s') =>
            match expect .rbrace s' with
            | .ok (_, s'') => .ok (Expr.record pos fields, s'')
            | .error msg => .error msg
          | .error msg => .error msg
        else
          -- Codata with patterns
          match parseCodataBlock s with
          | .ok (clauses, s') =>
            match expect .rbrace s' with
            | .ok (_, s'') => .ok (Expr.codata pos clauses, s'')
            | .error msg => .error msg
          | .error msg => .error msg
      | none => .error "unexpected EOF"
    | some .rbrace => .ok (Expr.record pos [], s.advance)
    | _ =>
      match parseCodataBlock s with
      | .ok (clauses, s') =>
        match expect .rbrace s' with
        | .ok (_, s'') => .ok (Expr.codata pos clauses, s'')
        | .error msg => .error msg
      | .error msg => .error msg

  -- Parse a codata/consumer block with clauses separated by comma, pipe, or newlines
  partial def parseCodataBlock : Parser (List (List Pat × Copattern × Expr)) := fun s =>
    -- parse the first clause
    match parseCodataClause s with
    | .ok (cl, s') =>
      -- keep parsing subsequent clauses if present
      let rec loop (acc : List (List Pat × Copattern × Expr)) (st : ParseState)
        : Except String (List (List Pat × Copattern × Expr) × ParseState) :=
        -- stop when we reach '}'
        match st.peekToken? with
        | some .rbrace => .ok (acc.reverse, st)
        | _ =>
          -- consume optional comma; if consumed but no following clause, it's an error
          let st1 := match tryToken .comma st with
            | .ok (true, stc) => stc
            | .ok (false, _) => st
            | .error _ => st
          match parseCodataClause st1 with
          | .ok (cl2, st2) => loop (cl2 :: acc) st2
          | .error msg => .error msg
      match loop [cl] s' with
      | .ok (cls, st) => .ok (cls, st)
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseCodataClause : Parser (List Pat × Copattern × Expr) := fun s =>
    -- Parse optional leading pipe for consumer syntax
    let s := match s.peekToken? with
      | some .pipe => s.advance
      | _ => s
    -- Parse patterns before #
    let (patterns, s) :=
      let rec loop (acc : List Pat) (st : ParseState) : List Pat × ParseState :=
        match st.peekToken? with
        | some .hash => (acc.reverse, st)
        | _ =>
          match parsePattern st with
          | .ok (p, st') => loop (p :: acc) st'
          | .error _ => (acc.reverse, st)
      loop [] s
    -- Parse # and copattern
    match s.peekToken? with
    | some .hash =>
      let s := s.advance
      match parseCopattern s with
      | .ok (copat, s') =>
        match expect .fatArrow s' with
        | .ok (_, s'') =>
          match parseExpr s'' with
          | .ok (body, s''') => .ok ((patterns, copat, body), s''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | _ =>
      -- Pattern-only clause (for consumers)
      match expect .fatArrow s with
      | .ok (_, s') =>
        match parseExpr s' with
        | .ok (body, s'') => .ok ((patterns, [], body), s'')
        | .error msg => .error msg
      | .error msg => .error msg

  partial def parseRecordFields : Parser (List (Ident × Expr)) :=
    sepBy parseRecordField (expect .comma)

  partial def parseRecordField : Parser (Ident × Expr) := do
    let name ← expectIdent
    expect .eq
    let value ← parseExpr
    return (name, value)

  -- Parse declaration
  partial def parseDecl : Parser Decl := fun s =>
    match s.peekToken? with
    | some .kData => parseDataDecl s
    | some .kCodata => parseCodataDecl s
    | some .kDef => parseDefDecl s
    | some .kModule => parseModuleDecl s
    | some .kImport => parseImportDecl s
    | some .kInfix => parseInfixDecl false s
    | some .kInfixr => parseInfixDecl true s
    | some .kInfixl => parseInfixDecl false s
    | some tok => .error s!"expected declaration but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
    | none => .error "expected declaration but found EOF"

  -- Parse data declaration: data T a b = | C1 ty1 | C2 ty2
  partial def parseDataDecl : Parser Decl := fun s =>
    let s := s.advance  -- skip 'data'
    match expectConId s with
    | .ok (name, s') =>
      let (tyParams, s') :=
        let rec loop (acc : List Ident) (st : ParseState) : List Ident × ParseState :=
          match expectIdent st with
          | .ok (id, st') => loop (id :: acc) st'
          | .error _ => (acc.reverse, st)
        loop [] s'
      match expect .eq s' with
      | .ok (_, s'') =>
        match parseConstructors s'' with
        | .ok (constrs, s''') => .ok (.data name tyParams constrs, s''')
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseConstructors : Parser (List ConDecl) := many1 parseConstructor

  partial def parseConstructor : Parser ConDecl := fun s =>
    match expect .pipe s with
    | .ok (_, s') =>
      match expectConId s' with
      | .ok (name, s'') =>
        let (args, s'') :=
          let rec loop (acc : List Ty) (st : ParseState) : List Ty × ParseState :=
            match parseAtomType st with
            | .ok (ty, st') => loop (ty :: acc) st'
            | .error _ => (acc.reverse, st)
          loop [] s''
        .ok ({ name := name, args := args }, s'')
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse codata declaration: codata T a { #.f : ty }
  partial def parseCodataDecl : Parser Decl := fun s =>
    let s := s.advance  -- skip 'codata'
    match expectConId s with
    | .ok (name, s') =>
      let (tyParams, s') :=
        let rec loop (acc : List Ident) (st : ParseState) : List Ident × ParseState :=
          match expectIdent st with
          | .ok (id, st') => loop (id :: acc) st'
          | .error _ => (acc.reverse, st)
        loop [] s'
      match expect .lbrace s' with
      | .ok (_, s'') =>
        match parseCodataSigs s'' with
        | .ok (sigs, s''') =>
          match expect .rbrace s''' with
          | .ok (_, s'''') => .ok (.codata name tyParams sigs, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseCodataSigs : Parser (List CopatSig) := many parseCodataSig

  partial def parseCodataSig : Parser CopatSig := fun s =>
    match expect .hash s with
    | .ok (_, s') =>
      match parseCopattern s' with
      | .ok (copat, s'') =>
        match expect .colon s'' with
        | .ok (_, s''') =>
          match parseType s''' with
          | .ok (ty, s'''') => .ok ({ accessors := copat, ty := ty }, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse def declaration
  partial def parseDefDecl : Parser Decl := fun s =>
    let s := s.advance  -- skip 'def'
    -- Handle operator definitions: def (++) : ty = e
    let (name, s') :=
      if s.peekToken? == some .lparen then
        let s := s.advance
        match s.peekToken? with
        | some (.ident op) =>
          let s := s.advance
          match expect .rparen s with
          | .ok (_, s') => (op, s')
          | .error _ => ("", s)
        | _ => ("", s)
      else
        match expectIdent s with
        | .ok (id, s') => (id, s')
        | .error _ =>
          match expectConId s with
          | .ok (id, s') => (id, s')
          | .error _ => ("", s)
    if name.isEmpty then .error "expected function name" else
    match expect .colon s' with
    | .ok (_, s'') =>
      match parseType s'' with
      | .ok (ty, s''') =>
        match s'''.peekToken? with
        | some .eq =>
          let s''' := s'''.advance
          match parseExpr s''' with
          | .ok (body, s'''') => .ok (.def_ name ty body, s'''')
          | .error msg => .error msg
        | some .pipe =>
          -- Pattern clauses
          match parseDefClauses s''' with
          | .ok (clauses, s'''') => .ok (.defPat name ty clauses, s'''')
          | .error msg => .error msg
        | some .lbrace =>
          -- Copattern block
          match parseDefClauses s''' with
          | .ok (clauses, s'''') => .ok (.defPat name ty clauses, s'''')
          | .error msg => .error msg
        | some tok => .error s!"expected '=' or '|' but found {tok}"
        | none => .error "unexpected EOF"
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseDefClauses : Parser (List DefClause) := many1 parseDefClause

  partial def parseDefClause : Parser DefClause := fun s =>
    match s.peekToken? with
    | some .pipe =>
      let s := s.advance
      let (patterns, s) :=
        let rec loop (acc : List Pat) (st : ParseState) : List Pat × ParseState :=
          match st.peekToken? with
          | some .fatArrow => (acc.reverse, st)
          | some .hash => (acc.reverse, st)
          | some .comma =>
            let st := st.advance
            match parsePattern st with
            | .ok (p, st') => loop (p :: acc) st'
            | .error _ => (acc.reverse, st)
          | _ =>
            match parsePattern st with
            | .ok (p, st') => loop (p :: acc) st'
            | .error _ => (acc.reverse, st)
        match parsePattern s with
        | .ok (p, s') => loop [p] s'
        | .error _ => ([], s)
      match s.peekToken? with
      | some .hash =>
        let s := s.advance
        match parseCopattern s with
        | .ok (copat, s') =>
          match expect .fatArrow s' with
          | .ok (_, s'') =>
            match parseExpr s'' with
            | .ok (body, s''') => .ok (.copatClause patterns copat body, s''')
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | _ =>
        match expect .fatArrow s with
        | .ok (_, s') =>
          match parseExpr s' with
          | .ok (body, s'') => .ok (.patClause patterns body, s'')
          | .error msg => .error msg
        | .error msg => .error msg
    | some tok => .error s!"expected '|' but found {tok}"
    | none => .error "unexpected EOF"

  -- Parse module declaration
  partial def parseModuleDecl : Parser Decl := fun s =>
    let s := s.advance  -- skip 'module'
    match expectConId s with
    | .ok (name, s') =>
      match expect .kWhere s' with
      | .ok (_, s'') =>
        match parseDecls s'' with
        | .ok (decls, s''') =>
          match expect .kEnd s''' with
          | .ok (_, s'''') => .ok (.module_ name decls, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  -- Parse import declaration
  partial def parseImportDecl : Parser Decl := fun s =>
    let s := s.advance  -- skip 'import'
    match expectConId s with
    | .ok (name, s') =>
      match s'.peekToken? with
      | some .lparen =>
        -- import M (a, b)
        let s' := s'.advance
        match sepBy expectIdent (expect .comma) s' with
        | .ok (items, s'') =>
          match expect .rparen s'' with
          | .ok (_, s''') => .ok (.import_ name (some items) none, s''')
          | .error msg => .error msg
        | .error msg => .error msg
      | some .kAs =>
        -- import M as N
        let s' := s'.advance
        match expectConId s' with
        | .ok (alias, s'') => .ok (.import_ name none (some alias), s'')
        | .error msg => .error msg
      | _ => .ok (.import_ name none none, s')
    | .error msg => .error msg

  -- Parse infix declaration
  partial def parseInfixDecl (rightAssoc : Bool) : Parser Decl := fun s =>
    let s := s.advance  -- skip 'infix'/'infixr'/'infixl'
    match s.peekToken? with
    | some (.int prec) =>
      let s := s.advance
      match expectIdent s with
      | .ok (op, s') => .ok (.infix_ prec.toNat rightAssoc op, s')
      | .error msg => .error msg
    | some tok => .error s!"expected precedence number but found {tok}"
    | none => .error "unexpected EOF"

  partial def parseDecls : Parser (List Decl) := many parseDecl

  -- A variant of expression parser that stops when encountering '>' (rangle).
  -- This is used inside `cut <producer | consumer>` so that the inner expression
  -- does not greedily consume the closing bracket as a comparison operator.

  -- Parse cut: cut <producer | consumer>
  -- Uses parseExprStop to avoid ambiguity with > comparison operator
  partial def parseCut : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'cut'
    match expect .langle s with
    | .ok (_, s') =>
      match parseExprStop s' with
      | .ok (producer, s'') =>
        match expect .pipe s'' with
        | .ok (_, s''') =>
          match parseExprStop s''' with
          | .ok (consumer, s'''') =>
            match expect .rangle s'''' with
            | .ok (_, s''''') => .ok (Expr.cut pos producer consumer, s''''')
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

  partial def parseExprStop : Parser Expr := parsePipeExprStop

  partial def parsePipeExprStop : Parser Expr := do
    let left ← parseOrExprStop
    parsePipeRestStop left

  partial def parsePipeRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .pipeGt =>
      let s := s.advance
      match parseOrExprStop s with
      | .ok (right, s') =>
        parsePipeRestStop (Expr.binOp pos .pipe left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseOrExprStop : Parser Expr := do
    let left ← parseAndExprStop
    parseOrRestStop left

  partial def parseOrRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .pipeOr =>
      let s := s.advance
      match parseAndExprStop s with
      | .ok (right, s') =>
        parseOrRestStop (Expr.binOp pos .or left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseAndExprStop : Parser Expr := do
    let left ← parseCompareExprStop
    parseAndRestStop left

  partial def parseAndRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .ampAmp =>
      let s := s.advance
      match parseCompareExprStop s with
      | .ok (right, s') =>
        parseAndRestStop (Expr.binOp pos .and left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseCompareExprStop : Parser Expr := do
    let left ← parseConcatExprStop
    parseCompareRestStop left

  partial def parseCompareRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .eqEq =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .eq left right, s')
      | .error msg => .error msg
    | some .neq =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .ne left right, s')
      | .error msg => .error msg
    | some .langle =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .lt left right, s')
      | .error msg => .error msg
    | some .le =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .le left right, s')
      | .error msg => .error msg
    | some .rangle =>
      -- Stop here; treat '>' as the end of cut
      .ok (left, s)
    | some .ge =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .ge left right, s')
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseConcatExprStop : Parser Expr := do
    let left ← parseAddExprStop
    parseConcatRestStop left

  partial def parseConcatRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .plusPlus =>
      let s := s.advance
      match parseConcatExprStop s with
      | .ok (right, s') => .ok (Expr.binOp pos .concat left right, s')
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseAddExprStop : Parser Expr := do
    let left ← parseMulExprStop
    parseAddRestStop left

  partial def parseAddRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .plus =>
      let s := s.advance
      match parseMulExprStop s with
      | .ok (right, s') => parseAddRestStop (Expr.binOp pos .add left right) s'
      | .error msg => .error msg
    | some .minus =>
      let s := s.advance
      match parseMulExprStop s with
      | .ok (right, s') => parseAddRestStop (Expr.binOp pos .sub left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseMulExprStop : Parser Expr := do
    let left ← parseUnaryExprStop
    parseMulRestStop left

  partial def parseMulRestStop (left : Expr) : Parser Expr := fun s =>
    let pos := left.pos
    match s.peekToken? with
    | some .star =>
      let s := s.advance
      match parseUnaryExprStop s with
      | .ok (right, s') => parseMulRestStop (Expr.binOp pos .mul left right) s'
      | .error msg => .error msg
    | some .slash =>
      let s := s.advance
      match parseUnaryExprStop s with
      | .ok (right, s') => parseMulRestStop (Expr.binOp pos .div left right) s'
      | .error msg => .error msg
    | _ => .ok (left, s)

  partial def parseUnaryExprStop : Parser Expr := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some .minus =>
      let s := s.advance
      match parseUnaryExprStop s with
      | .ok (e, s') => .ok (Expr.unaryOp pos .neg e, s')
      | .error msg => .error msg
    | some .kNot =>
      let s := s.advance
      match parseUnaryExprStop s with
      | .ok (e, s') => .ok (Expr.unaryOp pos .not e, s')
      | .error msg => .error msg
    | _ => parseAppExprStop s

  -- Application and field access expression (same precedence, left-to-right)
  partial def parseAppExprStop : Parser Expr := do
    let base ← parseAtomExprStop
    parsePostfixRestStop base

  -- Unified postfix parser: handles both field access and application left-to-right
  partial def parsePostfixRestStop (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken?, s.peekN 1 with
    -- Field access: .field (check this FIRST for left-to-right associativity)
    | some .dot, some ptok =>
      match ptok.token with
      | .ident field =>
        let s := s.advance.advance
        parsePostfixRestStop (Expr.field pos base field) s
      | _ =>
        -- Dot not followed by identifier - try application
        parsePostfixAppStop base s
    -- Parenthesized application: f(x) or f(x, y)
    | some .lparen, _ =>
      let s := s.advance
      match sepBy parseExprStop (expect .comma) s with
      | .ok (args, s') =>
        match expect .rparen s' with
        | .ok (_, s'') =>
          let result := args.foldl (Expr.app pos) base
          parsePostfixRestStop result s''
        | .error msg => .error msg
      | .error msg => .error msg
    -- Other tokens - try space-separated application
    | _, _ => parsePostfixAppStop base s

  -- Try space-separated application (used when no field access or paren found)
  partial def parsePostfixAppStop (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken? with
    | some .hash =>
      -- Don't consume # followed by . or ( as application argument
      match s.peekN 1 with
      | some ptok =>
        if ptok.token == .dot || ptok.token == .lparen then
          .ok (base, s)
        else
          match parseAtomExprStop s with
          | .ok (arg, s') => parsePostfixRestStop (Expr.app pos base arg) s'
          | .error _ => .ok (base, s)
      | none => .ok (base, s)
    | _ =>
      match parseAtomExprStop s with
      | .ok (arg, s') =>
        parsePostfixRestStop (Expr.app pos base arg) s'
      | .error _ => .ok (base, s)

  -- Keep parseFieldExprStop for backward compatibility
  partial def parseFieldExprStop : Parser Expr := do
    let base ← parseAtomExprStop
    parseFieldRestStop base

  partial def parseFieldRestStop (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken?, s.peekN 1 with
    | some .dot, some ptok =>
      match ptok.token with
      | .ident field =>
        let s := s.advance.advance
        parseFieldRestStop (Expr.field pos base field) s
      | _ => .ok (base, s)
    | _, _ => .ok (base, s)

  partial def parseAtomExprStop : Parser Expr := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some (.int n) => .ok (Expr.lit pos (.int n), s.advance)
    | some (.float f) => .ok (Expr.lit pos (.float f), s.advance)
    | some (.string str) => .ok (Expr.lit pos (.string str), s.advance)
    | some (.char c) => .ok (Expr.lit pos (.char c), s.advance)
    | some .kTrue => .ok (Expr.lit pos (.bool true), s.advance)
    | some .kFalse => .ok (Expr.lit pos (.bool false), s.advance)
    | some .hash => .ok (Expr.hash pos, s.advance)
    | some (.ident id) => .ok (Expr.var pos id, s.advance)
    | some (.conId id) => .ok (Expr.var pos id, s.advance)
    | some .backslash => parseLambda s
    | some .kLet => parseLet s
    | some .kMatch => parseMatch s
    | some .kIf => parseIf s
    | some .kCut => parseCut s
    | some .kMu => parseMu s
    | some .kLabel => parseLabel s
    | some .kGoto => parseGoto s
    | some .lparen =>
      let s := s.advance
      match s.peekToken? with
      | some .rparen => .ok (Expr.lit pos .unit, s.advance)
      | _ =>
        match parseExprStop s with
        | .ok (e, s') =>
          match s'.peekToken? with
          | some .colon =>
            let s' := s'.advance
            match parseType s' with
            | .ok (ty, s'') =>
              match expect .rparen s'' with
              | .ok (_, s''') => .ok (Expr.ann pos e ty, s''')
              | .error msg => .error msg
            | .error msg => .error msg
          | some .rparen => .ok (e, s'.advance)
          | some tok => .error s!"expected ')' or ':' but found {tok}"
          | none => .error "unexpected EOF"
        | .error msg => .error msg
    | some .lbrace => parseBraceExpr s
    | some tok => .error s!"expected expression but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
    | none => .error "expected expression but found EOF"
end

-- Parse a complete program
def parseProgram (input : String) : Except String Program := do
  let tokens ← tokenize input
  let s : ParseState := { tokens := tokens }
  let (decls, s') ← parseDecls s
  if s'.eof then
    .ok decls
  else
    .error s!"unexpected token at end of input: {s'.peekToken?}"

-- Parse a single expression (for REPL)
def parseExprString (input : String) : Except String Expr := do
  let tokens ← tokenize input
  let s : ParseState := { tokens := tokens }
  let (expr, s') ← parseExpr s
  if s'.eof then
    .ok expr
  else
    .error s!"unexpected token at end of input: {s'.peekToken?}"

-- Backward compatibility alias
def parse (input : String) : Except String Expr := parseExprString input

end Ziku
