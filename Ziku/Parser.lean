import Ziku.Syntax
import Ziku.Lexer

set_option linter.missingDocs false

namespace Ziku

/-!
# Ziku Parser

This module implements a recursive descent parser for the Ziku programming language.
The parser uses the token stream from the lexer to build an AST.
-/

-- Parser state
/-- Represents the state of the parser, containing the remaining tokens. -/
structure ParseState where
  /-- The list of tokens remaining to be parsed. -/
  tokens : List PosToken
  deriving Repr

/-- Returns the current token without advancing the parser. -/
def ParseState.peek? (s : ParseState) : Option PosToken :=
  s.tokens.head?

/-- Returns the type of the current token without advancing the parser. -/
def ParseState.peekToken? (s : ParseState) : Option Token :=
  s.tokens.head?.map (·.token)

/-- Returns the token at 'n' positions ahead. -/
def ParseState.peekN (s : ParseState) (n : Nat) : Option PosToken :=
  s.tokens[n]?

/-- Advances the parser state by one token. -/
def ParseState.advance (s : ParseState) : ParseState :=
  { s with tokens := s.tokens.drop 1 }

/-- Returns true if the parser has reached the end of the input or an EOF token. -/
def ParseState.eof (s : ParseState) : Bool :=
  match s.peekToken? with
  | some .eof => true
  | _ => false

-- Default position for end-of-file (no tokens remaining)
/-- Default position used for errors at the end of the file. -/
def eofPos : SourcePos := { line := 0, col := 0 }

/-- Returns the source position of the current token. -/
def ParseState.currentPos (s : ParseState) : SourcePos :=
  match s.peek? with
  | some tok => tok.pos
  | none => eofPos

/-- The 'Parser' type represents a stateful transformation from 'ParseState' to a result or error. -/
abbrev Parser α := ParseState → Except String (α × ParseState)

-- Parser combinators
/-- Wraps a value in the 'Parser' monad. -/
def Parser.pure (a : α) : Parser α := fun s => .ok (a, s)

/-- Fails the parser with a given message at the current position. -/
def Parser.fail (msg : String) : Parser α := fun s =>
  let pos := s.currentPos
  .error s!"{msg} at {pos.line}:{pos.col}"

/-- Chains two parsers together. -/
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
/-- Consumes the current token if it matches the expected token, otherwise fails. -/
def expect (expected : Token) : Parser Unit := fun s =>
  match s.peekToken? with
  | some tok =>
    if tok == expected then .ok ((), s.advance)
    else .error s!"expected {expected} but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error s!"expected {expected} but found EOF"

-- Expect and return identifier
/-- Consumes and returns the current token if it is an identifier, otherwise fails. -/
def expectIdent : Parser Ident := fun s =>
  match s.peekToken? with
  | some (.ident id) => .ok (id, s.advance)
  | some tok => .error s!"expected identifier but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected identifier but found EOF"

-- Expect constructor identifier
/-- Consumes and returns the current token if it is a constructor identifier, otherwise fails. -/
def expectConId : Parser Ident := fun s =>
  match s.peekToken? with
  | some (.conId id) => .ok (id, s.advance)
  | some tok => .error s!"expected constructor identifier but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected constructor identifier but found EOF"

/-- Consumes and returns the current token if it is a string literal, otherwise fails. -/
def expectString : Parser String := fun s =>
  match s.peekToken? with
  | some (.string str) => .ok (str, s.advance)
  | some tok => .error s!"expected string literal but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected string literal but found EOF"

/-- Consumes and returns the current token if it is an integer, otherwise fails. -/
def expectInt : Parser Int := fun s =>
  match s.peekToken? with
  | some (.int n) => .ok (n, s.advance)
  | some tok => .error s!"expected integer but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected integer but found EOF"

/-- Returns the current source position without consuming input. -/
def currentPos : Parser SourcePos := fun s => .ok (s.currentPos, s)

/-- Returns the current token without consuming input. -/
def peek? : Parser (Option Token) := fun s => .ok (s.peekToken?, s)

/-- Advances the parser by one token. -/
def advance : Parser Unit := fun s => .ok ((), s.advance)

-- Try to match a token, return true if matched
/-- Returns true and advances if the current token matches the given token, otherwise returns false. -/
def tryToken (tok : Token) : Parser Bool := fun s =>
  match s.peekToken? with
  | some t => if t == tok then .ok (true, s.advance) else .ok (false, s)
  | none => .ok (false, s)

-- Optional parser
/-- Optionally runs a parser, returning 'none' if it fails without consuming input. -/
def optional (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

-- Many parser (zero or more)
/-- Parses a sequence of zero or more occurrences of 'p'. -/
partial def many (p : Parser α) : Parser (List α) := fun s =>
  match p s with
  | .ok (a, s') =>
    match many p s' with
    | .ok (as, s'') => .ok (a :: as, s'')
    | .error _ => .ok ([a], s')
  | .error _ => .ok ([], s)

-- Many1 parser (one or more)
/-- Parses a sequence of one or more occurrences of 'p'. -/
partial def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  return first :: rest

-- Separated by (sep-separated list)
/-- Parses a sequence of zero or more occurrences of 'p' separated by 'sep'. -/
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
/-- Skips the result of the first parser and returns the result of the second. -/
def seqRight (x : Parser α) (y : Parser β) : Parser β := do
  let _ ← x
  y

/-- Parses a sequence of one or more occurrences of 'p' separated by 'sep'. -/
def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (seqRight sep p)
  return first :: rest

-- Forward declarations (using mutual recursion)
mutual
  -- Parse a type
  partial def parseType : Parser Ty := parseArrowType

  -- Parse arrow type (right associative)
  partial def parseArrowType : Parser Ty := do
    let pos ← currentPos
    let left ← parseAppType
    let hasArrow ← tryToken .arrow
    if hasArrow then
      let right ← parseArrowType
      return Ty.arrow pos left right
    else
      return left

  -- Parse type application
  partial def parseAppType : Parser Ty := do
    let pos ← currentPos
    let base ← parseAtomType
    let args ← many parseAtomType
    return args.foldl (Ty.app pos) base

  -- Parse variant type after '[' (handles row polymorphism)
  partial def parseVariantType (pos : SourcePos) : Parser Ty := do
    let cases ← parseVariantTypeCases
    let hasPipe ← tryToken .pipe
    if hasPipe then
      let tok? ← peek?
      match tok? with
      | some (.ident rowVar) =>
        -- Open variant with row variable: [Con | r]
        advance
        let _ ← expect .rbracket
        return .variant pos cases (some (.var pos rowVar))
      | some (.conId _) =>
        -- Another constructor case, continue parsing
        let moreCases ← parseVariantTypeCases
        let hasPipe' ← tryToken .pipe
        if hasPipe' then
          let rowVar ← expectIdent
          let _ ← expect .rbracket
          return .variant pos (cases ++ moreCases) (some (.var pos rowVar))
        else
          let _ ← expect .rbracket
          return .variant pos (cases ++ moreCases) none
      | _ =>
        -- Closed variant: [Con]
        let _ ← expect .rbracket
        return .variant pos cases none
    else
      let _ ← expect .rbracket
      return .variant pos cases none

  -- Parse atomic type
  partial def parseAtomType : Parser Ty := do
    let pos ← currentPos
    let tok? ← peek?
    match tok? with
    | some (.ident id) =>
      advance
      return .var pos id
    | some (.conId id) =>
      advance
      return .con pos id
    | some .kForall =>
      advance
      let vars ← parseTypeVars
      let _ ← expect .dot
      let ty ← parseType
      return vars.foldr (fun v acc => Ty.forall_ pos v acc) ty
    | some .lparen =>
      advance
      let ty ← parseType
      let _ ← expect .rparen
      return ty
    | some .lbrace =>
      -- Record type: { x : ty, ... } or { x : ty | r }
      advance
      let fields ← parseRecordTypeFields
      let hasPipe ← tryToken .pipe
      if hasPipe then
        let rowVar ← expectIdent
        let _ ← expect .rbrace
        return .record pos fields (some (.var pos rowVar))
      else
        let _ ← expect .rbrace
        return .record pos fields none
    | some .lbracket =>
      -- Variant type: [Con1 ty1 ty2 | Con2 | r]
      advance
      parseVariantType pos
    | some .tilde =>
      advance
      let ty ← parseAtomType
      return .tilde pos ty
    | some tok => throw s!"expected type but found {tok} at {pos.line}:{pos.col}"
    | none => throw "expected type but found EOF"

  partial def parseTypeVars : Parser (List Ident) := many1 expectIdent

  partial def parseRecordTypeFields : Parser (List (Ident × Ty)) :=
    sepBy parseRecordTypeField (expect .comma)

  partial def parseRecordTypeField : Parser (Ident × Ty) := do
    let name ← expectIdent
    expect .colon
    let ty ← parseType
    return (name, ty)

  -- Parse variant type cases: Con1 ty1 ty2 | Con2 ty3 | ...
  -- Returns list of (constructor name, argument types)
  partial def parseVariantTypeCases : Parser (List (Ident × List Ty)) :=
    sepBy1 parseVariantTypeCase (expect .pipe)

  partial def parseVariantTypeCase : Parser (Ident × List Ty) := do
    let name ← expectConId
    let argTys ← parseVariantArgTypes
    return (name, argTys)

  -- Parse argument types for a variant constructor (stops at | or ])
  partial def parseVariantArgTypes : Parser (List Ty) := do
    let tok? ← peek?
    match tok? with
    | some .pipe => return []
    | some .rbracket => return []
    | some _ =>
      match (← optional parseAtomType) with
      | some ty =>
        let rest ← parseVariantArgTypes
        return ty :: rest
      | none => return []
    | none => return []

  -- Parse a parameter: ident or ~ident
  partial def parseParam : Parser (Ident × Bool) := do
    let hasTilde ← tryToken .tilde
    let id ← expectIdent
    return (id, hasTilde)

  -- Parse an argument: expr or ~expr
  partial def parseArg : Parser (Expr × Bool) := do
    let hasTilde ← tryToken .tilde
    if hasTilde then
      let e ← parseAtomExpr
      return (e, true)
    else
      let e ← parseExpr
      return (e, false)

  -- Parse pattern
  partial def parsePattern : Parser Pat := parsePatternAtom

  partial def parsePatternAtom : Parser Pat := fun s =>
    let pos := s.currentPos
    match s.peekToken? with
    | some (.ident id) => .ok (.var pos id, s.advance)
    | some (.conId id) =>
      -- Constructor pattern: Con or Con(p1, p2, ...)
      let s := s.advance
      match s.peekToken? with
      | some .lparen =>
        -- Con(args...)
        let s := s.advance  -- skip (
        match s.peekToken? with
        | some .rparen =>
          -- Con() - nullary constructor with explicit parens
          .ok (.con pos id [], s.advance)
        | _ =>
          match sepBy1 parsePattern (expect .comma) s with
          | .ok (args, s') =>
            match expect .rparen s' with
            | .ok (_, s'') => .ok (.con pos id args, s'')
            | .error msg => .error msg
          | .error msg => .error msg
      | _ =>
        -- Con - nullary constructor
        .ok (.con pos id [], s)
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
  -- Supports: .field, (arg), and bare identifier arg (space-separated)
  partial def parseAccessor : Parser Accessor := do
    let tok? ← peek?
    match tok? with
    | some .dot =>
      advance
      let id ← expectIdent
      return .field id
    | some .lparen =>
      advance
      let id ← expectIdent
      let _ ← expect .rparen
      return .apply id
    -- Bare identifier as space-separated argument
    | some (.ident id) =>
      advance
      return .apply id
    | some tok => throw s!"expected '.', '(' or identifier but found {tok}"
    | none => throw "expected accessor"

  -- Parse copattern (after #)
  partial def parseCopattern : Parser Copattern := many parseAccessor

  -- Parse expression
  partial def parseExpr : Parser Expr := parsePipeExpr

  -- Pipe operator (lowest precedence, left associative)
  partial def parsePipeExpr : Parser Expr := do
    let left ← parseOrExpr
    parsePipeRest left

  partial def parsePipeRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let hasPipe ← tryToken .pipeGt
    if hasPipe then
      let right ← parseOrExpr
      parsePipeRest (Expr.binOp pos .pipe left right)
    else
      return left

  -- Or expression
  partial def parseOrExpr : Parser Expr := do
    let left ← parseAndExpr
    parseOrRest left

  partial def parseOrRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let hasOr ← tryToken .pipeOr
    if hasOr then
      let right ← parseAndExpr
      parseOrRest (Expr.binOp pos .or left right)
    else
      return left

  -- And expression
  partial def parseAndExpr : Parser Expr := do
    let left ← parseCompareExpr
    parseAndRest left

  partial def parseAndRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let hasAnd ← tryToken .ampAmp
    if hasAnd then
      let right ← parseCompareExpr
      parseAndRest (Expr.binOp pos .and left right)
    else
      return left

  -- Comparison expression
  partial def parseCompareExpr : Parser Expr := do
    let left ← parseConcatExpr
    parseCompareRest left

  partial def parseCompareRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let tok? ← peek?
    match tok? with
    | some .eqEq =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .eq left right
    | some .neq =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .ne left right
    | some .langle =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .lt left right
    | some .le =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .le left right
    | some .rangle =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .gt left right
    | some .ge =>
      advance
      let right ← parseConcatExpr
      return Expr.binOp pos .ge left right
    | _ => return left

  -- Concat expression (right associative)
  partial def parseConcatExpr : Parser Expr := do
    let left ← parseAddExpr
    parseConcatRest left

  partial def parseConcatRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let hasConcat ← tryToken .plusPlus
    if hasConcat then
      let right ← parseConcatExpr  -- Right associative
      return Expr.binOp pos .concat left right
    else
      return left

  -- Additive expression
  partial def parseAddExpr : Parser Expr := do
    let left ← parseMulExpr
    parseAddRest left

  partial def parseAddRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let tok? ← peek?
    match tok? with
    | some .plus =>
      advance
      let right ← parseMulExpr
      parseAddRest (Expr.binOp pos .add left right)
    | some .minus =>
      advance
      let right ← parseMulExpr
      parseAddRest (Expr.binOp pos .sub left right)
    | _ => return left

  -- Multiplicative expression
  partial def parseMulExpr : Parser Expr := do
    let left ← parseUnaryExpr
    parseMulRest left

  partial def parseMulRest (left : Expr) : Parser Expr := do
    let pos := left.pos
    let tok? ← peek?
    match tok? with
    | some .star =>
      advance
      let right ← parseUnaryExpr
      parseMulRest (Expr.binOp pos .mul left right)
    | some .slash =>
      advance
      let right ← parseUnaryExpr
      parseMulRest (Expr.binOp pos .div left right)
    | _ => return left

  -- Unary expression
  partial def parseUnaryExpr : Parser Expr := do
    let pos ← currentPos
    let tok? ← peek?
    match tok? with
    | some .minus =>
      advance
      let e ← parseUnaryExpr
      return Expr.unaryOp pos .neg e
    | some .kNot =>
      advance
      let e ← parseUnaryExpr
      return Expr.unaryOp pos .not e
    | _ => parseAppExpr

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
      match sepBy parseArg (expect .comma) s with
      | .ok (args, s') =>
        match expect .rparen s' with
        | .ok (_, s'') =>
          -- Apply arguments as curried: f(x, y) becomes (f x) y
          let result := args.foldl (fun acc (arg, isCov) => Expr.app pos acc arg isCov) base
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
          | .ok (arg, s') => parsePostfixRest (Expr.app pos base arg false) s'
          | .error _ => .ok (base, s)
      | none => .ok (base, s)
    | some .tilde =>
      let s := s.advance
      match parseAtomExpr s with
      | .ok (arg, s') => parsePostfixRest (Expr.app pos base arg true) s'
      | .error msg => .error msg
    | _ =>
      -- Try space-separated application with atom only (no field access)
      match parseAtomExpr s with
      | .ok (arg, s') =>
        parsePostfixRest (Expr.app pos base arg false) s'
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
    -- Extern: @("scheme", "foo") | @...
    | some .at_ =>
      match parseExternEntries s with
      | .ok (info, s') => .ok (Expr.extern pos info, s')
      | .error msg => .error msg
    -- Hash (self-reference) for codata
    | some .hash => .ok (Expr.hash pos, s.advance)
    -- Variable
    | some (.ident id) => .ok (Expr.var pos id, s.advance)
    -- Constructor expression: Con or Con(args)
    | some (.conId conName) =>
      let s := s.advance  -- skip constructor name
      match s.peekToken? with
      | some .lparen =>
        -- Con(args...)
        let s := s.advance  -- skip (
        match s.peekToken? with
        | some .rparen =>
          -- Con() - nullary constructor with explicit parens
          .ok (Expr.con pos conName [], s.advance)
        | _ =>
          match sepBy1 parseExpr (expect .comma) s with
          | .ok (args, s') =>
            match expect .rparen s' with
            | .ok (_, s'') => .ok (Expr.con pos conName args, s'')
            | .error msg => .error msg
          | .error msg => .error msg
      | _ =>
        -- Con - nullary constructor
        .ok (Expr.con pos conName [], s)
    -- Lambda
    | some .backslash => parseLambda s
    -- Let
    | some .kLet => parseLet s
    -- Match
    | some .kMatch => parseMatch s
    -- If
    | some .kIf => parseIf s
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
  partial def parseLambda : Parser Expr := do
    let pos ← currentPos
    advance  -- skip \
    let params ← many1 parseParam
    let _ ← expect .fatArrow
    let body ← parseExpr
    -- Desugar multi-param lambda to nested single-param lambdas
    return params.foldr (fun (param, isCov) acc => Expr.lam pos param isCov acc) body

  -- Parse optional type annotation (: Type)
  partial def parseOptionalTypeAnn : Parser (Option Ty) := optional do
    let _ ← expect .colon
    parseType

  -- Parse let: let x = e in body or let rec f = e in body
  partial def parseLet : Parser Expr := do
    let pos ← currentPos
    advance  -- skip 'let'
    let tok? ← peek?
    match tok? with
    | some .kRec =>
      advance
      let name ← expectIdent
      let tyOpt ← parseOptionalTypeAnn
      let _ ← expect .eq
      let value ← parseExpr
      let _ ← expect .kIn
      let body ← parseExpr
      return Expr.letRec pos name tyOpt value body
    | _ =>
      let name ← expectIdent
      let tyOpt ← parseOptionalTypeAnn
      let _ ← expect .eq
      let value ← parseExpr
      let _ ← expect .kIn
      let body ← parseExpr
      return Expr.let_ pos name tyOpt value body

  -- Parse match: match e { | p => e }
  partial def parseMatch : Parser Expr := do
    let pos ← currentPos
    advance  -- skip 'match'
    let scrutinee ← parseMatchScrutinee
    let _ ← expect .lbrace
    let cases ← parseMatchCases
    let _ ← expect .rbrace
    return Expr.match_ pos scrutinee cases

  -- Parse match scrutinee (stops at { to avoid consuming match block)
  partial def parseMatchScrutinee : Parser Expr := do
    let base ← parseAtomExpr
    parseMatchScrutineeRest base

  -- Like parsePostfixRest but stops when seeing { (for match scrutinee)
  partial def parseMatchScrutineeRest (base : Expr) : Parser Expr := fun s =>
    let pos := base.pos
    match s.peekToken?, s.peekN 1 with
    -- Field access: .field
    | some .dot, some ptok =>
      match ptok.token with
      | .ident field =>
        let s := s.advance.advance
        parseMatchScrutineeRest (Expr.field pos base field) s
      | _ => .ok (base, s)
    -- Parenthesized application: f(x) or f(x, y)
    | some .lparen, _ =>
      let s := s.advance
      match sepBy parseArg (expect .comma) s with
      | .ok (args, s') =>
        match expect .rparen s' with
        | .ok (_, s'') =>
          let result := args.foldl (fun acc (arg, isCov) => Expr.app pos acc arg isCov) base
          parseMatchScrutineeRest result s''
        | .error msg => .error msg
      | .error msg => .error msg
    -- Stop at { (match block delimiter)
    | some .lbrace, _ => .ok (base, s)
    -- Space-separated application (but not with { which starts match block)
    | _, _ =>
      match s.peekToken? with
      | some .lbrace => .ok (base, s)
      | some .tilde =>
        let s := s.advance
        match parseAtomExpr s with
        | .ok (arg, s') => parseMatchScrutineeRest (Expr.app pos base arg true) s'
        | .error msg => .error msg
      | _ =>
        match parseAtomExpr s with
        | .ok (arg, s') =>
          parseMatchScrutineeRest (Expr.app pos base arg false) s'
        | .error _ => .ok (base, s)

  -- Parse match cases: | is prefix (can start any case), , is suffix (separates cases)
  -- Grammar: (|? pat => expr) (, |? pat => expr)* ,?
  partial def parseMatchCases : Parser (List (Pat × Expr)) := fun s =>
    match parseFirstMatchCase s with
    | .ok (first, s') => parseRestMatchCases [first] s'
    | .error msg => .error msg

  -- First case: optional leading |, no leading ,
  partial def parseFirstMatchCase : Parser (Pat × Expr) := do
    let _ ← optional (expect .pipe)  -- Optional leading pipe
    let pat ← parsePattern
    let _ ← expect .fatArrow
    let body ← parseExpr
    return (pat, body)

  -- Rest of cases: , as separator, optional | as prefix, trailing , allowed
  partial def parseRestMatchCases (acc : List (Pat × Expr)) : Parser (List (Pat × Expr)) := fun s =>
    match s.peekToken? with
    | some .rbrace => .ok (acc.reverse, s)  -- End of cases
    | some .comma =>
      let s' := s.advance  -- consume ,
      -- Check for trailing comma (no more cases)
      match s'.peekToken? with
      | some .rbrace => .ok (acc.reverse, s')  -- Trailing comma is OK
      | _ =>
        -- Parse next case with optional leading |
        let s'' := match s'.peekToken? with
          | some .pipe => s'.advance
          | _ => s'
        match parsePattern s'' with
        | .ok (pat, s''') =>
          match expect .fatArrow s''' with
          | .ok (_, s'''') =>
            match parseExpr s'''' with
            | .ok (body, s''''') => parseRestMatchCases ((pat, body) :: acc) s'''''
            | .error msg => .error msg
          | .error msg => .error msg
        | .error msg => .error msg
    | some .pipe =>
      -- | as separator (alternative to ,)
      let s' := s.advance
      match parsePattern s' with
      | .ok (pat, s'') =>
        match expect .fatArrow s'' with
        | .ok (_, s''') =>
          match parseExpr s''' with
          | .ok (body, s'''') => parseRestMatchCases ((pat, body) :: acc) s''''
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | _ => .error s!"expected } or case separator but found {s.peekToken?}"

  -- Parse if: if c then t else f
  partial def parseIf : Parser Expr := do
    let pos ← currentPos
    advance  -- skip 'if'
    let cond ← parseExpr
    let _ ← expect .kThen
    let thenBranch ← parseExpr
    let _ ← expect .kElse
    let elseBranch ← parseExpr
    return Expr.if_ pos cond thenBranch elseBranch

  -- Parse label: label name { body }
  partial def parseLabel : Parser Expr := do
    let pos ← currentPos
    advance  -- skip 'label'
    let name ← expectIdent
    let _ ← expect .lbrace
    let body ← parseExpr
    let _ ← expect .rbrace
    return Expr.label pos name body

  -- Parse goto: goto(expr, expr)
  partial def parseGoto : Parser Expr := do
    let pos ← currentPos
    advance  -- skip 'goto'
    let _ ← expect .lparen
    let value ← parseExpr
    let _ ← expect .comma
    let continuation ← parseExpr
    let _ ← expect .rparen
    return Expr.goto pos value continuation

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

  -- Parse codata block: | is prefix (can start any clause), , is suffix (separates clauses)
  -- Grammar: (|? pats # copat => expr) (, |? pats # copat => expr)* ,?
  partial def parseCodataBlock : Parser (List (List Pat × Copattern × Expr)) := fun s =>
    match parseFirstCodataClause s with
    | .ok (first, s') => parseRestCodataClauses [first] s'
    | .error msg => .error msg

  -- First clause: optional leading |, no leading ,
  partial def parseFirstCodataClause : Parser (List Pat × Copattern × Expr) := fun s =>
    let s := match s.peekToken? with
      | some .pipe => s.advance  -- Optional leading pipe
      | _ => s
    parseCodataClauseBody s

  -- Rest of clauses: , as separator, optional | as prefix, trailing , allowed
  partial def parseRestCodataClauses (acc : List (List Pat × Copattern × Expr))
      : Parser (List (List Pat × Copattern × Expr)) := fun s =>
    match s.peekToken? with
    | some .rbrace => .ok (acc.reverse, s)  -- End of clauses
    | some .comma =>
      let s' := s.advance  -- consume ,
      -- Check for trailing comma
      match s'.peekToken? with
      | some .rbrace => .ok (acc.reverse, s')  -- Trailing comma is OK
      | _ =>
        -- Parse next clause with optional leading |
        let s'' := match s'.peekToken? with
          | some .pipe => s'.advance
          | _ => s'
        match parseCodataClauseBody s'' with
        | .ok (cl, s''') => parseRestCodataClauses (cl :: acc) s'''
        | .error msg => .error msg
    | some .pipe =>
      -- | as separator
      let s' := s.advance
      match parseCodataClauseBody s' with
      | .ok (cl, s'') => parseRestCodataClauses (cl :: acc) s''
      | .error msg => .error msg
    | _ => .error s!"expected }} or clause separator but found {s.peekToken?}"

  -- Parse the body of a codata clause (without leading separator)
  partial def parseCodataClauseBody : Parser (List Pat × Copattern × Expr) := fun s =>
    -- Note: leading pipe already consumed by caller
    let s := s
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

  -- Parse extern body: = @("backend", "symbol") | @("backend2", "symbol2")
  partial def parseExternBody : Parser (Option ExternInfo) := fun s =>
    match expect .eq s with
    | .ok (_, s') =>
      match s'.peekToken? with
      | some .at_ =>
        match parseExternEntries s' with
        | .ok (entries, s'') => .ok (some entries, s'')
        | .error msg => .error msg
      | _ => .ok (none, s) -- Not an extern body, let caller handle '='
    | .error _ => .ok (none, s)

  partial def parseExternEntries : Parser ExternInfo :=
    sepBy1 parseExternEntry (expect .pipe)

  partial def parseExternEntry : Parser ExternEntry := do
    let _ ← expect .at_
    let _ ← expect .lparen
    let backend ← expectString
    let _ ← expect .comma
    let symbol ← expectString
    let _ ← expect .comma
    let n ← expectInt
    let _ ← expect .rparen
    return { backend, symbol, arity := n.toNat }

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

  -- Parse data declaration: data T a b = ...
  partial def parseDataDecl : Parser Decl := do
    advance  -- skip 'data'
    let name ← expectConId
    let tyParams ← many expectIdent
    -- Check for extern body first
    let externOpt ← parseExternBody
    match externOpt with
    | some extern => return .data name tyParams [] (some extern)
    | none =>
      let _ ← expect .eq
      let constrs ← parseConstructors
      return .data name tyParams constrs none

  partial def parseConstructors : Parser (List ConDecl) := many1 parseConstructor

  partial def parseConstructor : Parser ConDecl := do
    let _ ← expect .pipe
    let name ← expectConId
    let args ← many parseAtomType
    return { name := name, args := args }

  -- Parse codata declaration: codata T a { ... }
  partial def parseCodataDecl : Parser Decl := do
    advance  -- skip 'codata'
    let name ← expectConId
    let tyParams ← many expectIdent
    -- Check for extern body
    let externOpt ← parseExternBody
    match externOpt with
    | some extern =>
      -- Extern codata is opaque (no observation signatures)
      return .codata name tyParams [] (some extern)
    | none =>
      let _ ← expect .lbrace
      let sigs ← parseCodataSigs
      let _ ← expect .rbrace
      return .codata name tyParams sigs none

  partial def parseCodataSigs : Parser (List CopatSig) := many parseCodataSig

  partial def parseCodataSig : Parser CopatSig := do
    let _ ← expect .hash
    let copat ← parseCopattern
    let _ ← expect .colon
    let ty ← parseType
    return { accessors := copat, ty := ty }

  -- Parse function name: identifier, constructor, or operator in parens
  partial def parseDefName : Parser Ident := do
    let tok? ← peek?
    match tok? with
    | some .lparen =>
      advance
      let op ← expectIdent
      let _ ← expect .rparen
      return op
    | some (.ident _) => expectIdent
    | some (.conId _) => expectConId
    | _ => throw "expected function name"

  -- Parse def declaration
  partial def parseDefDecl : Parser Decl := do
    advance  -- skip 'def'
    let name ← parseDefName
    let _ ← expect .colon
    let ty ← parseType
    let tok? ← peek?
    match tok? with
    | some .eq =>
      advance
      let body ← parseExpr
      return .def_ name ty (some body)
    | some .pipe =>
      let clauses ← parseDefClauses
      return .defPat name ty clauses
    | some .lbrace =>
      let clauses ← parseDefClauses
      return .defPat name ty clauses
    | some tok => throw s!"expected '=' or '|' but found {tok}"
    | none => throw "unexpected EOF"

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
  partial def parseModuleDecl : Parser Decl := do
    advance  -- skip 'module'
    let name ← expectConId
    let _ ← expect .kWhere
    let decls ← parseDecls
    let _ ← expect .kEnd
    return .module_ name decls

  -- Parse import declaration
  partial def parseImportDecl : Parser Decl := do
    advance  -- skip 'import'
    let name ← expectConId
    let tok? ← peek?
    match tok? with
    | some .lparen =>
      -- import M (a, b)
      advance
      let items ← sepBy expectIdent (expect .comma)
      let _ ← expect .rparen
      return .import_ name (some items) none
    | some .kAs =>
      -- import M as N
      advance
      let alias ← expectConId
      return .import_ name none (some alias)
    | _ => return .import_ name none none

  -- Parse infix declaration
  partial def parseInfixDecl (rightAssoc : Bool) : Parser Decl := do
    advance  -- skip 'infix'/'infixr'/'infixl'
    let prec ← expectInt
    let op ← expectIdent
    return .infix_ prec.toNat rightAssoc op

  partial def parseDecls : Parser (List Decl) := many parseDecl

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
