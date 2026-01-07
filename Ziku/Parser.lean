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

-- Default position for end-of-file (no tokens remaining)
def eofPos : SourcePos := { line := 0, col := 0 }

def ParseState.currentPos (s : ParseState) : SourcePos :=
  match s.peek? with
  | some tok => tok.pos
  | none => eofPos

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
      -- Record type: { x : ty, ... } or { x : ty | r } for row polymorphism
      let s := s.advance
      match parseRecordTypeFields s with
      | .ok (fields, s') =>
        -- Check for row tail: | ident
        match tryToken .pipe s' with
        | .ok (hasPipe, s'') =>
          if hasPipe then
            -- Open record with row variable: { x : ty | r }
            match expectIdent s'' with
            | .ok (rowVar, s''') =>
              match expect .rbrace s''' with
              | .ok (_, s'''') => .ok (.record pos fields (some (.var pos rowVar)), s'''')
              | .error msg => .error msg
            | .error msg => .error msg
          else
            -- Closed record: { x : ty }
            match expect .rbrace s'' with
            | .ok (_, s''') => .ok (.record pos fields none, s''')
            | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | some .lbracket =>
      -- Variant type: [Con1 ty1 ty2 | Con2 | r] for row polymorphic variants
      let s := s.advance
      match parseVariantTypeCases s with
      | .ok (cases, s') =>
        -- Check for row tail: | ident (lowercase = row variable)
        match tryToken .pipe s' with
        | .ok (hasPipe, s'') =>
          if hasPipe then
            -- Check if it's a row variable (lowercase) or another constructor (uppercase)
            match s''.peekToken? with
            | some (.ident rowVar) =>
              -- Open variant with row variable: [Con | r]
              let s''' := s''.advance
              match expect .rbracket s''' with
              | .ok (_, s'''') => .ok (.variant pos cases (some (.var pos rowVar)), s'''')
              | .error msg => .error msg
            | some (.conId _) =>
              -- Another constructor case, continue parsing
              match parseVariantTypeCases s'' with
              | .ok (moreCases, s''') =>
                match tryToken .pipe s''' with
                | .ok (hasPipe', s'''') =>
                  if hasPipe' then
                    match expectIdent s'''' with
                    | .ok (rowVar, s''''') =>
                      match expect .rbracket s''''' with
                      | .ok (_, s'''''') => .ok (.variant pos (cases ++ moreCases) (some (.var pos rowVar)), s'''''')
                      | .error msg => .error msg
                    | .error msg => .error msg
                  else
                    match expect .rbracket s'''' with
                    | .ok (_, s''''') => .ok (.variant pos (cases ++ moreCases) none, s''''')
                    | .error msg => .error msg
                | .error msg => .error msg
              | .error msg => .error msg
            | _ =>
              -- Closed variant: [Con]
              match expect .rbracket s'' with
              | .ok (_, s''') => .ok (.variant pos cases none, s''')
              | .error msg => .error msg
          else
            -- Closed variant: [Con]
            match expect .rbracket s'' with
            | .ok (_, s''') => .ok (.variant pos cases none, s''')
            | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | some .tilde =>
      let s := s.advance
      match parseAtomType s with
      | .ok (ty, s') => .ok (.tilde pos ty, s')
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

  -- Parse variant type cases: Con1 ty1 ty2 | Con2 ty3 | ...
  -- Returns list of (constructor name, argument types)
  partial def parseVariantTypeCases : Parser (List (Ident × List Ty)) :=
    sepBy1 parseVariantTypeCase (expect .pipe)

  partial def parseVariantTypeCase : Parser (Ident × List Ty) := fun s =>
    match s.peekToken? with
    | some (.conId name) =>
      let s := s.advance
      -- Parse argument types (atomic types only, until | or ])
      match parseVariantArgTypes s with
      | .ok (argTys, s') => .ok ((name, argTys), s')
      | .error msg => .error msg
    | some tok => .error s!"expected constructor name but found {tok}"
    | none => .error "expected constructor name but found EOF"

  -- Parse argument types for a variant constructor (stops at | or ])
  partial def parseVariantArgTypes : Parser (List Ty) := fun s =>
    match s.peekToken? with
    | some .pipe => .ok ([], s)
    | some .rbracket => .ok ([], s)
    | some _ =>
      match parseAtomType s with
      | .ok (ty, s') =>
        match parseVariantArgTypes s' with
        | .ok (rest, s'') => .ok (ty :: rest, s'')
        | .error msg => .error msg
      | .error _ => .ok ([], s)  -- No more types, return empty
    | none => .ok ([], s)

  -- Parse a parameter: ident or ~ident
  partial def parseParam : Parser (Ident × Bool) := fun s =>
    match s.peekToken? with
    | some .tilde =>
      let s := s.advance
      match expectIdent s with
      | .ok (id, s') => .ok ((id, true), s')
      | .error msg => .error msg
    | _ =>
      match expectIdent s with
      | .ok (id, s') => .ok ((id, false), s')
      | .error msg => .error msg

  -- Parse an argument: expr or ~expr
  partial def parseArg : Parser (Expr × Bool) := fun s =>
    match s.peekToken? with
    | some .tilde =>
      let s := s.advance
      match parseAtomExpr s with
      | .ok (e, s') => .ok ((e, true), s')
      | .error msg => .error msg
    | _ =>
      match parseExpr s with
      | .ok (e, s') => .ok ((e, false), s')
      | .error msg => .error msg

  -- Parse an argument (for parseExprStop): expr or ~expr
  partial def parseArgStop : Parser (Expr × Bool) := fun s =>
    match s.peekToken? with
    | some .tilde =>
      let s := s.advance
      match parseAtomExprStop s with
      | .ok (e, s') => .ok ((e, true), s')
      | .error msg => .error msg
    | _ =>
      match parseExprStop s with
      | .ok (e, s') => .ok ((e, false), s')
      | .error msg => .error msg

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
    -- Bare identifier as space-separated argument
    | some (.ident id) => .ok (.apply id, s.advance)
    | some tok => .error s!"expected '.', '(' or identifier but found {tok}"
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
    match many1 parseParam s with
    | .ok (params, s') =>
      match expect .fatArrow s' with
      | .ok (_, s'') =>
        match parseExpr s'' with
        | .ok (body, s''') =>
          -- Desugar multi-param lambda to nested single-param lambdas
          let result := params.foldr (fun (param, isCov) acc => Expr.lam pos param isCov acc) body
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

  -- Parse match: match e { | p => e }
  partial def parseMatch : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'match'
    match parseMatchScrutinee s with
    | .ok (scrutinee, s') =>
      match expect .lbrace s' with
      | .ok (_, s'') =>
        match parseMatchCases s'' with
        | .ok (cases, s''') =>
          match expect .rbrace s''' with
          | .ok (_, s'''') => .ok (Expr.match_ pos scrutinee cases, s'''')
          | .error msg => .error msg
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

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
  partial def parseFirstMatchCase : Parser (Pat × Expr) := fun s =>
    let s' := match s.peekToken? with
      | some .pipe => s.advance  -- Optional leading pipe
      | _ => s
    match parsePattern s' with
    | .ok (pat, s'') =>
      match expect .fatArrow s'' with
      | .ok (_, s''') =>
        match parseExpr s''' with
        | .ok (body, s'''') => .ok ((pat, body), s'''')
        | .error msg => .error msg
      | .error msg => .error msg
    | .error msg => .error msg

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

  -- Parse goto: goto(expr, expr)
  partial def parseGoto : Parser Expr := fun s =>
    let pos := s.currentPos
    let s := s.advance  -- skip 'goto'
    match expect .lparen s with
    | .ok (_, s') =>
      match parseExpr s' with
      | .ok (value, s'') =>
        match expect .comma s'' with
        | .ok (_, s''') =>
          match parseExpr s''' with
          | .ok (continuation, s'''') =>
            match expect .rparen s'''' with
            | .ok (_, s''''') => .ok (Expr.goto pos value continuation, s''''')
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
      match sepBy parseArgStop (expect .comma) s with
      | .ok (args, s') =>
        match expect .rparen s' with
        | .ok (_, s'') =>
          let result := args.foldl (fun acc (arg, isCov) => Expr.app pos acc arg isCov) base
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
          | .ok (arg, s') => parsePostfixRestStop (Expr.app pos base arg false) s'
          | .error _ => .ok (base, s)
      | none => .ok (base, s)
    | some .tilde =>
      let s := s.advance
      match parseAtomExprStop s with
      | .ok (arg, s') => parsePostfixRestStop (Expr.app pos base arg true) s'
      | .error msg => .error msg
    | _ =>
      match parseAtomExprStop s with
      | .ok (arg, s') =>
        parsePostfixRestStop (Expr.app pos base arg false) s'
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
