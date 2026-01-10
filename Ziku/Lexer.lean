import Ziku.Syntax

namespace Ziku

/-!
# Ziku Lexer

This module implements a lexer (tokenizer) for the Ziku programming language.
-/

-- Token types
inductive Token where
  -- Literals
  | int     : Int → Token
  | float   : Float → Token
  | string  : String → Token
  | char    : Char → Token
  -- Identifiers and keywords
  | ident   : String → Token
  | conId   : String → Token    -- Constructor identifier (starts with uppercase)
  -- Keywords
  | kData   : Token     -- data
  | kCodata : Token     -- codata
  | kDef    : Token     -- def
  | kLet    : Token     -- let
  | kRec    : Token     -- rec
  | kIn     : Token     -- in
  | kMatch  : Token     -- match
  | kWith   : Token     -- with
  | kEnd    : Token     -- end
  | kIf     : Token     -- if
  | kThen   : Token     -- then
  | kElse   : Token     -- else
  | kTrue   : Token     -- true
  | kFalse  : Token     -- false
  | kNot    : Token     -- not
  | kForall : Token     -- forall
  | kModule : Token     -- module
  | kWhere  : Token     -- where
  | kImport : Token     -- import
  | kAs     : Token     -- as
  | kInfix  : Token     -- infix
  | kInfixr : Token     -- infixr
  | kInfixl : Token     -- infixl
  | kLabel  : Token     -- label
  | kGoto   : Token     -- goto
  -- Punctuation
  | lparen  : Token     -- (
  | rparen  : Token     -- )
  | lbrace  : Token     -- {
  | rbrace  : Token     -- }
  | langle  : Token     -- <
  | rangle  : Token     -- >
  | lbracket : Token    -- [
  | rbracket : Token    -- ]
  | comma   : Token     -- ,
  | dot     : Token     -- .
  | colon   : Token     -- :
  | semi    : Token     -- ;
  | pipe    : Token     -- |
  | hash    : Token     -- #
  | underscore : Token  -- _
  -- Operators
  | arrow   : Token     -- ->
  | fatArrow : Token    -- =>
  | backslash : Token   -- \
  | eq      : Token     -- =
  | eqEq    : Token     -- ==
  | neq     : Token     -- !=
  | lt      : Token     -- <
  | le      : Token     -- <=
  | gt      : Token     -- >
  | ge      : Token     -- >=
  | plus    : Token     -- +
  | minus   : Token     -- -
  | star    : Token     -- *
  | slash   : Token     -- /
  | ampAmp  : Token     -- &&
  | pipeOr  : Token     -- ||
  | plusPlus : Token    -- ++
  | pipeGt  : Token     -- |>
  | at_     : Token     -- @ (constructor prefix)
  | tilde   : Token     -- ~ (covalue marker)
  -- Special
  | eof     : Token
  deriving Repr, BEq

def Token.toString : Token → String
  | .int n => s!"int({n})"
  | .float f => s!"float({f})"
  | .string s => s!"string(\"{s}\")"
  | .char c => s!"char('{c}')"
  | .ident s => s!"ident({s})"
  | .conId s => s!"conId({s})"
  | .kData => "data"
  | .kCodata => "codata"
  | .kDef => "def"
  | .kLet => "let"
  | .kRec => "rec"
  | .kIn => "in"
  | .kMatch => "match"
  | .kWith => "with"
  | .kEnd => "end"
  | .kIf => "if"
  | .kThen => "then"
  | .kElse => "else"
  | .kTrue => "true"
  | .kFalse => "false"
  | .kNot => "not"
  | .kForall => "forall"
  | .kModule => "module"
  | .kWhere => "where"
  | .kImport => "import"
  | .kAs => "as"
  | .kInfix => "infix"
  | .kInfixr => "infixr"
  | .kInfixl => "infixl"
  | .kLabel => "label"
  | .kGoto => "goto"
  | .lparen => "("
  | .rparen => ")"
  | .lbrace => "{"
  | .rbrace => "}"
  | .langle => "<"
  | .rangle => ">"
  | .lbracket => "["
  | .rbracket => "]"
  | .comma => ","
  | .dot => "."
  | .colon => ":"
  | .semi => ";"
  | .pipe => "|"
  | .hash => "#"
  | .underscore => "_"
  | .tilde => "~"
  | .arrow => "->"
  | .fatArrow => "=>"
  | .backslash => "\\"
  | .eq => "="
  | .eqEq => "=="
  | .neq => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .plus => "+"
  | .minus => "-"
  | .star => "*"
  | .slash => "/"
  | .ampAmp => "&&"
  | .pipeOr => "||"
  | .plusPlus => "++"
  | .pipeGt => "|>"
  | .at_ => "@"
  | .eof => "EOF"

instance : ToString Token := ⟨Token.toString⟩

-- Positioned token
structure PosToken where
  token : Token
  pos : SourcePos
  deriving Repr

-- Lexer state
structure LexState where
  input : String
  chars : List Char  -- Character list for proper UTF-8 handling
  pos : Nat := 0     -- Position in character list (not bytes)
  line : Nat := 1
  col : Nat := 1
  deriving Repr

def LexState.eof (s : LexState) : Bool :=
  s.pos >= s.chars.length

def LexState.peek? (s : LexState) : Option Char :=
  s.chars[s.pos]?

def LexState.peekN (s : LexState) (n : Nat) : Option Char :=
  s.chars[s.pos + n]?

def LexState.advance (s : LexState) : LexState :=
  match s.peek? with
  | some '\n' => { s with pos := s.pos + 1, line := s.line + 1, col := 1 }
  | some _ => { s with pos := s.pos + 1, col := s.col + 1 }
  | none => s

def LexState.advanceN (s : LexState) (n : Nat) : LexState :=
  match n with
  | 0 => s
  | n + 1 => s.advance.advanceN n

def LexState.sourcePos (s : LexState) : SourcePos :=
  { line := s.line, col := s.col }

abbrev Lexer α := LexState → Except String (α × LexState)

-- Keywords map
def keywords : List (String × Token) :=
  [ ("data", .kData), ("codata", .kCodata), ("def", .kDef)
  , ("let", .kLet), ("rec", .kRec), ("in", .kIn)
  , ("match", .kMatch), ("with", .kWith), ("end", .kEnd)
  , ("if", .kIf), ("then", .kThen), ("else", .kElse)
  , ("true", .kTrue), ("false", .kFalse), ("not", .kNot)
  , ("forall", .kForall), ("module", .kModule), ("where", .kWhere)
  , ("import", .kImport), ("as", .kAs)
  , ("infix", .kInfix), ("infixr", .kInfixr), ("infixl", .kInfixl)
  , ("label", .kLabel), ("goto", .kGoto)
  ]

def lookupKeyword (s : String) : Option Token :=
  (keywords.find? (fun (k, _) => k == s)).map Prod.snd

-- Skip whitespace and comments
partial def skipWhitespaceAndComments (s : LexState) : LexState :=
  let s := skipWs s
  match s.peek?, s.peekN 1 with
  | some '-', some '-' =>
    -- Single line comment
    let s := skipLine s
    skipWhitespaceAndComments s
  | some '{', some '-' =>
    -- Multi-line comment
    let s := skipBlockComment (s.advanceN 2) 1
    skipWhitespaceAndComments s
  | _, _ => s
where
  skipWs (s : LexState) : LexState :=
    match s.peek? with
    | some c => if c.isWhitespace then skipWs s.advance else s
    | none => s
  skipLine (s : LexState) : LexState :=
    match s.peek? with
    | some '\n' => s.advance
    | some _ => skipLine s.advance
    | none => s
  skipBlockComment (s : LexState) (depth : Nat) : LexState :=
    if depth == 0 then s
    else
      match s.peek?, s.peekN 1 with
      | some '{', some '-' => skipBlockComment (s.advanceN 2) (depth + 1)
      | some '-', some '}' => skipBlockComment (s.advanceN 2) (depth - 1)
      | some _, _ => skipBlockComment s.advance depth
      | none, _ => s  -- Unclosed comment, will be caught later

-- Lex a number: integer or float
partial def lexNumber (s : LexState) : Except String (Token × LexState) := do
  let startPos := s.sourcePos
  -- Optional leading minus for negative numbers
  let (negative, s) := match s.peek? with
    | some '-' => (true, s.advance)
    | _ => (false, s)
  -- Integral part (at least one digit)
  let (intDigits, s) := lexDigits s ""
  if intDigits.isEmpty then
    .error s!"expected digit at {startPos.line}:{startPos.col}"
  else
    match s.peek?, s.peekN 1 with
    -- Float if we see a dot followed by a digit
    | some '.', some c2 =>
      if c2.isDigit then
        let s := s.advance -- skip '.'
        let (fracDigits, s) := lexDigits s ""
        if fracDigits.isEmpty then
          .error s!"expected digit after '.' at {s.sourcePos.line}:{s.sourcePos.col}"
        else
          let intVal := stringDigitsToFloat intDigits
          let fracVal := stringFracToFloat fracDigits
          let f := (if negative then -1.0 else 1.0) * (intVal + fracVal)
          .ok (.float f, s)
      else
        -- It's just an int followed by '.' (handled elsewhere as dot token)
        let n := intDigits.toInt!
        .ok (.int (if negative then -n else n), s)
    | _, _ =>
      let n := intDigits.toInt!
      .ok (.int (if negative then -n else n), s)
where
  lexDigits (s : LexState) (acc : String) : String × LexState :=
    match s.peek? with
    | some c =>
      if c.isDigit then lexDigits s.advance (acc.push c)
      else (acc, s)
    | none => (acc, s)

  -- Convert a string of decimal digits to Float
  stringDigitsToFloat (ds : String) : Float :=
    let rec go (cs : List Char) (acc : Float) : Float :=
      match cs with
      | [] => acc
      | c :: cs' =>
        let d : Float := (Char.toNat c - Char.toNat '0') |>.toFloat
        go cs' (acc * 10.0 + d)
    go ds.toList 0.0

  -- Convert fractional digits "abc" into value abc / 10^len as Float
  stringFracToFloat (ds : String) : Float :=
    let numer := stringDigitsToFloat ds
    let rec pow10 (n : Nat) (acc : Float) : Float :=
      match n with
      | 0 => acc
      | n+1 => pow10 n (acc * 10.0)
    let denom := pow10 ds.length 1.0
    numer / denom

-- Lex an identifier or keyword
partial def lexIdent (s : LexState) : Except String (Token × LexState) := do
  let (chars, s) := lexIdentChars s []
  let str := String.ofList chars.reverse
  match lookupKeyword str with
  | some tok => .ok (tok, s)
  | none =>
    -- Check if it's a constructor (starts with uppercase)
    match chars.getLast? with
    | some c =>
      if c.isUpper then .ok (.conId str, s)
      else .ok (.ident str, s)
    | none => .error "empty identifier"
where
  lexIdentChars (s : LexState) (acc : List Char) : List Char × LexState :=
    match s.peek? with
    | some c =>
      if c.isAlphanum || c == '_' || c == '\'' then
        lexIdentChars s.advance (c :: acc)
      else (acc, s)
    | none => (acc, s)

-- Lex a string literal
partial def lexString (s : LexState) : Except String (Token × LexState) := do
  let startPos := s.sourcePos
  let s := s.advance  -- skip opening "
  let (chars, s) ← lexStringChars s []
  match s.peek? with
  | some '"' => .ok (.string (String.ofList chars.reverse), s.advance)
  | _ => .error s!"unterminated string at {startPos.line}:{startPos.col}"
where
  lexStringChars (s : LexState) (acc : List Char) : Except String (List Char × LexState) :=
    match s.peek? with
    | some '"' => .ok (acc, s)
    | some '\\' =>
      match s.peekN 1 with
      | some 'n' => lexStringChars (s.advanceN 2) ('\n' :: acc)
      | some 't' => lexStringChars (s.advanceN 2) ('\t' :: acc)
      | some 'r' => lexStringChars (s.advanceN 2) ('\r' :: acc)
      | some '\\' => lexStringChars (s.advanceN 2) ('\\' :: acc)
      | some '"' => lexStringChars (s.advanceN 2) ('"' :: acc)
      | some c => lexStringChars (s.advanceN 2) (c :: acc)
      | none => .error "unterminated escape sequence"
    | some c => lexStringChars s.advance (c :: acc)
    | none => .error "unterminated string"

-- Lex a character literal
def lexChar (s : LexState) : Except String (Token × LexState) := do
  let startPos := s.sourcePos
  let s := s.advance  -- skip opening '
  let (c, s) ← match s.peek? with
    | some '\\' =>
      match s.peekN 1 with
      | some 'n' => .ok ('\n', s.advanceN 2)
      | some 't' => .ok ('\t', s.advanceN 2)
      | some 'r' => .ok ('\r', s.advanceN 2)
      | some '\\' => .ok ('\\', s.advanceN 2)
      | some '\'' => .ok ('\'', s.advanceN 2)
      | some c => .ok (c, s.advanceN 2)
      | none => .error "unterminated escape sequence"
    | some c => .ok (c, s.advance)
    | none => .error s!"unterminated char literal at {startPos.line}:{startPos.col}"
  match s.peek? with
  | some '\'' => .ok (.char c, s.advance)
  | _ => .error s!"expected closing ' at {s.sourcePos.line}:{s.sourcePos.col}"

-- Lex a single token
partial def lexToken (s : LexState) : Except String (PosToken × LexState) := do
  let s := skipWhitespaceAndComments s
  let pos := s.sourcePos
  if s.eof then
    .ok ({ token := .eof, pos := pos }, s)
  else
    match s.peek?, s.peekN 1 with
    -- Two-character operators
    | some '-', some '>' => .ok ({ token := .arrow, pos }, s.advanceN 2)
    | some '=', some '>' => .ok ({ token := .fatArrow, pos }, s.advanceN 2)
    | some '=', some '=' => .ok ({ token := .eqEq, pos }, s.advanceN 2)
    | some '!', some '=' => .ok ({ token := .neq, pos }, s.advanceN 2)
    | some '<', some '=' => .ok ({ token := .le, pos }, s.advanceN 2)
    | some '>', some '=' => .ok ({ token := .ge, pos }, s.advanceN 2)
    | some '&', some '&' => .ok ({ token := .ampAmp, pos }, s.advanceN 2)
    | some '|', some '|' => .ok ({ token := .pipeOr, pos }, s.advanceN 2)
    | some '+', some '+' => .ok ({ token := .plusPlus, pos }, s.advanceN 2)
    | some '|', some '>' => .ok ({ token := .pipeGt, pos }, s.advanceN 2)
    -- Single-character tokens
    | some '(', _ => .ok ({ token := .lparen, pos }, s.advance)
    | some ')', _ => .ok ({ token := .rparen, pos }, s.advance)
    | some '{', _ => .ok ({ token := .lbrace, pos }, s.advance)
    | some '}', _ => .ok ({ token := .rbrace, pos }, s.advance)
    | some '[', _ => .ok ({ token := .lbracket, pos }, s.advance)
    | some ']', _ => .ok ({ token := .rbracket, pos }, s.advance)
    | some ',', _ => .ok ({ token := .comma, pos }, s.advance)
    | some '.', _ => .ok ({ token := .dot, pos }, s.advance)
    | some ':', _ => .ok ({ token := .colon, pos }, s.advance)
    | some ';', _ => .ok ({ token := .semi, pos }, s.advance)
    | some '|', _ => .ok ({ token := .pipe, pos }, s.advance)
    | some '#', _ => .ok ({ token := .hash, pos }, s.advance)
    | some '~', _ => .ok ({ token := .tilde, pos }, s.advance)
    | some '=', _ => .ok ({ token := .eq, pos }, s.advance)
    | some '<', _ => .ok ({ token := .langle, pos }, s.advance)
    | some '>', _ => .ok ({ token := .rangle, pos }, s.advance)
    | some '+', _ => .ok ({ token := .plus, pos }, s.advance)
    | some '-', _ =>
      -- Could be minus or start of negative number
      match s.peekN 1 with
      | some c =>
        if c.isDigit then lexNumber s >>= fun (t, s') => .ok ({ token := t, pos }, s')
        else .ok ({ token := .minus, pos }, s.advance)
      | none => .ok ({ token := .minus, pos }, s.advance)
    | some '*', _ => .ok ({ token := .star, pos }, s.advance)
    | some '/', _ => .ok ({ token := .slash, pos }, s.advance)
    | some '\\', _ => .ok ({ token := .backslash, pos }, s.advance)
    | some '@', _ => .ok ({ token := .at_, pos }, s.advance)
    | some '_', _ =>
      -- Check if it's a standalone underscore (wildcard) or start of identifier
      match s.peekN 1 with
      | some c =>
        if c.isAlphanum then
          -- Identifier starting with underscore
          lexIdent s >>= fun (t, s') => .ok ({ token := t, pos }, s')
        else
          .ok ({ token := .underscore, pos }, s.advance)
      | none => .ok ({ token := .underscore, pos }, s.advance)
    -- String literal
    | some '"', _ => lexString s >>= fun (t, s') => .ok ({ token := t, pos }, s')
    -- Character literal
    | some '\'', _ => lexChar s >>= fun (t, s') => .ok ({ token := t, pos }, s')
    -- Number
    | some c, _ =>
      if c.isDigit then
        lexNumber s >>= fun (t, s') => .ok ({ token := t, pos }, s')
      else if c.isAlpha then
        lexIdent s >>= fun (t, s') => .ok ({ token := t, pos }, s')
      else
        .error s!"unexpected character '{c}' at {pos.line}:{pos.col}"
    | none, _ => .error "unexpected end of input"

-- Tokenize entire input
partial def tokenize (input : String) : Except String (List PosToken) := do
  let s : LexState := { input := input, chars := input.toList }
  go s []
where
  go (s : LexState) (acc : List PosToken) : Except String (List PosToken) := do
    let (tok, s') ← lexToken s
    if tok.token == .eof then
      .ok (acc.reverse ++ [tok])
    else
      go s' (tok :: acc)

end Ziku
