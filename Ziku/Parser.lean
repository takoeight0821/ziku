import Ziku.Syntax

namespace Ziku

structure ParseState where
  input : String
  pos : Nat
  deriving Repr

def ParseState.eof (s : ParseState) : Bool :=
  s.pos >= s.input.length

def ParseState.peek? (s : ParseState) : Option Char :=
  let rec get? : List Char → Nat → Option Char
    | [], _ => none
    | c :: _, 0 => some c
    | _ :: cs, n + 1 => get? cs n
  get? s.input.toList s.pos

def ParseState.advance (s : ParseState) (n : Nat := 1) : ParseState :=
  { s with pos := s.pos + n }

abbrev Parser α := ParseState → Except String (α × ParseState)

partial def skipWhitespace (s : ParseState) : ParseState :=
  let rec loop (st : ParseState) : ParseState :=
    match st.peek? with
    | some c => if c.isWhitespace then loop (st.advance) else st
    | none => st
  loop s

partial def parseInt : Parser Int := fun s =>
  let s := skipWhitespace s
  let (negative, s') := match s.peek? with
    | some '-' => (true, s.advance)
    | _ => (false, s)
  let rec parseDigits (st : ParseState) (acc : Nat) : Option (Nat × ParseState) :=
    match st.peek? with
    | some c =>
      if c.isDigit then
        parseDigits (st.advance) (acc * 10 + (c.toNat - '0'.toNat))
      else
        some (acc, st)
    | none => some (acc, st)
  match parseDigits s' 0 with
  | some (n, s'') =>
    let result := if negative then -(n : Int) else (n : Int)
    .ok (result, skipWhitespace s'')
  | none => .error s!"expected integer at position {s.pos}"

partial def parseIdent : Parser String := fun s =>
  let s := skipWhitespace s
  match s.peek? with
  | some c =>
    if c.isAlpha then
      let rec loop (st : ParseState) (chars : List Char) : String × ParseState :=
        match st.peek? with
        | some ch =>
          if ch.isAlphanum || ch == '_' then
            loop (st.advance) (chars ++ [ch])
          else
            (String.ofList chars, st)
        | none => (String.ofList chars, st)
      let (id, s') := loop (s.advance) [c]
      .ok (id, skipWhitespace s')
    else
      .error s!"expected identifier at position {s.pos}"
  | none => .error s!"unexpected EOF"

mutual
  partial def parseAtom : Parser Expr := fun s =>
    let s := skipWhitespace s
    match s.peek? with
    | some '(' =>
      let s := s.advance
      match parseExpr s with
      | .ok (e, s') =>
        let s' := skipWhitespace s'
        match s'.peek? with
        | some ')' => .ok (e, skipWhitespace (s'.advance))
        | _ => .error s!"expected ')' at position {s'.pos}"
      | .error msg => .error msg
    | some c =>
      if c.isDigit || c == '-' then
        match parseInt s with
        | .ok (n, s') => .ok (Expr.lit n, s')
        | .error msg => .error msg
      else if c.isAlpha then
        match parseIdent s with
        | .ok (id, s') => .ok (Expr.var id, s')
        | .error msg => .error msg
      else
        .error s!"unexpected character '{c}' at position {s.pos}"
    | none => .error "unexpected EOF"

  partial def parseFactor : Parser Expr := fun s =>
    match parseAtom s with
    | .ok (e, s') =>
      let rec loop (expr : Expr) (st : ParseState) : Expr × ParseState :=
        let st := skipWhitespace st
        match st.peek? with
        | some '*' =>
          let st := skipWhitespace (st.advance)
          match parseAtom st with
          | .ok (rhs, st') => loop (Expr.mul expr rhs) st'
          | .error _ => (expr, st)
        | some '/' =>
          let st := skipWhitespace (st.advance)
          match parseAtom st with
          | .ok (rhs, st') => loop (Expr.div expr rhs) st'
          | .error _ => (expr, st)
        | _ => (expr, st)
      .ok (loop e s')
    | .error msg => .error msg

  partial def parseExpr : Parser Expr := fun s =>
    match parseFactor s with
    | .ok (e, s') =>
      let rec loop (expr : Expr) (st : ParseState) : Expr × ParseState :=
        let st := skipWhitespace st
        match st.peek? with
        | some '+' =>
          let st := skipWhitespace (st.advance)
          match parseFactor st with
          | .ok (rhs, st') => loop (Expr.add expr rhs) st'
          | .error _ => (expr, st)
        | some '-' =>
          let st := skipWhitespace (st.advance)
          match parseFactor st with
          | .ok (rhs, st') => loop (Expr.sub expr rhs) st'
          | .error _ => (expr, st)
        | _ => (expr, st)
      .ok (loop e s')
    | .error msg => .error msg
end

def parse (input : String) : Except String Expr :=
  let s : ParseState := { input := input, pos := 0 }
  match parseExpr s with
  | .ok (e, s') =>
    let s' := skipWhitespace s'
    if s'.eof then
      .ok e
    else
      .error s!"unexpected input at position {s'.pos}"
  | .error msg => .error msg

end Ziku
