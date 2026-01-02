# Ziku Syntax Design

Ziku is the successor of malgo and anma, featuring:

- Duality-aware design with explicit data/codata symmetry
- Sequent calculus foundation
- Copattern matching for codata construction

## Design Principles

1. **Duality-aware**: Explicit support for data/codata, pattern/copattern symmetry
2. **Sequent calculus foundation**: Producers and consumers as first-class concepts
3. **Minimal but expressive**: No syntactic sugar that obscures semantics
4. **Lean-verifiable**: Syntax should map cleanly to Lean AST

## Core Distinction

- **Pattern matching** (destructing data): uses `|` clauses
- **Copattern matching** (constructing codata): uses `{}` blocks
- **`#`** represents "the object being defined" (like `this` or `self`)

---

## Function Application and Currying

All functions in Ziku are curried. Multiple argument syntaxes are equivalent:

```ziku
-- These are all equivalent
f x y
f(x)(y)
f(x, y)      -- sugar for f(x)(y)

-- Method calls too
obj.method x y
obj.method(x)(y)
obj.method(x, y)
```

**No tuples**: Ziku does not have tuple types. Use anonymous records instead:

```ziku
-- Instead of (a, b), use records:
{ fst = a, snd = b }

-- Access fields with dot notation
r.fst
r.snd
```

---

## Basic Expressions

```ziku
-- Literals
42
3.14
"hello"
'c'
true

-- Variables
x
fooBar
snake_case

-- Arithmetic
1 + 2 * 3
(a - b) / c

-- Comparison
x == y
a < b
p && q
not r
```

---

## Type Declarations

### Data Types (constructed by patterns)

```ziku
data Bool =
  | True
  | False

data Nat =
  | Zero
  | Succ Nat

data List a =
  | Nil
  | Cons a (List a)

data Either a b =
  | Left a
  | Right b
```

### Codata Types (destructed by copatterns)

```ziku
codata Stream a {
  #.head : a
  #.tail : Stream a
}

codata Lazy a {
  #.force : a
}

-- Functions as codata
codata a -> b {
  #(a) : b
}

-- Records
codata Point {
  #.x : Int
  #.y : Int
}
```

---

## The `#` Pattern

- `#` represents "the object being defined" (like `this` or `self`)
- `#.field` means "when this object's field is accessed"
- `#.method(x)` means "when this object's method is called with x"
- Can be chained: `#.tail.head` for nested access

---

## Pattern Matching (for data)

```ziku
-- Function definitions with patterns
def length : List a -> Nat
  | Nil       => Zero
  | Cons _ xs => Succ (length xs)

def map : (a -> b) -> List a -> List b
  | f, Nil       => Nil
  | f, Cons x xs => Cons (f x) (map f xs)

-- Match expression (brace syntax)
match xs {
  | Nil       => "empty"
  | Cons x _  => "has: " ++ show x
}
```

### Separator Rules

Both `|` and `,` can be used as separators in match and codata blocks:
- `|` is a **prefix** separator (can appear at the start of the first clause)
- `,` is a **suffix** separator (can appear at the end of the last clause)

```ziku
-- Leading pipe (OK)
match x { | true => 1 | false => 0 }

-- Comma separator (OK)
match x { true => 1, false => 0 }

-- Trailing comma (OK)
match x { true => 1, false => 0, }

-- Mixed (OK)
match x { | true => 1, | false => 0 }
```

---

## Copattern Matching (for codata)

```ziku
-- Stream of naturals
def nats : Nat -> Stream Nat = \n => {
  #.head => n
  #.tail => nats (Succ n)
}

-- Fibonacci (nested copatterns)
def fibs : Stream Int = {
  #.head      => 0
  #.tail.head => 1
  #.tail.tail => zipWith (\x, y => x + y) fibs #.tail
}

-- Point construction
def origin : Point = {
  #.x => 0
  #.y => 0
}

-- Lazy value
def lazy : a -> Lazy a = \x => {
  #.force => x
}
```

---

## Functions with `#`

```ziku
-- Function as codata (explicit)
def const : a -> b -> a = \x => {
  #(y) => x
}

-- Curried
def add : Int -> Int -> Int = \x => {
  #(y) => x + y
}

-- Multi-argument
def compose : (b -> c) -> (a -> b) -> a -> c = \f => {
  #(g) => {
    #(x) => f (g x)
  }
}

-- Shorthand (sugar for single #(x) copattern)
def compose : (b -> c) -> (a -> b) -> a -> c = \f, g, x => f (g x)
```

---

## Mixed Patterns and Copatterns

```ziku
def zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c = \f, s1, s2 => {
  #.head => f (s1.head) (s2.head)
  #.tail => zipWith f (s1.tail) (s2.tail)
}

-- Pattern in copattern clause
def map : (a -> b) -> List a -> Stream b = {
  \f, Nil       => error "empty list"
  \f, Cons x xs => {
    #.head => f x
    #.tail => map f xs
  }
}

-- Alternative: patterns before #
def map : (a -> b) -> List a -> Stream b = {
  f, Cons x xs #.head => f x
  f, Cons x xs #.tail => map f xs
  f, Nil       #.head => error "empty"
  f, Nil       #.tail => error "empty"
}
```

**Note**: `#` can only appear in copattern positions (to the left of `=>`). For self-reference in expressions, you must explicitly use the defined name (e.g., `ones` instead of `#`).

---

## State Monad

```ziku
codata State s a {
  #.run : s -> { val : a, state : s }
}

def pure : a -> State s a = \x => {
  #.run => \s => { val = x, state = s }
}

def bind : State s a -> (a -> State s b) -> State s b = \m, f => {
  #.run => \s =>
    let r = m.run(s) in
    (f r.val).run(r.state)
}

def get : State s s = {
  #.run => \s => { val = s, state = s }
}

def put : s -> State s () = \s' => {
  #.run => \_ => { val = (), state = s' }
}
```

---

## Object-Oriented Style

```ziku
codata Counter {
  #.value     : Int
  #.increment : Counter
  #.decrement : Counter
  #.add(Int)  : Counter
}

def counter : Int -> Counter = \n => {
  #.value     => n
  #.increment => counter (n + 1)
  #.decrement => counter (n - 1)
  #.add(m)    => counter (n + m)
}

-- Usage
let c = counter 0 in
c.increment.add(5).value  -- evaluates to 6
```

---

## Control Flow: Label and Goto

Ziku provides `label` and `goto` for non-local control flow, which are translated to sequent calculus constructs internally.

### Label Expression

The `label name { body }` form creates a control point that can be jumped to:

```ziku
-- Basic label: if body completes normally, return its value
label result { 42 }                    -- evaluates to 42

-- Label with early exit via goto
label result {
  if condition then goto(42, result)
  else expensive_computation()
}

-- Nested labels
label outer {
  label inner {
    if x > 0 then goto(x, outer)       -- jump to outer
    else goto(0, inner)                 -- jump to inner
  }
}
```

### Goto Expression

The `goto(value, label)` form jumps to a label with a value:

```ziku
-- Jump with computed value
label sum {
  let x = 10 in
  goto(x + 5, sum)                     -- returns 15
}

-- Conditional early return
label validate {
  if input < 0 then goto("negative", validate)
  else if input > 100 then goto("too large", validate)
  else "valid"
}
```

**Scoping**: Labels are statically scoped. A `goto` can only reference labels that are lexically enclosing:

```ziku
-- This works:
label outer { goto(42, outer) }

-- This is an error (undefined label):
goto(42, undefined)
```

---

## Sequent Calculus IR (Internal)

Internally, Ziku compiles to a λμμ̃-calculus based intermediate representation. The surface language constructs are translated as follows:

| Surface               | IR Translation                           |
| --------------------- | ---------------------------------------- |
| `label α { t }`       | `μα.⟨⟦t⟧ \| α⟩`                          |
| `goto(t, α)`          | `μβ.⟨⟦t⟧ \| α⟩` (β fresh)                |
| `let x = t₁ in t₂`    | `μα.⟨⟦t₁⟧ \| μ̃x.⟨⟦t₂⟧ \| α⟩⟩`            |
| `if t₁ then t₂ else t₃` | `μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ \| α⟩, ⟨⟦t₃⟧ \| α⟩)` |
| `λx.t`                | `cocase {ap(x; α) ⇒ ⟨⟦t⟧ \| α⟩}`         |
| `t₁ t₂`               | `μα.⟨⟦t₁⟧ \| ap(⟦t₂⟧; α)⟩`               |

The IR has three syntactic categories:
- **Producers**: values that produce data (`var`, `lit`, `μα.s`, `cocase`)
- **Consumers**: contexts that consume data (`covar`, `μ̃x.s`, `case`, `destructor`)
- **Statements**: computations that drive evaluation (`⟨p | c⟩`, `binOp`, `ifz`)

### Advanced: Direct IR Access

For advanced users, Ziku also supports direct IR syntax (primarily for testing):

```ziku
-- Cut expression (IR)
cut <producer | consumer>

-- Mu abstraction (IR)
mu k => expr
μk => expr
```

---

## Let Bindings and Lambdas

```ziku
-- Let binding
let x = 42 in
let y = x + 1 in
x * y

-- Recursive let
let rec fact = \n =>
  match n {
    | Zero   => Succ Zero
    | Succ m => n * fact m
  }
in fact (Succ (Succ (Succ Zero)))

-- Lambda (shorthand for single #(x) copattern)
\x => x + 1
\x, y => x * y

-- Explicit copattern form
{ #(x) => x + 1 }
{ #(x) => { #(y) => x * y } }
```

---

## Anonymous Blocks

```ziku
-- Anonymous function
\x => x + 1              -- shorthand
{ #(x) => x + 1 }        -- explicit

-- Anonymous stream
let s = { #.head => 1, #.tail => s }

-- Anonymous record
let p = { #.x => 3, #.y => 4 }

-- Inline codata
list.map { #(x) => x * 2 }
```

---

## Type Annotations

```ziku
-- Inline annotation
(42 : Int)
(\x => x : a -> a)

-- Definition signature
def id : forall a. a -> a
  | x => x

-- Polymorphic types
def compose : forall a b c. (b -> c) -> (a -> b) -> a -> c = \f, g, x => f (g x)
```

---

## Modules

```ziku
module List where
  data List a =
    | Nil
    | Cons a (List a)

  def map : (a -> b) -> List a -> List b = ...
  def filter : (a -> Bool) -> List a -> List a = ...
end

-- Import
import List
import List (map, filter)
import List as L
```

---

## Operators

```ziku
-- Custom operators
infix 6 ++  -- precedence 6, left associative
infixr 5 :: -- precedence 5, right associative

def (++) : List a -> List a -> List a
  | Nil, ys       => ys
  | Cons x xs, ys => Cons x (xs ++ ys)

-- Pipe operator
x |> f      -- same as f x
x |> f |> g -- same as g (f x)
```

---

## Comments

```ziku
-- Single line comment

{-
   Multi-line
   comment
-}

--- Documentation comment
--- @param x the input value
--- @return the squared value
def square : Int -> Int = ...
```

---

## Complete Example: Infinite Structures

```ziku
codata Stream a {
  #.head : a
  #.tail : Stream a
}

codata Tree a {
  #.value : a
  #.left  : Tree a
  #.right : Tree a
}

-- Infinite stream of ones
def ones : Stream Int = {
  #.head => 1
  #.tail => #
}

-- Infinite tree of naturals (breadth-first labeling)
def natTree : Nat -> Tree Nat = \n => {
  #.value => n
  #.left  => natTree (2 * n + 1)
  #.right => natTree (2 * n + 2)
}

-- Take from stream
def take : Int -> Stream a -> List a
  | 0, _ => Nil
  | n, s => Cons (s.head) (take (n - 1) (s.tail))

-- Zip two streams
def zip : Stream a -> Stream b -> Stream { fst : a, snd : b } = \s1, s2 => {
  #.head => { fst = s1.head, snd = s2.head }
  #.tail => zip s1.tail s2.tail
}

-- Fibonacci
def fibs : Stream Int = {
  #.head      => 0
  #.tail.head => 1
  #.tail.tail => zipWith (\x, y => x + y) fibs #.tail
}

def zipWith : (a -> b -> c) -> Stream a -> Stream b -> Stream c = \f, s1, s2 => {
  #.head => f (s1.head) (s2.head)
  #.tail => zipWith f (s1.tail) (s2.tail)
}
```

---

## Grammar Summary (EBNF)

```ebnf
program     = decl*

decl        = dataDecl | codataDecl | defDecl | moduleDecl

dataDecl    = "data" IDENT tyParams? "=" ("|" constr)+
constr      = IDENT type*

codataDecl  = "codata" IDENT tyParams? "{" copatSig* "}"
copatSig    = "#" accessor* ":" type
accessor    = "." IDENT | "(" IDENT ")"   -- .field or (arg)

defDecl     = "def" IDENT ":" type "=" expr
            | "def" IDENT ":" type patternClauses
            | "def" IDENT ":" type copatternBlock

patternClauses  = ("|" pattern+ "=>" expr)+
copatternBlock  = "{" copatClause* "}"
copatClause     = pattern* "#" accessor* "=>" expr

expr        = atom
            | expr binop expr
            | "match" expr "{" ("|"? pattern "=>" expr) (","? "|"? pattern "=>" expr)* ","? "}"
            | "let" IDENT (":" type)? "=" expr "in" expr
            | "let" "rec" IDENT "=" expr "in" expr
            | "\" params "=>" expr
            | "{" copatClause* "}"
            | "{" "#" accessor "=>" expr ("," "#" accessor "=>" expr)* "}"
            | "{" (IDENT "=" expr ",")* IDENT "=" expr "}"   -- anonymous record
            | expr "." IDENT                                  -- field access
            | expr atom+                                      -- application (space)
            | expr "(" args ")"                               -- application (parens)
            | "label" IDENT "{" expr "}"                      -- label (control point)
            | "goto" "(" expr "," IDENT ")"                   -- goto (jump to label)
            | "cut" "<" expr "|" expr ">"                     -- sequent cut (IR)
            | ("μ" | "mu") IDENT "=>" expr                    -- mu abstraction (IR)
            | "if" expr "then" expr "else" expr               -- conditional
            | "#"
            | "(" expr ")"

args        = expr ("," expr)*                -- desugars to curried application

pattern     = IDENT | LITERAL | "_" | "(" pattern ")" | constr pattern*

type        = typeAtom | type "->" type | "forall" IDENT+ "." type
           | "{" (IDENT ":" type ",")* IDENT ":" type "}"    -- record type
typeAtom    = IDENT | IDENT type+ | "(" type ")"

tyParams    = IDENT+
params      = IDENT ("," IDENT)*

binop       = "+" | "-" | "*" | "/" | "==" | "<" | ">" | "<=" | ">="
            | "&&" | "||" | "++" | "|>"
```

---

## Visual Summary

| Syntax                   | Meaning                                        |
| ------------------------ | ---------------------------------------------- |
| `#`                      | The object being defined (this/self)           |
| `#.field`                | When field is accessed                         |
| `#(x)`                   | When called with argument x (callable codata)  |
| `#.tail.head`            | Nested: when `.tail.head` is accessed          |
| `{ #.x => e }`           | Codata block defining field x                  |
| `{ #(x) => e }`          | Function block (callable codata)               |
| `\x => e`                | Lambda (sugar for `{ #(x) => e }`)             |
| `\| p => e`              | Pattern match clause                           |
| `{ \| p => e }`          | Consumer block (pattern matching on producers) |
| `f(x, y)`                | Curried application: `f(x)(y)`                 |
| `f x y`                  | Same as above                                  |
| `{ a = x, b = y }`       | Anonymous record                               |
| `r.field`                | Field access                                   |
| `label n { e }`          | Control point: creates jumpable label n        |
| `goto(e, n)`             | Jump to label n with value e                   |
| `cut <p \| c>`           | Sequent cut (IR): producer p to consumer c     |
| `μk => e` or `mu k => e` | Mu abstraction (IR): bind continuation k       |
