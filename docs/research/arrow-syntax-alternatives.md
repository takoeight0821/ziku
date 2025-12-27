# Arrow Syntax Alternatives for Ziku

## Current Design

Ziku currently uses:

- **Type level**: `->` (thin arrow)
- **Term level**: `=>` (fat arrow)

This document explores alternative designs and their tradeoffs.

---

## Survey of Existing Languages

### Languages Using `->` for Both Type and Term

| Language       | Type       | Lambda       | Pattern Match | Notes                           |
| -------------- | ---------- | ------------ | ------------- | ------------------------------- |
| **Haskell**    | `a -> b`   | `\x -> e`    | `p -> e`      | Parser disambiguates by context |
| **OCaml**      | `'a -> 'b` | `fun x -> e` | `p -> e`      | `fun` keyword helps             |
| **F#**         | `'a -> 'b` | `fun x -> e` | `p -> e`      | Similar to OCaml                |
| **Elm**        | `a -> b`   | `\x -> e`    | `p -> e`      | Haskell-like                    |
| **PureScript** | `a -> b`   | `\x -> e`    | `p -> e`      | Haskell-like                    |

### Languages Using `=>` for Term Level

| Language       | Type         | Lambda       | Pattern Match | Notes                  |
| -------------- | ------------ | ------------ | ------------- | ---------------------- |
| **Scala**      | `A => B`     | `x => e`     | `case p => e` | Fat arrow everywhere   |
| **Kotlin**     | `(A) -> B`   | `{ x -> e }` | `p -> e`      | Mixed approach         |
| **Rust**       | `Fn(A) -> B` | `\|x\| e`    | `p => e`      | Fat arrow for patterns |
| **JavaScript** | N/A          | `x => e`     | N/A           | ES6 arrow functions    |
| **C#**         | `Func<A, B>` | `x => e`     | N/A           | Lambda expressions     |

### Languages Using Unicode

| Language   | Type                | Lambda       | Pattern Match | Notes                                   |
| ---------- | ------------------- | ------------ | ------------- | --------------------------------------- |
| **Agda**   | `A → B`             | `λ x → e`    | `p → e`       | Unicode throughout                      |
| **Idris**  | `A -> B`            | `\x => e`    | `p => e`      | Mixed (like current Ziku)               |
| **Lean 4** | `A → B` or `A -> B` | `fun x => e` | `\| p => e`   | Unicode optional, ASCII `->` also works |
| **Coq**    | `A -> B`            | `fun x => e` | `p => e`      | Similar to Lean                         |

---

## Possible Alternatives for Ziku

### Option 1: Uniform `->` (Haskell-style)

```ziku
-- Types
def f : Int -> Int

-- Lambda
\x -> x + 1

-- Pattern match
| Cons x xs -> x + 1

-- Copattern
#.head -> 42
```

**Pros:**

- Consistent across all contexts
- Familiar to Haskell/OCaml programmers
- Shorter to type

**Cons:**

- Less visual distinction between type and term
- Parser must disambiguate by context
- May be confusing for beginners

### Option 2: Current Design `->` / `=>` (Scala/Idris-style)

```ziku
-- Types
def f : Int -> Int

-- Lambda
\x => x + 1

-- Pattern match
| Cons x xs => x + 1

-- Copattern
#.head => 42
```

**Pros:**

- Clear visual distinction
- Easy to parse
- Familiar to Scala/JS/Rust programmers

**Cons:**

- Two symbols to learn
- Slightly longer to type

### Option 3: Unicode `→` / `⇒` (Agda-style)

```ziku
-- Types
def f : Int → Int

-- Lambda
\x ⇒ x + 1

-- Pattern match
| Cons x xs ⇒ x + 1

-- Copattern
#.head ⇒ 42
```

**Pros:**

- Maximum visual distinction
- Mathematically beautiful
- Follows mathematical notation

**Cons:**

- Requires Unicode input setup
- Not all editors/terminals display properly
- Accessibility concerns

### Option 4: Unicode Types Only `→` / `=>` (Lean-style)

```ziku
-- Types
def f : Int → Int

-- Lambda
\x => x + 1

-- Pattern match
| Cons x xs => x + 1

-- Copattern
#.head => 42
```

**Pros:**

- Types stand out visually
- Terms remain ASCII-friendly
- Good balance of clarity and accessibility

**Cons:**

- Mixed Unicode/ASCII may feel inconsistent
- Still requires Unicode input for types

### Option 5: Different Syntax for Copatterns `->` / `=>` / `:=`

```ziku
-- Types
def f : Int -> Int

-- Lambda
\x => x + 1

-- Pattern match
| Cons x xs => x + 1

-- Copattern (special syntax)
#.head := 42
#(x) := x + 1
```

**Pros:**

- Copatterns visually distinct from patterns
- Emphasizes data/codata duality
- `:=` suggests "definition"

**Cons:**

- Three different arrows to learn
- May be overkill for visual distinction

### Option 6: Uniform `=>` (Reverse Scala)

```ziku
-- Types
def f : Int => Int

-- Lambda
\x => x + 1

-- Pattern match
| Cons x xs => x + 1

-- Copattern
#.head => 42
```

**Pros:**

- Uniform at term level
- Types still different
- Consistent feel

**Cons:**

- Types with `=>` may be confusing (usually means function value)
- Breaks convention of `->` for function types

---

## Analysis by Design Criteria

### Criterion 1: Parser Simplicity

| Option        | Complexity | Notes                     |
| ------------- | ---------- | ------------------------- |
| Uniform `->`  | Medium     | Context-dependent parsing |
| `->` / `=>`   | **Low**    | Lexer-level distinction   |
| Unicode       | Low        | Distinct tokens           |
| Mixed Unicode | Low        | Distinct tokens           |
| Three arrows  | Low        | Distinct tokens           |
| Uniform `=>`  | Low        | Distinct tokens           |

**Winner**: Current design and alternatives with distinct arrows

### Criterion 2: Readability

| Option        | Beginner | Expert | Notes                       |
| ------------- | -------- | ------ | --------------------------- |
| Uniform `->`  | Medium   | High   | Requires learning context   |
| `->` / `=>`   | **High** | High   | Clear distinction           |
| Unicode       | Medium   | High   | Beautiful but input barrier |
| Mixed Unicode | High     | High   | Types stand out             |
| Three arrows  | Medium   | High   | May be excessive            |
| Uniform `=>`  | Medium   | Medium | Unusual type syntax         |

**Winner**: Current design `->` / `=>`

### Criterion 3: Typing Convenience

| Option        | ASCII Only | Easy to Type           |
| ------------- | ---------- | ---------------------- |
| Uniform `->`  | ✓          | ✓✓ (shortest)          |
| `->` / `=>`   | ✓          | ✓ (current)            |
| Unicode       | ✗          | ✗ (requires setup)     |
| Mixed Unicode | ✗          | ✗ (types need Unicode) |
| Three arrows  | ✓          | ✓                      |
| Uniform `=>`  | ✓          | ✓                      |

**Winner**: Uniform `->` (slightly shorter)

### Criterion 4: Familiarity

| Option        | Haskell | Scala/JS/Rust | Lean/Coq |
| ------------- | ------- | ------------- | -------- |
| Uniform `->`  | ✓✓      | ✗             | ✗        |
| `->` / `=>`   | ✗       | ✓✓            | ✓        |
| Unicode       | ✗       | ✗             | ✓ (Agda) |
| Mixed Unicode | ✗       | ✗             | ✓✓       |
| Three arrows  | ✗       | ✗             | ✗        |
| Uniform `=>`  | ✗       | ✗             | ✗        |

**Winner**: Depends on target audience

### Criterion 5: Sequent Calculus Connection

The sequent calculus traditionally uses different notation for:

- **Sequents**: `Γ ⊢ Δ` (turnstile)
- **Inference rules**: horizontal lines or `---`
- **Implications**: `A → B` or `A ⊃ B`

Neither `->` nor `=>` directly corresponds to sequent calculus notation, but:

- `=>` visually resembles the "produces" relationship
- `->` is standard for function types in type theory

**No clear winner** - both are reasonable abstractions

---

## Recommendation Matrix

### For Production Language

If Ziku aims to be a **production-ready** language:

**Recommended**: Current `->` / `=>` design

- Balances readability and typing convenience
- Familiar to large audience (Scala, JS, Rust, Idris, Lean)
- Easy to parse
- ASCII-only (no Unicode barriers)

### For Research/Educational Language

If Ziku is primarily for **type theory education**:

**Recommended**: Unicode `→` / `⇒` or Mixed `→` / `=>`

- Mathematical notation teaches proper concepts
- Visual beauty aids understanding
- Aligns with Agda/Coq community

### For Haskell Programmers

If target audience is **Haskell ecosystem**:

**Recommended**: Uniform `->` (Haskell-style)

- Zero learning curve for Haskellers
- Matches mental model
- Slightly shorter

---

## Copattern-Specific Considerations

### Should Copatterns Use Different Syntax?

**Arguments FOR separate syntax** (e.g., `:=`):

1. **Duality emphasis**: Data/codata are dual, syntax should reflect this
2. **Visual distinction**: Easier to spot copatterns
3. **Assignment semantics**: `:=` suggests "define this field to be..."

**Arguments AGAINST**:

1. **Complexity**: Three arrows is a lot to learn
2. **Inconsistency**: Why treat copatterns differently from patterns?
3. **Uniformity**: Both are just "cases" in computation

**Current Ziku approach**: Treats patterns and copatterns uniformly with `=>`

- Emphasizes that they're symmetric concepts
- Simpler mental model

---

## Alternative Notation Systems

### Using `:` for Copatterns

```ziku
-- Pattern match (destructor)
| Cons x xs => x + 1

-- Copattern (constructor)
#.head : 42
#(x) : x + 1
```

Inspired by OCaml's record field syntax `{ x : 1; y : 2 }`

**Analysis**: Could work, but `:` already means "type annotation"

### Using `=` for Copatterns

```ziku
-- Copattern
#.head = 42
#(x) = x + 1
```

**Analysis**: Too similar to let-binding, may cause confusion

### Using `~>` for Copatterns

```ziku
-- Pattern (data)
| Cons x xs => x + 1

-- Copattern (codata)
#.head ~> 42
```

**Analysis**: Interesting but obscure; `~>` has no established meaning

---

## Conclusion

### Current Design is Strong

The current `->` / `=>` design:

1. ✅ Clear visual distinction
2. ✅ Easy to parse
3. ✅ Familiar to many programmers
4. ✅ ASCII-only (accessible)
5. ✅ Uniform treatment of patterns/copatterns

### Viable Alternatives

If reconsidering, the best alternatives are:

1. **Uniform `->` (Haskell-style)**
   - Best if targeting Haskell programmers
   - Requires context-sensitive parsing

2. **Mixed Unicode `→` / `=>` (Lean-style)**
   - Best for educational/research use
   - Types visually distinct
   - Requires Unicode setup

3. **Full Unicode `→` / `⇒` (Agda-style)**
   - Best for mathematical aesthetics
   - Highest learning barrier

### Recommendation

**Keep current design** unless:

- Target audience is specifically Haskell programmers (then use uniform `->`)
- Ziku is primarily for academia (then use Unicode `→`)

The `->` / `=>` distinction is a good balance for a modern functional language.

---

## Implementation Notes

If changing the syntax:

1. **Lexer changes** ([Lexer.lean](../Ziku/Lexer.lean)):
   - Update token definitions
   - Handle Unicode if needed

2. **Parser changes** ([Parser.lean](../Ziku/Parser.lean)):
   - Update all `expect .fatArrow` calls
   - Update all `expect .arrow` calls

3. **Syntax documentation** ([syntax.md](../syntax.md)):
   - Update all code examples
   - Update grammar

4. **Test files**:
   - Update all `.ziku` test files
   - Regenerate `.golden` files

---

## References

### Lean 4 Syntax

**Official Documentation:**

- [Lean 4 Manual - Functions](https://lean-lang.org/lean4/doc/functions.html)
- [Lean 4 Tutorial - Function Syntax](https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html#functions)
- [Lean 4 Reference Manual](https://leanprover.github.io/reference/expressions.html)

**Example from Lean 4 Standard Library:**

```lean
-- Function types (both syntaxes work)
def id : α → α := fun x => x
def id' : α -> α := fun x => x

-- Pattern matching with fat arrow
def length : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

-- Lambda with fat arrow
def map (f : α → β) : List α → List β :=
  fun xs => match xs with
  | [] => []
  | x :: xs => f x :: map f xs
```

**Source Code:**

- [Lean 4 Parser (arrow syntax)](https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean)
- [Lean 4 Unicode input table](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/Unicode.lean)
  - `\->` or `\to` inputs `→` (U+2192)
  - `->` is kept as ASCII alternative

### Idris 2 Syntax

**Official Documentation:**

- [Idris 2 Tutorial - Functions](https://idris2.readthedocs.io/en/latest/tutorial/introduction.html#functions)
- [Idris 2 Language Reference](https://idris2.readthedocs.io/en/latest/reference/index.html)

**Examples:**

```idris
-- Types use ->
double : Int -> Int
double x = x * 2

-- Lambdas use =>
map : (a -> b) -> List a -> List b
map f xs = case xs of
  [] => []
  (x :: xs) => f x :: map f xs

-- Pattern matching uses =>
length : List a -> Nat
length [] = 0
length (x :: xs) = 1 + length xs
```

**Rationale** (from Idris documentation):

> "The fat arrow `=>` is used for function definitions to distinguish them from the thin arrow `->` used in types."

### Scala Syntax

**Official Documentation:**

- [Scala Language Specification - Function Types](https://scala-lang.org/files/archive/spec/2.13/03-types.html#function-types)
- [Scala Language Specification - Anonymous Functions](https://scala-lang.org/files/archive/spec/2.13/06-expressions.html#anonymous-functions)

**Examples:**

```scala
// Function types use =>
val f: Int => Int = x => x + 1

// Pattern matching uses =>
list match {
  case Nil => 0
  case x :: xs => x + sum(xs)
}

// Case classes
case class Point(x: Int, y: Int)
```

**Note:** Scala 3 also allows `->` for types: `Int -> Int` as synonym for `Int => Int`

### Agda Syntax

**Official Documentation:**

- [Agda Language Reference - Functions](https://agda.readthedocs.io/en/latest/language/function-types.html)
- [Agda Language Reference - Lambda](https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html)

**Examples:**

```agda
-- Unicode throughout
id : {A : Set} → A → A
id x = x

-- Lambda
map : {A B : Set} → (A → B) → List A → List B
map f xs = λ { [] → [] ; (x ∷ xs) → f x ∷ map f xs }
```

**Unicode Input** (in Emacs agda-mode):

- `\->` inputs `→`
- `\=>` inputs `⇒`
- `\lambda` inputs `λ`

### Haskell Syntax

**Official Documentation:**

- [Haskell 2010 Report - Expressions](https://www.haskell.org/onlinereport/haskell2010/haskellch3.html)
- [Haskell 2010 Report - Types](https://www.haskell.org/onlinereport/haskell2010/haskellch4.html)

**Examples:**

```haskell
-- Same arrow for types and terms
id :: a -> a
id x = x

-- Lambda
map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
  [] -> []
  (x:xs) -> f x : map f xs

-- Lambda expression
(\x -> x + 1)
```

**Parser behavior:**

- Context determines meaning of `->`
- After `::` or in type signature: function type
- After `\` or `case`: term-level arrow

### Other Language References

- [Idris 2 Tutorial](https://idris2.readthedocs.io/en/latest/tutorial/index.html)
- [Scala Language Specification](https://scala-lang.org/files/archive/spec/2.13/)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Agda Documentation](https://agda.readthedocs.io/)
- [Haskell 2010 Report](https://www.haskell.org/onlinereport/haskell2010/)
- [Arrow Functions in JavaScript (MDN)](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/Arrow_functions)
