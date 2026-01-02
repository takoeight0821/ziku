# Ziku Language Reference

Complete syntax reference for the Ziku programming language.

## Literals

| Type | Syntax | Examples |
|------|--------|----------|
| Integer | Decimal digits | `0`, `42`, `-5` |
| Float | Digits with decimal point | `3.14`, `-0.5` |
| String | Double-quoted | `"hello"`, `"line\nbreak"` |
| Character | Single-quoted | `'a'`, `'\n'` |
| Boolean | Keywords | `true`, `false` |
| Unit | Empty parentheses | `()` |

## Operators

### Arithmetic Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `+` | Addition | `1 + 2` |
| `-` | Subtraction | `5 - 3` |
| `*` | Multiplication | `4 * 5` |
| `/` | Division | `10 / 2` |
| `-` (unary) | Negation | `-x` |

### Comparison Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `==` | Equal | `x == y` |
| `!=` | Not equal | `x != y` |
| `<` | Less than | `x < y` |
| `<=` | Less than or equal | `x <= y` |
| `>` | Greater than | `x > y` |
| `>=` | Greater than or equal | `x >= y` |

### Logical Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `&&` | Logical and | `a && b` |
| `\|\|` | Logical or | `a \|\| b` |
| `not` | Logical not | `not x` |

### Other Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `++` | String concatenation | `"a" ++ "b"` |
| `\|>` | Pipe (left-to-right application) | `x \|> f \|> g` |

### Operator Precedence (highest to lowest)

1. Function application
2. Unary `-`, `not`
3. `*`, `/`
4. `+`, `-`
5. `++`
6. `<`, `<=`, `>`, `>=`
7. `==`, `!=`
8. `&&`
9. `||`
10. `|>`

## Expressions

### Variables

```
identifier
```

Identifiers start with a letter or underscore, followed by letters, digits, or underscores.

### Let Binding

```
let name = expr in body
let name : type = expr in body
```

### Recursive Let Binding

```
let rec name = expr in body
```

### Lambda Abstraction

```
\param => body
\param1, param2 => body
\param1 => \param2 => body
```

### Function Application

```
f x
f x y
f(x)
f(x)(y)
```

### Conditional

```
if condition then consequent else alternative
```

### Pattern Matching

```
match expr with
| pattern1 => result1
| pattern2 => result2
| _ => default
end
```

### Codata (Copattern Matching)

Codata is defined by specifying responses to observations. The `#` symbol represents the object being defined.

```
{ #.field => value }                        // Field observation
{ #(param) => body }                        // Call observation
{ #.field1 => value1, #.field2 => value2 }  // Multiple fields
{ #(p1)(p2) => body }                       // Multiple parameters
{ #.field => value, #(x) => body }          // Mixed observations
```

**Reading copatterns:**
- `#.x => 10` means "when `.x` is accessed, return `10`"
- `#(x) => x + 1` means "when called with `x`, return `x + 1`"

### Record

```
{ field1 = value1, field2 = value2 }
```

### Field Access

```
expr.field
expr.field1.field2
```

### Label/Goto

```
label name { body }
goto(value, name)
```

### Type Annotation

```
(expr : type)
```

## Patterns

| Pattern | Description | Example |
|---------|-------------|---------|
| Variable | Binds matched value | `x` |
| Wildcard | Matches anything | `_` |
| Literal | Matches exact value | `0`, `true`, `"hello"` |
| Constructor | Matches data constructor | `Cons x xs` |

## Copatterns

Copatterns define how codata responds to observations. The `#` represents the object being defined.

| Copattern | Description | Meaning | Example |
|-----------|-------------|---------|---------|
| Field | Field access | "when `.f` is accessed..." | `#.x => 42` |
| Application | Function call | "when called with arg..." | `#(x) => x + 1` |
| Chained field | Nested access | "when `.f.g` is accessed..." | `#.a.b => 0` |
| Chained call | Curried call | "when called with two args..." | `#(x)(y) => x + y` |
| Mixed | Field then call | "when `.f` is called..." | `#.method(x) => x` |

## Types

### Base Types

| Type | Description |
|------|-------------|
| `Int` | Integer numbers |
| `Float` | Floating-point numbers |
| `String` | Text strings |
| `Char` | Single characters |
| `Bool` | Boolean values |
| `Unit` | Unit type (single value `()`) |

### Type Constructors

```
List a          // List of a
Option a        // Optional value
```

### Function Types

```
Int -> Int              // Function from Int to Int
Int -> Int -> Int       // Curried function
(Int -> Int) -> Int     // Higher-order function
```

### Record Types

```
{ x : Int, y : Int }
```

### Type Variables

Lowercase identifiers represent polymorphic type variables:

```
a -> a                  // Identity function type
a -> b -> a             // Constant function type
```

### Polymorphic Types

Explicit universal quantification with `forall`:

```
forall a. a -> a           // Identity function type
forall a b. a -> b -> a    // Constant function type
```

### Bottom Type

The bottom type (`⊥`) represents expressions that never return a value.
This is used internally for typing `goto` expressions, which transfer control
and never produce a result at their call site.

```ziku
label result {
  if cond then goto(42, result) + 1  // goto never returns, "+ 1" is dead code
  else 0
}
```

### Row Polymorphism

Record types support row polymorphism through optional row tails:

```
{ x : Int | ρ }            // Record with at least field x, plus unknown fields ρ
```

This allows functions to work with records containing additional fields:

```ziku
let getX = \r => r.x in    // Inferred: { x : a | ρ } -> a
getX { x = 1, y = 2 }      // Works with extended records
```

## Reserved Words

```
let     rec     in      if      then    else
match   with    end     true    false   not
label   goto
```

## Comments

```
// Single-line comment
```

## Escape Sequences (in strings)

| Sequence | Character |
|----------|-----------|
| `\n` | Newline |
| `\t` | Tab |
| `\\` | Backslash |
| `\"` | Double quote |

## Grammar Summary

```
expr ::= literal
       | identifier
       | expr binop expr
       | unaryop expr
       | \params => expr
       | expr expr
       | let identifier = expr in expr
       | let rec identifier = expr in expr
       | if expr then expr else expr
       | match expr with clauses end
       | { copattern-clauses }
       | { field-assignments }
       | expr.identifier
       | label identifier { expr }
       | goto(expr, identifier)
       | (expr : type)
       | (expr)

pattern ::= identifier
          | _
          | literal
          | constructor patterns

type ::= base-type
       | type-var
       | type -> type
       | type-constructor types
       | { field-types }
```
