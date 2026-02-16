# Anma: A Research Programming Language with Copattern Matching

## Overview

- **Repository**: https://github.com/takoeight0821/anma
- **Author**: Yuya Kono (takoeight0821)
- **License**: Not specified (research project)
- **Implementation Language**: Go (98.4%), Nix (1.6%)
- **Stars**: 2
- **Created**: October 9, 2023
- **Last Updated**: June 30, 2024
- **Status**: Research/experimental

## Purpose

Anma is a research programming language designed as the successor to [Malgo](https://github.com/malgo-lang/malgo). It serves as the practical implementation of the copattern matching compilation algorithm described in the author's Master's thesis (2024).

## Features

According to the README, Anma supports:

- **First-class functions**: Functions are values that can be passed around
- **Anonymous functions**: Lambda expressions with copattern syntax
- **Records**: Object-like structures with named fields
- **(Co)patterns**: Both pattern matching and copattern matching
- **Continuation-passing style IO**: CPS-based I/O operations

## Syntax

### Grammar (EBNF excerpt)

```ebnf
decl = typeDecl | varDecl | infixDecl
varDecl = "def" IDENT "=" expr | "def" IDENT ":" type | "def" IDENT ":" type "=" expr
expr = let | with | assert
codata = "{" clause ("," clause)* ","? "}"
clause = clauseHead "->" clauseBody | clauseBody
clauseHead = "(" ")" | "(" pattern ("," pattern)* ","? ")" | pattern
pattern = methodPat
methodPat = atomPat (accessPatTail | callPatTail)*
```

### Example: Fibonacci Stream

```anma
def + = { #(x, y,) -> prim(add, x, y) }

def zipWith = {
  #(f, xs, ys).head -> f(xs.head, ys.head),
  #(f, xs, ys).tail -> zipWith(f, xs.tail, ys.tail),
}

def fib = {
  #.head -> 1,
  #.tail.head -> 1,
  #.tail.tail -> zipWith({#(x, y) -> x + y}, fib, fib.tail),
}

def main = { #() -> prim(print, fib.tail.tail.tail.head) }
```

### Example: Method-Style Copatterns

```anma
def printer = {
  #.print(x) -> prim(print, x),
}

def main = { printer.print(1) }
```

### Example: CPS I/O

```anma
def main = {
    let exit = { prim(exit) };
    let print = { s -> prim(print_cps, s, exit) };
    prim(read_all_cps, print)
}
```

## Architecture

### Compilation Pipeline

```
Source Code
    │
    ▼
┌──────────────┐
│    Parser    │  → AST with Codata nodes
└──────────────┘
    │
    ▼
┌──────────────┐
│ DesugarWith  │  → Desugars `with` expressions
└──────────────┘
    │
    ▼
┌──────────────┐
│  Codata.Flat │  → Transforms Codata to Object/Lambda/Case
└──────────────┘
    │
    ▼
┌──────────────┐
│InfixResolver │  → Resolves infix operators
└──────────────┘
    │
    ▼
┌──────────────┐
│ NameResolve  │  → Name resolution
└──────────────┘
    │
    ▼
┌──────────────┐
│  Evaluator   │  → Tree-walking interpreter
└──────────────┘
```

### Module Structure

| Module | Description |
|--------|-------------|
| `ast/` | AST node definitions with Plate pattern for traversal |
| `lexer/` | Tokenizer |
| `parser/` | Recursive descent parser |
| `codata/` | **Core copattern flattening algorithm** |
| `desugarwith/` | Desugaring for `with` expressions |
| `infix/` | Infix operator resolution with precedence |
| `nameresolve/` | Variable name resolution |
| `eval/` | Tree-walking evaluator |
| `driver/` | Pass runner orchestration |
| `token/` | Token type definitions |
| `utils/` | S-expression printer and utilities |

## Core Algorithm: Copattern Flattening

The key innovation is in `codata/flat.go`, which implements the thesis algorithm for transforming copattern matching into standard constructs.

### Algorithm Overview

The `Flat` transformation converts `Codata` nodes into combinations of:
- `Object` (records with fields)
- `Lambda` (functions)
- `Case` (pattern matching)

### Pattern List Construction

```go
// makePatternList makes a sequence of patterns from a pattern.
// For example, if the pattern is `#.f(x, y)`, the sequence is `[#.f, #(x, y)]`.
func makePatternList(pattern ast.Node) []ast.Node {
    switch pattern := pattern.(type) {
    case *ast.This:
        return []ast.Node{}
    case *ast.Access:
        pl := makePatternList(pattern.Receiver)
        return append(pl, &ast.Access{...})
    case *ast.Call:
        pl := makePatternList(pattern.Func)
        return append(pl, &ast.Call{...})
    }
}
```

### Build Strategy

The algorithm dispatches based on the kind of copattern:

```go
func (f *Flat) build(plists, bodys) (ast.Node, error) {
    if anyEmpty(plists) {
        return f.buildCase(plists, bodys)  // Generate pattern match
    }
    kind := kindOf(plists)
    switch kind {
    case Field:
        return f.buildObject(plists, bodys)  // Generate record
    case Function:
        return f.buildLambda(plists, bodys)  // Generate lambda
    case Mismatch:
        return nil, MismatchError{...}
    }
}
```

### Transformation Examples

**Field copatterns → Object:**
```
{ #.head -> 0, #.tail -> ... }
⟹
{ head: 0, tail: ... }
```

**Function copatterns → Lambda:**
```
{ #(x) -> x + 1 }
⟹
λx. x + 1
```

**Mixed copatterns → Nested structures:**
```
{ #(f, xs, ys).head -> f(xs.head, ys.head),
  #(f, xs, ys).tail -> zipWith(f, xs.tail, ys.tail) }
⟹
λf. λxs. λys. {
  head: f(xs.head, ys.head),
  tail: zipWith(f, xs.tail, ys.tail)
}
```

## Runtime Values

The evaluator supports these value types:

| Type | Description |
|------|-------------|
| `Int` | Integer values |
| `String` | String values |
| `Tuple` | Fixed-size tuples |
| `Function` | Closures with captured environment |
| `Object` | Records with named fields |
| `Data` | Algebraic data type values |
| `Constructor` | ADT constructors |
| `Thunk` | Lazy evaluation for object fields |

### Pattern Matching

Values implement the `match` interface for pattern matching:
```go
type Value interface {
    fmt.Stringer
    match(pattern ast.Node) (map[Name]Value, bool)
}
```

## AST Design

The AST uses the **Plate pattern** (inspired by Haskell's `lens` library) for generic traversals:

```go
type Node interface {
    Base() token.Token
    Plate(err error, fun func(Node, error) (Node, error)) (Node, error)
}

// Traverse the Node in depth-first order
func Traverse(n Node, f func(Node, error) (Node, error)) (Node, error) {
    n, err := n.Plate(nil, func(n Node, _ error) (Node, error) {
        return Traverse(n, f)
    })
    return f(n, err)
}
```

This allows uniform transformation of all AST nodes without explicit recursion.

## Relationship to Malgo

| Aspect | Malgo | Anma |
|--------|-------|------|
| **Implementation** | Haskell | Go |
| **Type System** | Statically typed with inference | Dynamically typed (currently) |
| **Target** | LLVM IR | Tree-walking interpreter |
| **Copatterns** | Not supported | Core feature |
| **Focus** | Production language | Research/prototyping |

Anma was created specifically to prototype and validate the copattern compilation algorithm from the thesis, which will eventually be incorporated into future versions of Malgo.

## Building and Running

### Prerequisites
- Go 1.21+
- Nix (optional, for reproducible builds)

### Run with Input File
```bash
go run . -i testdata/fib.anma
```

### REPL Mode
```bash
go run .
> def x = 42
> x
42
```

## Implementation Details

### Key Design Decisions

1. **Go over Haskell**: Chosen to demonstrate that the algorithm doesn't require advanced type system features
2. **Tree-walking interpreter**: Simple evaluation model suitable for research
3. **Thunks for laziness**: Object fields are lazily evaluated to support infinite structures
4. **First-match semantics**: Copattern clauses are matched in declaration order

### Error Handling

The codebase uses Go's error handling with position information:
```go
type PosError struct {
    Where token.Token
    Err   error
}
```

## Related Projects

- [Malgo](https://github.com/malgo-lang/malgo) - The author's statically typed functional language in Haskell
- [thesis_2024](https://github.com/takoeight0821/thesis_2024) - Master's thesis documenting the algorithm
- [hoc_nyan](https://github.com/takoeight0821/hoc_nyan) - The author's C compiler

## Limitations

- No type system (dynamically typed)
- No tail call optimization
- Limited standard library
- Research prototype, not production-ready

## Future Directions

Based on the milestone document:
1. Integer, Arithmetic, Bit Manipulation
2. String operations
3. Function improvements
4. Object enhancements
5. Rune, Stream support
6. Variant, Pattern Matching
7. Copattern extensions
8. Type system

## Sources

- [Anma Repository](https://github.com/takoeight0821/anma)
- [Malgo Repository](https://github.com/malgo-lang/malgo)
- [Author's Blog (星にゃーんのブログ)](https://takoeight0821.hatenablog.jp)
- [Copatterns: Programming Infinite Structures by Observations (Abel et al. 2013)](https://dl.acm.org/doi/10.1145/2480359.2429075)
- [Unnesting of Copatterns (Setzer et al. 2014)](https://link.springer.com/chapter/10.1007/978-3-319-08918-8_3)
