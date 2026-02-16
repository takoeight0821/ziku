# Malgo: A Statically Typed Functional Programming Language

## Overview

**Malgo** is a statically typed functional programming language created by Yuya Kono ([takoeight0821](https://github.com/takoeight0821)). The project has been in development since 2017 and is currently at version 2.0.0.

- **Repository**: [github.com/malgo-lang/malgo](https://github.com/malgo-lang/malgo)
- **Author**: Yuya Kono (takoeight0821)
- **License**: BSD-3-Clause
- **Implementation**: 99.3% Haskell (~224KB)
- **Stars**: 46

## Language Features

### Syntax Highlights
- **Pattern matching** with multi-clause function definitions using `{ }` blocks
- **Algebraic data types** (Sum types like `List`, `Either`)
- **Type annotations** with explicit signatures
- **Operator definitions** with fixity declarations (`infixl`, `infix`)
- **Module system** with imports (`import "path/to/module.mlg"`)
- **Pipe operator** (`|>`) for function composition
- **Records** and **tuples**
- **Copatterns** for codata definitions

### Example (List.mlg)
```malgo
def map : (a -> b) -> List a -> List b
def map =
  { _ Nil -> Nil,
    f (Cons x xs) -> Cons (f x) (map f xs)
  }

def main = {
  sum (map (addInt32 1) (below 10))
    |> toStringInt32
    |> putStrLn
}
```

## Compiler Architecture

The compiler uses a **sequent calculus-based intermediate representation**, which is a notable design choice. The compilation pipeline is:

```
Source (.mlg)
    ↓ Parser
Syntax.Module (Parse)
    ↓ Rename
Syntax.Module (Rename)
    ↓ ToFun
Sequent.Fun.Program
    ↓ ToCore
Sequent.Core.Full.Program
    ↓ Flat
Sequent.Core.Flat.Program
    ↓ Join
Sequent.Core.Join.Program
    ↓ Eval
Execution
```

### Key Intermediate Representations

1. **Fun** (`Malgo.Sequent.Fun`): A functional IR with:
   - Variables, Literals, Constructs
   - Lambda, Let, Apply
   - Select (pattern matching), Invoke

2. **Core.Full** (`Malgo.Sequent.Core.Full`): Sequent calculus-based IR with:
   - **Producers**: Values (Var, Literal, Construct, Lambda, Object, Do)
   - **Consumers**: Continuations (Label, Apply, Project, Then, Finish, Select)
   - **Statements**: Interactions (Cut, Primitive, Invoke)

3. **Core.Join** (`Malgo.Sequent.Core.Join`): Final IR with explicit join points for continuations

### Sequent Calculus Design

The core IR uses **Producer/Consumer duality**:
- **Producers** create values
- **Consumers** receive/process values
- **Cut** (written `Cut producer consumer`) represents the interaction between them

This is based on the [Curry-Howard correspondence for classical logic](https://takoeight0821.hatenablog.jp/entry/2021/01/28/230027), where:
- Producers ≈ Proofs/Terms
- Consumers ≈ Continuations/Contexts

### Evaluation

The interpreter (`Malgo.Sequent.Eval`) directly evaluates the Join IR:
- Supports primitives for arithmetic, comparison, string operations
- I/O handled via configurable handlers (stdin, stdout, stderr)
- Values: Immediate (literals), Struct (ADTs), Function, Record, Consumer (continuations)

## Implementation Details

- Built with **Effectful** for effects management
- Uses **s-cargot** for S-expression parsing/printing
- **Happy** parser generator for syntax
- **Data.Store** for serialization of interfaces
- Supports **lazy evaluation semantics** (important for parser combinators)

## Development Tools

- **mise** for task automation
- **Cabal** for building
- Uses **Conventional Commits** for version management

## Notable Technical Aspects

1. **No traditional type checker visible** - The compiler appears to use type inference but the type checking phase is integrated into the renaming/elaboration pass

2. **Strict by default** - The Haskell implementation uses `{-# LANGUAGE Strict #-}` but the language itself supports laziness

3. **Bytecode VM** - There are modules listed for bytecode compilation (`Malgo.Sequent.Bytecode.*`) suggesting planned/WIP native compilation

4. **Interface files** (`.mlgi`) - Supports separate compilation through serialized interfaces

## Related Projects

The author also works on:
- **Koriel**: An experimental intermediate language designed as "lambda calculus with code-generation-friendly semantics"
- **hoc_nyan**: A tiny C compiler written in C

## Sources

- [malgo-lang/malgo on GitHub](https://github.com/malgo-lang/malgo)
- [takoeight0821's Blog - 世の中間言語を集める](https://takoeight0821.hatenablog.jp/entry/2021/01/28/230027)
- [takoeight0821's Blog - Haskellのsomeを正格評価したら無限ループする話](https://takoeight0821.hatenablog.jp/entry/2021/08/29/165851)
