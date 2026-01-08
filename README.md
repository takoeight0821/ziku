# Ziku

[![CI](https://github.com/takoeight0821/ziku/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/takoeight0821/ziku/actions/workflows/lean_action_ci.yml)

A functional programming language exploring the duality between data and codata.

## Features

- **Pattern matching** for data types
- **Copattern matching** for codata types using `#` (self-reference)
- **First-class control** with `label`/`goto`
- **Hindley-Milner type inference** with let-polymorphism
- **Scheme backend** for compilation to Chez Scheme

## Quick Start

```bash
lake build         # Build
lake exe ziku      # Run REPL
lake test          # Run tests
```

## Examples

```ziku
// Arithmetic and let bindings
let x = 10 in x + 1

// Functions
let double = \x => x * 2 in double 5

// Recursion
let rec factorial = \n =>
  if n == 0 then 1
  else n * factorial (n - 1)
in factorial 5

// Codata: define by behavior, not construction
// #.x => 10 means "when .x is accessed, return 10"
let point = { #.x => 10, #.y => 20 } in
point.x + point.y

// Callable codata (functions are codata!)
// #(x) => ... means "when called with x, return ..."
let square = { #(x) => x * x } in
square(5)

// Early return with label/goto
label done {
  if condition then goto(result, done)
  else continue
}
```

## Documentation

- [Getting Started](docs/getting-started.md) - Installation and first steps
- [Tutorial](docs/tutorial.md) - Learn Ziku step by step
- [Reference](docs/reference.md) - Complete language reference
- [Internals](INTERNALS.md) - Implementation details
- [Development Workflow](docs/cdd-workflow.md) - Our GitHub-First development process

## Background

Ziku is inspired by ["Grokking the Sequent Calculus" (ICFP 2024)](https://dl.acm.org/doi/10.1145/3674639), implementing a λμμ̃-calculus based intermediate representation that makes the duality between data and codata explicit.

## License

See [LICENSE](LICENSE) file.
