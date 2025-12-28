# Getting Started

This guide will help you set up Ziku and run your first program.

## Prerequisites

- [Lean 4](https://lean-lang.org/) (version 4.x)
- [Lake](https://github.com/leanprover/lake) (included with Lean 4)

## Installation

Clone the repository and build:

```bash
git clone https://github.com/takoeight0821/ziku.git
cd ziku
lake build
```

## Running the REPL

Start the interactive REPL:

```bash
lake exe ziku
```

You'll see a prompt where you can type expressions:

```
> 1 + 2
3
> "hello" ++ " world"
"hello world"
```

Type `Ctrl+D` or `Ctrl+C` to exit.

## Your First Program

Try these expressions in the REPL:

```ziku
// Arithmetic
1 + 2 * 3

// Let binding
let x = 10 in x + 1

// Lambda function
(\x => x * x)(5)

// Conditional
if 5 > 3 then "yes" else "no"
```

## Next Steps

- [Tutorial](tutorial.md) - Learn Ziku step by step
- [Reference](reference.md) - Complete language reference
