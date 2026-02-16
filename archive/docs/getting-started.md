# Getting Started

This guide will help you set up Ziku and run your first program.

## Installation

### Docker (Recommended)

The easiest way to get started - no local dependencies required:

```bash
git clone https://github.com/takoeight0821/ziku.git
cd ziku
docker build -t ziku .
```

This may take a few minutes on first build.

### Native (Alternative)

If you prefer a native installation:

**Prerequisites:**
- [Lean 4](https://lean-lang.org/) (version 4.x)
- [Lake](https://github.com/leanprover/lake) (included with Lean 4)
- [Chez Scheme](https://cisco.github.io/ChezScheme/) (for Scheme backend)

```bash
git clone https://github.com/takoeight0821/ziku.git
cd ziku
lake build
```

## Running the REPL

### Docker

```bash
docker run --rm -it ziku nix develop --command lake exe ziku
```

### Native

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

## Running Tests

### Docker

```bash
docker run --rm ziku nix develop --command lake test
```

### Native

```bash
lake test
```

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
