# Ziku Language Support for VS Code

Syntax highlighting for the Ziku programming language.

## Features

- Syntax highlighting for `.ziku` files
- Support for:
  - Keywords (`let`, `rec`, `in`, `match`, `if`, `then`, `else`, `label`, `goto`, etc.)
  - Types (`Int`, `Float`, `String`, `Rune`, `Bool`, `Unit`)
  - Constructors (capitalized identifiers)
  - Built-in functions (`strLen`, `strAt`, `strSub`, etc.)
  - Literals (integers, floats, strings, characters, booleans)
  - Comments (single-line `--` and block `{- -}`)
  - Operators (`->`, `=>`, `==`, `!=`, `&&`, `||`, `++`, `|>`, etc.)
  - Special symbols (`#` for self-reference, `_` for wildcard)

## Installation

### From Source

1. Copy the `editors/vscode` directory to your VS Code extensions folder:
   - **macOS**: `~/.vscode/extensions/ziku-lang`
   - **Linux**: `~/.vscode/extensions/ziku-lang`
   - **Windows**: `%USERPROFILE%\.vscode\extensions\ziku-lang`

2. Restart VS Code

### Using Symlink (Development)

```bash
ln -s /path/to/ziku/editors/vscode ~/.vscode/extensions/ziku-lang
```

## Example

```ziku
-- Church numerals
let zero = \f => \x => x in
let succ = \n => \f => \x => f (n f x) in
let toInt = \n => n (\x => x + 1) 0 in
toInt (succ (succ (succ zero)))
```

```ziku
-- Pattern matching
match Just(Pair(1, 2)) {
| Just(Pair(a, b)) => a + b
| Nothing => 0
}
```

```ziku
-- Codata with copattern matching
{
  #.x => { #.y => 42 }
}.x.y
```
