# Ziku Tutorial

This tutorial introduces Ziku's features step by step.

## 1. Basic Expressions

### Literals

```ziku
42          // Integer
3.14        // Float
"hello"     // String
'c'         // Character
true        // Boolean
false
()          // Unit
```

### Arithmetic

```ziku
1 + 2       // Addition
10 - 3      // Subtraction
4 * 5       // Multiplication
15 / 3      // Division
```

### Comparisons

```ziku
1 < 2       // Less than
3 <= 3      // Less than or equal
5 > 4       // Greater than
5 >= 5      // Greater than or equal
1 == 1      // Equal
1 != 2      // Not equal
```

### Logical Operations

```ziku
true && false   // And
true || false   // Or
not true        // Not
```

### String Concatenation

```ziku
"hello" ++ " world"   // "hello world"
```

## 2. Variables and Let Bindings

### Let Bindings

Bind a value to a name:

```ziku
let x = 10 in x + 1         // 11
let name = "Ziku" in name   // "Ziku"
```

### Nested Bindings

```ziku
let x = 1 in
let y = 2 in
x + y                       // 3
```

### Type Annotations

Optionally specify types:

```ziku
let x : Int = 42 in x
let flag : Bool = true in flag
```

### Recursive Bindings

Use `let rec` for recursive definitions:

```ziku
let rec factorial = \n =>
  if n == 0 then 1
  else n * factorial (n - 1)
in factorial 5              // 120
```

## 3. Functions

### Lambda Syntax

```ziku
\x => x + 1                 // Function that adds 1
\x, y => x + y              // Two parameters
\x => \y => x + y           // Curried form (equivalent)
```

### Function Application

```ziku
(\x => x + 1)(5)            // 6
(\x, y => x + y)(2)(3)      // 5
```

### Named Functions

```ziku
let double = \x => x * 2 in
double 5                    // 10

let add = \x, y => x + y in
add 2 3                     // 5
```

### Pipe Operator

Chain operations with `|>`:

```ziku
5 |> (\x => x + 1)          // 6
5 |> (\x => x + 1) |> (\x => x * 2)  // 12
```

## 4. Conditionals

```ziku
if true then 1 else 0       // 1
if 5 > 3 then "yes" else "no"

let abs = \x =>
  if x < 0 then -x else x
in abs (-5)                 // 5
```

## 5. Pattern Matching

Match values against patterns:

```ziku
match x {
| 0 => "zero"
| 1 => "one"
| _ => "other"
}
```

### Pattern Types

```ziku
// Literal patterns
match n {
| 0 => "zero"
| 1 => "one"
| _ => "many"
}

// Boolean patterns
match flag {
| true => "yes"
| false => "no"
}

// Variable patterns bind the matched value
match x {
| n => n + 1
}
```

### Separator Rules

Both `|` and `,` can be used as separators:

```ziku
// Using pipe (prefix)
match x { | true => 1 | false => 0 }

// Using comma (suffix)
match x { true => 1, false => 0 }

// Trailing comma is OK
match x { true => 1, false => 0, }
```

## 6. Codata and Copatterns

### Data vs Codata

In most languages, you define data by specifying how to **construct** it:

```ziku
// Data: defined by constructors
// A list is either empty (Nil) or has a head and tail (Cons)
Cons 1 (Cons 2 Nil)
```

**Codata** flips this around: you define something by specifying how to **use** it - what happens when you observe or interact with it.

Think of the difference this way:
- **Data**: "Here's how to build it" → then you pattern match to take it apart
- **Codata**: "Here's how it behaves" → you define responses to observations

### Copatterns: Defining Behavior

A **copattern** describes an observation (like accessing a field or calling a function), and you specify what that observation returns.

```ziku
{
  #.x => 10,    // When you observe .x, return 10
  #.y => 20     // When you observe .y, return 20
}
```

The `#` symbol represents "the object being defined" - similar to `this` or `self` in other languages, but used in patterns rather than expressions.

### Field Access

Define an object by specifying what each field returns:

```ziku
let point = {
  #.x => 10,
  #.y => 20
} in
point.x + point.y           // 30
```

Reading `#.x => 10` as: "when someone accesses `.x` on me, return `10`"

### Callable Codata (Functions)

You can define codata that responds to being called:

```ziku
let square = { #(x) => x * x } in
square(5)                   // 25
```

Reading `#(x) => x * x` as: "when someone calls me with argument `x`, return `x * x`"

This is exactly how functions work in Ziku - a lambda `\x => x * x` is sugar for this codata definition.

### Multi-argument Functions

Chain copatterns for multiple arguments:

```ziku
let add = { #(x)(y) => x + y } in
add(2)(3)                   // 5
```

### Combining Fields and Calls

An object can have both fields and be callable:

```ziku
let counter = {
  #.value => 0,
  #(n) => n + 1
} in
counter.value               // 0
counter(5)                  // 6
```

### Infinite Structures

Codata naturally represents infinite or lazy structures because you only define what happens when observed - the structure isn't built until needed:

```ziku
// Infinite stream of ones
let ones = {
  #.head => 1,
  #.tail => ones
} in
ones.tail.tail.head         // 1
```

The stream `ones` is infinite, but we only evaluate what we observe.

### Why Codata Matters

Codata provides:

1. **Laziness by default**: Only compute what's observed
2. **Natural infinite structures**: Streams, processes, servers
3. **Behavioral definitions**: Define objects by their interface, not their representation
4. **Duality with data**: Pattern matching destructs data; copattern matching constructs codata

## 7. Records

### Anonymous Records

```ziku
{ x = 1, y = 2 }
```

### Field Access

```ziku
let point = { x = 10, y = 20 } in
point.x                     // 10
```

### Nested Records

```ziku
let obj = {
  pos = { x = 0, y = 0 },
  name = "origin"
} in
obj.pos.x                   // 0
```

## 8. Control Flow with Label/Goto

`label` and `goto` provide early exit and non-local control flow.

### Basic Label

```ziku
label done { 42 }           // 42
```

### Early Return

```ziku
label exit {
  if condition then goto(result, exit)
  else continue_computation
}
```

### Example: Find First

```ziku
let findFirst = \pred, xs =>
  label found {
    // ... iterate through xs ...
    // When pred matches: goto(element, found)
    // Otherwise: default value
  }
```

The value passed to `goto` becomes the result of the entire `label` block.

## 9. Type Annotations

Add explicit types when needed:

```ziku
(42 : Int)
(\x => x : Int -> Int)
let f : Int -> Int = \x => x + 1 in f 5
```

Types are usually inferred automatically, but annotations help with:
- Documentation
- Resolving ambiguous types
- Catching type errors early

## 10. Complete Examples

### Factorial

```ziku
let rec factorial = \n =>
  if n == 0 then 1
  else n * factorial (n - 1)
in factorial 10
```

### Fibonacci

```ziku
let rec fib = \n =>
  if n <= 1 then n
  else fib (n - 1) + fib (n - 2)
in fib 10
```

### Higher-Order Functions

```ziku
let applyTwice = \f, x => f (f x) in
let addOne = \x => x + 1 in
applyTwice addOne 5         // 7
```

### Codata Stream

```ziku
let ones = {
  #.head => 1,
  #.tail => ones
} in
ones.tail.tail.head         // 1
```

### Early Exit

```ziku
label result {
  let x = compute_something in
  if x < 0 then goto(0, result)
  else x * 2
}
```

## Next Steps

- [Reference](reference.md) - Complete syntax reference
- [Getting Started](getting-started.md) - Installation and setup
