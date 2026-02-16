# Succinct Compilation for Copattern Matching (Master's Thesis 2024)

## Metadata

- **Title**: 余パターンマッチの簡潔なコンパイル手法 〜観測に基づくオブジェクトの定義と操作のための言語機能の型検査が不要で多様な言語に導入可能な実装方式〜
- **English Title**: Succinct compilation for copattern matching: implementing a functionality that allows observation-based definition of objects and associated operators in a highly applicable way to various languages without requiring type-checking facilities
- **Author**: 河野 雄也 (Yuya Kono)
- **Supervisor**: 川端 英之 (Hideyuki Kawabata)
- **Institution**: 広島市立大学大学院 情報科学研究科 (Hiroshima City University, Graduate School of Information Sciences)
- **Submitted**: July 17, 2024
- **Repository**: https://github.com/takoeight0821/thesis_2024
- **Implementation**: https://github.com/takoeight0821/anma (thesis branch)

## Abstract

> Copattern matching is considered a language feature to simply describe objects, streams, and other codata. Copattern matching describes values in such a way that they are defined in terms of their behavior rather than their structure. It is known that programs using copattern matching can be compiled into combinations of well-known language features such as functions and records. Most existing compilation methods are complex because they compile both copatterns and patterns. Existing methods for typed languages perform type and exhaustiveness checking and compile based on exhaustiveness information. In methods without type information, expressions are converted to ones that does not contain copattern matching by partially evaluating expressions. Although these are used in existing languages, they are difficult to understand and implement due to their complexity. This puts the limit of applicability of copattern matching. We propose a more simple and easy-to-understand compilation method that separates processes of copattern matching from other processes including pattern matching.

## Problem Statement

Modern programming languages need to efficiently handle diverse objects like records with multiple fields, infinite streams, and first-class functions. These are collectively called **codata** (coinductive data). While **copattern matching** provides a unified and elegant way to describe codata, existing compilation methods are complex and tightly coupled with pattern matching, making it difficult to introduce copattern matching to existing languages.

## Key Contributions

1. **Novel Compilation Algorithm**: A succinct algorithm that compiles copattern matching to combinations of functions and records, without requiring type information
2. **Separation of Concerns**: Unlike existing methods, this approach separates copattern compilation from pattern matching, allowing existing pattern match compilers to be reused
3. **Wide Applicability**: The method works for both typed and untyped languages, and can be introduced as syntactic sugar to existing languages
4. **Prototype Implementation**: A working implementation in Go demonstrating the practical feasibility

## Background: Codata and Copattern Matching

### Inductive vs Coinductive Data

- **Inductive data** (帰納的データ): Finite data representable with a finite number of symbols (integers, lists)
- **Coinductive data / Codata** (余帰納的データ): Data potentially requiring infinite symbols (streams, functions)

### What is Copattern Matching?

Copattern matching defines codata by specifying its **behavior** rather than its **structure**.

Example - Fibonacci stream using copatterns:
```
fib = {
  [·].head            → 0
  [·].tail.head       → 1
  [·].tail.tail       → zipWith(+, fib, fib.tail)
}
```

Here:
- `[·]` (hole) represents the codata being defined
- `[·].head`, `[·].tail.head`, `[·].tail.tail` are **copatterns**
- Each copattern describes what happens when the codata is observed in that way

### Terminology

| Term | Japanese | Description |
|------|----------|-------------|
| Copattern | 余パターン | A pattern starting with `[·]` describing an observation |
| Clause | 節 | A pair of copattern and body expression `c → e` |
| Arm | 腕 | The body expression of a clause |
| Codata expression | 余データ式 | A set of clauses `{ ... }` |
| Copattern matching | 余パターンマッチ | The process of matching operations against copatterns |

## Existing Approaches and Their Limitations

### 1. Partial Evaluation Approach (Sullivan 2018, Downen 2019)

- Expands copattern matching by partially evaluating expressions
- Can run right after parsing
- **Limitation**: Requires complex decisions about when to stop evaluation and how to handle recursion

### 2. Type-Based Approach (Setzer 2014, Cockx & Abel 2018)

- Uses type checking and exhaustiveness checking to guide compilation
- Used in Agda and other proof assistants
- **Limitation**: Requires type information, cannot be applied to dynamically typed languages

### Common Problem

Both approaches compile copatterns and patterns simultaneously, making:
- Implementation complex
- Extension/optimization of pattern matching difficult
- Integration with existing languages hard

## Proposed Method

### Core Idea

Transform copattern matching independently from pattern matching using only AST transformations. The algorithm compiles from language L_co (with copattern matching) to L_ob (without copattern matching).

### Compilation Algorithm C

The algorithm `C⟦t⟧_{S;G}` takes:
- `t`: source term
- `S`: list of introduced variables (for tracking function parameters)
- `G`: list of pattern sets (for generating pattern match expressions)

#### Simple Terms (pass-through)
```
C⟦n⟧_{S;G} = n           (n is literal)
C⟦x⟧_{S;G} = x           (x is variable)
C⟦t₁(t₂)⟧_{S;G} = C⟦t₁⟧_{S;G}(C⟦t₂⟧_{S;G})
C⟦t₁.l⟧_{S;G} = C⟦t₁⟧_{S;G}.l
```

#### Function Copattern → Lambda
When copatterns start with function application `[·](p)`:
```
C⟦{ [·](pᵢ) cᵢ → tᵢ }⟧_{S;G} = λx. C⟦{ [·] cᵢ → tᵢ }⟧_{S,x;G,{pᵢ}}
```
The pattern `p` is recorded in `G` for later pattern match generation.

#### Field Access Copattern → Record
When copatterns start with field access `[·].l`:
```
C⟦{ [·].lₖ cᵢ → tᵢ }⟧_{S;G} = { lₖ : C⟦{ [·] cᵢ → tᵢ }⟧_{S;Gₖ} }
```
Generates a record with corresponding fields.

#### Empty Copattern → Pattern Match
When copatterns become empty `[·]`, generate pattern match expressions:
```
C⟦{ [·] → t₁, cⱼ → tⱼ }⟧_{S;G} =
  case S₁, S₂, ..., Sₛ {
    G₁ᵢ, G₂ᵢ, ..., Gₛᵢ → C⟦tᵢ⟧_{ε;ε}
    x₁, x₂, ..., xₛ → C⟦{ cⱼ → tⱼ }⟧_{S;G'}
  }
```

### Example Compilation

The Fibonacci stream:
```
fib_co = {
  [·].head            → 0
  [·].tail.head       → 1
  [·].tail.tail       → zipWith(+, fib_co, fib_co.tail)
}
```

Compiles to:
```
fib_ob = {
  head: 0,
  tail: {
    head: 1,
    tail: zipWith(+, fib_ob, fib_ob.tail)
  }
}
```

### Key Properties

1. **No type information required**: Works on AST alone
2. **Separates concerns**: Pattern matching is preserved in output, can use existing pattern match compilers
3. **Extensible**: Can add pattern matching extensions independently
4. **Implementable as syntactic sugar**: Can be added to existing languages as preprocessing

## Implementation

A prototype implementation was created:
- **Language**: Go
- **Repository**: https://github.com/takoeight0821/anma (thesis branch)
- **Features**: Extended to support multi-argument functions (0 to n arguments)

The implementation is compact and demonstrates the practical applicability of the proposed method.

## Discussion: Application to Existing Languages

### JavaScript
- Records `{l: t}` → JavaScript objects
- Functions `λx. t` → Arrow functions or function expressions
- Pattern matching → Can be simulated with destructuring or conditionals

### Java
- Records → Classes or records (Java 14+)
- Functions → Lambda expressions or anonymous classes
- For languages without first-class functions: Use method call copatterns instead of function application copatterns

### General Guidelines
1. `L_ob` records map to structs, associative arrays, or objects
2. Functions map to closures
3. Language-specific considerations may require customized copattern forms

## Related Work

### Key References

| Paper | Focus |
|-------|-------|
| Abel et al. (POPL 2013) | Introduced copatterns for programming infinite structures |
| Downen et al. (ESOP 2019) | Codata in Action - practical applications |
| Sullivan (2018) | Essence of Codata - partial evaluation approach |
| Setzer et al. (RTA-TLCA 2014) | Unnesting of Copatterns |
| Cockx & Abel (ICFP 2018) | Elaborating Dependent (Co)Pattern Matching |

### Applications of Copattern Matching
- Expressing the Expression Problem (Rendel et al. 2015)
- Symmetric data/codata transformations (Binder et al. 2019)

## Future Work

1. **Soundness proof**: Formal proof that the compilation preserves semantics
2. **Integration with existing languages**: Actual implementation in production language compilers
3. **Further copattern applications**: Exploring new use cases for copattern matching

## Personal Notes

This thesis addresses a practical problem in programming language implementation: how to add copattern matching to languages without massive changes to the compiler infrastructure.

Key insights:
- The separation of copattern and pattern compilation is elegant and practical
- The AST-only approach means it can be implemented as a preprocessing step
- The algorithm is simple enough to be implemented in any language with basic data structures

The implementation in Go (rather than Haskell) demonstrates that the method doesn't require advanced type system features, supporting the claim of wide applicability.

## Sources

- [thesis_2024 Repository](https://github.com/takoeight0821/thesis_2024)
- [Anma Implementation](https://github.com/takoeight0821/anma)
- [Copatterns: Programming Infinite Structures by Observations (Abel et al. 2013)](https://doi.org/10.1145/2480359.2429075)
- [Codata in Action (Downen et al. 2019)](https://doi.org/10.1007/978-3-030-17184-1_5)
- [Unnesting of Copatterns (Setzer et al. 2014)](https://doi.org/10.1007/978-3-319-08918-8_3)
- [Elaborating Dependent (Co)Pattern Matching (Cockx & Abel 2018)](https://doi.org/10.1145/3236770)
