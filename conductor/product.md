# Product Guide: Ziku

## Initial Concept
A functional programming language exploring the duality between data and codata.

## Target Audience
Ziku is designed for **Programming Language Researchers** exploring the λμμ̃-calculus, **Students** learning about Type Theory and Sequent Calculus through a practical implementation, and **Functional Programming Enthusiasts** interested in modern language design.

## Core Goals
- **Explicit Duality:** Provide a first-class experience for both data (construction) and codata (destruction/behavior).
- **Theoretical Grounding:** Implement a λμμ̃-calculus based intermediate representation that mirrors the symmetries of logic.
- **Practical Exploration:** Offer a usable surface syntax with powerful features like Hindley-Milner type inference and a Scheme backend.

## Key Features
- **Symmetric Matching:** Pattern matching for data types and copattern matching for codata types.
- **Control Flow:** First-class control primitives using `label` and `goto`.
- **Inference:** Robust let-polymorphism via Hindley-Milner type inference.
- **Backend:** High-performance compilation to Chez Scheme.
