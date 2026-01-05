# Product Guidelines

## Communication Style
- **Technical & Precise:** Given the project's roots in type theory and sequent calculus, documentation and communication should prioritize accuracy and correct terminology (e.g., "producer" vs "consumer", "data" vs "codata").
- **Research-Oriented:** Discussions should often reference relevant papers or theoretical concepts where applicable.
- **Clear & Structured:** Complex topics (like the λμμ̃-calculus IR) should be broken down clearly, but without oversimplifying the underlying mathematics.

## Design Philosophy
- **Symmetry First:** Design decisions should prioritize the duality between data and codata. If a feature exists for one, its dual should likely exist for the other.
- **Explicit over Implicit:** The IR should make control flow and evaluation order explicit.
- **Minimalism:** The core language should remain small and orthogonal, with features built upon the fundamental primitives of the sequent calculus.

## Development Standards
- **Formal Verification Mindset:** While not everything needs a proof, the code should be written with an awareness of the underlying properties being preserved (e.g., type safety, termination).
- **Golden Testing:** Maintain a robust suite of golden tests to catch regressions in parsing, type inference, and evaluation.
- **AI-Native:** Embrace the use of AI tools for generating boilerplate, writing tests, and exploring implementation strategies, while maintaining strict human review for correctness.
