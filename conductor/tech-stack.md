# Technology Stack: Ziku

## Primary Language
- **Lean 4**: Used for the language implementation (Parser, Type Inference, IR, Evaluator) and formal proofs of correctness.

## Backend and Compilation
- **Chez Scheme**: The primary compilation target. Ziku's IR is translated to Scheme for high-performance execution.
- **FFI (Foreign Function Interface)**: A dynamic wrapper mechanism in the Scheme backend that enables Ziku to call native host procedures with runtime arity checking and automatic currying.

## Infrastructure and Tooling
- **Lake**: The build system and package manager for the Lean 4 codebase.
- **Nix Flakes**: Ensures reproducible development environments by pinning all external dependencies (Chez Scheme, elan, etc.).
- **Docker**: Provides a consistent environment for CI/CD and simplifies local setup.

## Continuous Integration and Delivery
- **GitHub Actions**: Automates building, testing, and linting.
- **Renovate**: Handles automated dependency updates for Nix, GitHub Actions, and Lake.

## Testing Framework
- **Golden Tests**: A custom testing infrastructure for verifying parser output, type inference, and IR evaluation.
