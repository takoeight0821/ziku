# Technology Stack

## Core Language & Tools
- **Lean 4:** Primary implementation language, chosen for its expressive type system and formal verification capabilities.
- **Lake:** The standard build system and package manager for Lean 4.
- **Chez Scheme:** The target backend for the Ziku compiler, utilizing its efficient runtime and support for CPS-style code.

## Development & CI
- **GitHub Actions:** Automates the build and test pipeline (via `lean_action_ci.yml`).
- **Golden Testing:** A custom test framework that ensures stability by comparing output against known-good "golden" files.
- **Mise:** Used for managing development environment dependencies.

## Architecture & IR
- **Sequent Calculus (λμμ̃):** The core intermediate representation, providing a theoretically grounded model for data/codata duality.
- **CPS Translation:** Used to bridge the gap between the sequent calculus IR and the Scheme backend.
