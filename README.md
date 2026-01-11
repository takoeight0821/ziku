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

### Docker (Recommended)

No local dependencies required:

```bash
docker build -t ziku .                                        # Build image
docker run --rm -it ziku nix develop --command lake exe ziku  # Run REPL
docker run --rm ziku nix develop --command lake test          # Run tests
```

### Native

Requires [Lean 4](https://lean-lang.org/) and [Chez Scheme](https://cisco.github.io/ChezScheme/):

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

## For Developers

### Dependency Management

This project uses Renovate for automated dependency updates and Nix flakes for reproducible builds.

**Renovate Setup (for maintainers):**

1. **Create a GitHub App**

   GitHub Settings → Developer settings → GitHub Apps → **New GitHub App**

   Required settings:
   - **GitHub App name**: `renovate-ziku` (or any name)
   - **Homepage URL**: `https://github.com/takoeight0821/ziku`
   - **Webhook**: Uncheck "Active"

   **Repository permissions** (set all of the following):
   - Checks: Read and write
   - Contents: Read and write
   - Commit statuses: Read and write
   - Issues: Read and write
   - Pull requests: Read and write
   - Workflows: Read and write
   - Metadata: Read only (auto-set)

   After creation:
   - Note the **App ID** (needed later)
   - Click **Generate a private key** to download the `.pem` file

2. **Install the App to the repository**

   From the GitHub App page:
   - **Install App** → **Only select repositories** → Select `takoeight0821/ziku`
   - Get the **Installation ID** from the URL after installation
     - Example: `12345678` from `https://github.com/settings/installations/12345678`

3. **Add secrets to GitHub Actions**

   Repository Settings → Secrets and variables → Actions → **New repository secret**:
   - `RENOVATE_APP_ID`: The App ID from step 1
   - `RENOVATE_APP_PRIVATE_KEY`: The entire contents of the downloaded `.pem` file

4. **Verify**

   Actions → Renovate → **Run workflow** to trigger manually

**Auto-updated dependencies:**
- GitHub Actions (weekly, Mondays 9:00 UTC)
- Nix flake inputs (nixpkgs, flake-utils)
- Git submodules
- Lean toolchain
- Lake dependencies

See [CLAUDE.md](CLAUDE.md) for detailed dependency management information.

## Background

Ziku is inspired by ["Grokking the Sequent Calculus" (ICFP 2024)](https://dl.acm.org/doi/10.1145/3674639), implementing a λμμ̃-calculus based intermediate representation that makes the duality between data and codata explicit.

## License

See [LICENSE](LICENSE) file.
