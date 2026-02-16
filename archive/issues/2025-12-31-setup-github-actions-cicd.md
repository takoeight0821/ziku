---
date: 2025-12-31
title: Set up GitHub Actions CI/CD pipeline
status: in-progress
---

# Set up GitHub Actions CI/CD pipeline

## Description

Implement a comprehensive CI/CD pipeline using GitHub Actions to automate testing, building, and release processes for the Ziku project.

## Context

The Ziku project currently lacks automated CI/CD. Setting up GitHub Actions will ensure code quality and streamline the development workflow.

## Proposed Features

### Continuous Integration (CI)

- **Build verification**: Run `lake build` on every push and PR
- **Automated testing**: Execute `lake test` (golden tests for parser, eval, infer, ir-eval)
- **Multi-platform support**: Consider testing on ubuntu-latest (primary), potentially macOS

### Continuous Deployment (CD)

- **Release automation**: Create releases when tags are pushed
- **Artifact publishing**: Build and attach binaries to releases

## Implementation Tasks

- [x] Create `.github/workflows/lean_action_ci.yml` for build and test workflow
- [x] Configure Lean 4 / Lake toolchain setup in Actions
- [x] Set up caching for Lake dependencies (`.lake/` directory)
- [x] Add status badge to README
- [ ] (Optional) Create release workflow for tagged commits

## Technical Considerations

- Use `leanprover/lean4-action` or manual elan setup
- Cache `.lake/` and `.elan/` directories to speed up builds
- Consider matrix builds for multiple Lean versions if needed

## References

- [Lean 4 GitHub Action](https://github.com/leanprover/lean4-action)
- [Lake documentation](https://github.com/leanprover/lake)
