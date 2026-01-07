# Specification: Gemini CLI Sandbox Dockerfile

## Overview
Create a Dockerfile to provide a secure and reproducible sandboxed environment for the Gemini CLI, specifically tailored for developing and testing the Ziku programming language (Lean 4).

## Functional Requirements
- **Base Image:** Use `ubuntu:latest` as the foundation.
- **System Utilities:** Install `git`, `curl`, `wget`, `vim`, `nano`, and `build-essential`.
- **Lean 4 Integration:**
    - Install `elan` (the Lean toolchain manager).
    - Configure `elan` to use the version specified in the project's `lean-toolchain` file.
- **Security & User:**
    - Create a non-root user named `gemini`.
    - Set the working directory to `/home/gemini/workspace`.
    - Ensure the `gemini` user has ownership of their home directory.
- **Execution:**
    - Default command should be `bash`, providing an interactive shell.

## Non-Functional Requirements
- **Layer Optimization:** Minimize the number of layers in the Dockerfile for better performance and smaller image size.
- **Reproducibility:** Ensure the environment is consistent across different host machines.

## Acceptance Criteria
- [ ] Dockerfile builds successfully without errors.
- [ ] Running the container as the `gemini` user works as expected.
- [ ] `lean` and `lake` commands are available and functional within the container.
- [ ] The working directory is correctly set to `/home/gemini/workspace`.

## Out of Scope
- Integration with CI/CD pipelines (to be handled in a separate track).
- Automatic mounting of host volumes (this is a runtime configuration).
