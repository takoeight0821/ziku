# Plan: GitHub-First Context-Driven Development (CDD) System

This plan outlines the implementation of a GitHub-integrated development system to replace the current file-based `conductor` workflow.

## Phase 1: GitHub Integration & Templates [checkpoint: 1af9e09]
Setup the foundational GitHub artifacts (templates) and ensure the environment can interact with the GitHub API.

- [x] Task: Create GitHub Issue templates (Feature, Bug, Task) in `.github/ISSUE_TEMPLATE/` [c03473f]
- [x] Task: Create GitHub Pull Request template in `.github/PULL_REQUEST_TEMPLATE.md` [e604f5c]
- [x] Task: Verify GitHub CLI (`gh`) authentication and basic connectivity in the dev environment [b7ab536]
- [ ] Task: Conductor - User Manual Verification 'Phase 1: GitHub Integration & Templates' (Protocol in workflow.md) [ ]

## Phase 2: CLI Tooling - `task init` [checkpoint: b613e4e]
Implement the primary entry point for the new workflow.

- [x] Task: Implement `task init` CLI logic (branch creation, issue creation via `gh` or API) [b3b28d1]
- [x] Task: Write tests for `task init` ensuring correct branch naming and issue template application [b3b28d1]
- [x] Task: Implement automated linking of the local branch to the created GitHub Issue [bd81541]
- [ ] Task: Conductor - User Manual Verification 'Phase 2: CLI Tooling - `task init`' (Protocol in workflow.md) [ ]

## Phase 3: AI Agent Tools Implementation [ ]
Develop the tools that allow the AI agent to use GitHub as its source of truth.

- [x] Task: Implement `read_github_issue` tool for the agent [6edee5e]
- [ ] Task: Implement `update_github_issue` tool (for progress tracking/task checking) [ ]
- [ ] Task: Implement `manage_github_pr` tool (creation and summary updates) [ ]
- [ ] Task: Implement `dump_github_context` tool (LLM-optimized context aggregation) [ ]
- [ ] Task: Write unit tests for all new GitHub interaction tools using mocks [ ]
- [ ] Task: Conductor - User Manual Verification 'Phase 3: AI Agent Tools Implementation' (Protocol in workflow.md) [ ]

## Phase 4: Methodology Documentation & Deprecation [ ]
Formalize the new workflow and transition away from `conductor`.

- [ ] Task: Write `docs/cdd-workflow.md` defining the new system [ ]
- [ ] Task: Update project `README.md` to point to the new workflow [ ]
- [ ] Task: Create a deprecation notice in the `conductor/` directory [ ]
- [ ] Task: Conductor - User Manual Verification 'Phase 4: Methodology Documentation & Deprecation' (Protocol in workflow.md) [ ]

## Phase 5: Final System Integration Test [ ]
Verify the entire end-to-end flow using the new tools.

- [ ] Task: Perform a "dogfooding" run: use `task init` to create a small dummy task and complete it using the new agent tools [ ]
- [ ] Task: Verify that the GitHub Issue was updated correctly and the PR was managed as expected [ ]
- [ ] Task: Conductor - User Manual Verification 'Phase 5: Final System Integration Test' (Protocol in workflow.md) [ ]
