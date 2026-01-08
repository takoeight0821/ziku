# Specification: GitHub-First Context-Driven Development (CDD) System

## Overview
This track implements a new development system that replaces the current `conductor` framework with a "GitHub-First" approach. Context, planning, and task tracking will live directly on GitHub Issues and Pull Requests, following a standard GitHub Flow (branch-based development). The system will provide CLI tools to manage this lifecycle and expose specific tools for AI agents to interact with GitHub-hosted context.

## Functional Requirements
- **Task Initialization:** A CLI command `task init <optional description>` that:
    - Creates a new GitHub Issue with a standardized template.
    - Automatically sets up the local environment (e.g., creates a branch linked to the issue).
- **GitHub-First Source of Truth:**
    - The GitHub Issue body serves as the primary specification and plan.
    - AI agents read from the Issue to understand requirements and track progress.
- **CLI Automation:**
    - Integration with `gh` CLI or direct GitHub API usage.
    - Tools for agents to read/update issues and manage PRs.
- **Standardized Templates:**
    - GitHub Issue templates for consistent requirement gathering.
    - Pull Request templates with automated checklists.
- **Documentation:**
    - A new set of documentation defining the CDD methodology, replacing the current `conductor/workflow.md`.

## AI Agent Tools (Capabilities)
- **Issue Reader:** Fetches and parses Issue body/metadata.
- **Status Updater:** Modifies Issue body (task lists) or adds progress comments.
- **PR Manager:** Handles creation and descriptive updates of Pull Requests.
- **Context Dumper:** Aggregates Issue content, comments, and PR status into an LLM-optimized context block.

## Acceptance Criteria
- [ ] Running `task init "Feature description"` creates a GitHub Issue and a local branch.
- [ ] AI agent can successfully retrieve its "plan" by reading the GitHub Issue.
- [ ] AI agent can mark a task as complete by updating the GitHub Issue body.
- [ ] A Pull Request can be created with an automated summary derived from the task context.
- [ ] The `conductor` directory is deprecated/replaced by the new CDD documentation and tools.

## Out of Scope
- Migrating existing `conductor` tracks to the new system (new tasks only).
- Multi-repository task management.
