# GitHub-First Context-Driven Development (CDD)

This document defines the development workflow for the Ziku project, replacing the previous `conductor` framework. This methodology prioritizes GitHub Issues and Pull Requests as the primary sources of truth for context, planning, and task tracking.

## Guiding Principles

1. **GitHub is the Source of Truth**: All context, requirements, and plans live in GitHub Issues.
2. **Branch-Based Development**: Every task has its own branch linked to an issue.
3. **Automated Context**: AI agents use specialized tools to "read" the project state from GitHub.
4. **Visibility and Collaboration**: Progress is visible to everyone via the GitHub interface, not hidden in local files.

## The Workflow Lifecycle

### 1. Task Initialization
To start a new task (feature, bug fix, or technical task), use the `task init` CLI tool:

```bash
./scripts/task-init.sh "Description of the task"
```

This command will:
- Create a new GitHub Issue using the `task.md` template.
- Create a local branch named `task/<issue-number>-<slug>`.
- Link the branch to the issue on GitHub.
- Automatically check out the new branch.

### 2. Implementation and Iteration
During implementation, the AI agent (or human developer) follows the standard development cycle:
- **Red**: Write failing tests.
- **Green**: Implement code to pass tests.
- **Refactor**: Improve code quality.

AI agents should use the following tools to manage context:
- `scripts/github/dump_context.sh`: Aggregates issue details and PR status into a single block for the LLM.
- `scripts/github/read_issue.sh <number>`: Reads the full content of a specific issue.
- `scripts/github/update_issue.sh <number> <action> <content>`: Updates the issue (comments or body).

### 3. Pull Request and Review
Once a task or sub-task is ready for review:

1. **Create/Update PR**:
   ```bash
   ./scripts/github/manage_pr.sh create "Title" "Body"
   ```
2. **Verify Checklist**: Ensure all items in the `.github/PULL_REQUEST_TEMPLATE.md` are addressed.
3. **Review**: Human review occurs on the GitHub PR interface.

### 4. Completion
A task is considered done when:
- The PR is approved and merged.
- All tests pass in CI.
- The corresponding GitHub Issue is closed.

## Agent Tool Reference

| Tool | Purpose |
| :--- | :--- |
| `scripts/task-init.sh` | Start a new task and setup environment. |
| `scripts/github/dump_context.sh` | Get full task context (issue + comments + PR). |
| `scripts/github/read_issue.sh` | Fetch issue details. |
| `scripts/github/update_issue.sh` | Progress tracking (marking task lists, commenting). |
| `scripts/github/manage_pr.sh` | Lifecycle management of Pull Requests. |

## Deprecation of Conductor
The `conductor/` directory and its associated `plan.md` files are now deprecated. New development should strictly follow the CDD workflow. Existing tracks in `conductor/` should be finished using the old workflow or migrated if they are long-running.
