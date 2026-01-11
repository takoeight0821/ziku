# GitHub-First Context-Driven Development (CDD)

This document defines the development workflow for the Ziku project. This methodology prioritizes GitHub Issues and Pull Requests as the primary sources of truth for context, planning, and task tracking.

## The 10-Step Workflow

All developers (including AI agents) must strictly follow these steps:

1.  **Task Initialization**: User gives the initial instruction with `task init`.
2.  **Clarification**: The agent dialogues with the user to clarify the task scope and details.
3.  **Requirements Definition**: The agent writes down the requirements as a GitHub issue draft and seeks user review.
4.  **Issue Creation**: Once approved, the agent creates the GitHub Issue.
5.  **Branch Creation**: The agent creates a local branch linked to the issue.
6.  **Planning**: The agent writes down a detailed implementation plan and seeks user review.
7.  **Empty Commit**: The agent creates an empty commit (`git commit --allow-empty -m "chore: initial commit for PR"`) and pushes it.
8.  **PR Creation**: The agent creates a Pull Request, using the approved plan as the PR body. The plan MUST be formatted as a Markdown TODO list (e.g., `- [ ] Task`).
9.  **Execution**: The agent executes the task, performing commits and pushes, and updating the PR body as progress is made.
10. **Final Review & Merge**: Once the requirements are met, the agent seeks final review. The user merges the PR to complete the task.

## Setup and Prerequisites

**Requirements:**
- GitHub CLI (`gh`) installed and authenticated.
- Local repository setup.

## CLI Tools

### Task Initialization
To start a new task, use GitHub CLI directly:

```bash
# Create issue and linked branch
gh issue create --title "Description of the task" --body "Task details"
gh issue develop <issue-number> --name "task/<issue-number>-slug" --checkout
```

### GitHub CLI Commands
AI agents use standard `gh` commands to manage context:

```bash
# View issue details
gh issue view <number>
gh issue view <number> --comments

# Update issues
gh issue comment <number> --body "Comment text"
gh issue edit <number> --body "New body"

# Manage PRs
gh pr create --title "Title" --body "Body"
gh pr edit <number> --title "New title" --body "New body"
gh pr list --head <branch-name>
```

## Guiding Principles

1.  **GitHub is the Source of Truth**: All context, requirements, and plans live in GitHub Issues/PRs.
2.  **Branch-Based Development**: Every task has its own branch linked to an issue.
3.  **Visibility and Collaboration**: Progress is visible to everyone via the GitHub interface.
4.  **No Reverts**: Do not revert changes unless explicitly asked or if they cause errors.