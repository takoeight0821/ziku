---
description: Create a conventional commit for current changes
allowed-tools: Bash(git:*)
---

Create a git commit following conventional commit format.

**Current Status:**
!`git status --short`

**Staged Changes:**
!`git diff --cached --stat`

**Unstaged Changes:**
!`git diff --stat`

**Recent Commits (for style reference):**
!`git log --oneline -5`

**Instructions:**

1. Analyze the changes shown above
2. If there are unstaged changes to include, stage them with `git add`
3. Determine the appropriate commit type (feat, fix, refactor, docs, chore, etc.)
4. Write a concise commit message in imperative mood
5. Create the commit using conventional commit format

Use the commit skill for guidance on commit types and message format.

End the commit message with:
```

Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
```
