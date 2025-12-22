---
description: Create a conventional commit for current changes
allowed-tools: Bash(git:*)
---

Create a git commit following conventional commit format.

**Instructions:**

1. Run `git status` and `git diff` to analyze changes
2. If there are unstaged changes to include, stage them with `git add`
3. Check recent commits with `git log --oneline -5` for style reference
4. Determine the appropriate commit type:
   - feat: New feature
   - fix: Bug fix
   - refactor: Code change (no new feature or bug fix)
   - docs: Documentation only
   - chore: Build process, dependencies
   - test: Adding or correcting tests
5. Write a concise commit message in imperative mood
6. Create the commit
