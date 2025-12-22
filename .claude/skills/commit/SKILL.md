---
name: commit
description: This skill should be used when the user asks to "create a commit", "commit changes", "write a commit message", "make a commit", needs help with "conventional commits", or wants to understand commit message format and best practices.
---

# Conventional Commit Guidelines

Guidance for creating well-structured commit messages following the Conventional Commits specification.

## Commit Message Structure

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

## Commit Types

| Type | When to Use |
|------|-------------|
| `feat` | New feature or capability added |
| `fix` | Bug fix |
| `refactor` | Code change that neither fixes a bug nor adds a feature |
| `docs` | Documentation only changes |
| `style` | Formatting, whitespace, semicolons (no code change) |
| `test` | Adding or correcting tests |
| `chore` | Build process, dependencies, auxiliary tools |
| `perf` | Performance improvement |
| `ci` | CI/CD configuration changes |
| `build` | Build system or external dependency changes |
| `revert` | Reverting a previous commit |

## Writing Good Commit Messages

### Description Guidelines

- Use imperative mood ("add feature" not "added feature")
- Keep under 50 characters when possible
- Do not end with a period
- Focus on the "what" and "why", not the "how"

### Examples

**Good:**
```
feat: add user authentication endpoint
fix: resolve null pointer in data parser
refactor: extract validation logic to helper
docs: update API documentation for v2
chore: update dependencies to latest versions
```

**With scope:**
```
feat(auth): add OAuth2 support
fix(parser): handle empty input gracefully
refactor(api): simplify request handling
```

**With body:**
```
feat: add rate limiting to API endpoints

Implement token bucket algorithm for rate limiting.
Default limit is 100 requests per minute per user.

Closes #123
```

## Commit Workflow

1. Review changes with `git status` and `git diff`
2. Determine the appropriate commit type based on the nature of changes
3. Identify scope if changes are focused on a specific component
4. Write a concise description in imperative mood
5. Add body for complex changes explaining the "why"
6. Include footer for issue references or breaking changes

## Breaking Changes

Mark breaking changes with `!` after type/scope:

```
feat!: remove deprecated API endpoints
feat(api)!: change response format to JSON:API
```

Or include `BREAKING CHANGE:` in the footer:

```
feat: update authentication flow

BREAKING CHANGE: JWT tokens now expire after 1 hour instead of 24 hours
```
