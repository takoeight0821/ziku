---
date: 2025-12-31
title: Field access has higher precedence than application
status: closed
---

# Field access has higher precedence than application

## Description

The parser incorrectly parses field access (`.field`) with higher precedence than function application. This causes expressions like `nats 0 .head` to be parsed as `nats (0 .head)` instead of the expected `(nats 0) .head`.

## Context

- File: `Ziku/Parser.lean`
- Field access should bind less tightly than application
- In most languages, postfix operators like field access associate left-to-right with application

## Expected Behavior

```
nats 0 .head
```

Should parse as:

```
(nats 0) .head
```

Meaning: apply `nats` to `0`, then access `.head` on the result.

## Actual Behavior

```
nats 0 .head
```

Parses as:

```
nats (0 .head)
```

Meaning: access `.head` on `0`, then apply `nats` to the result.

## Steps to Reproduce

1. Parse the expression `nats 0 .head`
2. Observe the AST structure shows field access binding to `0` instead of `nats 0`

## Verified Example

Input:
```
fib 5 .tail .tail .head
```

Current (wrong) AST:
```
(App (Var "fib") (Field (Field (Field (Lit 5) "tail") "tail") "head"))
```

Expected AST:
```
(Field (Field (Field (App (Var "fib") (Lit 5)) "tail") "tail") "head")
```

## Root Cause

In `Ziku/Parser.lean`, the precedence chain is:

```
parseAppExpr (lines 452-455)
  → parseFieldExpr (lines 496-510)
    → parseAtomExpr
```

`parseAppExpr` calls `parseFieldExpr` for each argument (line 489), which eagerly consumes `.field` suffixes before returning. This causes field access to bind to individual arguments rather than the accumulated application.

## Suggested Fix

Restructure the parser so that application and field access are at the **same precedence level** with left-to-right associativity. Create a combined `parseAppAndFieldExpr` that:

1. Parses atoms without field access for arguments
2. After each application or field access, checks for both more arguments AND `.field`
3. Processes left-to-right to get correct associativity

Example processing of `fib 5 .tail`:
1. Parse `fib` (atom)
2. See `5`, apply: `(fib 5)`
3. See `.tail`, access: `((fib 5).tail)`
