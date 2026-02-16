---
date: 2026-01-05
title: Multi-argument Covalues
status: open
---

# Feature Request: Multi-argument Covalues

## Context
This feature was identified as out-of-scope during the initial implementation of "First Class Covalues" (Track: `first_class_covalues`).

## Description
Currently, first-class covalues (continuations) are typically unary (accepting a single value). The underlying IR might support multi-argument consumers (via multiple `mu` binders or destructors), but the surface language support is limited.

## Goals
- Support defining and using covalues that accept multiple arguments.
- Example syntax might need extension: `\~k(a, b) => ...` or similar.
- Ensure `goto` can handle multiple arguments if targeting such a covalue.