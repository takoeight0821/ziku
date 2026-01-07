---
date: 2026-01-05
title: Store Covalues in Data Structures
status: open
---

# Feature Request: Store Covalues in Data Structures

## Context
This feature was identified as out-of-scope during the initial implementation of "First Class Covalues" (Track: `first_class_covalues`).

## Description
Currently, first-class covalues (continuations) can only be passed as function arguments. We should extend this support to allow storing them in data structures like records, lists, or as fields in other types.

## Goals
- Allow types like `List (~Int)` or `{ callback: ~String }`.
- Update type system and runtime to handle these values safely.