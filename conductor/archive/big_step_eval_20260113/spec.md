# Track Spec: Refactor IR Evaluator to a Big-Step Interpreter

## Overview
The current IR evaluator uses a small-step reduction model (μ/μ̃-reduction). While theoretically elegant, it can be complex to implement efficiently and can get stuck on certain patterns. This track aims to implement a big-step interpreter for the λμμ̃-calculus IR.

## Goals
- Implement a big-step evaluator in `Ziku/IR/BigStepEval.lean`.
- Support all existing IR constructs: Producers, Consumers, and Statements.
- Handle built-in functions and control flow (label/goto).
- Ensure compatibility with existing tests.

## Acceptance Criteria
- All existing `ir-eval` golden tests pass with the big-step interpreter.
- The new evaluator handles recursive functions and complex data/codata structures.
- Performance is comparable to or better than the small-step evaluator.
