# Spec: Fix IR Evaluator Stuck on Complex Patterns

## Problem Statement
The current IR evaluator in Ziku uses a substitution-based model for reducing $\mu$ and $\mũ$ abstractions. In complex programs (like the MAL implementation), this leads to exponential code growth (code explosion) during evaluation, eventually causing the evaluator to exhaust its fuel limit or return a `Stuck` state when it cannot find a reduction rule due to the sheer size and complexity of the IR term.

## Proposed Solution
Refactor the IR evaluator from a substitution-based model to an environment-based model.

### Key Changes
1.  **Introduce Environments:** Create a data structure to store mappings from variables to their values (or thunks).
2.  **Closures:** Define a closure type that pairs an abstraction ($\mu$, $\mũ$, or `cocase`) with its environment.
3.  **Evaluator Update:** Modify the evaluation rules to look up variables in the environment instead of performing textual substitution.
4.  **Handle Duality:** Ensure the environment-based model correctly handles both producers (values) and consumers (continuations).

## Acceptance Criteria
1.  The test `tests/golden/ir-eval/success/mal_step3_eval.ziku` completes successfully within a reasonable fuel limit using the IR evaluator.
2.  All existing golden tests in `tests/golden/ir-eval/` continue to pass.
3.  Evaluation performance is significantly improved for complex nested expressions.
