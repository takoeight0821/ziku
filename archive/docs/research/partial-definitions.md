# Justification for Partial Definitions in Ziku

Ziku uses `partial def` in several key areas where termination is either non-guaranteed (by design) or difficult to prove using Lean's automated tactics.

## 1. Evaluators and Interpreters
**Files:** `Ziku/IR/Eval.lean`, `Ziku/IR/BigStepEval.lean`

The Ziku language supports general recursion and fixpoint operators. Consequently, programs written in Ziku may not terminate. The evaluators must reflect this reality. Using `partial def` allows the implementation of these evaluators without providing a termination proof (which would be impossible for a Turing-complete language).

## 2. Parser and Lexer
**Files:** `Ziku/Parser.lean`, `Ziku/Lexer.lean`

The parser and lexer are implemented as recursive descent processors. While they are intended to terminate on all finite inputs, the complex state transitions and nested recursion (especially in expression parsing) make it difficult to define a strictly decreasing metric that Lean can automatically verify. Since these components are performance-sensitive and well-understood, `partial` is used for practical implementation.

## 3. Type Inference
**File:** `Ziku/Infer.lean`

The type inference engine performs unification and constraint solving. Although Hindley-Milner type inference is known to terminate, the implementation of row polymorphism and bottom type propagation introduces complex recursive dependencies. Using `partial` simplifies the implementation of these algorithms while we focus on correctness rather than formal termination proofs.

## 4. Syntax and Utilities
**File:** `Ziku/Syntax.lean`, `Ziku/Translate.lean`, `Ziku/Backend/Scheme.lean`

Various utility functions (like `toString` or `exprSize`) and translation passes traverse the AST recursively. While these are guaranteed to terminate on finite ASTs, `partial` is sometimes used to avoid the overhead of complex termination proofs for functions that are purely for debugging or code generation.
