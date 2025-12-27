# Plan: Implement Codata Elaboration (Final)

Add an elaboration pass that transforms codata expressions into records and curried lambdas before type inference and evaluation, following anma's approach. All record fields are lazy-by-default. `#` is rejected at parse-time when used in expressions. Multi-param copatterns are kept in AST and desugared during elaboration.

## Steps

1. **Refactor lambda to single-param** by changing [Ziku/Syntax.lean](Ziku/Syntax.lean#L110) `Expr.lam` from `List Ident → Expr` to `Ident → Expr`, updating [Ziku/Parser.lean](Ziku/Parser.lean#L552-L563) to desugar `\x, y => e` into `\x => \y => e`, and migrating all existing pattern matches on `lam pos params body` in [Ziku/Eval.lean](Ziku/Eval.lean) and [Ziku/Infer.lean](Ziku/Infer.lean)

2. **Remove `Expr.hash` and reject at parse-time** by deleting `hash` constructor from [Ziku/Syntax.lean](Ziku/Syntax.lean), modifying [Ziku/Parser.lean](Ziku/Parser.lean) to only allow `#` in copattern positions, throw parse error "# can only appear in copattern positions, not in expressions" when found elsewhere, update [docs/syntax.md](docs/syntax.md#L260-L280) to remove "Referencing # in Expressions" section and document explicit naming requirement for self-reference

3. **Make record fields lazy-by-default** in [Ziku/Eval.lean](Ziku/Eval.lean) by wrapping all record field values in closures during record creation and forcing them only on field access, enabling infinite structures

4. **Create [Ziku/Elaborate.lean](Ziku/Elaborate.lean)** implementing anma's transformation: keep `Accessor.call : List Pat` in AST but desugar multi-param `#(x, y)` to nested `#(x) => { #(y) => ... }` during elaboration, classify by first accessor (field/callable/mixed-error), handle arbitrary nesting depth recursively, generate outer `match` for pattern guards, provide descriptive errors with source positions ("incompatible copattern kinds: mixing field accessors with function calls")

5. **Integrate elaboration** into [Ziku/Infer.lean](Ziku/Infer.lean#L155) calling `elaborate` before type inference for `Expr.codata`, into [Ziku/Eval.lean](Ziku/Eval.lean#L96) before evaluation, add golden tests in tests/golden/eval/codata/ and tests/golden/infer/codata/ covering field copatterns, single-param callables, multi-param callables, arbitrary nesting, pattern guards, update [tests/GoldenTest.lean](tests/GoldenTest.lean) and [lakefile.lean](lakefile.lean)

## Further Considerations

None - the plan is complete and ready for implementation.
