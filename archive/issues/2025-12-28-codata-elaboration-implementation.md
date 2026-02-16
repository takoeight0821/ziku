# Codata Elaboration Implementation

**Date**: 2025-12-28  
**Status**: ✅ Completed

## Overview

Implemented codata elaboration pass that transforms codata expressions into records and curried lambdas before type inference and evaluation, following anma's copattern flattening algorithm.

## Implementation Details

### 1. Lambda Refactoring

- Changed `Expr.lam` from multi-param (`List Ident → Expr`) to single-param (`Ident → Expr`)
- Parser now desugars `\x, y => e` into nested lambdas `\x => \y => e`
- Updated all pattern matches in `Eval.lean` and `Infer.lean`

### 2. Hash Symbol Restrictions

- Removed `Expr.hash` constructor from AST
- Parser now rejects `#` in expression positions with error: "# can only appear in copattern positions, not in expressions"
- Updated documentation to reflect explicit naming requirement for self-reference

### 3. Lazy-by-Default Records

- Extended `Value` type with `closure` and `thunk` constructors
- All record fields are wrapped in thunks during creation
- Field values are forced only on access, enabling infinite structures
- Prevents universe level issues by inlining environment in closure/thunk constructors

### 4. Elaboration Module (`Ziku/Elaborate.lean`)

- **Algorithm**: Classifies copatterns by first accessor kind (field vs. call)
- **Field copatterns** → Records: `{ #.x => e1, #.y => e2 }` becomes `{ x = e1, y = e2 }`
- **Call copatterns** → Curried lambdas: `{ #(x)(y) => e }` becomes `\x => \y => e`
- **Error handling**: Descriptive errors for mixed accessor kinds
- **Recursion**: Handles arbitrary nesting depth recursively
- **Pattern guards**: Basic support (single clause with no patterns)

### 5. Integration Points

- `Ziku/Infer.lean`: Elaboration called before type inference for `Expr.codata`
- `Ziku/Eval.lean`: Elaboration called before evaluation for `Expr.codata`
- Added `Inhabited` instance for `Except ElaborateError Expr` to support partial def compilation

### 6. Testing

- **Eval tests**: `codataField`, `codataCallable`, `codataMultiParam`, `codataNested`
- **Infer tests**: `codata_field`, `codata_callable`, `codata_multi_param`, `codata_nested`
- **Results**: 109 tests passing, 12 failing (pre-existing parser issues)

## Working Examples

```ziku
-- Field copatterns → Record
{
  #.x => 42,
  #.y => 100
}.x  -- Evaluates to 42

-- Single-param callable
{
  #(x) => x + 1
}(5)  -- Evaluates to 6

-- Multi-param callable (curried)
{
  #(x)(y) => x + y
}(3)(4)  -- Evaluates to 7
```

## Known Limitations

1. **Pattern guards**: Only single clause with no patterns supported; general pattern matching not yet implemented
2. **Mixed accessors in nested context**: Parser doesn't fully support syntax like `#(x).value` (combination of call then field access in single clause)
3. **Some existing parser tests**: 12 pre-existing test failures unrelated to this implementation

## Files Modified

- `Ziku/Syntax.lean` - Refactored lambda, removed hash
- `Ziku/Parser.lean` - Lambda desugaring, hash rejection
- `Ziku/Eval.lean` - Lazy evaluation, elaboration integration
- `Ziku/Infer.lean` - Type inference updates, elaboration integration
- `Ziku/Elaborate.lean` - NEW: Elaboration pass implementation
- `Ziku.lean` - Added Elaborate module import
- `docs/syntax.md` - Updated documentation
- `tests/GoldenTest.lean` - Added new test cases
- `tests/golden/eval/*` - Added codata evaluation tests
- `tests/golden/infer/*` - Added codata inference tests

## Future Improvements

1. Implement full pattern guard support with outer match generation
2. Extend parser to handle `#(x).field` syntax
3. Add more comprehensive error messages with examples
4. Consider optimization opportunities in elaboration
5. Add support for codata type declarations (not just expressions)

## References

- [anma repository](https://github.com/takoeight0821/anma) - Reference implementation
- `docs/research/anma.md` - Algorithm documentation
- [Copatterns: Programming Infinite Structures by Observations](https://dl.acm.org/doi/10.1145/2480359.2429075) - Theoretical foundation
