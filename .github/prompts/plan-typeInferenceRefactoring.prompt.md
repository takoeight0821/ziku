# Plan: Implement Ziku Type Inference with Refactoring-First Approach (Final)

Implement type inference by refactoring the AST to include source positions, building a monadic architecture with detailed error messages, creating a recursive test discovery system, then implementing core HM, patterns, records, codata, and sequent calculus features with simple substitutions and raw type variable names. Remove `partial` where structural recursion can be proven.

## Steps

1. **Add SourcePos to AST** - Add `pos : SourcePos` field to every constructor in [Expr](Ziku/Syntax.lean#L60-L81), [Pat](Ziku/Syntax.lean#L49-L54), and [Ty](Ziku/Syntax.lean#L40-L46), update [Parser.lean](Ziku/Parser.lean) to thread `currentPos` through all parsing functions and store in constructors, update [Eval.lean](Ziku/Eval.lean), [toString](Ziku/Syntax.lean#L177-L216), and all pattern matches (~50 locations), add dummy positions in [Main.lean](Main.lean) REPL for backward compatibility

2. **Refactor to InferM Monad with Detailed Errors** - Add `TypeError` type with `SourcePos`, `expected : Ty`, `actual : Ty`, and `message : String` fields to [Infer.lean](Ziku/Infer.lean), create `StateT InferState (ExceptT TypeError IO)` monad, rewrite all 11 inference cases to use `do` notation, implement `zonk` applying current substitution, add `occursCheck` throwing `TypeError.infiniteType pos var ty`, add helper `unifyAt : SourcePos → Ty → Ty → InferM Unit` with detailed messages

3. **Build Recursive Test Infrastructure** - Implement `walkDirectory : String → IO (List String)` in [GoldenTest.lean](tests/GoldenTest.lean) finding all `.ziku` files recursively, modify [runCategory](tests/GoldenTest.lean#L49-L67) to use relative paths from category root, add `runInferTest : String → Except String String` calling `infer` and formatting `TypeError` with position, create directory structure [tests/golden/infer/](tests/golden/infer/) with `literals/`, `operators/`, `functions/`, `bindings/`, `errors/`, populate with 20 basic tests

4. **Fix Core HM Soundness** - Add `Scheme` type `mono : Ty → Scheme | forall_ : List Ident → Ty → Scheme` to [Type.lean](Ziku/Type.lean), implement `generalize : TyEnv → Ty → Scheme` quantifying free variables not in environment, implement `instantiate : Scheme → InferM Ty` replacing bound variables with fresh ones, change [TyEnv](Ziku/Infer.lean#L14) from `List (Ident × Ty)` to `List (Ident × Scheme)`, update [let\_/letRec](Ziku/Infer.lean#L117-L143) to generalize bindings, add `tests/golden/infer/polymorphism/` with 10 tests

5. **Implement Pattern Matching** - Add `inferPat : TyEnv → Pat → InferM (List (Ident × Ty) × Ty)` with structural recursion (remove `partial`), add `TyEnv.dataCons : List (Ident × Scheme)` for constructor types, implement [match\_](Ziku/Infer.lean#L153) inferring scrutinee type, unifying with each pattern type, checking branches with extended environments, add `tests/golden/infer/patterns/` with 8 tests including nested patterns and type errors

6. **Add Row-Polymorphic Records** - Extend [Ty.record](Ziku/Type.lean#L17) to `List (Ident × Ty) → Option Ty → Ty`, implement `unifyRecords` with 4 cases: both closed (exact match), left open (unify row with right-only fields), right open (symmetric), both open (unify rows with opposite-only fields), update [Ty.toString](Ziku/Type.lean#L80-L87) showing `{ x : Int | _t5 }`, implement [record](Ziku/Infer.lean#L155) and [field](Ziku/Infer.lean#L154) inference, add `tests/golden/infer/records/` with 8 tests

7. **Implement Codata Typing** - Add `hashType : Option Ty` to `InferState` storing type of `#` in current codata block, implement `splitCopatterns : List (List Pat × Copattern × Expr) → InferM Expr` grouping by first accessor and recursively building nested blocks, distinguish `.field` (add to record type) vs `(arg)` (create function type), handle [codata](Ziku/Infer.lean#L153) and [hash](Ziku/Infer.lean#L85) cases, add `tests/golden/infer/codata/` with 12 tests covering streams, callable codata, mixed forms

8. **Add Sequent Calculus Features** - Add `Ty.bottom : Ty` as `con "⊥"`, define `contTy : Ty → Ty := fun t => arrow t bottom`, implement [cut](Ziku/Infer.lean#L156) synthesizing producer to `τ`, checking consumer against `contTy τ`, implement [mu](Ziku/Infer.lean#L157) binding `k : contTy τ` in body and returning `τ`, add `tests/golden/infer/sequent/` with 6 tests for cut/mu interactions

## Further Considerations

1. **AST migration impact** - Adding `pos` to every Expr constructor is ~200 lines of mechanical changes across [Syntax.lean](Ziku/Syntax.lean), [Parser.lean](Ziku/Parser.lean), [Eval.lean](Ziku/Eval.lean). Generate migration script or manual? Manual safer but tedious.

2. **Test count targets** - Plan specifies 20 initial + 10 polymorphism + 8 patterns + 8 records + 12 codata + 6 sequent = 64 tests. Sufficient for coverage? Add more negative tests (type errors) in each category?

3. **Error message verbosity** - Show full type in errors `"Cannot unify (Int -> Int) with Int"` or simplified `"Expected function, got Int"`? Full types better for debugging but verbose in golden files.

4. **Termination proofs** - `inferPat` provably terminates (structural on Pat), `unify` provably terminates (sum of type sizes decreases), but main `infer` may not (cut/mu). Mark these with `termination_by` hints or leave as `partial` for complex cases?
