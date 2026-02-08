# 2026-02-08: Combined stream/zipWith/fib codata example

## Context
A single Ziku code example showcasing:
- Infinite codata streams with copatterns (`#`)
- `zipWith` as a higher-order stream combinator
- Fibonacci stream defined via `zipWith` with three explicit copattern cases (`#.head`, `#.tail.head`, `#.tail.tail`)
- `take` function converting a codata stream to a `Cons`/`Nil` list
- Final result: first 5 Fibonacci elements as a cons list

**Key finding**: `ir-eval` skips type inference (parse → elaborate → translate → eval), so recursive codata types that fail the occurs check during `infer` work fine in `ir-eval`.

## Plan

### 1. Write `tests/golden/ir-eval/success/stream_zipwith_fib.ziku`

```ziku
-- zipWith: combines two codata streams element-wise
let rec zipWith = \f => \s1 => \s2 => {
  #.head => f s1.head s2.head,
  #.tail => zipWith f s1.tail s2.tail
} in

-- take: convert first n elements of a stream to a Cons/Nil list
let rec take = \n => \s =>
  if n == 0 then Nil
  else Cons(s.head, take (n - 1) s.tail)
in

-- fib: Fibonacci stream with three explicit copattern cases
-- fib = [0, 1, 1, 2, 3, 5, 8, 13, ...]
let rec fib = {
  #.head => 0,
  #.tail.head => 1,
  #.tail.tail => zipWith (\x => \y => x + y) fib fib.tail
} in

-- First 5 Fibonacci numbers as a cons list
take 5 fib
```

Expected result: `Cons(0, Cons(1, Cons(1, Cons(2, Cons(3, Nil)))))`

### 2. Clean up the three separate files created earlier
- Remove `stream_example.ziku` (already trashed)
- Remove `stream_fib.ziku` (already trashed)
- Remove `stream_zipwith.ziku` (already trashed)

### 3. Create golden file
- `tests/golden/ir-eval/success/stream_zipwith_fib.golden` with expected output
- Exact format TBD — depends on how `ir-eval` prints `Cons`/`Nil` values (need to check via `mise run docker:run`)

### 4. Test
- `mise run docker:run ir-eval tests/golden/ir-eval/success/stream_zipwith_fib.ziku` — verify output
- `mise run docker:test:category ir-eval` — all ir-eval tests should pass

## Files to modify
- **Overwrite**: `tests/golden/ir-eval/success/stream_zipwith_fib.ziku` (already created, needs update)
- **Overwrite**: `tests/golden/ir-eval/success/stream_zipwith_fib.golden` (update with correct output)
- **Delete**: `stream_example.ziku`, `stream_fib.ziku`, `stream_zipwith.ziku` (already trashed)

## Verification
- `mise run docker:run ir-eval <file>` — should output the cons list of `[0, 1, 1, 2, 3]`
- `mise run docker:test:category ir-eval` — all tests pass
