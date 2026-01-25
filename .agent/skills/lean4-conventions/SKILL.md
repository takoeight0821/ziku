---
description: Lean 4 coding conventions for Ziku. Use when writing new Lean code, reviewing implementations, or deciding between `partial` functions vs termination proofs.
---

# Lean 4 Conventions for Ziku

This skill covers Lean 4 coding patterns and conventions specific to the Ziku project.

## `partial` vs Termination Proofs

### When to Use `partial`

Use `partial def` when:
- Termination depends on runtime values that are hard to prove decreasing
- The function is used only for computation, not in proofs
- Implementing interpreters, evaluators, or parsers

```lean
-- OK: Interpreter where termination depends on program behavior
partial def eval (stmt : Statement) : IO Value := ...

-- OK: Parser with complex backtracking
partial def parseExpr : Parser Expr := ...
```

### Alternatives to `partial`

Consider these before using `partial`:

1. **`termination_by` clause**: When a decreasing measure exists
   ```lean
   def factorial (n : Nat) : Nat :=
     if n = 0 then 1 else n * factorial (n - 1)
   termination_by n
   ```

2. **Fuel parameter**: Bounded execution with explicit limit
   ```lean
   def evalWithFuel (fuel : Nat) (stmt : Statement) : Option Value :=
     match fuel with
     | 0 => none
     | n + 1 => ... evalWithFuel n ...
   ```

3. **Step-based execution**: Return intermediate state
   ```lean
   def step (state : State) : State ⊕ Value := ...
   ```

### Trade-offs

| Approach | Proofs | Performance | Complexity |
|----------|--------|-------------|------------|
| `partial` | ❌ Cannot prove properties | ✅ Best | ✅ Simple |
| `termination_by` | ✅ Full proofs | ✅ Best | ⚠️ Need measure |
| Fuel | ⚠️ Limited (bounded) | ⚠️ May timeout | ⚠️ Extra parameter |
| Step-based | ✅ Per-step proofs | ⚠️ Overhead | ⚠️ State management |

## Mutual Recursion

### Use Explicit Function Calls

In mutual recursive functions, use explicit function calls instead of dot notation:

```lean
-- ❌ WRONG: Dot notation in mutual recursion can cause issues
mutual
  def Producer.eval (prod : Producer) : ... :=
    match prod with
    | .cut p c => c.eval p  -- DON'T do this

  def Consumer.eval (cons : Consumer) (prod : Producer) : ... := ...
end

-- ✅ CORRECT: Explicit function calls
mutual
  def Producer.eval (prod : Producer) : ... :=
    match prod with
    | .cut p c => Consumer.eval c p  -- DO this

  def Consumer.eval (cons : Consumer) (prod : Producer) : ... := ...
end
```

### Substitution Pattern

For substitution in IR, use explicit calls consistently:

```lean
def Producer.substVar (x : String) (p : Producer) (prod : Producer) : Producer :=
  match prod with
  | .cut prod cons =>
    .cut (Producer.substVar x p prod) (Consumer.substVar x p cons)
  | ...

def Consumer.substVar (x : String) (p : Producer) (cons : Consumer) : Consumer :=
  match cons with
  | .mu x' stmt =>
    if x == x' then cons
    else .mu x' (Statement.substVar x p stmt)
  | ...
```

## Source Position Tracking

Track source positions throughout the AST for error reporting:

```lean
structure Pos where
  line : Nat
  column : Nat

structure Located (α : Type) where
  pos : Pos
  val : α

-- Use Located for AST nodes
inductive Expr where
  | var (name : Located String)
  | app (fn : Located Expr) (arg : Located Expr)
  | ...
```

Error messages should include position information:

```lean
def formatError (pos : Pos) (msg : String) : String :=
  s!"{pos.line}:{pos.column}: {msg}"
```

## Naming Conventions

| Item | Convention | Example |
|------|------------|---------|
| Types | PascalCase | `Producer`, `Consumer`, `Statement` |
| Functions | camelCase | `evalStmt`, `substVar`, `translateExpr` |
| Theorems | snake_case | `eval_deterministic`, `subst_preserves_type` |
| Namespaces | PascalCase | `Ziku.IR.Eval` |
| Local variables | camelCase | `stmt`, `prodVal`, `consEnv` |

## Module Organization

```
Ziku/
├── Syntax.lean       -- Surface language AST
├── Parser.lean       -- Hand-written parser
├── Infer.lean        -- Type inference
├── Translate.lean    -- Surface → IR translation
├── IR/
│   ├── Syntax.lean   -- IR AST (Producer, Consumer, Statement)
│   ├── Eval.lean     -- IR interpreter
│   └── Emit.lean     -- Scheme code generation
└── Proofs/
    └── IR/           -- IR-related proofs
```

## Checklist

When writing new Lean code:

- [ ] Consider termination: Can you prove it? Is `partial` acceptable?
- [ ] Use explicit function calls in mutual recursion
- [ ] Track source positions for user-facing errors
- [ ] Follow naming conventions
- [ ] Place code in appropriate module

## References

- [CLAUDE.md](../../CLAUDE.md) - Project conventions
- [Ziku/IR/](../../Ziku/IR/) - IR implementation examples
- [Ziku/Proofs/](../../Ziku/Proofs/) - Proof examples
