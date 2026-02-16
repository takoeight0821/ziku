# Small-Step vs Big-Step Interpreters: A Comprehensive Comparison

## Overview

Small-step and big-step semantics are two fundamental styles for operationally defining the meaning of programming languages. This document examines their differences, trade-offs, and practical considerations for interpreter implementation.

**Key Distinction:**
- **Small-step semantics**: Define a relation between program configurations that denotes *one computational step*
- **Big-step semantics**: Define a relation directly associating each program configuration to its *final result*

## Big-Step Semantics (Natural Semantics)

Also known as: *natural semantics*, *relational semantics*, *evaluation semantics*

Introduced by Gilles Kahn when presenting Mini-ML, big-step semantics relate initial program configurations directly to final results in one "big" evaluation step.

### Characteristics

```
⟨e, σ⟩ ⇓ v    (expression e in state σ evaluates to value v)
```

The key insight: "think about how a recursive interpreter would evaluate the expression in question."

### Advantages

1. **Simpler definitions**: Often need fewer inference rules
2. **Direct correspondence to interpreters**: Maps naturally to recursive evaluation functions
3. **Natural transcription**: Closely matches informal language descriptions
4. **Easier proofs**: Big steps in reasoning make it quicker to prove some properties
5. **Compiler verification**: Well-suited for verifying program optimizations and semantic preservation for terminating programs

### Disadvantages

1. **Cannot model divergence**: Non-terminating computations have no inference tree
2. **Conflates stuck and divergent**: All programs without final configurations look the same
3. **Cannot model concurrency**: No way to talk about intermediate states for interleaving
4. **Weaker type soundness**: Can only prove preservation, not progress

### Example Rule (Function Application)

```
   ⟨e₁, σ⟩ ⇓ λx.e    ⟨e₂, σ⟩ ⇓ v₂    ⟨e[v₂/x], σ⟩ ⇓ v
  ─────────────────────────────────────────────────────
                    ⟨e₁ e₂, σ⟩ ⇓ v
```

## Small-Step Semantics (Structural Operational Semantics)

Introduced by Gordon Plotkin in 1981, small-step semantics (SOS) define behavior in terms of individual computational steps.

### Characteristics

```
⟨e, σ⟩ → ⟨e', σ'⟩    (one step of computation)
⟨e, σ⟩ →* ⟨v, σ'⟩    (reflexive-transitive closure)
```

### Advantages

1. **Models divergence**: Can reason about non-terminating computations
2. **Models concurrency**: Intermediate states allow interleaving semantics
3. **Distinguishes errors from divergence**: "Stuck" states vs infinite reduction
4. **Stronger type soundness**: Enables progress + preservation proofs
5. **Step-indexed logical relations**: Enables powerful proof techniques
6. **Debugging and tracing**: Can observe intermediate program states

### Disadvantages

1. **Higher implementation complexity**: Requires explicit continuation/stack management
2. **More verbose rules**: Tedious "congruence rules" for evaluation contexts
3. **Proof complexity**: Step-star proofs can be mechanical and tedious

### Example Rule (Function Application)

```
        ⟨e₁, σ⟩ → ⟨e₁', σ'⟩
  ─────────────────────────────────
  ⟨e₁ e₂, σ⟩ → ⟨e₁' e₂, σ'⟩

        ⟨e₂, σ⟩ → ⟨e₂', σ'⟩
  ─────────────────────────────────
    ⟨v e₂, σ⟩ → ⟨v e₂', σ'⟩

  ⟨(λx.e) v, σ⟩ → ⟨e[v/x], σ⟩
```

## Hybrid and Extended Approaches

### 1. Coinductive Big-Step Semantics (Leroy & Grall)

**Problem**: Standard big-step cannot distinguish divergence from stuck states.

**Solution**: Use coinductive definitions to model infinite derivation trees for diverging programs.

**Key insight**: The coinductive interpretation allows infinite proof trees, capturing divergent behavior while maintaining the big-step style.

**Reference**: [Coinductive Big-Step Operational Semantics](https://xavierleroy.org/publi/coindsem.pdf) (Information and Computation, 2009)

### 2. Functional Big-Step Semantics (Owens et al., CakeML)

**Problem**: Big-step semantics cannot model divergence; small-step is tedious.

**Solution**: Write the semantics as a total recursive function with a "clock" (fuel) parameter.

```lean
def eval (fuel : Nat) (e : Expr) (env : Env) : Result :=
  if fuel = 0 then Timeout
  else match e with
    | Lit n => Value n
    | App f x =>
        match eval (fuel - 1) f env with
        | Value (Closure body env') => eval (fuel - 1) body (extend env' x v)
        | r => r
    ...
```

**Advantages**:
- Better induction theorem than relational big-step
- Less duplication than small-step
- Accessible to functional programmers
- Easy symbolic simulation via rewriting
- Natural divergence preservation proofs

**Used extensively in**: CakeML verified compiler (12 intermediate languages, ~40,000 lines of proof)

**Reference**: [Functional Big-Step Semantics](https://cakeml.org/esop16.pdf) (ESOP 2016)

### 3. Pretty-Big-Step Semantics (Charguéraud)

**Problem**: Big-step semantics suffer from rule duplication when handling exceptions and divergence.

**Solution**: Use intermediate "result" forms and outcome propagation to eliminate duplication.

```
    ⟨e, σ⟩ ⇓ r
  ───────────────────
  ⟨abort e, σ⟩ ⇓ r       (outcome propagation)
```

**Key insight**: Represent divergence and abrupt termination using status flags, eliminating copy-pasted premises.

**Reference**: [Pretty-Big-Step Semantics](https://www.chargueraud.org/research/2012/pretty/pretty.pdf) (ESOP 2013)

## Abstract Machines

Abstract machines provide an operational perspective that bridges interpreters and hardware. Two prominent examples:

### CEK Machine

A state consists of three components:
- **C**ontrol: The expression being evaluated
- **E**nvironment: Variable bindings
- **K**ontinuation: What to do next

```
⟨(λx.e), ρ, κ⟩ → ⟨e, ρ[x↦v], κ'⟩
```

**Classification**: Small-step, explicit continuations

### CESK Machine

Extends CEK with:
- **S**tore: Heap for mutable state

**Use case**: Imperative languages with mutation

### Relationship to Semantics Styles

| Style | Machine |
|-------|---------|
| Big-step | Direct recursive interpreter |
| Small-step | Abstract machine with explicit state |

**Key insight** (Danvy): Defunctionalization transforms a big-step interpreter in CPS into an abstract machine. Refunctionalization does the inverse.

**Reference**: [A Functional Correspondence Between Evaluators and Abstract Machines](https://www.brics.dk/RS/03/13/BRICS-RS-03-13.pdf)

## Type Soundness Proofs

### Progress and Preservation (Wright-Felleisen)

**Progress**: Well-typed expressions are either values or can step.
**Preservation**: Typing is preserved across steps.

Together they prove: well-typed programs don't get stuck.

### Style Comparison

| Approach | Progress | Preservation | Divergence |
|----------|----------|--------------|------------|
| Small-step | Yes | Yes | Distinguished from stuck |
| Big-step | No | Yes | Conflated with stuck |
| Functional big-step | Yes | Yes | Timeout vs error |
| Coinductive big-step | Yes | Yes | Infinite derivation |

**Key insight**: Small-step is traditionally preferred for type soundness because it naturally distinguishes stuck states from divergence, enabling the progress theorem.

**Reference**: [What Type Soundness Theorem Do You Really Want to Prove?](https://blog.sigplan.org/2019/10/17/what-type-soundness-theorem-do-you-really-want-to-prove/)

## Implementation Considerations

### Lean 4 Specific

For implementing interpreters in Lean 4:

1. **`partial def`**: Allows recursive functions without termination proof
   - Enables practical implementation
   - Cannot be used in proofs

2. **Fuel parameter**: Structural recursion with explicit bound
   ```lean
   def eval (fuel : Nat) : Expr → Env → Option Value
   ```
   - Provably total
   - Can be used in proofs
   - Natural model of "functional big-step"

3. **`termination_by`**: Provide explicit termination measure
   ```lean
   def eval (e : Expr) : Value :=
     match e with ...
   termination_by sizeOf e
   ```

### When to Use Each Style

| Use Case | Recommended Style |
|----------|-------------------|
| Simple evaluator | Big-step (direct recursion) |
| Type soundness proof | Small-step or functional big-step |
| Compiler verification | Functional big-step |
| Concurrency | Small-step |
| Debugging/tracing | Small-step |
| Quick prototyping | Big-step |

## Application to Ziku (λμμ̃-calculus)

The current Ziku evaluator (`Ziku/IR/Eval.lean`) uses a **functional big-step style** with fuel:

```lean
partial def evalWithFuel (fuel : Nat) (state : State) : IO EvalResult :=
  if fuel == 0 then
    match state with
    | .stmt s env => return .stuck s env
    | ...
  else do
    match ← stateStep state with
    | .ok (some state') => evalWithFuel (fuel - 1) state'
    | .ok none => -- halt
    | .error e => return .error e
```

### Current Design Analysis

**Strengths**:
1. Fuel-based termination guarantee
2. Explicit state representation (`State` with `cut` and `stmt`)
3. Clear error handling with `EvalError` type
4. Environment-based evaluation (efficient for closures)

**Characteristics**:
- The `stateStep` function is essentially a small-step transition
- `evalWithFuel` iterates small steps, making it a "functional small-step" style
- The `State` type explicitly represents evaluation contexts

### Potential Improvements

1. **True big-step for proofs**: For formal verification, consider a relational big-step definition alongside the functional one

2. **Coinductive divergence**: For proving properties about divergent programs, consider coinductive semantics

3. **Step counting**: For debugging, the fuel parameter naturally provides step counting

4. **Trace generation**: Small-step structure allows easy addition of execution tracing

## Summary Table

| Property | Big-Step | Small-Step | Functional Big-Step |
|----------|----------|------------|---------------------|
| Simplicity | High | Medium | Medium |
| Divergence handling | Poor | Good | Good |
| Concurrency | Poor | Good | Poor |
| Type soundness proofs | Weak | Strong | Strong |
| Compiler verification | Good | Medium | Excellent |
| Implementation effort | Low | High | Medium |
| Proof effort | Low | High | Medium |
| Debugging support | Poor | Excellent | Good |

## Sources

### Primary References
- [Architectures for interpreters](https://matt.might.net/articles/writing-an-interpreter-substitution-denotational-big-step-small-step/) - Matt Might
- [Software Foundations - Small-step Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)
- [Operational Semantics - Wikipedia](https://en.wikipedia.org/wiki/Operational_semantics)

### Academic Papers
- [Coinductive Big-Step Operational Semantics](https://arxiv.org/abs/0808.0586) - Leroy & Grall
- [Functional Big-Step Semantics](https://link.springer.com/chapter/10.1007/978-3-662-49498-1_23) - Owens et al.
- [Pretty-Big-Step Semantics](https://link.springer.com/chapter/10.1007/978-3-642-37036-6_3) - Charguéraud
- [From Big-Step to Small-Step Semantics and Back](https://arxiv.org/abs/2008.02931)
- [Grokking the Sequent Calculus](https://arxiv.org/abs/2406.14719) - Binder et al.

### Course Materials
- [Cornell CS 6110 - Big-Step and Small-Step Semantics](https://www.cs.cornell.edu/courses/cs6110/2009sp/lectures/lec05-fa07.pdf)
- [CMU - Small-Step Operational Semantics](https://www.cs.cmu.edu/~aldrich/courses/17-363-fa22/notes/lecture06-small-step.pdf)

### Tools and Implementations
- [CakeML Verified Compiler](https://cakeml.org/)
- [Lean 4 Well-Typed Interpreter](https://lean-lang.org/lean4/doc/examples/interp.lean.html)
