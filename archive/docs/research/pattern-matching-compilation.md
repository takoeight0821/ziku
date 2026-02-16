# Research: Compiling Pattern Matching

## Overview

Pattern matching compilation transforms high-level pattern match expressions into efficient low-level code (typically nested case/switch statements or decision trees). This research covers the key algorithms, tradeoffs, and connections to sequent calculus-based languages like Ziku.

## Key Papers

| Paper                                             | Author(s)             | Year | Key Contribution                                  |
| ------------------------------------------------- | --------------------- | ---- | ------------------------------------------------- |
| Compiling Pattern Matching                        | Augustsson            | 1985 | Foundational backtracking automata algorithm      |
| Optimizing Pattern Matching                       | Le Fessant & Maranget | 2001 | OCaml's backtracking optimizations                |
| Compiling Pattern Matching to Good Decision Trees | Maranget              | 2008 | Decision tree algorithm with necessity heuristics |
| Focusing on Pattern Matching                      | Krishnaswami          | 2009 | Logical foundations via focusing                  |
| Unnesting of Copatterns                           | Setzer et al.         | 2014 | Copattern compilation                             |
| GADTs Meet Their Match                            | Karachalias et al.    | 2015 | Exhaustiveness with GADTs                         |
| Grokking the Sequent Calculus                     | Binder et al.         | 2024 | Compiler-oriented intro to λμμ̃                    |

## Two Main Approaches

### 1. Decision Trees

**Advantages:**

- Never re-tests a subterm (optimal runtime)
- Easy to analyze for warnings
- No dead code in output

**Disadvantages:**

- Potential exponential code size
- More complex to implement

**Key idea:** Build a tree where each internal node tests a constructor, branches lead to specialized subtrees.

### 2. Backtracking Automata

**Advantages:**

- Linear code size guarantee
- Simpler implementation

**Disadvantages:**

- May re-test subterms (runtime overhead)
- Harder to analyze for diagnostics

**Key idea:** Generate code that tries patterns top-to-bottom, backtracking on failure.

## The Pattern Matrix Algorithm (Maranget 2008)

### Core Data Structures

1. **Pattern Matrix**: Rows = clauses, Columns = scrutinees (occurrences)
2. **Occurrence Vector**: Access paths to subvalues (e.g., `x.0.1`)
3. **Action Vector**: Right-hand side expressions for each row

### The Algorithm

```
compile(matrix, occurrences, actions):
  if matrix is empty:
    return FAIL
  if first row is all wildcards:
    return actions[0]

  col = select_column(matrix)  # using heuristics
  swap column `col` to position 0

  signatures = collect_constructors(matrix, col=0)

  for each constructor C in signatures:
    specialized = specialize(matrix, C)
    default = default_matrix(matrix, C)
    emit: case occurrences[0] of
            C(args) -> compile(specialized, ...)
            _       -> compile(default, ...)
```

### Column Selection Heuristics

**Necessity-based scoring:**

- Wildcards score 0 (no test needed)
- Patterns below wildcards score 0 (already satisfied)
- Actual patterns score 1

Select the column with highest score.

**The "fnr" heuristic (first-needed-row):**

1. Specializer must be in first row
2. Pick pattern that specializes most rows
3. Tie-break by smallest pattern size

### Specialization

For constructor `C(p1, ..., pn)`:

- Keep only rows where column 0 matches C (or is wildcard)
- Replace column 0 with n columns for C's arguments
- Expand nested patterns into new columns

### Defaulting

- Keep rows where column 0 is wildcard
- Remove column 0

## Handling Different Pattern Types

| Pattern Type            | Handling                     |
| ----------------------- | ---------------------------- |
| Wildcard `_`            | Irrefutable, always succeeds |
| Variable `x`            | Like wildcard + binding      |
| Literal `42`            | Test equality                |
| Constructor `C(p1, p2)` | Test tag, then recurse       |
| Tuple `(p1, p2)`        | Decompose into columns       |
| Or-pattern `p1 \| p2`   | Expand to multiple rows      |
| As-pattern `p as x`     | Bind + continue matching     |

## Code Size Optimization

### Hash Consing / DAG Sharing

Identical subtrees share nodes:

```
        switch x
       /        \
    A(y)        B
     |           |
   switch y   switch y   <- can share if identical
```

### Join Points

Instead of duplicating continuations, use labeled jumps:

```
match x with
| A -> e
| B -> e     -- duplicate e

becomes:

let join k = e in
match x with
| A -> jump k
| B -> jump k
```

## Exhaustiveness and Redundancy Checking

The decision tree algorithm naturally supports:

1. **Exhaustiveness**: If compilation produces a FAIL node reachable from root, pattern match is non-exhaustive.

2. **Redundancy**: If a row's action is never reached (dead code), that clause is redundant.

### With GADTs

GADTs complicate exhaustiveness because type refinement makes some cases impossible. Solutions:

- Use type constraints during compilation
- Integrate with type inference (OutsideIn(X))
- Accept some false positives

## Connection to Sequent Calculus

### Pattern/Copattern Duality

In λμμ̃-calculus (Ziku's IR):

| Data (patterns)      | Codata (copatterns)     |
| -------------------- | ----------------------- |
| `case { C(x) -> e }` | `cocase { .m(x) -> e }` |
| Destructs producers  | Constructs consumers    |
| Consumer (context)   | Producer (term)         |

The sequent calculus makes pattern matching **symmetric**:

- Pattern match = consumer (μ̃-abstraction)
- Copattern match = producer (cocase)

### Translation Rules

```
Surface: match e with | C(x) -> body

IR: ⟨⟦e⟧ | case { C(x) ⇒ ⟨⟦body⟧ | α⟩ }⟩
```

Where `α` is the continuation.

### Benefits for Compilation

1. First-class continuations: evaluation contexts are explicit
2. Uniform treatment: patterns and copatterns share infrastructure
3. Natural CPS: μ/μ̃ reductions = continuation passing

## Copattern Compilation

From "Unnesting of Copatterns" (Setzer et al. 2014):

Nested copatterns are flattened to simple ones:

```
f .head       = 1
f .tail .head = 2
f .tail .tail = f

becomes:

f .head = 1
f .tail = g where
  g .head = 2
  g .tail = f
```

The algorithm mirrors pattern compilation but for observations instead of constructions.

## Implementation Recommendations for Ziku

### Phase 1: Simple Patterns Only

1. Flatten nested patterns during surface-to-IR translation
2. Generate `case` expressions with simple patterns
3. Each arm tests one constructor at the top level

### Phase 2: Decision Tree Generation

1. Implement pattern matrix representation
2. Use necessity-based column selection
3. Generate optimized IR with sharing

### Phase 3: Exhaustiveness Checking

1. Track constructor coverage during compilation
2. Warn on non-exhaustive patterns
3. Warn on redundant clauses

### Relevant Ziku Files

- `Ziku/Surface/Syntax.lean` - Surface patterns
- `Ziku/IR/Syntax.lean` - IR case/cocase
- `Ziku/Translate.lean` - Surface → IR
- `Ziku/Syntax.lean` - Shared Pat type

## Sources

### Primary References

- [Compiling Pattern Matching to Good Decision Trees (Maranget 2008)](https://www.cs.tufts.edu/~nr/cs257/archive/luc-maranget/jun08.pdf)
- [Colin James - Compiling Pattern Matching](https://compiler.club/compiling-pattern-matching/)
- [Clojure core.match Wiki](https://github.com/clojure/core.match/wiki/Understanding-the-algorithm)
- [Grokking the Sequent Calculus (ICFP 2024)](https://dl.acm.org/doi/10.1145/3674639)

### Foundational Papers

- [Compiling Pattern Matching (Augustsson 1985)](https://dl.acm.org/doi/10.5555/5280.5303)
- [Optimizing Pattern Matching (Le Fessant & Maranget 2001)](https://dl.acm.org/doi/10.1145/507635.507641)
- [Focusing on Pattern Matching (Krishnaswami 2009)](https://www.cl.cam.ac.uk/~nk480/pattern-popl09.pdf)

### Exhaustiveness and GADTs

- [GADTs and Exhaustiveness (arXiv 2017)](http://arxiv.org/abs/1702.02281)
- [GADTs Meet Their Match (ICFP 2015)](https://www.researchgate.net/publication/281777268)
- [A Generic Algorithm for Exhaustivity Checking (Scala 2016)](https://infoscience.epfl.ch/record/225497)

### Codata and Copatterns

- [Unnesting of Copatterns (RTA-TLCA 2014)](https://link.springer.com/chapter/10.1007/978-3-319-08918-8_3)
- [Copatterns (POPL 2013)](https://www.cs.mcgill.ca/~dthibo1/papers/popl170-abel.pdf)
- [Codata in Action](https://www.researchgate.net/publication/332248372_Codata_in_Action)

### Sequent Calculus for Compilers

- [Sequent Calculus as a Compiler IL (ICFP 2016)](https://dl.acm.org/doi/10.1145/2951913.2951931)
- [What Functional Programmers Can Learn from Sequent Calculus](https://hackernoon.com/what-functional-programmers-can-learn-from-sequent-calculus)
- [Tour of a Pattern Matcher: Decision Trees](https://crumbles.blog/posts/2025-11-28-extensible-match-decision-tree.html)
