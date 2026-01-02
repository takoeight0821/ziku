# Ziku Internals

Implementation details for developers and contributors.

## Architecture

```
Ziku/
├── Syntax.lean         # Shared types: SourcePos, Ident, Lit, BinOp, Pat, Ty
├── Surface/
│   └── Syntax.lean     # Surface AST with label/goto
├── IR/
│   ├── Syntax.lean     # Sequent calculus IR (Producer, Consumer, Statement)
│   └── Eval.lean       # IR evaluator with μ/μ̃-reduction
├── Backend/
│   └── Scheme.lean     # Scheme code generator (CPS translation)
├── Translate.lean      # Surface → IR translation
├── Lexer.lean          # UTF-8 hand-written lexer
├── Parser.lean         # Recursive descent parser
├── Type.lean           # Type utilities: Subst, Scheme
├── Infer.lean          # HM type inference
└── Proofs/             # Lean proofs (Arithmetic, Eval, Identities, Soundness)
```

## Pipeline

```
Source → [Parse] → Surface.Expr → [Translate] → IR.Statement → [Eval]
                        ↓                              ↓
                   [Elaborate] → [Infer]          [Scheme Backend]
```

## Sequent Calculus IR

The IR is based on the λμμ̃-calculus with three syntactic categories:

### Producers

Construct/produce elements of a type:

- `var x` - Variable
- `lit n` - Literal
- `μα.s` - Mu abstraction (captures continuation α)
- `cocase {D(x̄; ᾱ) ⇒ s, ...}` - Copattern match
- `{x = p, y = q}` - Record

### Consumers

Consume/destruct elements of a type:

- `covar α` - Covariable
- `μ̃x.s` - Mu-tilde abstraction (binds value x)
- `case {K(x̄; ᾱ) ⇒ s, ...}` - Pattern match
- `D(p̄; c)` - Destructor application

### Statements

Drive computation (no return type):

- `⟨p | c⟩` - Cut (connects producer with consumer)
- `⊙(p₁, p₂; c)` - Binary operation
- `ifz(p, s₁, s₂)` - Conditional
- `f(p̄; c̄)` - Function call

## Reduction Rules

```
⟨μα.s | c̄⟩    ⊲  s[c̄/α]     (μ-reduction)
⟨v̄ | μ̃x.s⟩    ⊲  s[v̄/x]     (μ̃-reduction, v is value)
```

## Translation Rules

From the surface language to IR (from "Grokking the Sequent Calculus"):

```
⟦x⟧                     =  x
⟦⌜n⌝⟧                   =  ⌜n⌝
⟦t₁ ⊙ t₂⟧               =  μα. ⊙(⟦t₁⟧, ⟦t₂⟧; α)
⟦if t₁ then t₂ else t₃⟧ =  μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ | α⟩, ⟨⟦t₃⟧ | α⟩)
⟦let x = t₁ in t₂⟧      =  μα.⟨⟦t₁⟧ | μ̃x.⟨⟦t₂⟧ | α⟩⟩
⟦λx.t⟧                  =  cocase {ap(x; α) ⇒ ⟨⟦t⟧ | α⟩}
⟦t₁ t₂⟧                 =  μα.⟨⟦t₁⟧ | ap(⟦t₂⟧; α)⟩
⟦label α {t}⟧           =  μα.⟨⟦t⟧ | α⟩
⟦goto(t; α)⟧            =  μβ.⟨⟦t⟧ | α⟩  (β fresh)
```

## Design Insights

### Duality in the Sequent Calculus

| Concept | Data | Codata |
|---------|------|--------|
| Definition | Constructors | Destructors |
| Usage | Pattern matching (case) | Copattern matching (cocase) |
| IR Category | case is Consumer | cocase is Producer |
| Evaluation | Eager | Lazy |

### Let-Bindings are Dual to Control Operators

- `let x = t₁ in t₂` binds a value (μ̃)
- `label α {t}` binds a continuation (μ)
- These are precise duals in the λμμ̃-calculus

### Evaluation Contexts are First-Class

Unlike CPS where evaluation contexts are functions, in the λμμ̃-calculus they are first-class citizens bound to covariables. This provides:

- Cleaner types than CPS
- Flexible evaluation order (not fixed by translation)
- Natural compiler optimizations (case-of-case emerges from μ-reduction)

## Scheme Backend

The Scheme backend (`Ziku/Backend/Scheme.lean`) compiles IR to Chez Scheme code using continuation-passing style.

### Translation Strategy

The λμμ̃-calculus maps naturally to CPS:

| IR Construct | Scheme Translation |
|--------------|-------------------|
| `var x` | `x` |
| `lit n` | `n` / `#t` / `#f` / `"str"` |
| `μα.s` | `(vector 'ziku-thunk (lambda (α) <s>))` |
| `μ̃x.s` | `(lambda (x) <s>)` |
| `covar α` | `α` |
| `⟨p \| c⟩` | `(<c> <p>)` or compile-time reduction |
| `cocase {ap(x;α)=>s}` | `(lambda (x) (lambda (α) <s>))` |
| `record {f=v,...}` | `(list (cons 'f <v>) ...)` |
| `fix x.p` | `(letrec ((x <p>)) x)` |
| `binOp op p1 p2 c` | `(<c> (<op> <p1> <p2>))` |
| `ifz p s1 s2` | `(if <p> <s1> <s2>)` |

### Runtime Tagging

The backend uses vector tagging to distinguish special values:
- `#(ziku-thunk <func>)` - Lazy computation (μ-abstraction)
- `#(ziku-dispatch <func>)` - Record with recursive fields (from `fix`)

This allows runtime checks to properly evaluate thunks when needed.

## Testing

Golden tests are in `tests/golden/`:

- `parser/`: Parser output tests (.ziku → .golden)
- `eval/`: Surface language evaluation tests
- `infer/`: Type inference tests
- `ir-eval/`: IR evaluation tests (via translation)

### Adding Tests

1. Create `tests/golden/{category}/{name}.ziku`
2. Add test name to `tests/GoldenTest.lean`
3. Run `lake test` to auto-generate `.golden` file

## References

- "Grokking the Sequent Calculus" (ICFP 2024) - [Paper](https://dl.acm.org/doi/10.1145/3674639) | [arXiv](https://arxiv.org/abs/2406.14719)
- Curien & Herbelin (2000) - "The Duality of Computation"
- Downen et al. (2016) - "Sequent calculus as a compiler intermediate language"
- Abel et al. (2013) - "Copatterns: Programming Infinite Structures by Observations"
