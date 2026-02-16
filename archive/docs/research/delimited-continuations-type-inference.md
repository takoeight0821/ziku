# Delimited Continuations Type Inference for Label/Goto

## Problem Statement

Zikuの`label`/`goto`構文において、デッドコード（`goto`の後に続くコード）を正しく型付けするための型推論手法を調査する。

### 具体的な問題

```ziku
label result { if true then goto(true, result) + 1 else false }
```

この式は`Bool`型を持つべきだが、現在の単純な型推論では：
- `goto(true, result) + 1` は `goto`が`Int`を返す必要がある（`+`演算子のため）
- `else false` は `Bool`
- 両分岐の型が一致しないためエラー

しかし、`goto(true, result)`は戻らない（labelにジャンプする）ため、`+ 1`は実行されない「デッドコード」である。

## Key Concepts

### 1. Bottom Type (⊥)

[Bottom type](https://en.wikipedia.org/wiki/Bottom_type)は、値を持たない型であり、全ての型のサブタイプである。

> "When the bottom type is uninhabited, a function whose return type is bottom cannot return any value. In such a language, the bottom type may be known as the zero, never or empty type."

制御フローの文脈では：
- `throw`、`abort`、`return`などの「戻らない」操作の型
- Rust: `!` (never type)
- TypeScript: `never`
- Kotlin: `Nothing`

### 2. Sequent Calculus Translation

[Grokking the Sequent Calculus](https://arxiv.org/abs/2406.14719) (Binder et al., 2024) より：

```
⟦goto(t; α)⟧ = μβ.⟨⟦t⟧ | α⟩  (β fresh)
```

重要な点：**β（戻り値の継続変数）は本体で使用されない**。
したがって、`goto`式は任意の型を持つことができる。

### 3. Answer Type Polymorphism

[Polymorphic Delimited Continuations](https://www.cs.tsukuba.ac.jp/~kam/paper/aplas07.pdf) (Asai & Kameyama, 2007) より：

> "If an expression does not contain shift, it can be placed in a context of any answer type... This property is called answer type polymorphism."

純粋な式（制御効果を持たない式）は、任意のanswer typeを持つコンテキストに配置できる。
同様に、**絶対に戻らない式**は、任意の型を持つことができる。

## Typing Rules Analysis

### Grokking the Sequent Calculusにおける型付け規則

**Label規則**:
```
Γ, α:cns τ ⊢ t₁ : τ
─────────────────────
Γ ⊢ label α {t₁} : τ
```

- `α`は継続変数（consumer type `cns τ`）
- `label`の本体`t₁`は`τ`型を持つ
- `label`式全体も`τ`型を持つ

**Goto規則**:
```
Γ ⊢ t₁ : τ    α:cns τ ∈ Γ
──────────────────────────
Γ ⊢ goto(t₁; α) : σ
```

- `t₁`は`τ`型を持つ（labelが期待する型）
- **`goto`式自体は任意の型`σ`を持てる**（戻らないため）

### Danvy & Filinski Type System

[A type-theoretic foundation of delimited continuations](https://link.springer.com/article/10.1007/s10990-007-9006-0) (Ariola, Herbelin, Sabry) より：

shift/resetの型システムでは、`shift`が継続をキャプチャして別の値を返す際に**answer type modification**が発生する。これにより、delimited contextの型が変わる可能性がある。

## Implementation Strategies

### Strategy 1: Fresh Type Variable with Universal Unification

現在のZikuの実装（`Infer.lean:332-337`）：
```lean
| .goto _pos _value _name => do
    let ty ← freshTyVar
    return (ty, [])
```

**問題**: フレッシュな型変数を返すだけでは不十分。`goto(...) + 1`において：
1. `goto`は`_t0`を返す
2. `+`は両オペランドが`Int`を要求
3. `_t0`を`Int`に単一化
4. しかしlabelは`Bool`を期待

**解決策**: `goto`の型変数が**どの型にも単一化可能**であることを保証しつつ、**label環境を追跡**してvalueの型を検証する必要がある。

### Strategy 2: Bottom Type Implementation

新しい型コンストラクタ `⊥` (Bottom/Never) を導入：

```lean
inductive Ty where
  | con : SourcePos → Ident → Ty
  | var : SourcePos → Ident → Ty
  | bottom : SourcePos → Ty  -- 新規追加
  | ...
```

単一化規則を拡張：
```lean
partial def unifyAt (pos : SourcePos) (t1 t2 : Ty) : InferM Subst :=
  match t1, t2 with
  | .bottom _, _ => return []  -- ⊥ は任意の型に単一化可能
  | _, .bottom _ => return []
  | ...
```

**利点**: 明示的でわかりやすい
**欠点**: サブタイピングの概念が必要になる可能性

### Strategy 3: Label Environment Tracking

label環境を明示的に追跡し、`goto`の型付けを改善：

```lean
-- 型環境を拡張
structure TyEnv where
  vars : List (Ident × Scheme)
  labels : List (Ident × Ty)  -- label名 → 期待される値の型

-- goto の型推論
| .goto pos value labelName => do
    -- valueの型を推論
    let (valueTy, subst1) ← infer env value
    -- labelの期待する型を取得
    match env.labels.lookup labelName with
    | some expectedTy =>
        let subst2 ← unifyAt pos valueTy expectedTy
        -- gotoは戻らないので任意の型を返せる
        let resultTy ← freshTyVar
        return (resultTy, subst1 ++ subst2)
    | none => throw $ .unboundVariable pos labelName
```

### Strategy 4: CPS-Based Answer Type Tracking

Asai & Kameyama (2007) のアプローチに基づき、answer typeを明示的に追跡：

型判定を拡張：
```
Γ ⊢ e : τ / α → β
```
- `τ`: 式の直接型
- `α`: 現在のanswer type
- `β`: 式評価後のanswer type

`goto`の場合、answer typeを変更する効果を持つ。

## Recommended Approach for Ziku

Zikuの現在の設計（λμμ̃-calculusベースのIR）を考慮すると、**Strategy 3: Label Environment Tracking** が最も適切：

1. **既存のHM型推論と互換性がある**
2. **λμμ̃-calculusの意味論と一致する**
3. **実装が比較的シンプル**

### 具体的な変更点

1. **型環境の拡張**: label情報を追跡
2. **label式の型推論**: 環境にlabel情報を追加して本体を推論
3. **goto式の型推論**:
   - valueの型がlabelの期待する型と一致することを確認
   - gotoの結果型はフレッシュ変数（任意の型に単一化可能）

### 擬似コード

```lean
| .label pos name body => do
    -- labelの結果型のためのフレッシュ変数
    let resultTy ← freshTyVar
    -- label環境を更新してbodyを推論
    let env' := { env with labels := (name, resultTy) :: env.labels }
    let (bodyTy, subst) ← infer env' body
    -- bodyの型とresultTyを単一化
    let subst' ← unifyAt pos bodyTy resultTy
    return (resultTy.applySubst (subst ++ subst'), subst ++ subst')

| .goto pos value labelName => do
    let (valueTy, subst1) ← infer env value
    match env.labels.lookup labelName with
    | some labelTy =>
        -- valueの型がlabelの期待する型と一致
        let subst2 ← unifyAt pos valueTy labelTy
        -- gotoは戻らないので任意の型
        let resultTy ← freshTyVar
        return (resultTy, subst1 ++ subst2)
    | none => throw $ .unboundVariable pos labelName
```

## References

1. **Grokking the Sequent Calculus (Functional Pearl)**
   - Authors: David Binder, Marco Tzschentke, Marius Müller, Klaus Ostermann
   - Year: 2024
   - Links: [arXiv](https://arxiv.org/abs/2406.14719) | [PDF](https://ps.informatik.uni-tuebingen.de/publications/binder24grokking.pdf) | [GitHub](https://github.com/grokking-sc/grokking-sc)

2. **Polymorphic Delimited Continuations**
   - Authors: Kenichi Asai, Yukiyoshi Kameyama
   - Year: 2007 (APLAS)
   - Links: [PDF](https://www.cs.tsukuba.ac.jp/~kam/paper/aplas07.pdf) | [Springer](https://link.springer.com/chapter/10.1007/978-3-540-76637-7_16)

3. **A type-theoretic foundation of delimited continuations**
   - Authors: Zena Ariola, Hugo Herbelin, Amr Sabry
   - Year: 2007
   - Links: [Springer](https://link.springer.com/article/10.1007/s10990-007-9006-0)

4. **An Approach to Call-by-Name Delimited Continuations**
   - Authors: Hugo Herbelin, Silvia Ghilezan
   - Links: [PDF](http://pauillac.inria.fr/~herbelin/articles/popl-HerGhi08-cbn-delim+errata.pdf)

5. **A Classical Sequent Calculus with Dependent Types**
   - Author: Étienne Miquey
   - Year: 2019
   - Links: [ACM](https://dl.acm.org/doi/10.1145/3230625)

6. **Bottom Type (Wikipedia)**
   - Links: [Wikipedia](https://en.wikipedia.org/wiki/Bottom_type)

7. **Lambda Mu Calculus**
   - Original: Parigot (1992)
   - Links: [PLS Lab](https://www.pls-lab.org/Lambda_mu_calculus)

8. **Sequent Calculus as a Compiler Intermediate Language**
   - Authors: Paul Downen, Luke Maurer
   - Links: [PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/sequent-calculus-icfp16.pdf)
