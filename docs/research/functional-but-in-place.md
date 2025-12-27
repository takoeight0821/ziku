# Functional But In-Place (FBIP)

純粋関数型プログラミングでありながら、in-place更新（破壊的更新）を自動的に実現する技術についてのリサーチノート。

## Overview

**FBIP (Functional But In-Place)** は、純粋関数型言語において参照カウントを活用し、実行時に安全な場合は自動的にin-place更新を行う最適化パラダイム。

主な実装:
- **Lean 4**: "Counting Immutable Beans" (IFL 2019)
- **Koka**: "Perceus" (PLDI 2021), "FP²" (ICFP 2023)

---

## Key Papers

### 1. Counting Immutable Beans (IFL 2019)

**Authors**: Sebastian Ullrich, Leonardo de Moura

**Links**:
- [arXiv](https://arxiv.org/abs/1908.05647)
- [PDF](https://pp.ipd.kit.edu/uploads/publikationen/ullrich19counting.pdf)
- [ACM DL](https://dl.acm.org/doi/10.1145/3412932.3412935)

#### Key Contributions

1. **非共有値のメモリ回収機構**: グローバルアロケータへの負荷を軽減
2. **借用参照 (Borrowed References)**: 参照カウント更新を最小化
3. **自動借用推論**: ヒューリスティックによる自動アノテーション

#### Resurrection Hypothesis（復活仮説）

> "Many objects die just before creating an object of the same kind."

関数型データ構造の更新時、古いオブジェクトが死に、同じ種類の新しいオブジェクトが生成されることが多い。この観察に基づき、参照カウントが1のオブジェクトは**その場で再利用**できる。

---

### 2. Perceus (PLDI 2021)

**Authors**: Alex Reinking, Ningning Xie, Leonardo de Moura, Daan Leijen

**Links**:
- [ACM DL](https://dl.acm.org/doi/10.1145/3453483.3454032)
- [Microsoft Research](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)

#### Key Features

1. **Garbage-Free**: 生きている参照のみを保持
2. **Reuse Analysis**: in-place更新を可能にする静的解析
3. **形式的検証**: 線形リソース計算による健全性証明

---

### 3. FP² : Fully in-Place Functional Programming (ICFP 2023)

**Authors**: Anton Lorenzen, Daan Leijen, Wouter Swierstra

**Links**: [PDF](https://webspace.science.uu.nl/~swier004/publications/2023-icfp.pdf)

Kokaの `fip` / `fbip` キーワードの理論的基盤。

---

## Lean 4 Implementation Details

### Reference Counting Architecture

Lean 4は**トレースGCではなく参照カウント**を採用している。

> "Each value in memory contains a field that tracks how many other values refer to it, and the run-time system maintains these counts as references appear or disappear."

Source: [Functional Programming in Lean - Summary](https://leanprover.github.io/functional_programming_in_lean/programs-proofs/summary.html)

### Memory Representation

```
┌─────────────────────────────────────┐
│ Object Header                       │
│ ├── Tag (constructor identifier)    │
│ └── Reference Count                 │
├─────────────────────────────────────┤
│ Pointer to field 1                  │
│ Pointer to field 2                  │
│ ...                                 │
└─────────────────────────────────────┘
```

Source: [Special Types](https://leanprover.github.io/functional_programming_in_lean/programs-proofs/special-types.html)

### In-Place Update Condition

参照カウントが **1** の場合、破壊的更新が可能:

> "If there are no other references to the array, then it is modified in-place."

Source: [Arrays - Lean Reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/)

### `dbgTraceIfShared` によるデバッグ

開発時に参照カウントを確認するための関数:

```lean
-- 参照カウントが1より大きい場合、メッセージを出力
dbgTraceIfShared "array" arr
```

**重要**: `#eval` では実際より多くの共有が報告される。正確なテストには `lake build` でコンパイルしたバイナリを使用すること。

Source: [Insertion Sort and Array Mutation](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Insertion-Sort-and-Array-Mutation/)

---

## Compiler IR: Reset/Reuse Optimization

### ExpandResetReuse Pass

Lean 4コンパイラのIRパスで、`reset` と `reuse` 命令を展開・最適化する。

Source: [Lean.Compiler.IR.ExpandResetReuse](https://florisvandoorn.com/carleson/docs/Lean/Compiler/IR/ExpandResetReuse.html)

#### IR命令

| 命令 | 説明 |
|------|------|
| `inc x` | 参照カウントをインクリメント |
| `dec x` | 参照カウントをデクリメント（0になったら解放） |
| `reset x` | オブジェクトを再利用準備 |
| `reuse x ctor ...` | オブジェクトを再利用して新しいコンストラクタを構築 |
| `isShared x` | 参照カウントが1より大きいかチェック |

#### 最適化パターン

**Before:**
```
x := reset y
z := reuse x ctor_i ws
```

**After (Fast Path):**
```
-- 参照カウント=1の場合
set x i ws[i]  -- 各フィールドを直接更新
```

**After (Slow Path):**
```
-- 参照カウント>1の場合
dec x
z := ctor_i ws  -- 新規アロケーション
```

---

## Practical Examples

### Array Operations

```lean
-- push: 参照カウント=1なら破壊的更新
def Array.push (arr : Array α) (x : α) : Array α := ...

-- set: 参照カウント=1なら破壊的更新
def Array.set (arr : Array α) (i : Fin arr.size) (x : α) : Array α := ...

-- swap: 参照カウント=1なら破壊的更新
def Array.swap (arr : Array α) (i j : Fin arr.size) : Array α := ...
```

### Insertion Sort Example

```lean
def insertionSort (arr : Array α) [Ord α] : Array α :=
  let rec loop (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      let arr := insertSorted arr i
      loop arr (i + 1)
    else
      arr
  loop arr 1

-- arr の参照カウントが1なら、全てのswapがin-placeで実行される
```

### デバッグ例

```lean
def testSort : IO Unit := do
  let arr := #[5, 3, 1, 4, 2]
  -- 最初の呼び出しでは arr が共有されている可能性
  let sorted := dbgTraceIfShared "input array" arr |> insertionSort
  IO.println s!"{sorted}"
```

---

## Performance Characteristics

### Best Practices

1. **線形使用パターン**: 配列を複数箇所で参照しない
2. **末尾再帰**: ループをfor文ではなく末尾再帰で書く
3. **専用API使用**: `Array.uset` は `Array.set` より高速（bounds checkなし）

### Overhead

| 操作 | コスト |
|------|--------|
| 参照カウント更新 | O(1)、ただしアトミック操作 |
| 共有チェック | O(1) |
| コピー発生時 | O(n) |

### Comparison with GC

| 特性 | Tracing GC | Reference Counting (Lean 4) |
|------|-----------|----------------------------|
| 解放タイミング | 不定期 | 即座（決定的） |
| メモリオーバーヘッド | 高い | 低い |
| 参照カウントコスト | なし | あり（最適化で軽減） |
| In-place更新 | 不可能 | 可能 |
| 循環参照 | 問題なし | N/A（Leanでは作れない） |

---

## Current Limitations and Ongoing Work

### Issue #7374: Return Object Recognition

[GitHub Issue](https://github.com/leanprover/lean4/issues/7374)

現在のFBIPコンパイラは、入力と同一のオブジェクトを返す場合でも不要な `isShared` チェックを生成する。

**例**: `EStateM.bind` のエラーケース
```lean
match ma s with
| .error e s => .error e s  -- 入力と同一だが再構築される
```

手動最適化で **stdlib C行数 3.2%削減** を達成。新コードジェネレータで対応予定。

### Borrowed Parameters (Lean 4.20.0+)

新コンパイラでは借用パラメータをサポート:
- パラメータを所有権転送なしで渡せる
- 参照カウント操作を削減

---

## Implications for ziku

### 現在のLean 4実装で得られる恩恵

1. **自動最適化**: 意識せずにFBIPが適用される
2. **Array/ByteArray**: 効率的なin-place更新
3. **AST操作**: コンパイラ内部でのAST変換に最適

### 設計上の注意点

1. **共有を避ける**: 同じデータ構造を複数箇所で参照しない
2. **線形パターン**: データを「消費」して新しいデータを返す設計
3. **`dbgTraceIfShared`**: パフォーマンスクリティカルな部分で確認

### 将来の可能性

- ziku言語自体にFBIP的な最適化を導入？
- コパターンマッチングとFBIPの組み合わせ？

---

## Sources

### Papers
- [Counting Immutable Beans (arXiv)](https://arxiv.org/abs/1908.05647)
- [Perceus (ACM DL)](https://dl.acm.org/doi/10.1145/3453483.3454032)
- [FP² (PDF)](https://webspace.science.uu.nl/~swier004/publications/2023-icfp.pdf)
- [Lean 4 Paper](https://lean-lang.org/papers/lean4.pdf)

### Documentation
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)
- [Lean Reference - Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/)
- [Lean 日本語 - Functional But In-Place](https://lean-ja.github.io/lean-by-example-legacy/build/FunctionalButInPlace.html)

### Implementation
- [Lean 4 GitHub](https://github.com/leanprover/lean4)
- [ExpandResetReuse IR Pass](https://florisvandoorn.com/carleson/docs/Lean/Compiler/IR/ExpandResetReuse.html)
- [Issue #7374: FBIP Optimization](https://github.com/leanprover/lean4/issues/7374)

### Related
- [Koka Language](https://koka-lang.github.io/koka/doc/book.html)
- [Microsoft Research - Perceus](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)
