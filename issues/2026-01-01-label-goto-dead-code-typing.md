---
date: 2026-01-01
title: label/goto dead code typing with bottom type
status: closed
---

# label/goto dead code typing with bottom type

## Description

`label`/`goto` 構文において、デッドコード（`goto`の後に続くコード）を正しく型付けできない問題があった。

### 具体的な問題

```ziku
label result { if true then goto(true, result) + 1 else false }
```

この式は `Bool` 型を持つべきだが、従来の型推論では：

- `goto(true, result) + 1` は `goto` が `Int` を返す必要がある（`+` 演算子のため）
- `else false` は `Bool`
- 両分岐の型が一致しないためエラー

しかし、`goto(true, result)` は戻らない（labelにジャンプする）ため、`+ 1` は実行されない「デッドコード」である。

## Root Cause

従来の型推論は `goto` に対してフレッシュな型変数を返すだけで、「戻らない式」の特殊な性質を考慮していなかった。

## Solution

制約ベースの型推論アーキテクチャを導入：

### 1. Bottom Type (`⊥`) の追加

`Ty.bottom` を追加。これは「値を持たない型」で、全ての型のサブタイプとして機能する。

```lean
inductive Ty where
  | ...
  | bottom : SourcePos → Ty  -- 戻らない式の型
```

### 2. 2フェーズ型推論

1. **制約生成フェーズ**: AST を走査して制約を収集
2. **制約解決フェーズ**: 単一化 + bottom 型伝播

### 3. bottomProp 制約

`goto(...) + 1` のような式で bottom を伝播させる制約：

```lean
| bottomProp (sources : List Ty) (target : Ty)
-- sources のいずれかが ⊥ なら target も ⊥
```

### 4. fieldAccess 制約

レコードフィールドアクセスの型解決を遅延させる制約：

```lean
| fieldAccess (pos : SourcePos) (recTy : Ty) (fieldName : Ident) (resultTy : Ty)
```

## Files Changed

- `Ziku/Syntax.lean`: `Ty.bottom` 追加
- `Ziku/Type.lean`: bottom 型のサポート
- `Ziku/Infer.lean`: 制約ベース型推論の実装
- `tests/golden/infer/success/goto_dead_code.ziku`: 新規テスト
- `tests/golden/infer/success/goto_if_dead_code.ziku`: 新規テスト

## Related Research

- `docs/research/delimited-continuations-type-inference.md` に詳細な調査結果を記録

## References

- [Grokking the Sequent Calculus](https://arxiv.org/abs/2406.14719) - goto の型付け規則
- [Polymorphic Delimited Continuations](https://www.cs.tsukuba.ac.jp/~kam/paper/aplas07.pdf) - answer type polymorphism
- [Bottom Type (Wikipedia)](https://en.wikipedia.org/wiki/Bottom_type) - ⊥ 型の概念

## Resolution

Commit `01a894d` で解決。全 332 テストがパス。
