# Ziku

Lean 4で実装された算術式評価器（型推論付き）

## 概要

- **AST**: 整数リテラル、変数、四則演算（+、-、*、/）
- **パーサー**: 手書きパーサー（演算子優先順位対応）
- **評価器**: 環境ベースの評価
- **型システム**: Int型のみの単純な型推論基盤（将来の拡張用）

## ファイル構成

```
ziku/
├── lakefile.toml
├── lean-toolchain
├── Main.lean            # REPLエントリポイント
├── Ziku.lean           # ライブラリルート
└── Ziku/
    ├── Syntax.lean     # AST定義
    ├── Parser.lean     # パーサー
    ├── Type.lean       # 型定義
    ├── Infer.lean      # 型推論
    └── Eval.lean       # 評価器
```

## ビルド

```bash
lake build
```

## 実行

```bash
./.lake/build/bin/ziku
```

REPLが起動します：

```
Ziku REPL
Type :quit or :q to exit
> 1 + 2
3
> 3 * 4
12
> 10 - 5
5
> 20 / 4
5
> :quit
Goodbye!
```

## 演算子優先順位

- `*`, `/` > `+`, `-`
- 括弧 `()` でグルーピング可能

## 拡張方針

型推論基盤（Type.lean、Infer.lean）は将来的な多相型対応を想定した設計。現状は算術式のみなのでInt型固定だが、以下のような拡張が容易：

- let束縛
- ラムダ抽象
- 関数適用
- Hindley-Milner型推論

## 実装のポイント

- **パーサー**: Std.Internal.ParsecのAPI問題により手書きパーサーを採用
- **partial関数**: 停止性証明が困難な再帰関数にpartialを使用
- **mutual recursion**: parseExpr、parseFactor、parseAtomの相互再帰