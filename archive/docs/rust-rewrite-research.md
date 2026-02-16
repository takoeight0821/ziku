# Ziku Rust Rewrite Research

Date: 2026-02-14

Ziku を Rust で書き直す際に必要な要素の調査結果。

## 現在のコードベース概要

### モジュール構成と規模

| モジュール | LOC | 役割 |
|-----------|-----|------|
| Parser.lean | 1,279 | 再帰下降パーサー |
| Infer.lean | 1,039 | HM型推論（レベルベースlet汎化） |
| Backend/Scheme.lean | 618 | Scheme コード生成 |
| Syntax.lean | 585 | Surface AST定義 |
| Lexer.lean | 551 | 手書きレクサー |
| IR/Eval.lean | 481 | Small-step IR評価器 |
| Translate.lean | 477 | Surface → IR変換 |
| Elaborate.lean | 429 | Codata エラボレーション |
| IR/BigStepEval.lean | 404 | Big-step IR評価器 |
| IR/Syntax.lean | 229 | λμμ̃ IR定義 |
| IR/Focusing.lean | 214 | IR focusing変換 |
| Soundness.lean | 153 | 型健全性 |
| IR/Simplify.lean | 132 | IR簡約化 |
| Import.lean | 126 | インポート解決 |
| Path.lean | 96 | パス解決 |
| Type.lean | 79 | 型ユーティリティ |
| Builtins.lean | 66 | 組み込み関数レジストリ |
| FreshName.lean | 57 | 衛生的名前生成 |
| Proofs/ | 763 | 各種証明 |
| **コア合計** | **~7,867** | |
| テスト基盤 | ~1,633 | TestRunner, BigStepEvalTest等 |
| **総計** | **~9,500** | |

外部依存は **batteries** (Lean標準ライブラリ拡張) のみ。

### パイプライン

```
Source Text
  │ Lexer (Lexer.lean)
  ↓
Tokens
  │ Parser (Parser.lean)
  ↓
Surface AST (Syntax.Expr)
  │ Import Resolution (Import.lean)
  ↓
Expanded AST
  │ Elaboration (Elaborate.lean)
  ↓ codata → records/lambdas
Elaborated AST
  │ Type Inference (Infer.lean) [optional]
  ↓
Typed AST
  │ Translation (Translate.lean)
  ↓
IR Statement (IR.Syntax)
  │
  ├→ Small-step Eval (IR/Eval.lean)
  ├→ Big-step Eval (IR/BigStepEval.lean)
  └→ Scheme Backend (Backend/Scheme.lean)
       ↓
     Scheme Code → Chez Scheme で実行
```

### 主要データ構造

**Surface AST** (`Syntax.lean`):
- `Expr`: lit, var, binOp, lam, app, let_, match_, codata, field, record, label, goto, con, extern, import_ 等
- `Pat`: var, lit, wild, con, paren, ann
- `Ty`: var, con, app, arrow, forall_, record, variant, bottom, tilde
- `Decl`: data, codata, def_, defPat, infix_, module_, import_

**IR** (`IR/Syntax.lean`):
- `Producer`: var, lit, mu, cocase, record, fix, dataCon (値を構成)
- `Consumer`: covar, muTilde, case, destructor (値を分解)
- `Statement`: cut, binOp, ifz, call, builtin, externalCall (計算を駆動)

**型システム** (`Type.lean`, `Infer.lean`):
- `Subst`: 型代入 `List (Ident × Ty)`
- `Scheme`: 型スキーム `{ vars : List Ident, ty : Ty }`
- `Constraint`: unify, bottomProp, instantiateField
- `GenState`: nextVar, constraints, labelEnv, currentLevel, varLevels, solvedSubst

---

## Rust での推奨クレート構成

### 1. Lexer / Parser

| クレート | 用途 | 理由 |
|---------|------|------|
| **[logos](https://github.com/maciejhirsz/logos)** | レクサー | proc macro ベースの FSM 生成。高速かつゼロコピー |
| **[chumsky](https://github.com/zesterer/chumsky)** | パーサーコンビネータ | エラーリカバリが優秀。logos と統合しやすい。ariadne と同じ作者 |

代替選択肢:
- **lalrpop**: LR(1) パーサー生成器。文法ファイルから直接 AST 構造体を生成できるがビルドが遅い
- **winnow**: nom の後継。最速のパーサーコンビネータと主張。手書き制御が最も効く
- **pest**: PEG パーサー。文法ファイルが読みやすい

現在の手書きパーサーの構造を考えると logos + chumsky が最も自然に移植できる。

### 2. エラー報告

| クレート | 用途 | 理由 |
|---------|------|------|
| **[ariadne](https://github.com/zesterer/ariadne)** | 診断メッセージ | chumsky と同作者。rustc 品質のエラー表示。マルチラインラベル対応 |

代替:
- **[miette](https://docs.rs/miette)**: Rust のエラーハンドリング (`Result`, `Error` trait) との統合が深い
- **[codespan-reporting](https://github.com/brendanzab/codespan)**: 安定性重視。プロダクションコンパイラで実績あり

### 3. 文字列インターニング

| クレート | 用途 | 理由 |
|---------|------|------|
| **[lasso](https://github.com/Kixiron/lasso)** | 識別子インターニング | O(1) 比較。`Rodeo`（シングルスレッド）と `ThreadedRodeo`（マルチスレッド）を提供 |

代替: **[string-interner](https://docs.rs/string-interner)** — よりシンプルな API

Lean の `String` 比較に比べ、Symbol ベースの O(1) 比較は大きな性能改善になる。

### 4. アリーナアロケーション

| クレート | 用途 | 理由 |
|---------|------|------|
| **[bumpalo](https://github.com/fitzgen/bumpalo)** | AST ノードのアロケーション | 異種型を同一アリーナに格納可能。コンパイラの典型的パターン |

代替: **[typed-arena](https://github.com/thomcc/rust-typed-arena)** — 単一型のみだが Drop を実行する

使い方:
- フェーズごとにアリーナを確保し、フェーズ完了時に一括解放
- AST ノード間の参照はアリーナ内のライフタイムで管理
- `Box` はフェーズをまたぐ所有が必要な場合に使用

### 5. 型推論 / 単一化

| クレート | 用途 | 理由 |
|---------|------|------|
| **[ena](https://github.com/rust-lang/ena)** | Union-Find | rustc から抽出。path compression 付き Tarjan アルゴリズム。`UnificationTable` が主要型 |

ena の `UnificationTable` を核に、現在の制約生成・ソルビングを移植する。
レベルベースの let 汎化、多相レコードフィールドは自前実装が必要。

参考実装:
- **[Gluon](https://github.com/gluon-lang/gluon)**: Rust 製の HM 型推論言語。最も参考になる
- **[polytype](https://crates.io/crates/polytype)**: HM 型システムライブラリ

### 6. バックエンド（Scheme 出力）

| クレート | 用途 | 理由 |
|---------|------|------|
| **[lexpr](https://github.com/rotty/lexpr-rs)** | S式の生成・シリアライズ | R6RS/R7RS 対応。serde 統合あり |

serde-lexpr を使えば、IR の Rust 構造体から直接 S式（Scheme コード）を生成できる可能性がある。

将来のネイティブコード生成:
- **[cranelift](https://cranelift.dev)**: LLVM の ~10倍高速なコード生成。出力は LLVM の 2-14% 遅い程度。2025H2 にプロダクション品質目標
- **[inkwell](https://github.com/TheDan64/inkwell)**: LLVM の安全な Rust ラッパー。最適化重視なら

### 7. REPL / CLI

| クレート | 用途 | 理由 |
|---------|------|------|
| **[rustyline](https://github.com/kkawakam/rustyline)** | REPL のラインエディタ | ヒストリ、補完、vi/emacs キーバインド。Rust REPL の事実上の標準 |
| **[clap](https://github.com/clap-rs/clap)** | CLI 引数パース | derive macro でサブコマンド定義。2025年版で 30% 高速化 |

代替 REPL: **[reedline](https://docs.rs/reedline)** — nushell で使用。より多機能

### 8. テスト

| クレート | 用途 | 理由 |
|---------|------|------|
| **[insta](https://github.com/mitsuhiko/insta)** | スナップショットテスト | CLI でスナップショットの確認・承認。`cargo insta review` で差分確認 |
| **[datatest-stable](https://docs.rs/datatest-stable)** | データ駆動テスト | ファイルベースのテスト自動検出。`.ziku` ファイルの自動ディスカバリに最適 |

組み合わせ方:
- datatest-stable で `tests/golden/` 内の `.ziku` ファイルを自動検出
- insta で各テストの出力をスナップショット比較
- 既存の `.golden` ファイルをそのまま再利用可能

### 9. ユーティリティ

| クレート | 用途 | 理由 |
|---------|------|------|
| **[pretty](https://docs.rs/pretty)** | Wadler 式プリティプリンタ | IR・AST のフォーマット出力に |
| **[derive-visitor](https://docs.rs/derive-visitor)** | Visitor パターンの自動導出 | 複数の AST 走査パスを簡潔に書ける |
| **[salsa](https://docs.rs/salsa)** | インクリメンタル計算 | rust-analyzer で使用。将来 LSP サーバーを作る際に有用 |
| **[tower-lsp](https://github.com/ebkalderon/tower-lsp)** | LSP サーバー実装 | エディタ統合。salsa と組み合わせて使用 |

---

## Lean 固有機能の Rust での対応

| Lean の機能 | Rust での対策 |
|------------|-------------|
| `inductive` 型 | `enum` |
| `structure` | `struct` |
| パターンマッチの網羅性検査 | `enum` + `match` でコンパイラが警告 |
| `partial def`（停止性証明不要） | Rust は停止性を要求しないのでそのまま再帰可能 |
| `deriving Repr, BEq` | `#[derive(Debug, PartialEq)]` |
| `deriving Hashable` | `#[derive(Hash)]` |
| `Except` モナド | `Result<T, E>` |
| `StateT` モナド | `&mut State` を引数で持ち回す |
| `do` 記法 | `?` 演算子 + `let` バインディング |
| `List` / `Array` | `Vec<T>` |
| `HashMap` (Batteries) | `std::collections::HashMap` |
| `IO` モナド | 直接的な副作用（Rust は純粋言語ではない） |
| Proofs (763 LOC) | 移植不要。Rust の型システムで不変条件を表現 |

### 設計上の主な変更点

1. **所有権とライフタイム**: AST ノード間の参照は bumpalo アリーナ + ライフタイムで管理。または `enum` の再帰は `Box` で包む
2. **エラーハンドリング**: `Result<T, E>` + `?` 演算子で Lean の `Except` モナドより簡潔になる
3. **可変状態**: Lean の `StateT` を `&mut InferCtx` に。型推論の `GenState` は直接可変参照で操作
4. **証明コード**: 763 LOC の証明は移植不要。代わりに Rust の型システム（`enum` の網羅性、借用チェッカー）で安全性を保証

---

## 参考プロジェクト

| プロジェクト | 特徴 | URL |
|-------------|------|-----|
| **Gluon** | Rust 製 HM 型推論言語。最も参考になる | https://github.com/gluon-lang/gluon |
| **rust-langdev** | 言語開発用 Rust クレートのキュレーションリスト | https://github.com/Kixiron/rust-langdev |
| **Rune** | 組み込み可能な動的言語 | https://github.com/rune-rs/rune |
| **Ketos** | Lisp 方言。Scheme バックエンド参考 | https://github.com/murarth/ketos |

sequent calculus IR を持つ Rust 製言語は見つからず、Ziku は Rust エコシステムでもユニークな位置づけになる。

---

## 推奨移植順序

### Phase 1: 基盤

1. **プロジェクトセットアップ**: cargo workspace 構成、CI 設定
2. **Lexer** (`logos`): トークン定義の移植。最も機械的
3. **AST 定義**: `enum`/`struct` への直訳
4. **Parser** (`chumsky`): logos トークン列を入力とするパーサー
5. **テスト基盤**: `insta` + `datatest-stable` で parser の golden test を通す

### Phase 2: 意味解析

6. **Elaborate**: codata → records/lambdas のパターン変換
7. **型推論**: `ena` ベースの単一化 + 制約ソルビング。最も複雑な移植対象
8. **テスト**: infer の golden test を通す

### Phase 3: IR + 実行

9. **IR 定義**: Producer/Consumer/Statement の `enum` 定義
10. **Translate**: Surface → IR 変換規則の移植
11. **IR 評価器**: Big-step のみで十分（Small-step は開発用で不要かも）
12. **テスト**: ir-eval の golden test を通す

### Phase 4: バックエンド + CLI

13. **Scheme バックエンド**: `lexpr` で S式出力
14. **REPL**: `rustyline` でインタラクティブモード
15. **CLI**: `clap` でコマンドライン引数
16. **テスト**: scheme, consistency の golden test を通す

### Phase 5: 発展

17. **Import 系**: パス解決、インポート展開
18. **LSP サーバー**: `salsa` + `tower-lsp`（オプション）
19. **ネイティブバックエンド**: `cranelift`（オプション）

---

## リスクと注意点

- **証明コードの喪失**: Lean 版にある型健全性等の形式証明 (763 LOC) は移植できない
- **所有権設計の学習コスト**: AST の再帰構造と借用チェッカーの相性に慣れが必要
- **chumsky のバージョン**: v1.0 がまだ安定版でない可能性がある。v0.9 系も検討
- **既存テスト資産**: `.golden` ファイルは再利用可能だが、出力フォーマットの微調整が必要な場合あり
