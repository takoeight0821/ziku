# Ziku Haskell 書き直し調査

Date: 2026-02-14

## 概要

Ziku (Lean 4実装) を Haskell で書き直す場合に必要な要素の調査結果。

## 現状のコードベース規模

| 区分 | ファイル数 | 推定行数 |
|------|-----------|---------|
| コア (Lexer, Parser, Syntax, Infer, Translate, etc.) | ~44 | ~8,000-10,000 |
| 形式証明 (Proofs/) | 7 | ~1,000+ |
| テスト (TestRunner, etc.) | 5 | ~1,000+ |

### パイプライン

```
Source Code (.ziku)
    ↓
[Lexer] → Tokens
    ↓
[Parser] → Surface AST (Expr/Decl)
    ↓
[Import Resolution] → Expanded AST
    ↓
[Elaborate] → Desugared AST (codata → records/lambdas)
    ↓
[Type Inference] → Typed AST + constraints solved
    ↓
[Translate] → IR (λμμ̃-calculus: Producer/Consumer/Statement)
    ↓
[Focusing] → Focused IR
    ↓
┌─────────┴─────────┐
│                   │
[IR Eval]      [Scheme Backend]
(Small-step /       ↓
 Big-step)     Scheme Code (.ss)
                    ↓
              [Chez Scheme Runtime]
```

## コンポーネント別ライブラリ対応表

| コンポーネント | Lean 4 現状 | Haskell 推奨 | 備考 |
|---------------|-------------|-------------|------|
| ビルド | Lake + Docker | **Cabal** (via GHCup) | GHC 9.14 LTS 推奨 |
| パーサ | 手書き (1280行) | **megaparsec** | 手書きスタイルに最適、エラーメッセージ優秀 |
| Pretty Print | 自前実装 | **prettyprinter** | Text ベース、ANSI 色対応 |
| 型推論 | 手書き HM (~900行) | **手書き** | 適切なライブラリなし |
| テスト | 自前 TestRunner | **tasty + tasty-golden** | `findByExtension` で自動発見、`--accept` でゴールデン更新 |
| エラー報告 | 自前 | **diagnose** | Rust 風の美しいエラーメッセージ |
| コード生成 | String 連結 | **text-builder** | 効率的な Scheme コード出力 |
| REPL | 自前 | **repline** (haskeline wrapper) | タブ補完、履歴、コマンドシステム |
| エフェクト | Lean monad | **effectful** or **mtl** | effectful は ReaderT IO 並の性能 |
| データ構造 | Lean stdlib | **containers** + **unordered-containers** + **text** | `String` は使わず `Text` 統一 |
| CLI 引数 | 自前 | **optparse-applicative** | 標準的な CLI パーサ |
| 性質テスト | N/A | **QuickCheck** or **hedgehog** | 形式証明の代替 |

## 各コンポーネント詳細

### 1. ビルドシステム: Cabal (via GHCup)

- GHC 9.14 LTS (2025年12月リリース、2年サポート)
- GHCup でツールチェーン管理
- `cabal.project` でマルチパッケージ対応

```bash
ghcup install ghc 9.14.1
ghcup install cabal latest
ghcup install hls latest
```

### 2. パーサ: megaparsec

手書きパーサからの移植に最適。

- モナド変換子ベース、エフェクトスタックと統合可能
- ソース位置の自動追跡
- `try` によるバックトラッキング制御
- カスタムエラーメッセージ

Alternative: Alex (lexer generator) + Happy (parser generator) — GHC 自体が使っている組み合わせ。

### 3. Pretty Print: prettyprinter

- Wadler のアルゴリズムベース
- `Text` ベース (`String` ではない)
- ANSI カラー、HTML レンダリング対応

### 4. 型推論: 手書き

Haskell エコシステムに HM 型推論の成熟したライブラリはない。手書きが標準。

Ziku 固有の要素:
- Level-based let-generalization
- 行多相 (レコード・バリアント)
- 多相レコードフィールド (`forall` の保存)
- `instantiateField` 制約

参考実装:
- [Write You a Haskell - HM chapter](https://github.com/sdiehl/write-you-a-haskell/blob/master/006_hindley_milner.md)
- [HM with constraints tutorial](https://kseo.github.io/posts/2017-01-02-hindley-milner-inference-with-constraints.html)

### 5. テスト: tasty + tasty-golden

既存の `.ziku` テストファイルをそのまま流用可能。

```haskell
import Test.Tasty.Golden (goldenVsString, findByExtension)

tests = do
  zkFiles <- findByExtension [".ziku"] "tests/golden/parser/success"
  return $ testGroup "Parser success"
    [ goldenVsString name (replaceExtension zkFile ".golden") (parseFile zkFile)
    | zkFile <- zkFiles
    , let name = takeBaseName zkFile
    ]
```

- `tasty-discover` でテストモジュール自動発見も可能
- `--accept` フラグでゴールデンファイル一括更新

### 6. エラー報告: diagnose

- ソーススパン付きの美しいエラーメッセージ
- マルチライン・マルチファイル対応
- Severity レベル (Error, Warning, Hint)

### 7. コード生成: text-builder

- `Data.Text.Lazy.Builder` の2倍高速
- `text-builder-linear` は線形型で更に高速 (GHC 9.0+)
- モノイダル API で Scheme コードを構築

### 8. REPL: repline

- `haskeline` のハイレベルラッパー
- GHCi ライクなインターフェース
- MTL 変換子と合成可能
- `:command` システム

### 9. エフェクトシステム

**effectful (モダン推奨):**
```haskell
import Effectful
import Effectful.State.Static.Local
import Effectful.Error.Static

type CompilerEff es a =
  ( State CompilerState :> es
  , Error CompilerError :> es
  , IOE :> es
  ) => Eff es a
```

**mtl (伝統的):**
```haskell
type CompilerM = StateT CompilerState (ExceptT CompilerError IO)
```

effectful は性能・合成性で mtl を上回るが、mtl はエコシステムが大きい。

### 10. 行多相

参考ライブラリ:
- `row-types`: closed type families ベース
- `CTRex`: 元祖実装

ただし Ziku の行多相は型推論内部で実装するため、これらのライブラリを直接使うのではなく、実装の参考にする。

## 形式証明の扱い

Lean の `Proofs/` にある証明 (Soundness, Arithmetic, Substitution, Semantics 等) は Haskell では直接表現できない。

| 選択肢 | 労力 | 保証レベル |
|--------|------|-----------|
| **証明を捨てる** | 低 | テストのみ |
| **QuickCheck で性質テストに変換** | 中 | 統計的保証 |
| **Agda で別途維持 (agda2hs)** | 高 | 形式的保証 |
| **Coq で別途維持 (hs-to-coq)** | 高 | 形式的保証 |

推奨: まず証明を捨て、QuickCheck で重要な性質をテストする。形式証明が必要になったら Agda を検討。

## 推奨プロジェクト構成

```
ziku-hs/
├── ziku.cabal
├── cabal.project
├── app/
│   └── Main.hs                  # エントリポイント (REPL, コンパイラモード)
├── src/
│   └── Ziku/
│       ├── Syntax.hs            # Surface AST (Expr, Pat, Ty, Decl)
│       ├── FreshName.hs         # # prefix によるハイジェニックな名前生成
│       ├── Lexer.hs             # megaparsec lexer
│       ├── Parser.hs            # megaparsec parser
│       ├── Elaborate.hs         # codata → record/lambda 展開
│       ├── Type.hs              # Subst, Scheme, applySubst, freeVars
│       ├── Infer.hs             # HM 型推論 (constraint-based)
│       ├── Builtins.hs          # 組み込み関数定義
│       ├── Translate.hs         # Surface → IR 変換
│       ├── Import.hs            # インポート解決
│       ├── Error.hs             # エラー型 + diagnose 統合
│       ├── IR/
│       │   ├── Syntax.hs        # λμμ̃ IR (Producer, Consumer, Statement)
│       │   ├── Eval.hs          # Small-step 評価器
│       │   ├── BigStepEval.hs   # Big-step 評価器
│       │   ├── Simplify.hs      # IR 単純化
│       │   └── Focusing.hs      # Focusing 変換
│       └── Backend/
│           └── Scheme.hs        # Chez Scheme コード生成
├── test/
│   ├── Main.hs                  # tasty test harness
│   ├── Golden/
│   │   ├── Parser.hs
│   │   ├── Infer.hs
│   │   ├── IrEval.hs
│   │   └── Scheme.hs
│   └── Property/
│       ├── Infer.hs             # QuickCheck: 型推論の性質
│       └── IR.hs                # QuickCheck: IR の性質
└── tests/golden/                # テストデータ (Lean 版から流用)
    ├── parser/{success,error}/
    ├── infer/{success,error}/
    ├── ir-eval/{success,error}/
    └── scheme/
```

### cabal ファイルスケルトン

```cabal
cabal-version: 3.0
name: ziku
version: 0.1.0.0
synopsis: A functional language exploring data/codata duality
license: BSD-3-Clause

common warnings
    ghc-options: -Wall -Wcompat -Wno-name-shadowing

library
    import: warnings
    exposed-modules:
        Ziku.Syntax
        Ziku.FreshName
        Ziku.Lexer
        Ziku.Parser
        Ziku.Elaborate
        Ziku.Type
        Ziku.Infer
        Ziku.Builtins
        Ziku.Translate
        Ziku.Import
        Ziku.Error
        Ziku.IR.Syntax
        Ziku.IR.Eval
        Ziku.IR.BigStepEval
        Ziku.IR.Simplify
        Ziku.IR.Focusing
        Ziku.Backend.Scheme
    build-depends:
        base >= 4.16 && < 5
      , text >= 2.0
      , containers
      , unordered-containers
      , megaparsec >= 9.0
      , prettyprinter
      , text-builder
      , effectful-core
      , diagnose
      , filepath
    hs-source-dirs: src
    default-language: GHC2021

executable ziku
    import: warnings
    main-is: Main.hs
    build-depends:
        base
      , ziku
      , repline
      , optparse-applicative
      , effectful
    hs-source-dirs: app
    default-language: GHC2021

test-suite ziku-test
    import: warnings
    type: exitcode-stdio-1.0
    main-is: Main.hs
    other-modules:
        Golden.Parser
        Golden.Infer
        Golden.IrEval
        Golden.Scheme
        Property.Infer
        Property.IR
    build-depends:
        base
      , ziku
      , tasty
      , tasty-golden
      , tasty-quickcheck
      , filepath
      , text
    hs-source-dirs: test
    default-language: GHC2021
```

## 参考プロジェクト

| プロジェクト | 関連性 | URL |
|------------|--------|-----|
| **Write You a Haskell** | HM 型推論の実装チュートリアル | https://github.com/sdiehl/write-you-a-haskell |
| **PureScript compiler** | HM + 行多相 + ADT の本格コンパイラ | https://hackage.haskell.org/package/purescript |
| **Sequent Core** | GHC でシーケント計算を IR として使う研究 | https://dl.acm.org/doi/10.1145/2951913.2951931 |
| **Sixty** | Haskell で書かれた依存型言語 | https://github.com/ollef/sixty |
| **Elm Compiler** | クリーンなアーキテクチャ、良いエラーメッセージ | https://github.com/elm/compiler |

## 移植の推奨順序

1. **Syntax.hs** — ADT 定義 (Lean → Haskell はほぼ直訳)
2. **Lexer + Parser** — megaparsec で再実装
3. **Elaborate** — codata → record/lambda 変換
4. **Type + Infer** — 最も複雑。level-based let-generalization + 行多相
5. **Translate** — Surface → IR (パターンコンパイル含む)
6. **IR/Eval** — μ/μ̃ の簡約
7. **Backend/Scheme** — text-builder でコード出力
8. **テスト** — tasty-golden、既存 `.ziku` ファイルをそのまま流用
9. **REPL** — repline で実装

## Lean 4 → Haskell の主な違い

| 項目 | Lean 4 | Haskell |
|------|--------|---------|
| 全域性 | コンパイラが証明 | 保証なし (`-Wall` で補完) |
| `do` 記法 | ほぼ同じ | ほぼ同じ |
| 型クラス | あり | あり (より成熟したエコシステム) |
| パターンマッチ | 網羅性チェック | 網羅性チェック (`-Wincomplete-patterns`) |
| 性能 | C にコンパイル | ネイティブ/LLVM (同等) |
| ツーリング | lean4 language server | HLS (GHC 9.14 で大幅改善) |
| 依存型 | あり | なし (GADTs, TypeFamilies で部分的に可能) |

## メリット・デメリット

### Haskell に移行するメリット

- Hackage の豊富なライブラリエコシステム
- コンパイラ開発の知見・先行事例が多い
- HLS が成熟し開発体験が良い
- GHC 9.14 LTS で長期サポート
- megaparsec, tasty-golden 等の成熟したツール

### Lean 4 に留まるメリット

- 形式証明をそのまま維持できる
- 既にコードが動いている (移植コスト 0)
- Lean 4 自体もエコシステムが成長中
- 依存型による強い型保証
