# Ziku Haskell Rewrite: Migration Track

## Phase 0: Project Skeleton
- [x] `haskell-rewrite` ブランチを作成
- [x] 既存の Lean 4 実装ファイルを `archive/` ディレクトリに移動 (Ziku/, lakefile.lean, lean-toolchain, lake-manifest.json, Makefile, Dockerfile, tests/, etc.)
- [x] 古いドキュメントを `archive/docs/` に移動 (docs/architecture.md, docs/research/ etc.)
- [x] `cabal init` — ziku.cabal, cabal.project 作成
- [x] mise.toml — ghcup + tasks 設定
- [x] cabal.project.ci — `-Werror` 設定
- [x] fourmolu.yaml
- [x] .hlint.yaml
- [x] .gitignore — Haskell 固有の除外設定 (dist-newstyle/ etc.)
- [x] .github/workflows/ci.yml
- [x] test/Main.hs — tasty テストハーネスエントリポイント
- [x] tests/golden/ を Lean リポジトリから保持 (330 files)
- **Gate**: `mise run setup` が成功、`mise run check` が通る (テストは空でよい) **PASSED**

## Phase 1: Data Types + Parser
- [ ] src/Ziku/Syntax.hs — Surface AST
- [ ] src/Ziku/FreshName.hs — Hygienic name generation
- [ ] src/Ziku/Syntax/Pretty.hs — prettyprinter
- [ ] src/Ziku/Lexer.hs — megaparsec lexer
- [ ] src/Ziku/Parser.hs — megaparsec parser
- [ ] test/Golden/Parser.hs — golden test harness
- **Gate**: `parser/success/` + `parser/error/` golden tests pass

## Phase 2: Type Inference
- [ ] src/Ziku/Type.hs
- [ ] src/Ziku/Builtins.hs
- [ ] src/Ziku/Elaborate.hs
- [ ] src/Ziku/Infer.hs
- [ ] test/Golden/Infer.hs
- **Gate**: `infer/success/` + `infer/error/` golden tests pass

## Phase 3: IR + Translation
- [ ] src/Ziku/IR/Syntax.hs
- [ ] src/Ziku/IR/Syntax/Pretty.hs
- [ ] src/Ziku/Translate.hs
- [ ] src/Ziku/IR/Simplify.hs
- [ ] src/Ziku/IR/Focusing.hs
- [ ] test/Golden/IrEval.hs (translate tests)
- **Gate**: `emit-translate/`, `truncate/` golden tests pass

## Phase 4: Evaluators + Backend
- [ ] src/Ziku/IR/Eval.hs
- [ ] src/Ziku/IR/BigStepEval.hs
- [ ] src/Ziku/Backend/Scheme.hs
- [ ] test/Golden/Scheme.hs
- **Gate**: `ir-eval/`, `ir-eval-big-step/`, `big-step/`, `big-step-consistency/`, `emit-scheme/`, `scheme-only/`, `scheme/`, `consistency/` golden tests pass

## Phase 5: Import + CLI + REPL
- [ ] src/Ziku/Import.hs
- [ ] src/Ziku/Error.hs
- [ ] app/Main.hs
- **Gate**: `io/` tests pass, REPL starts

## Phase 6: Polish
- [ ] hlint 指摘 0 件
- [ ] fourmolu --mode check 通過
- [ ] cabal-gild --mode check 通過
- [ ] CI 全 green
- [ ] CLAUDE.md, README.md をHaskell プロジェクト用に更新
