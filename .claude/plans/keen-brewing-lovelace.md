# CLAUDE.md最適化計画

**日付**: 2026-01-24
**Issue**: #48 - CLAUDE.mdの最適化と簡潔化

## 目標

現在257行のCLAUDE.mdを約100行程度に削減し、重要な指示が埋もれないようにする。

## 現状分析

| セクション | 行数 | 問題 |
|-----------|------|------|
| Project Overview | 14行 | 維持 |
| Build Commands | 32行 | 維持 |
| Dependency Management | 80行 | 長すぎる、README.mdと重複 |
| Architecture | 90行 | コードから推測可能 |
| Testing | 14行 | 維持 |
| Conventions | 14行 | 維持 |
| Hints | 6行 | 維持 |

## 実装計画

### 1. アーキテクチャ詳細を`docs/architecture.md`に分離

**移動内容**:
- ファイル構造 (Ziku/ディレクトリツリー)
- Pipeline図
- Key Types (Surface Language, Sequent Calculus IR, Built-in Functions, Types)
- Core Design (Surface Language, IR説明)
- Translation Rules
- IR Reduction Rules

**CLAUDE.mdに残す内容**:
```markdown
## Architecture

See [docs/architecture.md](docs/architecture.md) for detailed architecture.

Key points:
- Surface language → IR translation via `Translate.lean`
- IR based on λμμ̃-calculus from "Grokking the Sequent Calculus"
- Scheme backend for code generation
```

### 2. 依存管理セクションをREADME.mdを参照するよう簡略化

**CLAUDE.mdに残す内容**:
```markdown
## Dependency Management

See [README.md#for-developers](README.md#for-developers) for detailed dependency management setup.

Quick reference:
- Nix flakes (`flake.nix`, `flake.lock`) for reproducible builds
- Renovate for automated dependency updates (weekly)
- Lean toolchain pinned via `lean-toolchain`
- Lake dependencies managed by `lake-manifest.json`
```

### 3. Translation Rules / IR Reduction Rulesをskillに移動

**新規作成**: `.claude/skills/sequent-calculus.md`

```yaml
---
name: sequent-calculus
description: Surface → IR translation rules and IR reduction semantics for Ziku's λμμ̃-calculus based intermediate representation. Use when implementing translation, IR evaluation, or understanding the core semantics.
---
```

内容:
- Translation Rules (⟦−⟧記法)
- IR Reduction Rules (μ/μ̃-reduction)
- 参照: `docs/research/grokking-the-sequent-calculus.md`

## 変更対象ファイル

1. **CLAUDE.md** - 削減・簡略化
2. **docs/architecture.md** - 新規作成（アーキテクチャ詳細移動）
3. **.claude/skills/sequent-calculus.md** - 新規作成

## 削減見込み

| 項目 | 前 | 後 |
|------|-----|-----|
| CLAUDE.md | 257行 | ~100行 |
| 削減行数 | - | ~157行 |

## 検証方法

1. 新しいClaude Codeセッションで`/clear`してCLAUDE.mdのみ読み込まれた状態を確認
2. アーキテクチャに関する質問 → `@docs/architecture.md`で詳細を取得できることを確認
3. Translation Rulesに関する質問 → `/sequent-calculus` skillで情報取得できることを確認
4. ビルド・テストコマンドが正しく実行されることを確認
