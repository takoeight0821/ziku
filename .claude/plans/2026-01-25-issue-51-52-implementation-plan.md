# Issue 51 and 52 Implementation Plan

**日付**: 2026-01-25

## 概要

Claude Code HooksとSubagentsを導入し、開発ワークフローを自動化・効率化する。

---

## Issue #51: Claude Code Hooksの導入

### 作成するファイル

#### 1. Hookスクリプト

```
.claude/hooks/
├── lean-build.sh           # Leanファイル編集後にビルド実行
├── protect-proofs.sh       # Proofs/ディレクトリの保護確認
└── test-golden.sh          # テストファイル作成後にテスト実行
```

#### 2. settings.json への追加

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit",
        "hooks": [
          {
            "type": "command",
            "command": "$CLAUDE_PROJECT_DIR/.claude/hooks/lean-build.sh"
          }
        ]
      },
      {
        "matcher": "Write",
        "hooks": [
          {
            "type": "command",
            "command": "$CLAUDE_PROJECT_DIR/.claude/hooks/test-golden.sh"
          }
        ]
      }
    ],
    "PreToolUse": [
      {
        "matcher": "Edit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "$CLAUDE_PROJECT_DIR/.claude/hooks/protect-proofs.sh"
          }
        ]
      }
    ]
  }
}
```

### Hookスクリプト詳細

#### lean-build.sh
- 入力JSONからファイルパスを取得
- `.lean`ファイルの場合のみ`lake build`を実行
- 終了コード: 0=成功、2=ブロック

#### protect-proofs.sh
- `Proofs/`ディレクトリへの変更を検出
- stderr に警告メッセージを出力
- 終了コード: 0（警告のみ、ブロックしない）

#### test-golden.sh
- `.ziku`ファイルの場合のみ`lake test`を実行
- goldenファイル生成を自動化

---

## Issue #52: Claude Code Subagentsの導入

### 作成するファイル

```
.claude/agents/
├── proof-verifier.md       # 証明検証エージェント
├── ir-analyzer.md          # IR分析エージェント
└── type-checker.md         # 型検証エージェント
```

### エージェント定義

#### proof-verifier.md

```yaml
---
name: proof-verifier
description: Lean 4の証明を検証。Proofs/ディレクトリのsorry有無や証明の完全性をチェックする際に使用。
tools: Read, Grep, Glob, Bash
model: sonnet
---
```

用途: 証明コードの品質検証

#### ir-analyzer.md

```yaml
---
name: ir-analyzer
description: Surface言語からIRへの変換結果を分析。IR構造の検証やデバッグに使用。
tools: Read, Grep, Glob
model: haiku
---
```

用途: IR変換の正確性確認（軽量タスク向けにhaiku）

#### type-checker.md

```yaml
---
name: type-checker
description: 型推論の結果を検証。推論された型の正しさやエラーメッセージの適切さを確認。
tools: Read, Grep, Glob, Bash
model: sonnet
---
```

用途: 型推論結果の検証

---

## 実装順序

1. **Hooks基盤** (Issue #51)
   - [ ] `.claude/hooks/`ディレクトリ作成
   - [ ] lean-build.sh作成
   - [ ] protect-proofs.sh作成
   - [ ] test-golden.sh作成
   - [ ] settings.jsonにhooks設定追加
   - [ ] 動作確認

2. **Subagents** (Issue #52)
   - [ ] `.claude/agents/`ディレクトリ作成
   - [ ] proof-verifier.md作成
   - [ ] ir-analyzer.md作成
   - [ ] type-checker.md作成
   - [ ] 動作確認

---

## 検証方法

### Hooks検証

```bash
# Hook登録確認
claude /hooks

# 各hookの手動テスト
echo '{"tool_input":{"file_path":"test.lean"}}' | .claude/hooks/lean-build.sh
```

### Subagents検証

```bash
# エージェント一覧確認
claude /agents

# 各エージェントの呼び出しテスト
# Task toolで proof-verifier を呼び出し
```

---

## 変更ファイル一覧

| ファイル | 操作 |
|---------|------|
| `.claude/hooks/lean-build.sh` | 新規作成 |
| `.claude/hooks/protect-proofs.sh` | 新規作成 |
| `.claude/hooks/test-golden.sh` | 新規作成 |
| `.claude/settings.json` | hooks設定追加 |
| `.claude/agents/proof-verifier.md` | 新規作成 |
| `.claude/agents/ir-analyzer.md` | 新規作成 |
| `.claude/agents/type-checker.md` | 新規作成 |
