# Large Scheme File Mitigation and Scripts Directory Cleanup

**日付**: 2026-01-25

## 問題

1. mal step6のデバッグ時、生成されるSchemeコードが巨大でClaude CodeがReadでクラッシュする
2. scriptsディレクトリの命名規則が不統一（ハイフン vs アンダースコア）
3. `run-mal.sh`の名前が機能を適切に表していない

## 解決策

### 1. 新規スクリプト: `scheme-analyze.sh`

巨大なSchemeファイルを部分的に分析するツール。

**機能**:
- `--stats`: ファイル統計情報（行数、文字数、define数、lambda数）
- `--functions`: 関数定義一覧（行番号付き、最初の100件）
- `--head N`: 先頭N行
- `--tail N`: 末尾N行
- `--range START END`: 指定範囲の行
- `--section runtime|main`: ランタイム部分またはメインプログラム部分を抽出
- `--search PATTERN`: パターン検索（コンテキスト付き）

**使用例**:
```bash
# 統計情報を確認
./scripts/scheme-analyze.sh --stats .mal_tmp.scm

# 関数定義一覧
./scripts/scheme-analyze.sh --functions .mal_tmp.scm

# メインプログラム部分のみ（ランタイム除外）
./scripts/scheme-analyze.sh --section main .mal_tmp.scm

# 特定の関数を検索
./scripts/scheme-analyze.sh --search "ziku-eval" .mal_tmp.scm
```

### 2. 新規スクリプト: `scheme-split.sh`

生成されたSchemeコードをランタイムとメインに分割。

**使用例**:
```bash
./scripts/scheme-split.sh .mal_tmp.scm output
# -> output-runtime.scm, output-main.scm が生成される
```

### 2.5 新規スクリプト: `scheme-format.sh`

S式をインデント整形して読みやすくする。

**機能**:
- 標準入力またはファイルからS式を読み込み
- 適切なインデント付きで整形出力
- `scheme-analyze.sh`と組み合わせて使用可能

**使用例**:
```bash
# ファイルを整形
./scripts/scheme-format.sh .mal_tmp.scm

# パイプで使用（部分抽出→整形）
./scripts/scheme-analyze.sh --section main .mal_tmp.scm | ./scripts/scheme-format.sh

# 特定の関数を検索して整形
./scripts/scheme-analyze.sh --search "define ziku-eval" .mal_tmp.scm | ./scripts/scheme-format.sh
```

**実装**: Chez Schemeの`pretty-print`を活用（依存関係なし）

### 3. 新規エージェント: `scheme-analyzer`

`.claude/agents/scheme-analyzer.md` - 巨大なSchemeファイルを分析するエージェント

**概要**:
- 生成されたSchemeコードを分析スクリプトを使って調査
- Claude Codeが直接ファイルを読めない場合でもデバッグ可能

**ツール**: Bash, Read, Grep, Glob
**モデル**: haiku（軽量タスク向け）

**機能**:
- `scheme-analyze.sh`を使って統計情報を取得
- 関数定義一覧を抽出
- 特定セクションのみを取得して分析
- フォーマット後のコードを部分的に読み取り

### 4. 新規スキル: `scheme-debug`

`.agent/skills/scheme-debug/SKILL.md` - Schemeデバッグワークフローのスキル

**概要**:
- 分析スクリプト群の使い方
- デバッグワークフローの手順
- 巨大ファイル対策のベストプラクティス

**内容**:
1. Quick Start
2. 利用可能なスクリプト一覧
3. デバッグワークフロー（統計→分割→部分分析→整形）
4. 使用例

### 5. スクリプト名変更

| 現在の名前 | 新しい名前 | 理由 |
|-----------|-----------|------|
| `run-mal.sh` | `concat-run.sh` | 複数ファイル連結・実行という機能を明確化 |
| `run_docker.sh` | `run-docker.sh` | ハイフン命名規則に統一 |
| `compare_big_step.py` | `compare-big-step.py` | ハイフン命名規則に統一 |

### 4. 整理後のscriptsディレクトリ構造

```
scripts/
├── README.md                   # 各スクリプトの説明（新規）
├── # 実行ツール
├── concat-run.sh               # 複数ファイル連結・実行（旧run-mal.sh）
├── run-scheme.sh               # Ziku→Scheme実行
├── run-docker.sh               # Docker起動（旧run_docker.sh）
├── # 分析/デバッグツール
├── scheme-analyze.sh           # Scheme分析（新規）
├── scheme-split.sh             # Scheme分割（新規）
├── scheme-format.sh            # S式整形（新規）
├── ziku-test.sh                # フェーズテスト
├── # テストインフラ
├── aggregate-test-results.sh   # テスト結果集計
├── golden-test-viewer.sh       # ゴールデンテストビューア
└── compare-big-step.py         # 一貫性検証（旧compare_big_step.py）
```

## 実装手順

### Step 1: 分析スクリプト作成
- [ ] `scripts/scheme-analyze.sh` を作成
- [ ] 動作確認

### Step 2: 分割スクリプト作成
- [ ] `scripts/scheme-split.sh` を作成
- [ ] 動作確認

### Step 2.5: フォーマットスクリプト作成
- [ ] `scripts/scheme-format.sh` を作成（Chez Schemeのpretty-print活用）
- [ ] 動作確認

### Step 3: エージェント作成
- [ ] `.claude/agents/scheme-analyzer.md` を作成
- [ ] エージェント動作確認

### Step 4: スキル作成
- [ ] `.agent/skills/scheme-debug/SKILL.md` を作成
- [ ] スキル確認

### Step 5: 既存スクリプトのリネーム
- [ ] `run-mal.sh` → `concat-run.sh`
- [ ] `run_docker.sh` → `run-docker.sh`
- [ ] `compare_big_step.py` → `compare-big-step.py`

### Step 6: ドキュメント
- [ ] `scripts/README.md` を作成（各スクリプトの説明）

## 検証方法

```bash
# 分析スクリプトのテスト
./scripts/concat-run.sh --scheme examples/mal/core.ziku examples/mal/step5_tco.ziku > /tmp/test.scm
./scripts/scheme-analyze.sh --stats /tmp/test.scm
./scripts/scheme-analyze.sh --functions /tmp/test.scm
./scripts/scheme-analyze.sh --section main /tmp/test.scm | head -50

# 分割スクリプトのテスト
./scripts/scheme-split.sh /tmp/test.scm /tmp/split
ls -la /tmp/split-*.scm

# フォーマットスクリプトのテスト
./scripts/scheme-analyze.sh --section main /tmp/test.scm | ./scripts/scheme-format.sh | head -100

# concat-runのテスト（名前変更後）
./scripts/concat-run.sh examples/mal/core.ziku examples/mal/step5_tco.ziku
```

## 修正対象ファイル

### スクリプト
- `scripts/scheme-analyze.sh` (新規作成)
- `scripts/scheme-split.sh` (新規作成)
- `scripts/scheme-format.sh` (新規作成)
- `scripts/run-mal.sh` → `scripts/concat-run.sh` (リネーム)
- `scripts/run_docker.sh` → `scripts/run-docker.sh` (リネーム)
- `scripts/compare_big_step.py` → `scripts/compare-big-step.py` (リネーム)
- `scripts/README.md` (新規作成)

### エージェント/スキル
- `.claude/agents/scheme-analyzer.md` (新規作成)
- `.agent/skills/scheme-debug/SKILL.md` (新規作成)
- `scripts/run_docker.sh` → `scripts/run-docker.sh` (リネーム)
- `scripts/compare_big_step.py` → `scripts/compare-big-step.py` (リネーム)
- `scripts/README.md` (新規作成)
