# テスト高速化プラン

**日付**: 2026-01-24

## 現状分析

### テスト実行時間の内訳（推定）

| テスト種類 | テスト数 | 推定時間 | 割合 |
|-----------|---------|---------|------|
| **Scheme consistency** | 124 | 60〜250秒 | **50〜70%** |
| IR-eval (小ステップ) | 128 | 5〜20秒 | 10〜15% |
| Big-step consistency | 124 | 5〜15秒 | 5〜10% |
| Type inference | 82 | 4〜16秒 | 5〜10% |
| Parser | 99 | 0.1〜1秒 | <1% |
| その他 | 339 | 10〜30秒 | 10〜15% |
| **合計** | **約896** | **70〜290秒** | 100% |

### 主要なボトルネック

1. **Scheme外部プロセス呼び出し（最大のボトルネック）**
   - 124回のSchemeプロセス起動（各0.5〜2秒）
   - 毎回の一時ファイル作成・削除
   - プロセス間通信のオーバーヘッド

2. **逐次実行**
   - `TestRunner.lean`は全テストを順次実行
   - CPUマルチコアを活用していない

3. **環境操作のO(n)問題**
   - `Env.lookup`が`List.find?`で線形探索
   - 大規模テスト（mal_step4_fn等）で顕著

4. **Docker/Nixのオーバーヘッド**
   - Docker起動: 数秒〜十数秒
   - Nix環境構築: 初回数分

## 高速化オプション

### Option A: Scheme REPL永続化（効果：高、工数：中）

**概要**: 各テストで新プロセスを起動する代わりに、1つのScheme REPLを永続化して再利用

**実装方法**:
1. テスト開始時にScheme REPLをバックグラウンドで起動
2. 各テストはREPLに式を送信して結果を受信
3. テスト終了時にREPLを終了

**期待効果**: Scheme consistencyテストを60〜250秒 → 10〜30秒に短縮

### Option B: テストの並列実行（効果：高、工数：高）

**概要**: 独立したテストを複数スレッドで並列実行

**実装方法**:
1. `IO.asTask`を使用してテストを並列起動
2. 結果を集約して表示
3. スレッド数を設定可能に

**期待効果**: 全体の実行時間を1/N（Nはコア数）に短縮

**注意点**:
- Lean 4のIO.asTaskの制限を確認する必要あり
- 出力の競合を避ける設計が必要

### Option C: 環境のハッシュテーブル化（効果：中、工数：低）

**概要**: `Env`の内部表現を`List`から`HashMap`に変更

**実装方法**:
```lean
-- 現在
structure Env where
  bindings : List (Ident × EnvValue)

-- 変更後
structure Env where
  bindings : Std.HashMap Ident EnvValue
```

**期待効果**: IR-evalテストを5〜20秒 → 2〜8秒に短縮

### Option D: ネイティブ実行への移行（効果：中、工数：低）

**概要**: ローカル開発時はDockerを使わずネイティブ実行を推奨

**実装方法**:
1. CLAUDE.mdの推奨コマンドを更新
2. CIでのみDockerを使用

**期待効果**: Docker起動オーバーヘッド（数秒〜十数秒）を削減

### Option E: テストの分類と選択的実行（効果：中、工数：低）

**概要**: 変更に関連するテストのみを実行

**実装方法**:
1. `lake test --category parser`のようなオプションを追加
2. 開発中は関連テストのみ実行
3. CIでは全テスト実行

**期待効果**: 開発サイクルを大幅に短縮

### Option F: Scheme consistencyテストのスキップオプション（効果：高、工数：低）

**概要**: 通常のテスト実行ではScheme consistencyをスキップ

**実装方法**:
1. 環境変数`ZIKU_FULL_TEST`でフル実行を制御
2. デフォルトではScheme consistencyをスキップ
3. CIと明示的な指定時のみフル実行

**期待効果**: 通常のテスト実行を60〜250秒短縮

## 推奨アプローチ

### Phase 1: カテゴリ別実行の実装（Lean側）

**目的**: 各カテゴリを独立して実行可能にする

**実装内容**:
- コマンドライン引数でカテゴリを指定可能に
- `lake test -- parser` でパーサーテストのみ実行
- `lake test -- infer` で型推論テストのみ実行
- 引数なしで全テスト実行（現状維持）

### Phase 2: シェルレベルでの並列実行

**目的**: xargs/GNU parallelでカテゴリを並列実行

**実装内容**:
- Makefileまたはシェルスクリプトを追加
- 各カテゴリを独立プロセスで並列実行

```bash
# xargsでの並列実行例
echo "parser infer ir-eval" | xargs -P3 -n1 lake test --

# GNU parallelでの並列実行例
parallel lake test -- ::: parser infer ir-eval

# Makefileでの並列実行
make -j4 test
```

**利点**:
- Lean側の実装がシンプル（引数処理のみ）
- シェルの成熟した並列化機構を活用
- 出力の競合はシェル側で制御可能

## 実装の詳細

### Phase 1: カテゴリ別実行

`tests/TestRunner.lean`の`main`関数を修正：

```lean
def main (args : List String) : IO UInt32 := do
  let categories := if args.isEmpty then
    ["truncate", "big-step", "parser", "infer", "ir-eval", "consistency", "scheme"]
  else
    args

  IO.println s!"Running tests: {categories}"

  let mut totalPassed := 0
  let mut totalFailed := 0

  for cat in categories do
    let (passed, failed) ← match cat with
      | "truncate" => runTruncateTests
      | "big-step" => BigStepEvalTest.runTests
      | "parser" => runCategory "parser" "parser"
      | "infer" => runCategory "infer" "infer"
      | "ir-eval" => runCategory "ir-eval" "ir-eval"
      | "consistency" => runConsistencyCategory
      | "scheme" => runSchemeOnlyCategory
      | _ => do
        IO.println s!"Unknown category: {cat}"
        pure (0, 0)
    totalPassed := totalPassed + passed
    totalFailed := totalFailed + failed

  -- Summary...
```

**使用例**:
```bash
lake test              # 全テスト
lake test -- parser    # パーサーテストのみ
lake test -- parser infer  # パーサー＋型推論
```

### Phase 2: 並列実行と結果集約

**テスト結果のファイル出力**（Lean側）:
- 各カテゴリ実行時に結果をJSONファイルに出力
- `lake test -- parser --report .test-results/parser.json`

**結果集約スクリプト** (`scripts/aggregate-test-results.sh`):
```bash
#!/bin/bash
# 各カテゴリの結果を集約してレポートを出力

RESULTS_DIR=".test-results"
TOTAL_PASSED=0
TOTAL_FAILED=0
FAILED_CATEGORIES=""

for result in "$RESULTS_DIR"/*.json; do
  cat=$(basename "$result" .json)
  passed=$(jq -r '.passed' "$result")
  failed=$(jq -r '.failed' "$result")

  TOTAL_PASSED=$((TOTAL_PASSED + passed))
  TOTAL_FAILED=$((TOTAL_FAILED + failed))

  if [ "$failed" -gt 0 ]; then
    FAILED_CATEGORIES="$FAILED_CATEGORIES $cat"
  fi

  echo "$cat: $passed passed, $failed failed"
done

echo "========================"
echo "Total: $TOTAL_PASSED passed, $TOTAL_FAILED failed"

if [ "$TOTAL_FAILED" -gt 0 ]; then
  echo "Failed categories:$FAILED_CATEGORIES"
  exit 1
fi
```

**Makefile**:
```makefile
.PHONY: test test-parallel test-report clean-results

RESULTS_DIR := .test-results
CATEGORIES := parser infer ir-eval consistency

# 逐次実行（従来通り）
test:
	lake test

# 並列実行
test-parallel: clean-results $(addprefix test-,$(CATEGORIES))
	@./scripts/aggregate-test-results.sh

test-%:
	@mkdir -p $(RESULTS_DIR)
	lake test -- $* --report $(RESULTS_DIR)/$*.json

clean-results:
	@rm -rf $(RESULTS_DIR)
```

**使用方法**:
```bash
make -j4 test-parallel   # 並列実行 + 結果集約
```

## 期待される効果

| Phase | 推定高速化 | 備考 |
|-------|----------|------|
| Phase 1（カテゴリ別） | 開発時2-5倍 | 必要なテストのみ実行 |
| Phase 2（並列実行） | 全体2-4倍 | CPUコア数に依存 |

## 検証方法

### Phase 1 完了時
```bash
# カテゴリ別実行が動作することを確認
time lake test -- parser
time lake test -- infer
time lake test -- ir-eval
time lake test  # 全テスト（引数なし）
```

### Phase 2 完了時
```bash
# 逐次 vs 並列の比較
time lake test                    # 逐次
time make -j4 test-parallel       # 並列
```

### CI での確認
- GitHub Actionsで`make -j4 test-parallel`を使用
- 実行時間を比較

## 関連ファイル

- `tests/TestRunner.lean:744-825` - main関数（テスト実行順序）
- `tests/TestRunner.lean:340-370` - runConsistencyTest（Schemeプロセス呼び出し）
- `tests/TestRunner.lean:538-566` - runConsistencyCategory（124回のループ）
- `lakefile.lean` - ビルド設定
- `Ziku/IR/Env.lean` - 環境実装
- `.github/workflows/` - CI設定
