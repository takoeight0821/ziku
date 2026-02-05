# Legacy Test Binary Removal Plan

**日付**: 2026-01-25
**状態**: ✅ 完了

## 目的

TestRunnerに統合済みのレガシーテストバイナリを削除し、コードベースを整理する。

## 実行結果

| バイナリ | 状態 | 備考 |
|----------|------|------|
| `test-runner` | ✅ マスター | すべてのテストを統合 |
| `golden-test` | ✅ 削除済み | lakefile.lean、tests/GoldenTest.lean を削除 |
| `truncate-test` | ✅ 削除済み | lakefile.lean、tests/TruncateTest.lean を削除 |
| `ziku-test` | ✅ 残す | 開発者向けデバッグツール（各フェーズを個別実行） |
| `emit-compiled-code` | ✅ 使用中 | テストで使用 |

## 削除対象（完了）

### 1. lakefile.lean から削除

```lean
-- 削除: Legacy golden test runner
lean_exe «golden-test» where
  root := `tests.GoldenTest

-- 削除: Legacy truncate test runner
lean_exe «truncate-test» where
  root := `tests.TruncateTest
```

### 2. テストファイルを削除

- `tests/GoldenTest.lean` - TestRunnerに統合済み
- `tests/TruncateTest.lean` - TestRunnerに統合済み

### 3. Dockerfile を更新

```dockerfile
# 変更前
RUN lake build && lake build test-runner truncate-test

# 変更後
RUN lake build && lake build test-runner
```

### 4. CI ワークフローを更新

```yaml
# 変更前
run: lake build && lake build test-runner truncate-test

# 変更後
run: lake build && lake build test-runner
```

## 修正対象ファイル

1. `lakefile.lean` - レガシーターゲット削除
2. `tests/GoldenTest.lean` - 削除
3. `tests/TruncateTest.lean` - 削除
4. `Dockerfile` - ビルドコマンド更新
5. `.github/workflows/lean_action_ci.yml` - ビルドコマンド更新

## 検証方法

1. ローカルでビルド確認
   ```bash
   lake build && lake build test-runner
   ```

2. テスト実行
   ```bash
   make -j4 test-parallel
   ```

3. Dockerビルド確認
   ```bash
   docker build -t ziku:test .
   docker run --rm ziku:test
   ```

## 検証結果

- ✅ ローカルビルド成功
- ✅ 並列テスト成功（960テスト全パス）
- ✅ Dockerビルド成功
- ✅ Dockerコンテナでのテスト成功（960テスト全パス）
