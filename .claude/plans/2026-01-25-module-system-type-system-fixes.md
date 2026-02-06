# Module System Type System Fixes

Date: 2026-01-25
Status: 計画中

## 概要

PR #66 のコードレビューで指摘された型システムの問題を修正する。

## 問題点

### 1. 多相型のインスタンス化が行われていない（最重要）

**現在の実装** (`Ziku/Infer.lean:695-701`):
```lean
| .import_ pos path => do
    let s ← get
    match s.importTypes.find? (fun (p, _) => p == path) with
    | some (_, ty) => return ty  -- 問題：型をそのまま返している
    | none => throw ...
```

シグネチャに多相型が含まれる場合（例: `{ id : forall a. a -> a }`）、同じ型変数が異なるimport箇所で共有される。

**期待動作**: 各import式で型変数をフレッシュ化する。

### 2. コード重複

| 関数 | Main.lean | TestRunner.lean | 重複度 |
|------|-----------|-----------------|--------|
| `collectImports` | 12-32行 | 27-47行 | 100% |
| `resolveImportTypes` | 36-60行 | 50-71行 | 99% |
| `expandImports` | 64-186行 | なし | - |

### 3. 循環import検出がない

`expandImports`は再帰的にimportを展開するが、訪問済みパスの追跡がない。

## 修正計画

### Step 1: `Ziku/Infer.lean` の修正（1行変更）

**修正箇所**: 699行目

```diff
- | some (_, ty) => return ty
+ | some (_, ty) => instantiateTy ty
```

既存の`instantiateTy`関数（413-422行）がforall型変数をフレッシュ化する。

### Step 2: `Ziku/Import.lean` の新規作成

共通コードを抽出:
- `collectImports` 関数
- `resolveImportTypes` 関数
- `expandImports` 関数（循環検出付き）

```lean
namespace Ziku.Import

/-- Collect all import paths from an expression -/
partial def collectImports : Expr → List String := ...

/-- Resolve import types by loading signature files -/
def resolveImportTypes (basePath : System.FilePath) (imports : List String)
    : IO (Except String ImportTypeMap) := ...

/-- Expand imports with circular detection -/
partial def expandImports (basePath : System.FilePath) (expr : Expr)
    (visited : List String := []) : IO (Except String Expr) := ...

end Ziku.Import
```

### Step 3: `Ziku.lean` の更新

```lean
import Ziku.Import
```

### Step 4: `Main.lean` の修正

- 重複コード削除（12-186行の大部分）
- `open Ziku.Import` を追加
- `expandImports`呼び出しを更新

### Step 5: `tests/TestRunner.lean` の修正

- 重複コード削除（27-71行）
- `open Ziku.Import` を追加

### Step 6: テストケース追加

#### 多相型シグネチャテスト

**`tests/golden/infer/success/import/poly.ziki`**:
```
{ id : forall a. a -> a }
```

**`tests/golden/infer/success/import/poly.ziku`**:
```ziku
{ id = \x => x }
```

**`tests/golden/infer/success/import_polymorphic.ziku`**:
```ziku
let m1 = import "import/poly.ziku" in
let m2 = import "import/poly.ziku" in
let a = m1.id 42 in
let b = m2.id true in
a + 1
```

**`tests/golden/infer/success/import_polymorphic.golden`**:
```
Int
```

#### 循環importテスト

**`tests/golden/infer/error/import_circular.ziku`**:
```ziku
let m = import "import/circular_a.ziku" in m
```

**`tests/golden/infer/error/import/circular_a.ziku`**:
```ziku
let m = import "circular_b.ziku" in m
```

**`tests/golden/infer/error/import/circular_b.ziku`**:
```ziku
let m = import "circular_a.ziku" in m
```

## 修正対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `Ziku/Infer.lean` | 699行目: `instantiateTy ty` に変更 |
| `Ziku/Import.lean` | **新規**: 共通import処理関数 |
| `Ziku.lean` | `import Ziku.Import` 追加 |
| `Main.lean` | 重複コード削除、Import使用 |
| `tests/TestRunner.lean` | 重複コード削除、Import使用 |
| `tests/golden/infer/**` | 新規テストケース追加 |

## 検証方法

```bash
# ビルド
lake build

# 全テスト実行
lake test

# 多相型テストの確認
echo 'let m = import "import/poly.ziku" in m.id 42' | lake exe ziku --infer
# 期待: Int

# 循環importのエラー確認
# 期待: Circular import detected
```

## 成功基準

1. 既存の962テストが全てパス
2. 多相型シグネチャのimportで型変数がフレッシュ化される
3. 循環importが検出されエラーになる
4. コード重複が解消される
