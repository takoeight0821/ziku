# MAL Step 6 Implementation Plan

Date: 2026-01-25
Updated: 2026-01-25 (コンパイル時間問題対応)

## 現在の状況

### 完了した作業
1. ✅ `Ziku/Backend/Scheme.lean` に `ziku-slurp` 追加済み
2. ✅ `examples/mal/core.ziku` に新関数追加済み（read-string, str, 比較演算子等）
3. ✅ `examples/mal/step6_file.ziku` 作成済み（ただしコンパイルが終わらない）

### 問題
- step6_file.ziku のコンパイルが妥当な時間内に終了しない

## Overview

MAL Step 6 (Files, Mutation, and Evil) の実装計画。Issue #17 の一部。

---

## Ziku処理系への変更の必要性

### 結論: 最小限の変更のみ必要

| 機能 | Ziku変更 | 理由 |
|------|----------|------|
| read-string | 不要 | MALの既存 `read_str` を使用 |
| slurp | **1行追加** | Schemeヘルパー関数の追加 |
| str | 不要 | MALで実装 |
| eval | 不要 | MALで実装 |
| load-file | 不要 | MALで定義 |
| Atoms | 不要 | Chez Schemeの `box`/`unbox`/`set-box!` をextern経由で使用 |

### 唯一のZiku変更: `slurp` ヘルパー

**ファイル**: `Ziku/Backend/Scheme.lean`
**場所**: `schemeRuntime` 文字列内 (573行目付近)
**変更内容**: 以下の1関数を追加

```scheme
(define (ziku-slurp filename)
  (call-with-input-file filename (lambda (p) (get-string-all p))))
```

**理由**:
- `call-with-input-file` は第2引数にScheme手続きを取る
- extern経由で直接呼ぶとCPS変換で複雑になる
- ラッパー関数を用意することでシンプルに `@("scheme", "ziku-slurp", 1)` で呼べる

### Atoms が Ziku変更不要な理由

Chez Schemeには組み込みのbox機能がある:
```scheme
(box 5)        ; 値5のboxを作成
(unbox b)      ; boxから値を取得
(set-box! b 10) ; boxの値を更新
```

これらは全てトップレベル手続きなので、Zikuの既存extern機構で直接呼び出せる:
```ziku
let makeBox = @("scheme", "box", 1) in
let unbox = @("scheme", "unbox", 1) in
let setBox = @("scheme", "set-box!", 2) in
```

---

## 実装する機能

1. **read-string** - 既存の `read_str` をMAL関数として公開
2. **slurp** - ファイル読み込み (Scheme extern経由)
3. **str** - 文字列連結関数 (load-fileに必要)
4. **eval** - REPL環境でASTを評価
5. **load-file** - MAL自身で定義
6. **Atoms** - `atom`, `atom?`, `deref`, `reset!`, `swap!`

---

## ファイル変更一覧

### 1. `Ziku/Backend/Scheme.lean` (Ziku処理系)
**変更**: schemeRuntime に `ziku-slurp` を追加 (1関数のみ)

```lean
-- 既存の ziku-read-line 定義の後に追加
(define (ziku-slurp filename)
  (call-with-input-file filename (lambda (p) (get-string-all p))))
```

### 2. `examples/mal/core.ziku` (MAL実装)
**変更**: `applyNative` に新しい関数を追加

- `read-string` - `read_str` を呼び出し
- `str` - 引数を文字列に変換して連結
- `atom?` - atomかどうかチェック

### 3. `examples/mal/step6_file.ziku` (MAL実装 - 新規作成)
**内容**: step5_tco.ziku をベースに以下を追加

1. **extern定義**:
   ```ziku
   let slurpScheme : String -> String = @("scheme", "ziku-slurp", 1) in
   let makeBox = @("scheme", "box", 1) in
   let unbox = @("scheme", "unbox", 1) in
   let setBox = @("scheme", "set-box!", 2) in
   ```

2. **MAtom型の追加**: `MAtom(box)` でboxをラップ

3. **apply関数の拡張**:
   - `MEval` - eval関数のハンドリング
   - Atom操作 (`deref`, `reset!`, `swap!`)

4. **applyNativeの拡張**:
   - `slurp` - `slurpScheme` を呼び出し
   - `atom` - `MAtom(makeBox val)` を返す

5. **replEnvの拡張**: 新しい関数を登録

6. **load-fileの定義** (MALで):
   ```mal
   (def! load-file (fn* (f) (eval (read-string (str "(do " (slurp f) "\nnil)")))))
   ```

---

## 実装順序

### Phase 1: Ziku処理系の変更 (5分)
1. `Ziku/Backend/Scheme.lean` に `ziku-slurp` を追加
2. `lake build` で確認

### Phase 2: MAL基本機能 (MALのみ)
1. `core.ziku` に `read-string`, `str` を追加
2. テスト: `(read-string "(+ 1 2)")`

### Phase 3: slurp (MALのみ)
1. `step6_file.ziku` を作成
2. extern定義を追加
3. `slurp` を `applyNative` に追加
4. テスト: `(slurp "test.txt")`

### Phase 4: eval と load-file (MALのみ)
1. `MEval` 型を追加
2. `apply` で `MEval` をハンドリング
3. `replEnv` に `eval` を登録
4. MALで `load-file` を定義
5. テスト: `(eval (read-string "(+ 1 2)"))`

### Phase 5: Atoms (MALのみ)
1. extern box関数を定義
2. `MAtom` 型を追加
3. `atom`, `atom?`, `deref`, `reset!`, `swap!` を実装
4. テスト: `(def! a (atom 2)) (swap! a + 1)`

---

## テスト計画

### ビルド確認
```bash
lake build  # Ziku変更後
lake test   # 既存テストの破壊がないこと
```

### 手動テスト
```bash
docker run --rm -it ziku lake exe ziku < examples/mal/step6_file.ziku
```

### 公式MALテスト (vendor/mal/tests/step6_file.mal より)
- `(read-string "(1 2 (3 4) nil)")` => `(1 2 (3 4) nil)`
- `(eval (read-string "(+ 2 3)"))` => `5`
- `(def! a (atom 2))` => `(atom 2)`
- `(deref a)` => `2`
- `(swap! a + 3)` => `5`

---

## リスク・注意点

1. **swap! のCPS**: 関数適用を含むため継続処理に注意
2. **eval の環境**: replEnv のスコープを正しく参照する
3. **ファイルパス**: slurpテスト時は相対パスに注意

---

## 問題発生 (2026-01-25)

### 問題
`step6_file.ziku` のコンパイルが妥当な時間内に終了しない。

### 原因分析
1. ファイルが約400行と大きく、コンパイルに時間がかかる
2. `load-file` の MAL 定義を静的にコンパイルしようとしている
3. `swap!` の実装が複雑な CPS 変換を必要とする

### 解決策: 段階的アプローチ

#### Step 6a: 最小限のファイル機能
1. `step6a_minimal.ziku` を作成
2. 含める機能:
   - `slurp` (ファイル読み込み)
   - `read-string` (文字列からAST)
   - `str` (文字列連結)
3. load-file, eval, Atoms は後回し

#### Step 6b: Atoms (load-file なし)
1. box/unbox/set-box! の extern 追加
2. `atom`, `deref`, `reset!` の実装
3. `swap!` は単純なケースのみ

#### Step 6c: eval と load-file
1. 外部から replEnv を参照できる仕組み
2. `eval` 関数
3. `load-file` の定義

### 修正版実装計画

#### 調査結果
- step5_tco.ziku: 196行、約1秒でコンパイル
- step6_file.ziku: 395行、コンパイルが終わらない

#### 実装ステップ

**Step 1: step6_file.ziku を簡略化**
- load-file の MAL 定義部分を削除（363-373行）
- swap! の複雑な実装を簡略化（318-327行）
- 最小限の機能でまずコンパイルを確認

**Step 2: 機能テスト**
```bash
# Schemeへコンパイル
lake exe ziku --scheme examples/mal/step6_file.ziku > /tmp/step6.scm

# Chez Scheme で実行
echo "(+ 1 2)" | scheme /tmp/step6.scm
```

**Step 3: 機能追加（動作確認後）**
- load-file: MAL REPL 内で手動定義
- swap!: 必要に応じて実装

---

## 検証方法

1. Schemeコンパイル成功の確認
2. 基本的なMAL式のテスト: `(+ 1 2)`, `(str "a" "b")`
3. Atom 操作のテスト: `(def! a (atom 5))`, `(deref a)`, `(reset! a 10)`
4. slurp のテスト: `(slurp "test.txt")`

---

## Docker Compose 設定 (2026-01-25 追加)

### 目的
ローカルディレクトリを `/workspaces/ziku` としてマウントし、ファイル変更が即座に反映されるようにする。

### 作成ファイル: `docker-compose.yml`

```yaml
services:
  ziku:
    build: .
    volumes:
      - .:/workspaces/ziku
    working_dir: /workspaces/ziku
    stdin_open: true
    tty: true
```

### 使用方法

```bash
# ビルド
docker compose build

# テスト実行
docker compose run --rm ziku make -j4 test-parallel

# lake コマンド実行
docker compose run --rm ziku lake exe ziku --scheme examples/mal/step6_file.ziku

# インタラクティブシェル
docker compose run --rm ziku bash
```

### 利点
- ローカルファイルの変更が即座に反映される
- キャッシュの再ビルド不要
- 開発効率の向上

---

## 次のアクション

1. `docker-compose.yml` を作成
2. Docker Compose でビルド確認
3. step6_file.ziku のコンパイルテスト
4. 動作確認
5. 必要に応じて機能を段階的に追加
