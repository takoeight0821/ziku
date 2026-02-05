# Scheme Backend Pretty Print Implementation Plan

Date: 2026-01-25

## 概要

Scheme バックエンドのコード生成後に **必ず** Chez Scheme の `pretty-print` を使ってフォーマットする。

## 現状の問題

- 生成される Scheme コードは改行・インデントなしの長い1行
- 108行で約4MBのファイル（1行が数万文字）
- デバッグが非常に困難

## 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `Backend/SchemeMain.lean` | 生成後に必ずフォーマット処理を実行 |
| `scripts/format-scheme.scm` | 新規作成、フォーマット用スクリプト |

## 実装計画

### Phase 1: フォーマット用 Scheme スクリプト作成

`scripts/format-scheme.scm`:

```scheme
;; Read and pretty-print all expressions from stdin
(let loop ()
  (let ((expr (read)))
    (unless (eof-object? expr)
      (pretty-print expr)
      (newline)
      (loop))))
```

### Phase 2: SchemeMain.lean の修正

`--scheme` オプションでコード生成後、必ず Chez Scheme でフォーマット処理を実行:

1. 生成したコードを一時ファイルに書き出し
2. `scheme --quiet format-scheme.scm < temp.scm` を実行
3. フォーマット結果を stdout に出力

```lean
def formatSchemeCode (code : String) : IO String := do
  -- 一時ファイルに書き出し
  let tempFile ← IO.FS.createTempFile
  IO.FS.writeFile tempFile code
  -- Chez Scheme でフォーマット
  let result ← IO.Process.output {
    cmd := "scheme"
    args := #["--quiet", "scripts/format-scheme.scm"]
    stdin := IO.Process.Stdio.piped
  }
  -- 結果を返す
  pure result.stdout
```

### Phase 3: Main 関数の更新

`main` 関数で `--scheme` 処理後にフォーマットを実行:

```lean
-- 現状
IO.println (Ziku.compile prog)

-- 変更後
let code := Ziku.compile prog
let formatted ← formatSchemeCode code
IO.print formatted
```

## 検証方法

### フォーマット確認
```bash
# 簡単な式でフォーマットを確認
echo "let x = 1 in let y = 2 in x + y" | lake exe ziku --scheme /dev/stdin | head -20

# MAL step5 で確認（フォーマット済みで出力されるはず）
cat examples/mal/core.ziku examples/mal/step5_tco.ziku | lake exe ziku --scheme /dev/stdin | head -200
```

### テスト通過確認
```bash
docker compose run --rm ziku lake build
docker compose run --rm ziku lake test
```

### Golden テスト更新
- `emit-scheme` カテゴリのテストは golden ファイルの更新が必要
- フォーマット後の出力に合わせて `.golden` ファイルを再生成

## リスク管理

| リスク | 対策 |
|--------|------|
| Chez Scheme 依存 | Docker 環境・ローカル環境どちらも Chez Scheme 必須なので問題なし |
| パフォーマンス | 大きなファイルでは遅くなる可能性があるが、デバッグの利便性を優先 |
| コメント消失 | `pretty-print` はコメントを保持しないが、生成コードにコメントは少ない |
| Golden テスト失敗 | フォーマット追加後に golden ファイルを再生成 |
