# Codata 構文修正 + パイプライン修正

## Date: 2026-02-07

## Context

PR #70 (型システム改善) の後、codata について2つの問題が明らかになった:

1. **構文設計の誤り**: 現在 `Pat... # Copattern => Body` のように `#` の前にパターンが来る。正しくは `# Copattern => Body` のように `#` が常に先頭に来て、パターンは copattern の一部（アプリケーションアクセサ）として統合されるべき。
2. **パイプライン不備**: eval/translate モードで `elaborateAll` が実行されないため、codata ブロックが IR 変換でエラーになる。

### 構文変更の例

```
-- 現在 (誤)
{ x #.value => x }
{ x #.fst => x, y #.snd => y }
{ Pair(a, b) #.fst => a, Pair(a, b) #.snd => b }

-- 修正後 (正)
{ # x .value => x }
{ # x .fst => x, # y .snd => y }
{ # Pair(a, b) .fst => a, # Pair(a, b) .snd => b }
```

既に `#` から始まる構文は変更不要:
```
{ #.x => 10, #.y => 20 }       -- そのまま
{ #(x) => x + 1 }              -- そのまま
{ # x => x + 1 }               -- そのまま
```

## 変更計画

### Step 1: `Accessor` の型変更 (`Ziku/Syntax.lean:210-215`)

`Accessor.apply` の引数を `Ident` から `Pat` に変更:

```lean
inductive Accessor where
  | field : Ident → Accessor       -- .field (変更なし)
  | apply : Pat → Accessor         -- (pat) or pat (Ident → Pat)
```

`toString`, `Repr`, `BEq` のインスタンスもあれば更新。

### Step 2: パーサー修正 (`Ziku/Parser.lean`)

#### 2a: `parseAccessor` の変更 (line 397-414)

`apply` がパターンを受け取るように変更:

- `.field` ケース: 変更なし
- `(pat)` ケース (line 404-408): `expectIdent` → `parsePattern` に変更
- bare ident ケース (line 410-412): `Ident` → `Pat.var` にラップ。さらに、ident の後に `(` が続く場合はコンストラクタパターン `Con(args)` としてパース

#### 2b: `parseCodataClauseBody` の変更 (line 1005-1038)

パターン-before-`#` のループ (line 1009-1017) を**削除**。`#` が常に先頭であることを期待し、`#` を consume してから `parseCopattern` を呼ぶ。

現在:
```
patterns = parse patterns until #
consume #
copattern = parseCopattern
```

修正後:
```
consume #
copattern = parseCopattern    -- パターンは copattern 内の apply アクセサとして統合
```

#### 2c: `parseBraceExpr` の `ident` ケース見直し (line 933-953)

現在、先頭が `ident` で次が `=` でなければ codata と判定している。修正後、codata は常に `#` から始まるので、この分岐のロジックを調整。ident 始まりはレコード `{ x = ... }` か、エラー。

### Step 3: エラボレーション修正 (`Ziku/Elaborate.lean`)

`Accessor.apply Pat` への対応:

- `Pat.var x` の場合: 今と同じ。`\x => ...` を生成
- 複合パターン (例: `Pat.con "Pair" [...]`) の場合: `\fresh => match fresh { pat => ... }` を生成。現在の `elaborateWithPatternGuards` のロジックを流用

`elaborateWithPatternGuards` 関数自体は不要になる可能性が高い（パターンが accessor に統合されるため）。

### Step 4: パイプラインに `elaborateAll` を追加 (`Main.lean`)

#### 4a: `runOnInput` (line 67-97)

`Translate.translateToStatement expanded` の前に `elaborateAll expanded` を挿入:

```lean
| .ok expanded =>
  match elaborateAll expanded with
  | .error err =>
    IO.eprintln s!"Elaboration error: {err}"
    IO.Process.exit 1
  | .ok elaborated =>
    match Translate.translateToStatement elaborated with
    ...
```

#### 4b: REPL (line 117-136)

`Translate.translateToStatement expr` の前に `elaborateAll expr` を挿入。

### Step 5: テスト更新

#### 構文変更に伴うテスト修正

| ファイル | 現在 | 修正後 |
|---------|------|--------|
| `infer/success/codata_pattern_simple.ziku` | `{ x #.value => x }` | `{ # x .value => x }` |
| `infer/success/codata_pattern_multi_field.ziku` | `{ x #.fst => x, y #.snd => y }` | `{ # x .fst => x, # y .snd => y }` |
| `infer/success/codata_pattern_constructor.ziku` | `{ Pair(a, b) #.fst => a, Pair(a, b) #.snd => b }` | `{ # Pair(a, b) .fst => a, # Pair(a, b) .snd => b }` |

#### パーサーテスト

`parser/success/` 内の codata テストを確認し、`#` が先頭に来る形に更新。golden ファイルも再生成。

#### パイプライン修正のテスト

新規: codata ブロックの `ir-eval` テスト（elaboration 経由で eval まで通ることを検証）

### Step 6: ドキュメント更新

`docs/tutorial.md` の codata セクション（Section 6）のコード例が `#.x => ...` 形式であることを確認。パターン構文の例があれば更新。

## 影響範囲

| ファイル | 変更種別 |
|---------|---------|
| `Ziku/Syntax.lean` | `Accessor.apply` の引数型変更 |
| `Ziku/Parser.lean` | `parseAccessor`, `parseCodataClauseBody`, `parseBraceExpr` |
| `Ziku/Elaborate.lean` | パターンアクセサの処理追加、`elaborateWithPatternGuards` のリファクタ |
| `Ziku/Infer.lean` | 変更なし（elaborate 済み式を処理するため） |
| `Ziku/Translate.lean` | 変更なし（elaborate 済み式が来るため notImplemented は到達しない） |
| `Main.lean` | `elaborateAll` 呼び出し追加 |
| `tests/golden/infer/success/codata_pattern_*.ziku` | 構文更新 |
| `tests/golden/parser/success/codata*.ziku` | 必要に応じて構文更新 |
| `docs/tutorial.md` | パターン構文例の確認・更新 |

## 検証

1. `mise run docker:build-check` — ビルド成功
2. `mise run docker:test` — 全テストパス
3. codata パイプラインの手動テスト:
   ```
   mise run docker:run infer '{ # x .value => x }'
   mise run docker:run eval '{ # Pair(a, b) .fst => a, # Pair(a, b) .snd => b }'
   ```
