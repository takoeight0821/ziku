# Plan: パーサー可読性改善 - parseExternEntry

## 概要

`Ziku/Parser.lean` の `parseExternEntry` 関数（1178-1209行）の可読性を改善する。現在の深くネストしたmatch式をdo記法に書き換える。

## 現状の問題点

1. **深いネスト**: 最大7段階のmatch式
2. **冗長な変数名**: `s'`, `s''`, `s'''`, ..., `s''''''''`
3. **重複エラーハンドリング**: `| .error msg => .error msg` の繰り返し

## 改善方針

Parser型はMonadインスタンスを持つため、do記法が利用可能。以下のステップで改善:

### Step 1: ヘルパー関数の追加

`expectString` と `expectInt` を追加（既存の`expectIdent`パターンに準拠）

```lean
/-- Expect a string literal token. -/
def expectString : Parser String := fun s =>
  match s.peekToken? with
  | some (.string str) => .ok (str, s.advance)
  | some tok => .error s!"expected string literal but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected string literal but found EOF"

/-- Expect an integer literal token. -/
def expectInt : Parser Int := fun s =>
  match s.peekToken? with
  | some (.int n) => .ok (n, s.advance)
  | some tok => .error s!"expected integer but found {tok} at {s.currentPos.line}:{s.currentPos.col}"
  | none => .error "expected integer but found EOF"
```

### Step 2: parseExternEntryのリライト

do記法と既存コンビネータを活用:

```lean
partial def parseExternEntry : Parser ExternEntry := do
  let _ ← expect .at_
  let _ ← expect .lparen
  let backend ← expectString
  let _ ← expect .comma
  let symbol ← expectString
  let arity ← optional do
    let _ ← expect .comma
    let n ← expectInt
    pure n.toNat
  let _ ← expect .rparen
  return { backend, symbol, arity }
```

## 変更対象ファイル

- `Ziku/Parser.lean`
  - 新規: `expectString` 関数（85行付近、expectIdentの後に追加）
  - 新規: `expectInt` 関数（同上）
  - 変更: `parseExternEntry` 関数（1178-1209行）

## 検証方法

```bash
lake test
```

特に以下のテストが成功することを確認:
- `tests/golden/parser/success/extern.ziku`
- `tests/golden/infer/success/extern_typing.ziku`
- `tests/golden/scheme/success/extern_*.ziku`
