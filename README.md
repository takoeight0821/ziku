# Ziku

[![CI](https://github.com/takoeight0821/ziku/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/takoeight0821/ziku/actions/workflows/lean_action_ci.yml)

A functional programming language exploring the duality between data and codata.

## Features

- **Pattern matching** for data types
- **Copattern matching** for codata types using `#` (self-reference)
- **First-class control** with `label`/`goto`
- **Hindley-Milner type inference** with let-polymorphism
- **Scheme backend** for compilation to Chez Scheme

## Quick Start

```bash
lake build         # Build
lake exe ziku      # Run REPL
lake test          # Run tests
```

## Examples

```ziku
// Arithmetic and let bindings
let x = 10 in x + 1

// Functions
let double = \x => x * 2 in double 5

// Recursion
let rec factorial = \n =>
  if n == 0 then 1
  else n * factorial (n - 1)
in factorial 5

// Codata: define by behavior, not construction
// #.x => 10 means "when .x is accessed, return 10"
let point = { #.x => 10, #.y => 20 } in
point.x + point.y

// Callable codata (functions are codata!)
// #(x) => ... means "when called with x, return ..."
let square = { #(x) => x * x } in
square(5)

// Early return with label/goto
label done {
  if condition then goto(result, done)
  else continue
}
```

## Documentation

- [Getting Started](docs/getting-started.md) - Installation and first steps
- [Tutorial](docs/tutorial.md) - Learn Ziku step by step
- [Reference](docs/reference.md) - Complete language reference
- [Internals](INTERNALS.md) - Implementation details
- [Development Workflow](docs/cdd-workflow.md) - Our GitHub-First development process

## For Developers

### Dependency Management

このプロジェクトは、依存関係の自動更新にRenovateを使用しています。

**Renovateのセットアップ（メンテナー向け）:**

1. **GitHub Appを作成**

   GitHub Settings → Developer settings → GitHub Apps → **New GitHub App**

   必要な設定：
   - **GitHub App name**: `renovate-ziku`（または任意の名前）
   - **Homepage URL**: `https://github.com/takoeight0821/ziku`
   - **Webhook**: "Active" のチェックを**外す**

   **Repository permissions**（以下を全て設定）:
   - Checks: Read and write
   - Contents: Read and write
   - Commit statuses: Read and write
   - Issues: Read and write
   - Pull requests: Read and write
   - Workflows: Read and write
   - Metadata: Read only（自動設定）

   作成後：
   - **App ID**をメモ（後で使用）
   - **Generate a private key**をクリックして `.pem` ファイルをダウンロード

2. **Appをリポジトリにインストール**

   作成したGitHub Appのページから：
   - **Install App** → **Only select repositories** → `takoeight0821/ziku` を選択
   - インストール後のURLから **Installation ID** を取得
     - 例: `https://github.com/settings/installations/12345678` の `12345678` 部分

3. **GitHub Actionsにシークレットを追加**

   Repository Settings → Secrets and variables → Actions → **New repository secret**:
   - `RENOVATE_APP_ID`: 手順1でメモしたApp ID
   - `RENOVATE_APP_PRIVATE_KEY`: ダウンロードした `.pem` ファイルの内容全体

4. **動作確認**

   Actions → Renovate → **Run workflow** で手動実行

**自動更新される依存関係:**
- GitHub Actions（週次、月曜 9:00 UTC）
- Docker base images
- Git submodules
- Lean toolchain
- Lake dependencies
- elanバージョン

詳細は[CLAUDE.md](CLAUDE.md)を参照してください。

## Background

Ziku is inspired by ["Grokking the Sequent Calculus" (ICFP 2024)](https://dl.acm.org/doi/10.1145/3674639), implementing a λμμ̃-calculus based intermediate representation that makes the duality between data and codata explicit.

## License

See [LICENSE](LICENSE) file.
