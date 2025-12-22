---
name: translate
description: Translate documents, comments, or code documentation to Japanese. Use when the user asks to "translate", "translate to Japanese", "Japanese translation", or wants to convert English documentation, README files, code comments, or any text content to Japanese.
---

# Translate to Japanese Skill

Translate documents, code comments, and documentation content to natural Japanese.

## When to Use

- User asks to translate a file or document to Japanese
- User wants Japanese translation of code comments
- User needs README or documentation translated to Japanese
- User asks for Japanese version of any text content

## Translation Guidelines

### General Principles

1. **Natural Japanese**: Produce natural-sounding Japanese, not word-for-word translation
2. **Technical Terms**: Keep widely-used technical terms in English (API, GitHub, HTTP, etc.)
3. **Code Identifiers**: Never translate variable names, function names, or code syntax
4. **Formatting**: Preserve markdown formatting, code blocks, and structure

### Technical Term Handling

| English      | Japanese                      | Notes                 |
| ------------ | ----------------------------- | --------------------- |
| function     | 関数                          | Standard translation  |
| variable     | 変数                          | Standard translation  |
| type         | 型                            | Standard translation  |
| class        | クラス                        | Katakana              |
| interface    | インターフェース              | Katakana              |
| module       | モジュール                    | Katakana              |
| parameter    | パラメータ/引数               | Context-dependent     |
| return value | 戻り値                        | Standard translation  |
| error        | エラー                        | Katakana              |
| exception    | 例外                          | Standard translation  |
| bug          | バグ                          | Katakana              |
| feature      | 機能                          | Standard translation  |
| repository   | リポジトリ                    | Katakana              |
| commit       | コミット                      | Katakana              |
| branch       | ブランチ                      | Katakana              |
| merge        | マージ                        | Katakana              |
| pull request | Pull request / プルリクエスト | Often kept in English |
| issue        | Issue / イシュー              | Often kept in English |

### Style Guidelines

- Use です/ます form for documentation
- Use である form for technical specifications
- Keep sentences concise and clear
- Add appropriate particles (は, が, を, に, etc.) correctly
- Use appropriate honorifics when translating user-facing text

## Workflow

### 1. Read the Source Content

Use the Read tool to get the content:

```
Read: <file-path>
```

Or receive content directly from the user.

### 2. Analyze Content Type

Determine what type of content you're translating:

- README / Documentation
- Code comments (inline or block)
- API documentation
- Error messages
- UI text
- Academic/technical paper

### 3. Translate

Translate the content following these rules:

**For Documentation:**

- Maintain the original structure (headings, lists, code blocks)
- Translate prose naturally
- Keep code examples unchanged
- Translate comments within code blocks if they exist

**For Code Comments:**

- Translate only the comment text
- Keep code unchanged
- Preserve comment style (`//`, `/* */`, `#`, etc.)

**For Mixed Content:**

- Clearly separate translated and original parts
- Use consistent terminology throughout

### 4. Output the Translation

Present the translation directly to the user in the terminal. Format options:

**For full documents:**

```markdown
## Japanese Translation

<translated content here>
```

**For code comments:**

```
// Original: <english comment>
// 翻訳: <japanese translation>
```

**For inline review:**
Show original and translation side by side or sequentially for review.

## Examples

### Documentation Translation

**Original:**

```markdown
## Installation

Install the package using npm:

\`\`\`bash
npm install my-package
\`\`\`

This will install all dependencies automatically.
```

**Translation:**

```markdown
## インストール

npmを使用してパッケージをインストールします:

\`\`\`bash
npm install my-package
\`\`\`

これにより、すべての依存関係が自動的にインストールされます。
```

### Code Comment Translation

**Original:**

```javascript
// Calculate the total price including tax
function calculateTotal(price, taxRate) {
  return price * (1 + taxRate);
}
```

**Translation:**

```javascript
// 税込みの合計金額を計算する
function calculateTotal(price, taxRate) {
  return price * (1 + taxRate);
}
```

### Error Message Translation

**Original:**

```
Error: File not found. Please check the path and try again.
```

**Translation:**

```
エラー: ファイルが見つかりません。パスを確認して再度お試しください。
```

## Tips

- For ambiguous terms, provide the original English in parentheses: `継承（inheritance）`
- When uncertain about context, ask the user for clarification
- For long documents, translate section by section and show progress
- Preserve all URLs, file paths, and code references unchanged
- Consider the target audience (developers, end users, etc.) when choosing formality level
