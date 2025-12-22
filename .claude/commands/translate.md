---
name: translate
description: Translate a document, code comments, or text content to Japanese
arguments:
  - name: target
    description: File path to translate, or paste text directly
    required: true
---

# Translate to Japanese: $ARGUMENTS.target

Translate the specified content to natural Japanese.

## Determine Input Type

First, identify what kind of input this is:
- **File path**: If `$ARGUMENTS.target` looks like a file path (contains `/` or `.`), read the file
- **Inline text**: Otherwise, treat it as text to translate directly

## For File Input

1. Use the Read tool to get the file content
2. Determine the file type:
   - `.md` - Markdown documentation
   - `.js`, `.ts`, `.py`, etc. - Code file (translate comments only)
   - `.txt` - Plain text
   - Other - Analyze and handle appropriately

## Translation Guidelines

Follow these rules when translating:

### Keep in English
- Code syntax and identifiers
- URLs and file paths
- Package names and commands
- Well-known acronyms (API, HTTP, JSON, etc.)

### Translate to Japanese
- Prose and documentation text
- Code comments
- Error messages and descriptions
- Section headings (while keeping code-like headings)

### Technical Terms
Use standard Japanese technical terminology:
- function = 関数
- variable = 変数
- type = 型
- parameter = パラメータ/引数
- return value = 戻り値
- class = クラス
- module = モジュール

### Style
- Use です/ます form for documentation
- Keep sentences concise and clear
- Preserve original formatting and structure

## Output

Display the translated content directly in the terminal.

For documentation files, show the full translated content.

For code files, show the code with translated comments.

Format the output clearly so the user can review and copy it.
