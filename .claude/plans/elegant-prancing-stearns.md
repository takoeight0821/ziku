# Ziku コンパイラ正当性証明の追加計画

**作成日**: 2026-01-22

## 概要

Zikuコンパイラに形式的証明を追加する。`docs/research/compiler-correctness-proofs.md`の調査結果に基づき、段階的なアプローチを採用する。

### 二重実装アーキテクチャ

Zikuは将来的に以下の2つの実装をサポートする:

1. **証明された実装 (Verified Implementation)**
   - `Ziku/Proofs/` 配下に帰納的関係として定義
   - Leanの型チェッカーによる形式的検証が可能
   - 仕様としての役割を果たす

2. **実用言語としての実装 (Practical Implementation)**
   - 現在の `Ziku/` 配下の実装（`partial def` を含む）
   - 実行性能と開発の柔軟性を優先
   - 証明された仕様に従うべき参照実装

**関係性**:
- 証明された実装は仕様（specification）
- 実用言語実装は参照実装（reference implementation）
- 将来的に「実用言語実装が証明された仕様を満たす」ことをテスト等で検証可能
- 既存コードは変更せず、証明は別モジュールに配置

## 現状分析

### 既存のインフラ
- `Ziku/Soundness.lean`: 基本的な型安全性の補題（リテラルの評価可能性など）
- `Ziku/Proofs/Eval.lean`: 空のプレースホルダー
- `Ziku/Proofs/Soundness.lean`: `lookup_some_mem`補題のみ

### 課題: `partial def` 関数
コードベース全体に59個の`partial def`関数があり、形式的証明を妨げている:
- 置換関数 (`substVar`, `substCovar`) - 6関数
- 評価関数 (`stateStep`, `evalWithFuel`) - IR/Eval.lean
- 翻訳関数 (`translateExpr`) - Translate.lean

**解決策**: 関係型（inductive relation）として定義し直す

---

## 実装計画

### Phase 1: IR操作的意味論の形式化 (基盤)

#### 1.1 Small-step意味論の定義
**ファイル**: `Ziku/Proofs/IR/Semantics.lean` (新規作成)
**対応する実装**: `Ziku/IR/Eval.lean` の `stateStep : State → EvalResult State`

```lean
-- 簡約規則を帰納的関係として定義
-- 実装の stateStep 関数（IR/Eval.lean:135-250）の各 match 分岐を形式化
inductive Step : Statement → Statement → Prop where
  -- μ-reduction: ⟨μα.s | c⟩ ⊲ s[c/α]
  -- 対応: IR/Eval.lean:143 の cut (mu ...) c のケース
  | muRed : ...
  -- μ̃-reduction: ⟨v | μ̃x.s⟩ ⊲ s[v/x]
  -- 対応: IR/Eval.lean:150 の cut v (muTilde ...) のケース
  | muTildeRed : ...
  -- 二項演算の評価
  -- 対応: IR/Eval.lean:165 の binOp のケース
  | binOpRed : ...
  -- 条件分岐
  -- 対応: IR/Eval.lean:178 の ifz のケース
  | ifzTrue : ...
  | ifzFalse : ...
```

#### 1.2 値の定義
**ファイル**: `Ziku/Proofs/IR/Values.lean` (新規作成)
**対応する実装**: `Ziku/IR/Eval.lean` の `Producer.isTerminal`, `Producer.isSimpleValue`

```lean
-- 値（終端producer）の帰納的定義
-- 実装の isTerminal (IR/Eval.lean:67-75) と isSimpleValue (IR/Eval.lean:77-87) を形式化
inductive IsValue : Producer → Prop where
  | lit : ∀ pos l, IsValue (.lit pos l)         -- isTerminal で true を返す
  | cocase : ∀ pos branches, IsValue (.cocase pos branches)  -- isTerminal で true
  | record : ...                                 -- isSimpleValue で true
  | dataCon : ...                               -- isSimpleValue で引数が全て値なら true
```

#### 1.3 多段階簡約
**ファイル**: `Ziku/Proofs/IR/Evaluation.lean` (新規作成)
**対応する実装**: `Ziku/IR/Eval.lean` の `evalWithFuel : Nat → State → EvalResult Lit`

```lean
-- Stepの反射推移閉包
-- 実装の evalWithFuel (IR/Eval.lean:256-262) のループを形式化
inductive Steps : Statement → Statement → Prop where
  | refl : ∀ s, Steps s s
  | step : ∀ s1 s2 s3, Step s1 s2 → Steps s2 s3 → Steps s1 s3
```

---

### Phase 2: 置換補題

#### 2.1 置換の関係型定義
**ファイル**: `Ziku/Proofs/IR/Substitution.lean` (新規作成)
**対応する実装**: `Ziku/IR/Eval.lean` の以下の6つの`partial def`関数:
- `Producer.substVar` (IR/Eval.lean:19-30)
- `Consumer.substVar` (IR/Eval.lean:32-40)
- `Statement.substVar` (IR/Eval.lean:42-50)
- `Producer.substCovar` (IR/Eval.lean:52-60)
- `Consumer.substCovar` (IR/Eval.lean:62-70)
- `Statement.substCovar` (IR/Eval.lean:72-80)

`partial`な置換関数の代わりに、関係型として定義:

```lean
-- 変数置換を関係として定義
-- Producer.substVar (IR/Eval.lean:19-30) の各ケースを帰納的に定義
inductive SubstVar : Ident → Producer → Producer → Producer → Prop where
  | var_eq : ∀ x p pos, SubstVar x p (.var pos x) p           -- 同じ変数なら置き換え
  | var_neq : ∀ x y p pos, x ≠ y → SubstVar x p (.var pos y) (.var pos y)  -- 異なる変数はそのまま
  | lit : ∀ x p pos l, SubstVar x p (.lit pos l) (.lit pos l)  -- リテラルは変化なし
  | mu : ∀ x p pos α s s',
      SubstVarStmt x p s s' →
      SubstVar x p (.mu pos α s) (.mu pos α s')  -- μ内部に再帰的に適用
  -- ... 他のケース（cocase, record, fix, dataCon）

-- 同様に SubstCovar も定義（covariable用の置換）
inductive SubstCovar : Ident → Consumer → Producer → Producer → Prop where
  ...
```

#### 2.2 置換の性質
証明すべき定理:
- 置換の可換性（変数が異なる場合）
- 型保存（置換が型を保存する）
- 置換と簡約の可換性（`Step`との関係）

---

### Phase 3: 翻訳正当性

#### 3.1 Surface言語の意味論
**ファイル**: `Ziku/Proofs/Surface/Semantics.lean` (新規作成)
**対応する実装**: `Ziku/Surface/Syntax.lean` の `Expr` 型定義

Surface言語のbig-step意味論を定義。実装にはSurface言語の評価器がないため、
新規に帰納的関係として定義する。

```lean
-- Surface/Syntax.lean の Expr 型に対する評価関係
inductive SurfaceEval : Expr → Value → Prop where
  | lit : ∀ pos l, SurfaceEval (.lit pos l) (.lit l)
  | binOp : ∀ pos op e1 e2 v1 v2 result,
      SurfaceEval e1 v1 → SurfaceEval e2 v2 →
      EvalOp op v1 v2 = some result →
      SurfaceEval (.binOp pos op e1 e2) result
  | lam : ...  -- クロージャとして評価
  | app : ...  -- 関数適用
```

#### 3.2 翻訳の関係型定義
**ファイル**: `Ziku/Proofs/Translate/Relation.lean` (新規作成)
**対応する実装**: `Ziku/Translate.lean` の以下の関数:
- `translateExpr` (Translate.lean:45-150) - メインの翻訳関数
- `translateStmt` (Translate.lean:152-180) - Statement翻訳
- `compileCases` (Translate.lean:182-250) - パターンマッチのコンパイル

```lean
-- translateExpr の各ケースを帰納的に定義
-- CLAUDE.md の翻訳規則に対応:
-- ⟦x⟧ = x, ⟦⌜n⌝⟧ = ⌜n⌝, ⟦λx.t⟧ = cocase {ap(x; α) ⇒ ⟨⟦t⟧ | α⟩}, etc.
inductive Translates : Surface.Expr → IR.Producer → Prop where
  | lit : ∀ pos l, Translates (.lit pos l) (.lit pos l)    -- ⟦⌜n⌝⟧ = ⌜n⌝
  | var : ∀ pos x, Translates (.var pos x) (.var pos x)    -- ⟦x⟧ = x
  | lam : ∀ pos x body irBody α,                           -- ⟦λx.t⟧ = cocase {...}
      Fresh α →
      Translates body irBody →
      Translates (.lam pos x false body)
                 (.cocase pos [("ap", [x, α], .cut pos irBody (.covar pos α))])
  | binOp : ∀ pos op e1 e2 p1 p2 α,                        -- ⟦t₁ ⊙ t₂⟧ = μα.⊙(...)
      Fresh α →
      Translates e1 p1 → Translates e2 p2 →
      Translates (.binOp pos op e1 e2)
                 (.mu pos α (.binOp pos op p1 p2 (.covar pos α)))
  -- ... 他の構文要素
```

#### 3.3 翻訳正当性定理
**ファイル**: `Ziku/Proofs/Translate/Correctness.lean` (新規作成)
**対応する実装**: `Ziku/Translate.lean` 全体の正当性

```lean
-- Surface評価結果 ↔ IR評価結果
-- CompCert スタイルのシミュレーション図による証明
theorem translation_correct :
  ∀ e v p, SurfaceEval e v → Translates e p →
    ∃ v', Evaluates (cut p halt) v' ∧ TranslatesValue v v'
```

---

### Phase 4: 型安全性

#### 4.1 IR型システムの形式化
**ファイル**: `Ziku/Proofs/Typing/System.lean` (新規作成)
**対応する実装**:
- `Ziku/Type.lean` - 型の定義 (`Ty`, `Scheme`, `Subst`)
- `Ziku/Infer.lean` - 型推論 (`genConstraints`, `solveUnify`, `infer`)
- `Ziku/Soundness.lean` - 既存の簡易版`HasType`（拡張の基盤）

```lean
-- Type.lean の Ty 型を使用
-- Infer.lean の型推論結果を検証する型判断規則

-- Producer の型付け（IR用に拡張）
inductive ProducerHasType : TyEnv → LabelEnv → Producer → Ty → Prop where
  | var : ∀ Γ L pos x τ,
      Γ.lookup x = some τ →
      ProducerHasType Γ L (.var pos x) τ
  | lit_int : ∀ Γ L pos n,
      ProducerHasType Γ L (.lit pos (.int n)) (.con pos "Int")
  | mu : ∀ Γ L pos α s τ,
      StatementOk (L.extend α τ) Γ s →
      ProducerHasType Γ L (.mu pos α s) τ
  -- ... cocase, record, fix, dataCon

-- Consumer の型付け
inductive ConsumerHasType : TyEnv → LabelEnv → Consumer → Ty → Prop where
  | covar : ∀ Γ L pos α τ, L.lookup α = some τ → ConsumerHasType Γ L (.covar pos α) τ
  | muTilde : ∀ Γ L pos x s τ,
      StatementOk L (Γ.extend x τ) s →
      ConsumerHasType Γ L (.muTilde pos x s) τ
  -- ... case, destructor

-- Statement の well-formedness
inductive StatementOk : LabelEnv → TyEnv → Statement → Prop where
  | cut : ∀ L Γ pos p c τ,
      ProducerHasType Γ L p τ →
      ConsumerHasType Γ L c τ →
      StatementOk L Γ (.cut pos p c)
  -- ... binOp, ifz, call, builtin
```

#### 4.2 Type Preservation
**ファイル**: `Ziku/Proofs/Typing/Preservation.lean` (新規作成)
**依存**: Phase 1の`Step`関係、Phase 2の置換補題、Phase 4.1の型システム

```lean
-- 簡約が型を保存することを証明
-- 核心: μ-reduction と μ̃-reduction で置換が型を保存すること
theorem preservation :
  ∀ s s' L Γ, StatementOk L Γ s → Step s s' → StatementOk L Γ s'
```

#### 4.3 Progress
**ファイル**: `Ziku/Proofs/Typing/Progress.lean` (新規作成)
**依存**: Phase 1の`IsValue`定義、Phase 4.1の型システム

```lean
-- 型付き閉じた項は値か簡約可能
-- IR/Eval.lean の stateStep が停止しないケースがないことを保証
theorem progress :
  ∀ s τ, HasType [] s τ → IsTerminal s ∨ (∃ s', Step s s')
```

---

## 実装コードと証明ファイルの対応関係

以下の表は、**実用言語実装**（既存コード）と**証明された実装**（新規作成）の対応を示す。
証明された実装は仕様として機能し、実用言語実装の「あるべき動作」を形式的に定義する。

```
実用言語実装 (Ziku/)           証明された実装 (Ziku/Proofs/)
─────────────────────────     ──────────────────────────────
partial def stateStep    ←─→   inductive Step (仕様として定義)
partial def substVar     ←─→   inductive SubstVar (仕様として定義)
partial def translateExpr ←─→  inductive Translates (仕様として定義)
```

### IR関連の証明

| 新規証明ファイル | 対応する実装ファイル | 形式化対象 |
|-----------------|---------------------|-----------|
| `Ziku/Proofs/IR/Semantics.lean` | `Ziku/IR/Eval.lean` | `stateStep`関数の簡約ルールを帰納的関係`Step`として形式化。実装の`stateStep`は`partial def`で定義されているが、証明用に同等のルールを`inductive`で再定義 |
| `Ziku/Proofs/IR/Values.lean` | `Ziku/IR/Eval.lean` | `Producer.isTerminal`, `Producer.isSimpleValue`関数を`IsValue`述語として形式化 |
| `Ziku/Proofs/IR/Evaluation.lean` | `Ziku/IR/Eval.lean` | `evalWithFuel`関数の多段階評価を`Steps`関係として形式化 |
| `Ziku/Proofs/IR/Substitution.lean` | `Ziku/IR/Eval.lean` | `Producer.substVar`, `Consumer.substVar`, `Statement.substVar`, `Producer.substCovar`, `Consumer.substCovar`, `Statement.substCovar`（6つの`partial def`関数）を関係型`SubstVar`, `SubstCovar`として形式化 |

### Surface言語関連の証明

| 新規証明ファイル | 対応する実装ファイル | 形式化対象 |
|-----------------|---------------------|-----------|
| `Ziku/Proofs/Surface/Semantics.lean` | `Ziku/Surface/Syntax.lean` | Surface.Expr型のbig-step意味論を帰納的関係として新規定義（実装には評価器がないため） |

### 翻訳関連の証明

| 新規証明ファイル | 対応する実装ファイル | 形式化対象 |
|-----------------|---------------------|-----------|
| `Ziku/Proofs/Translate/Relation.lean` | `Ziku/Translate.lean` | `translateExpr`, `translateStmt`関数（`partial def`）を関係型`Translates`として形式化。CLAUDE.mdの翻訳規則（⟦x⟧, ⟦⌜n⌝⟧, etc.）を帰納的定義で表現 |
| `Ziku/Proofs/Translate/Correctness.lean` | `Ziku/Translate.lean` | 翻訳が意味を保存することの証明。Surface意味論とIR意味論の間のシミュレーション関係を証明 |

### 型システム関連の証明

| 新規証明ファイル | 対応する実装ファイル | 形式化対象 |
|-----------------|---------------------|-----------|
| `Ziku/Proofs/Typing/System.lean` | `Ziku/Infer.lean`, `Ziku/Type.lean` | `genConstraints`, `solveUnify`の型推論結果を検証する型判断規則`HasType`を定義。既存の`Ziku/Soundness.lean`の`HasType`を拡張してIR全体をカバー |
| `Ziku/Proofs/Typing/Preservation.lean` | `Ziku/IR/Eval.lean`, `Ziku/Infer.lean` | `Step`関係による簡約が型を保存することを証明 |
| `Ziku/Proofs/Typing/Progress.lean` | `Ziku/IR/Eval.lean` | 型付き項は必ず値か簡約可能であることを証明 |

---

## ファイル構造

```
Ziku/Proofs/
├── IR/
│   ├── Semantics.lean      # ← Ziku/IR/Eval.lean の stateStep を形式化
│   ├── Values.lean         # ← Ziku/IR/Eval.lean の isTerminal/isSimpleValue を形式化
│   ├── Evaluation.lean     # ← Ziku/IR/Eval.lean の evalWithFuel を形式化
│   └── Substitution.lean   # ← Ziku/IR/Eval.lean の substVar/substCovar (6関数) を形式化
├── Surface/
│   └── Semantics.lean      # ← Ziku/Surface/Syntax.lean の Expr 型に意味論を定義
├── Translate/
│   ├── Relation.lean       # ← Ziku/Translate.lean の translateExpr を形式化
│   └── Correctness.lean    # ← Ziku/Translate.lean の正当性証明
├── Typing/
│   ├── System.lean         # ← Ziku/Infer.lean, Ziku/Type.lean の型システムを形式化
│   ├── Preservation.lean   # ← 型保存定理
│   └── Progress.lean       # ← 進行定理
├── Eval.lean               # 既存（拡張）
└── Soundness.lean          # 既存（拡張）
```

---

## 推奨実装順序

### MVP (最小実行可能証明) - 推奨
1. **Phase 1**: IR意味論の形式化
   - `Proofs/IR/Semantics.lean`
   - `Proofs/IR/Values.lean`
   - `Proofs/IR/Evaluation.lean`

2. **Phase 2.1**: 置換の関係型定義
   - `Proofs/IR/Substitution.lean`

これにより:
- IR意味論がLeanで形式化される
- 将来の証明の基盤ができる
- `partial`問題を回避しつつ形式的推論が可能になる

### 次のステップ
Phase 3（翻訳正当性）を追加し、コンパイラ正当性の核心部分を証明。

---

## 重要な参照ファイル

| ファイル | 目的 |
|---------|------|
| `Ziku/IR/Syntax.lean` | Producer, Consumer, Statement型定義 |
| `Ziku/IR/Eval.lean` | 現在の評価ルール（`partial`） |
| `Ziku/Translate.lean` | 翻訳ルールの参照 |
| `Ziku/Soundness.lean` | 既存証明パターン |

---

## 検証方法

1. **ビルド確認**: `docker run --rm ziku nix develop --command lake build`
2. **テスト実行**: `docker run --rm ziku nix develop --command lake test`
3. **証明検証**: Leanの型チェッカーが全ての定理を検証
4. **インクリメンタル検証**: 各Phaseの完了後にビルド・テスト実行

---

## 注意事項

### 二重実装の分離原則
- **証明された実装** (`Ziku/Proofs/`): 帰納的関係として定義、形式的検証可能
- **実用言語実装** (`Ziku/`): 既存の`partial def`を含む実装、変更しない
- 両者は完全に分離され、互いに依存しない

### 技術的制約
- `partial def`関数は直接証明に使用できないため、証明用に関係型として再定義
- 証明された実装は仕様として機能し、実用言語実装の正しさの基準となる
- 将来的には、実用言語実装が証明された仕様を満たすことをプロパティベーステスト等で検証可能

### 参考手法
- CompCert/CakeMLのシミュレーション図技法を参考
- `docs/research/compiler-correctness-proofs.md`の推奨事項に従う

### 拡張性
- 実用言語実装は証明の対象外として自由に拡張可能
- 証明された実装は言語コアの仕様として安定性を維持
- 新機能追加時: まず実用言語実装で実験 → 安定したら証明された実装に追加
