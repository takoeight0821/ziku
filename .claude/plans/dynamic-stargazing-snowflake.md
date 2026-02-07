# 型システム段階的改善計画

## Date: 2026-02-06

## Context

Ziku の型推論には2つの問題がある:

1. **`let` が generalize しない**: `let id = \x => x in (id 42, id true)` が型エラーになる。制約を全て収集してから一括解決する現在のアーキテクチャでは、`let` 境界での中間的な generalize ができない。
2. **レコード内の `forall` が機能しない**: `{ id : forall a. a -> a }` は Rank-2 型。`instantiateTy` が全ての `forall` を再帰的に剥がすため、フィールド単位の多相性が失われる。

将来的に bidirectional type checking を導入する前提で、段階的に改善する。

## Phase 1: Level-based let-generalization

### 方針

`genConstraints` のアーキテクチャを「全制約収集 → 一括解決」から「`let` 境界で中間解決 + generalize」に変更する。型変数にレベル（`let` ネスト深度）を付与し、解決後にレベルの高い変数を量化する。

これは将来の bidirectional type checking にも必要な変更（`let` 境界での型情報確定）であり、Phase 3 の基盤になる。

参考: [Efficient and Insightful Generalization](https://okmij.org/ftp/ML/generalization.html) (Kiselyov)

### 変更対象ファイル

**`Ziku/Infer.lean`** — 主な変更箇所

#### 1.1 `GenState` にレベル情報を追加 (line 88-97)

```lean
structure GenState where
  nextVar : Nat := 0
  constraints : List Constraint := []
  labelEnv : LabelEnv := []
  importTypes : ImportTypeMap := []
  currentLevel : Nat := 0                  -- NEW
  varLevels : List (Ident × Nat) := []     -- NEW: 型変数名 → 作成時レベル
  solvedSubst : Subst := []                -- NEW: 中間解決の累積代入
  deriving Inhabited
```

#### 1.2 `freshTyVar` にレベル記録を追加 (line 107-111)

新しい型変数に `currentLevel` を記録する。

#### 1.3 `enterLevel` / `exitLevel` ヘルパー追加

```lean
def enterLevel : GenM Unit :=
  modify fun s => { s with currentLevel := s.currentLevel + 1 }

def exitLevel : GenM Unit :=
  modify fun s => { s with currentLevel := s.currentLevel - 1 }
```

#### 1.4 `let_` ケースの変更 (line 595-612) — 核心部分

```lean
| .let_ pos x tyOpt e1 e2 => do
    enterLevel
    let t1 ← genConstraints env e1
    exitLevel

    let scheme ← match tyOpt with
      | some ty => do
        -- 注釈あり: 既存ロジック維持
        let instantiated ← instantiateTy ty
        addConstraint (.unify pos t1 instantiated)
        let s := tyToScheme ty
        pure (if s.vars.isEmpty then { vars := [], ty := t1 } else s)
      | none => do
        -- 注釈なし: ここで中間解決 + level-based generalize
        let st ← get
        let letLevel := st.currentLevel + 1  -- enterLevel で上げた値
        let allConstraints := st.constraints.reverse
        match solveConstraints allConstraints st.nextVar with
        | .error e => throw e
        | .ok solverState =>
          let fullSubst := composeSubst st.solvedSubst solverState.subst
          let resolvedTy := t1.applySubst fullSubst
          let envVars := (env.map (·.2)).flatMap Scheme.freeVars
          let freeInTy := resolvedTy.freeVars
          let generalizable := freeInTy.filter fun v =>
            !envVars.contains v &&
            match st.varLevels.find? (fun (n, _) => n == v) with
            | some (_, lvl) => lvl >= letLevel
            | none => false
          set { st with
            nextVar := solverState.nextVar
            constraints := []      -- 消費済み
            solvedSubst := fullSubst
          }
          pure { vars := generalizable.eraseDups, ty := resolvedTy }

    let env' := (x, scheme) :: env
    genConstraints env' e2
```

#### 1.5 `runInfer` の変更 (line 884+)

最終解決で `solvedSubst` と合成する:

```lean
let fullSubst := composeSubst finalGenState.solvedSubst solverState.subst
```

#### 1.6 `unifyAt` でのレベル伝播

変数の unification 時に、レベルの最小値を伝播する。`varLevels` を `GenState` ではなく `SolverState` にも持たせるか、`unifyAt` にレベル更新ロジックを追加する。

具体的には: `?a (level 2) = ?b (level 1)` の場合、`?a` のレベルを 1 に下げる。これにより `?a` が外側スコープに「脱出」したことを記録し、generalize 対象から外れる。

### テスト変更

**error/ → success/ に移動:**
- `forall_mono_let_reuse.ziku` — golden を `Int` に変更
- `forall-row-limitation.ziku` — golden を `Int` に変更

**新規追加:**
- `let_generalize_basic.ziku`: `let id = \x => x in { a = id 42, b = id true }` → `{ a : Int, b : Bool }`
- `let_generalize_nested.ziku`: `let id = \x => x in let a = id 42 in let b = id true in a` → `Int`
- `let_generalize_no_escape.ziku`: `let f = \x => let y = x in y in f 42` → `Int` (x は lambda-bound なので escape)

### リスク

- 中間解決により制約処理順序が変わる → 既存テスト全110件で回帰確認
- `composeSubst` の正確性 → 既に line 768 に実装あり。合成テストを追加
- `bottomProp` との相互作用 → 中間解決時にも `propagateBottomFixpoint` が走るため問題なし

---

## Phase 2: 多相レコードフィールド

### 方針

レコードフィールド内の `forall` を保存し、フィールドアクセス時に instantiate する。OCaml の多相レコードフィールドと同様のアプローチ。

参考: [OCaml Manual: Polymorphism](https://ocaml.org/manual/5.4/polymorphism.html)

### 変更対象ファイル

**`Ziku/Infer.lean`**

#### 2.1 `instantiateTy` の変更 (line 410-438)

レコードフィールド内の `forall` を剥がさないようにする:

```lean
| .record pos fields rowVar => do
    -- フィールド内の forall は保存（多相フィールド）
    -- 行変数のみ instantiate
    let rowVar' ← match rowVar with
      | some rv => do let rv' ← instantiateTy rv; pure (some rv')
      | none => pure none
    return .record pos fields rowVar'
```

#### 2.2 新しい制約型 `instantiateField` の追加 (line 63-85)

```lean
inductive Constraint where
  | unify (pos : SourcePos) (t1 : Ty) (t2 : Ty)
  | bottomProp (sources : List Ty) (target : Ty)
  | instantiateField (pos : SourcePos) (fieldTy : Ty) (resultTy : Ty)  -- NEW
```

#### 2.3 `.field` ケースの変更 (line 658-669)

```lean
| .field pos e field => do
    let recTy ← genConstraints env e
    let rawFieldTy ← freshTyVar
    let resultTy ← freshTyVar
    let rowVar ← freshTyVar
    addConstraint (.unify pos recTy (.record pos [(field, rawFieldTy)] (some rowVar)))
    addConstraint (.instantiateField pos rawFieldTy resultTy)
    addConstraint (.bottomProp [recTy] resultTy)
    return resultTy
```

#### 2.4 `solveConstraints` の変更 (line 842-863)

`unify` 制約を全て処理した後に `instantiateField` を処理:

```lean
-- unify 処理後
for c in constraints do
  match c with
  | .instantiateField pos rawField result =>
    let resolved := rawField.applySubst state.subst
    let (instantiated, newNextVar) := instantiateForallPure resolved state.nextVar
    state := { state with nextVar := newNextVar }
    state ← solveUnify pos instantiated (result.applySubst state.subst) state
    state := propagateBottomFixpoint bottomProps state
  | _ => pure ()
```

#### 2.5 `instantiateForallPure` ヘルパー追加

`GenM` を使わず純粋に `forall` を剥がす関数（solver 内で使用）:

```lean
def instantiateForallPure (ty : Ty) (nextVar : Nat) : Ty × Nat :=
  match ty with
  | .forall_ _ x inner =>
    let fresh := Ty.var synthesizedPos s!"_t{nextVar}"
    let body := inner.applySubst [(x, fresh)]
    instantiateForallPure body (nextVar + 1)
  | _ => (ty, nextVar)
```

#### 2.6 `unifyRecords` 内のフィールド unification 修正

共通フィールドの unification 時に、フィールド型に `forall` が含まれる場合は `instantiateForallPure` で剥がしてから unify する。

### テスト追加

- `record_poly_field_access.ziku`: `let r : { id : forall a. a -> a } = ... in r.id 42 + (if r.id true then 1 else 0)` → `Int`
- `record_poly_multi_field.ziku`: 複数の多相フィールドを持つレコード
- `record_poly_field_wrong_type.ziku` (error): `{ id = \x => x + 1 }` を `{ id : forall a. a -> a }` として使用 → 型エラー

### Phase 1 との関係

Phase 1 の let-generalize では `let r = { id = \x => x }` の `r` は `forall a. { id : a -> a }` に generalize される（レコード全体で a が共有）。Phase 2 の多相フィールドは型注釈 `{ id : forall a. a -> a }` を付けた場合にのみフィールド単位の多相性が得られる。注釈なしでフィールド単位の多相性が欲しい場合は Phase 3 が必要。

---

## Phase 3 (将来): Bidirectional Type Checking

### 設計方針

`genConstraints` に省略可能な `expected : Option Ty` パラメータを追加し、checking mode と synthesis mode を統一する。

```lean
partial def genConstraints (env : TyEnv) (expr : Expr) (expected : Option Ty := none) : GenM Ty
```

### 主要な checking mode ルール

- **Lambda**: `expected = some (arrow A B)` → パラメータを `A` に束縛、body を `B` に対して check
- **Application**: function type が判明していれば引数を check
- **Record construction**: `expected = some (record fields)` → 各フィールドを対応する型（`forall` 含む）に対して check
- **Let body**: `let` 束縛の型が判明していれば body に伝播

### Phase 1, 2 との関係

- Phase 1 の「`let` 境界での中間解決」が bidirectional の前提条件
- Phase 2 の「レコード内 `forall` 保存」が record checking mode の前提条件
- 既存の checking mode 箇所（演算子, builtin, 注釈, パターン, if 条件）が Phase 3 のパターンと一致

参考: [Complete and Easy Bidirectional Typechecking](https://arxiv.org/abs/1306.6032) (Dunfield & Krishnaswami, ICFP 2013)

---

## 実装順序

### Phase 1 の実装順序
1. `GenState` に `currentLevel`, `varLevels`, `solvedSubst` 追加
2. `freshTyVar` にレベル記録追加
3. `enterLevel`/`exitLevel` 追加
4. `let_` ケースを中間解決 + level-based generalize に変更
5. `runInfer` で `solvedSubst` との合成
6. テスト移動 (`forall_mono_let_reuse`, `forall-row-limitation`)
7. 新規テスト追加
8. 全テスト実行で回帰確認: `docker run --rm ziku`

### Phase 2 の実装順序
1. `instantiateTy` のレコードフィールド処理変更
2. `Constraint` に `instantiateField` 追加
3. `instantiateForallPure` ヘルパー追加
4. `.field` の制約生成変更
5. `solveConstraints` に `instantiateField` 処理追加
6. `unifyRecords` のフィールド unification 修正
7. テスト追加
8. 全テスト実行: `docker run --rm ziku`

## 検証

各フェーズ完了後:
```bash
docker run --rm ziku lake build     # ビルド確認
docker run --rm ziku                # 全テスト実行
```
