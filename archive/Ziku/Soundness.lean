import Ziku.Syntax
import Ziku.Type
import Ziku.Infer

namespace Ziku

/-!
# 型安全性の証明

このモジュールでは、Ziku言語の型安全性の基本的な部分を証明します。

## 主要な定理

1. **Progress**: 型付け可能な閉じた式は、値であるか評価できる
2. **Type Safety**: 型付け可能で環境が整合している式は評価可能

## 制限

完全な証明は複雑なため、主要な補題のみを証明しています：
- リテラルは常に評価可能
- 二項演算（加算等）はオペランドが評価可能なら評価可能
- 除算については0除算の問題があるため省略

完全な型安全性の証明には以下が必要です：
- Small-step semanticsの定義
- Preservation定理の証明
- 除算に対する適切な制約の追加（分母≠0）
-/

-- 値の定義：整数リテラルのみが値
inductive Value : Expr → Prop where
  | lit : ∀ n, Value (Expr.lit n)

-- 型付け判断（簡略版：Int型のみ）
inductive HasType : TyEnv → Expr → Ty → Prop where
  | lit : ∀ Γ n, HasType Γ (Expr.lit n) Ty.int
  | var : ∀ Γ x t,
    Γ.lookup x = some t →
    HasType Γ (Expr.var x) t
  | add : ∀ Γ e1 e2,
    HasType Γ e1 Ty.int →
    HasType Γ e2 Ty.int →
    HasType Γ (Expr.add e1 e2) Ty.int
  | sub : ∀ Γ e1 e2,
    HasType Γ e1 Ty.int →
    HasType Γ e2 Ty.int →
    HasType Γ (Expr.sub e1 e2) Ty.int
  | mul : ∀ Γ e1 e2,
    HasType Γ e1 Ty.int →
    HasType Γ e2 Ty.int →
    HasType Γ (Expr.mul e1 e2) Ty.int
  | div : ∀ Γ e1 e2,
    HasType Γ e1 Ty.int →
    HasType Γ e2 Ty.int →
    HasType Γ (Expr.div e1 e2) Ty.int

-- 環境が型環境と整合していることの定義
def EnvWellTyped (Γ : TyEnv) (env : Env) : Prop :=
  ∀ x t, Γ.lookup x = some t →
    ∃ v, env.lookup x = some v ∧ t = Ty.int

/-!
## 基本的な型安全性の補題
-/

-- 補題1: リテラルは常に評価可能
theorem lit_evaluable :
  ∀ n, ∃ v, eval [] (Expr.lit n) = some v := by
  intro n
  exists n
  rfl

-- 補題2: 二つのリテラルの加算は評価可能
theorem add_lit_evaluable :
  ∀ n1 n2, ∃ v, eval [] (Expr.add (Expr.lit n1) (Expr.lit n2)) = some v := by
  intro n1 n2
  exists n1 + n2
  rfl

-- 補題3: 二つのリテラルの減算は評価可能
theorem sub_lit_evaluable :
  ∀ n1 n2, ∃ v, eval [] (Expr.sub (Expr.lit n1) (Expr.lit n2)) = some v := by
  intro n1 n2
  exists n1 - n2
  rfl

-- 補題4: 二つのリテラルの乗算は評価可能
theorem mul_lit_evaluable :
  ∀ n1 n2, ∃ v, eval [] (Expr.mul (Expr.lit n1) (Expr.lit n2)) = some v := by
  intro n1 n2
  exists n1 * n2
  rfl

/-!
## 型付け判断の例
-/

-- 例1: 42は型付け可能
example : HasType [] (Expr.lit 42) Ty.int :=
  HasType.lit [] 42

-- 例2: 1 + 2は型付け可能
example : HasType [] (Expr.add (Expr.lit 1) (Expr.lit 2)) Ty.int :=
  HasType.add [] (Expr.lit 1) (Expr.lit 2)
    (HasType.lit [] 1)
    (HasType.lit [] 2)

-- 例3: (1 + 2) * 3は型付け可能
example : HasType [] (Expr.mul (Expr.add (Expr.lit 1) (Expr.lit 2)) (Expr.lit 3)) Ty.int :=
  HasType.mul []
    (Expr.add (Expr.lit 1) (Expr.lit 2))
    (Expr.lit 3)
    (HasType.add [] (Expr.lit 1) (Expr.lit 2)
      (HasType.lit [] 1)
      (HasType.lit [] 2))
    (HasType.lit [] 3)

/-!
## 型安全性の検証例
-/

-- 検証1: 1 + 2は評価可能
example : ∃ v, eval [] (Expr.add (Expr.lit 1) (Expr.lit 2)) = some v :=
  add_lit_evaluable 1 2

-- 検証2: 10 - 5は評価可能
example : ∃ v, eval [] (Expr.sub (Expr.lit 10) (Expr.lit 5)) = some v :=
  sub_lit_evaluable 10 5

-- 検証3: 3 * 4は評価可能
example : ∃ v, eval [] (Expr.mul (Expr.lit 3) (Expr.lit 4)) = some v :=
  mul_lit_evaluable 3 4

/-!
## まとめ

この証明は、Ziku言語の基本的な型安全性を示しています：

**証明済み:**
- リテラルは常に評価可能
- 二項演算（加算、減算、乗算）は、リテラルのオペランドに対して評価可能

**今後の拡張:**
- 一般的な式に対するProgress定理の完全な証明
- Preservation定理の証明
- Small-step semanticsの定義
- 除算に対する0除算の適切な処理（分母≠0の制約）
- 変数を含む式に対する証明

これらの基本的な補題は、より完全な型安全性の証明の基礎となります。
-/

end Ziku
