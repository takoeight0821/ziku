# コンパイラ正当性証明: 包括的調査レポート

**調査日**: 2026-01-22

## 概要

コンパイラ正当性（Compiler Correctness）は、コンパイラが言語仕様に従って正しく動作することを示すコンピュータサイエンスの分野である。主なアプローチとして、形式手法を用いたコンパイラ開発と、既存コンパイラに対する厳密なテストがある。

本レポートでは、コンパイラ正当性証明の主要な技術、代表的なプロジェクト、および証明手法について包括的に調査した結果をまとめる。

## 目次

1. [主要な検証アプローチ](#主要な検証アプローチ)
2. [代表的な検証済みコンパイラ](#代表的な検証済みコンパイラ)
3. [証明技術](#証明技術)
4. [意味論的基盤](#意味論的基盤)
5. [関連プロジェクト](#関連プロジェクト)
6. [Zikuへの適用可能性](#zikuへの適用可能性)
7. [参考文献](#参考文献)

---

## 主要な検証アプローチ

コンパイラの正当性を確立するための形式的検証には、主に2つのアプローチがある。

### 1. 検証済みコンパイル（Verified Compilation）

すべての入力プログラムに対してコンパイラの正当性を事前に証明するアプローチ。

**特徴:**
- コンパイラ全体を定理証明器で実装・検証
- ソース言語、中間言語、ターゲット言語すべてに形式的意味論を定義
- 各変換パスに対して意味保存を証明
- 証明は機械検証可能

**利点:**
- 一度証明すれば、すべての入力に対して正当性が保証される
- 信頼性が高い

**欠点:**
- 開発コストが非常に高い（CompCertは6人年以上）
- 既存コンパイラへの適用が困難
- 最適化の追加が難しい

### 2. 翻訳検証（Translation Validation）

個々のコンパイル実行に対して、生成されたコードが正しいことを事後的に検証するアプローチ。

**特徴:**
- コンパイラ自体の検証は不要
- 各コンパイル実行後に検証フェーズを追加
- 記号推論を用いて等価性を検証

**利点:**
- 既存コンパイラに適用可能
- コンパイラと独立に保守可能
- コンパイラが時々不正なコードを生成しても、そのコードが検証に失敗すれば検出可能

**欠点:**
- 毎回の検証にコストがかかる
- 検証器自体の正当性が問題になる

### 3. ハイブリッドアプローチ

CompCertでは、一部のパスで翻訳検証を使用している。各パスごとに、パス自体を検証するか、検証済み検証器を使用するかを選択できる。

---

## 代表的な検証済みコンパイラ

### CompCert

| 項目 | 内容 |
|------|------|
| **リポジトリ** | [AbsInt/CompCert](https://github.com/AbsInt/CompCert) |
| **言語** | Rocq Prover (Coq) |
| **Stars** | 2,102 |
| **ソース言語** | C (Clight) |
| **ターゲット** | ARM, PowerPC, x86, RISC-V |
| **ライセンス** | 非商用・商用両方あり |

#### アーキテクチャ

CompCertは20のコンパイルパスを通じて、C言語からアセンブリへ変換する。8つの中間言語を経由する。

```
CompCert C → Clight → C#minor → Cminor → CminorSel → RTL → LTL → Linear → Mach → Assembly
```

**中間言語の概要:**

| 言語 | 説明 |
|------|------|
| **Clight** | 副作用のない式を持つ簡略化されたC |
| **C#minor** | 型なし、ループをブロック+多レベル脱出に変換 |
| **Cminor** | アーキテクチャ非依存の最後の言語 |
| **CminorSel** | マシン固有演算子を認識 |
| **RTL** | 制御フローグラフ、無限の擬似レジスタ |
| **LTL** | 物理レジスタとスタックスロット |
| **Linear** | 明示的なスピル/リロード |
| **Mach** | より具体的な活性化レコード |

#### 意味保存定理

CompCertの正当性定理は以下の形式で述べられる:

> すべてのソースプログラムSとコンパイラ生成コードCについて、コンパイラをソースSに適用してコードCを生成し、コンパイル時エラーを報告しない場合、Cの観測可能な振る舞いはSの許容される観測可能な振る舞いの1つを改良する。

#### 証明手法

CompCertはシミュレーション図（Simulation Diagram）を用いて正当性を証明する。

```
    S₁ ----t----> S₁'     (ソースの遷移)
    |              |
    ~              ~      (状態の対応関係)
    |              |
    T₁ ====t====> T₁'     (ターゲットの遷移)
```

各パスについて独立にシミュレーション図を証明し、それらを合成して全体の意味保存を導く。

---

### CakeML

| 項目 | 内容 |
|------|------|
| **リポジトリ** | [CakeML/cakeml](https://github.com/CakeML/cakeml) |
| **言語** | Standard ML, HOL4 |
| **Stars** | 1,110 |
| **ソース言語** | ML (Standard MLのサブセット) |
| **ターゲット** | x86-64, ARMv6, ARMv8, MIPS-64, RISC-V |

#### 特徴

CakeMLの最大の特徴は**ブートストラップ**である。コンパイラ自身がCakeMLで書かれ、HOL4内でコンパイラが自分自身をコンパイルすることが証明されている。

**エンドツーエンド検証:**
- レキシング、パーシング、型検査
- インクリメンタル・動的コンパイル
- ガベージコレクション
- 任意精度演算
- コンパイラブートストラップ

#### 中間言語

CakeMLは12の中間言語を通過する。

```
CakeML → ... → closLang → dataLang → wordLang → stackLang → labLang → Machine Code
```

| 言語 | 説明 |
|------|------|
| **closLang** | 明示的クロージャを持つ最後の言語。多引数関数をサポート |
| **dataLang** | 抽象データを扱う |
| **wordLang** | マシンワードを扱う。レジスタ割り当てを実行 |
| **stackLang** | 構造化プログラミング言語。スタック操作を最適化 |
| **labLang** | ターゲット中立なアセンブリ言語 |

#### 派生プロジェクト

- **Candle**: 検証済みHOL Light実装
- **PureCake**: 検証済み遅延関数型言語コンパイラ（Haskellスタイル）
- **Pancake**: システムプログラミング言語コンパイラ

---

### Vellvm

| 項目 | 内容 |
|------|------|
| **リポジトリ** | [vellvm/vellvm](https://github.com/vellvm/vellvm) |
| **言語** | LLVM (Coq) |
| **Stars** | 454 |
| **対象** | LLVM IR |

#### 概要

VellvmはLLVMの中間表現（IR）の形式的意味論をCoqで定義し、LLVM IRで表現されたプログラムと、それに対する変換について推論するフレームワークを提供する。

**主な機能:**
- LLVM IRの機械化された形式的意味論
- 型システムの形式化
- SSA形式の性質の証明
- 複数の操作的意味論と、それらの間の関係の証明

**応用例:**
SoftBound計装パスの正当性検証に使用され、空間的メモリ安全性の保証が達成されることが証明された。

---

### CertiCoq

| 項目 | 内容 |
|------|------|
| **リポジトリ** | [CertiCoq/certicoq](https://github.com/CertiCoq/certicoq) |
| **言語** | Rocq Prover (Coq) |
| **Stars** | 158 |
| **ソース言語** | Gallina (Coq) |
| **ターゲット** | Clight (CompCert C) |

#### 概要

CertiCoqはCoqの仕様言語であるGallinaのコンパイラである。CompCertのClightをターゲットとするため、CompCertと合成してGallinaから機械語への検証済みコンパイルパイプラインを構成できる。

**関連プロジェクト:**
- **VeriFFI**: CoqプログラムとCプログラム間の検証済み外部関数インターフェース

---

## 証明技術

### シミュレーション図（Simulation Diagrams）

#### 前方シミュレーション（Forward Simulation）

ソースプログラムの遷移に対応するターゲットプログラムの遷移が存在することを示す。

```
    S ----t----> S'
    |            |
    R            R
    |            |
    T ====t====> T'
```

**利点:** ソースの遷移に関する帰納法で証明できるため、比較的容易

#### 後方シミュレーション（Backward Simulation）

ターゲットプログラムの遷移に対応するソースプログラムの遷移が存在することを示す。

**前方から後方への変換:**
- ターゲット言語の決定性
- ソース言語の入力全体性（receptiveness）

これらの条件の下で、前方シミュレーションを後方シミュレーションに「フリップ」できる。

---

### 論理関係（Logical Relations）

型に関する構造的帰納法で関係を定義する強力な技法。

#### ステップインデックス付き論理関係（Step-indexed Logical Relations）

**動機:** 再帰型や一般参照型を持つ言語では、型に関する直接の帰納法が機能しない

**解決策:** 関係の解釈にインデックス（残りの実行ステップ数）を追加

```
(e₁, e₂) ∈ V_τ[k] ≝ k ステップ以内で e₁ と e₂ が τ 型の値として等価
```

**応用:**
- MLとアセンブリ間のKripke論理関係
- 合成的コンパイラ正当性

#### 双直交性（Biorthogonality）

論理関係に拡張性と合成性を与えるための技法。プログラムとコンテキストの間の双対的な関係を用いる。

---

### トレース関連コンパイラ正当性（Trace-Relating Compiler Correctness）

#### 問題

標準的なコンパイラ正当性の定義:
> コンパイル済みプログラムのトレース集合 ⊆ 元のプログラムのトレース集合

この定義は、ソース言語とターゲット言語のトレース集合が同一であることを要求する。

#### 一般化

ソースとターゲットのトレースを任意の関係で結ぶ一般化された定義。

これにより:
- 言語間の距離が大きい場合
- 観測が細粒度の場合

でも正当性を定式化できる。

---

### 合成的コンパイラ正当性（Compositional Compiler Correctness）

#### 問題

従来の正当性定理は**全体プログラム**のコンパイルのみを扱う。現実には:
- 別々にコンパイルされたコンポーネント間のリンク
- 異なるコンパイラでコンパイルされたコードとのリンク
- FFI経由での他言語コードとの連携

が必要。

#### 解決策: Next 700 Compiler Correctness Theorems

Patterson & Ahmed (ICFP 2019) は、合成的コンパイラ正当性の様々な定式化を統一的な枠組みで分類した。

**垂直合成性（Vertical Compositionality）:**
多パスコンパイラのモジュラー検証のための推移性

**水平合成性（Horizontal Compositionality）:**
リンクのサポート。コンパイラ出力がリンク可能なプログラムの集合を指定する必要がある。

---

## 意味論的基盤

### 操作的意味論

#### Small-step vs Big-step

| 特性 | Small-step | Big-step |
|------|-----------|----------|
| **表現** | 1ステップの遷移関係 | 評価全体の関係 |
| **発散** | 無限遷移列として表現 | 直接表現不可 |
| **帰納法** | 導出に関する帰納法 | 評価に関する帰納法 |
| **並行性** | インターリーブを自然に表現 | 困難 |

CompCertはsmall-step意味論を全言語で採用し、共通のラベル付き遷移系（LTS）フレームワークを使用。

#### 余帰納的big-step意味論

Xavier Leroyらによる発展。余帰納的定義を用いることで、big-step意味論でも発散を表現可能にした。

**利点:**
- 終了する評価と発散する評価を統一的に扱える
- 型健全性証明やコンパイラ正当性証明に適用可能

---

### 分離論理（Separation Logic）

#### Iris

Coqで実装・検証された高階並行分離論理フレームワーク。

**特徴:**
- 言語非依存
- ゴースト状態の汎用的な定式化（カメラ）
- ステップインデックス付きリソース代数

**CompCertとの統合:**
VST（Verified Software Toolchain）のプログラム論理をIrisで再実装し、CompCert Cプログラムの正当性証明を可能にした。

---

## 関連プロジェクト

### seL4マイクロカーネル

検証済みオペレーティングシステムカーネル。

**バイナリ正当性:**
- Cソースコードからバイナリへの正しいコンパイルを証明
- コンパイラとリンカを信頼する必要がない
- ARMv7とRISC-V (64-bit)で証明済み

**実績:**
2009年の機能正当性証明完了以降、15年以上にわたり検証済みコードに機能正当性欠陥なし。

### Lean 4からCへの検証済みコンパイル

最近の研究で、Lean 4からCへの検証済みコンパイルパイプラインが提案された。

**特徴:**
- 最小コア計算（LeanCoreV2）
- 型付き中間表現（λ-IR）
- 命令型中間言語（MiniC）
- 各下降ステップに形式的正当性定理

---

## Zikuへの適用可能性

Zikuプロジェクトは、λμμ̃計算に基づく順序計算IRを持つ言語実装である。コンパイラ正当性証明を適用する際の考慮点を以下にまとめる。

### 1. 形式的意味論の定義

**必要な定義:**
- Surface言語の操作的意味論（big-stepまたはsmall-step）
- IR（λμμ̃計算）の操作的意味論
- Schemeバックエンドの出力の意味論

**推奨:** small-step意味論をラベル付き遷移系として定義することで、CompCertと同様のシミュレーション図による証明が可能になる。

### 2. 証明すべき定理

```
∀ e : Surface.Expr, s : IR.Statement.
  translate(e) = s →
  ∀ v. eval_surface(e) = v ↔ eval_ir(s) = translate_value(v)
```

### 3. 中間言語の活用

Zikuの現在のパイプライン:
```
Surface → [Translate] → IR → [Eval]
                         ↓
                    [Scheme Backend]
```

各変換パスに対して独立に意味保存を証明し、合成することが推奨される。

### 4. Lean 4での検証

Zikuの実装言語であるLean 4は、証明と実装の両方に使用できる。

**戦略:**
1. `Proofs/`ディレクトリの拡張
2. 各IRの意味論をLeanで定義
3. 翻訳関数の正当性をLeanで証明
4. 必要に応じて`partial`関数の代わりにfuelベースの停止性証明

### 5. 段階的アプローチ

1. **Phase 1:** Surface → IR翻訳の正当性
2. **Phase 2:** IR評価器の正当性（既存の`Proofs/Eval.lean`を拡張）
3. **Phase 3:** Schemeバックエンドの正当性
4. **Phase 4:** 合成による全体の正当性

---

## 参考文献

### 主要論文

1. Leroy, X. (2009). [Formal verification of a realistic compiler](https://dl.acm.org/doi/10.1145/1538788.1538814). Communications of the ACM, 52(7), 107-115.

2. Kumar, R., Myreen, M. O., Norrish, M., & Owens, S. (2014). [CakeML: a verified implementation of ML](https://dl.acm.org/doi/10.1145/2535838.2535841). POPL 2014.

3. Patterson, D., & Ahmed, A. (2019). [The next 700 compiler correctness theorems (functional pearl)](https://dl.acm.org/doi/10.1145/3341689). ICFP 2019.

4. Leroy, X., & Grall, H. (2009). [Coinductive big-step operational semantics](https://dl.acm.org/doi/10.1016/j.ic.2007.12.004). Information and Computation, 207(2), 284-304.

5. Abate, C., et al. (2021). [An Extended Account of Trace-relating Compiler Correctness and Secure Compilation](https://dl.acm.org/doi/10.1145/3460860). TOPLAS.

### プロジェクトサイト

- [CompCert](https://compcert.org/)
- [CakeML](https://cakeml.org/)
- [Vellvm](https://www.cis.upenn.edu/~stevez/vellvm/)
- [CertiCoq](https://certicoq.org/)
- [Iris Project](https://iris-project.org/)

### コースノート・チュートリアル

- [The formal verification of compilers (DeepSpec Summer School)](https://deepspec.org/event/dsss17/leroy-dsss17.pdf)
- [A beginner's guide to Iris, Coq and separation logic](https://arxiv.org/abs/2105.12077)
- [Compositional Compiler Verification & Secure Compilation (Oregon PL Summer School)](https://www.cs.uoregon.edu/research/summerschool/summer19/lectures/ahmed4.pdf)

### Cornell CS 6120 (Advanced Compilers)

- [CompCert: Formally Verified C Compiler](https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/comp-cert/)
- [CompCert: the Double-Edged Sword of Verification](https://www.cs.cornell.edu/courses/cs6120/2020fa/blog/compcert/)
