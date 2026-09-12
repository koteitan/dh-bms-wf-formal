[← Back](../README.md) | [English](README_en.md) | [Japanese](README.md)

# BM4 停止性証明の Lean 4 形式化

DH 氏の論文「Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性」の形式化。
Lean 4 v4.30.0、Mathlib v4.30.0。

## 状態

**論文全体が形式化済みで、`sorry` は 0 件。** 主定理は次の 2 つ。

```lean
theorem BM4.ST.terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A)
    (n : ℕ → ℕ) : ∃ T, (BM4.seq A n T).len = 0        -- 定理 1.2
theorem BM4.ST.R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r)   -- 命題 22.1
```

証明された全ての宣言が依存する公理は `propext`、`Classical.choice`、`Quot.sound` の 3 つだけ。

Part I, II, IV, V は抽象界面 `LabelSystem`（`Bm4/Label.lean`）に対して証明されており、
Part III（`Bm4/SetTheory/`）がその実体を構成する。従って上の 2 定理は無条件形である。

## ファイル

| ファイル | 論文 | 内容 |
|---|---|---|
| `Bm4/Defs.lean` | 定義 1.1, 2.1, 5.1 | 配列 `Arr r`、親、祖先、`tildeCol`、`expand`、`E r`、`Reachable`、`seq`、`R` |
| `Bm4/Basic.lean` | 補題 2.2, 3.1, 4.1 | 祖先関係の基本性質、接頭部分の不変性（`anc_congr_iff`）、凸性（`convex`） |
| `Bm4/Copy.lean` | §6 | bad root のデータ `BadRoot`、その位置と成分、コピー後の配列の関係を書く型 `ParForm` / `AncForm` |
| `Bm4/Expand.lean` | 定義 5.1 | `expand` と `BadRoot` の接続 |
| `Bm4/Standard.lean` | 命題 7.1, 備考 7.2 | 標準性不変量 `standard_invariant`、公開規則 `expandOfficial` と `expandOfficial_eq_expand` |
| `Bm4/Label.lean` | 定義 18.1, 命題 19.1 | `LabelSystem` 界面、安定ラベル `Stable`、高さの降下 `descent` |
| `Bm4/Main.lean` | 補題 20.1, 定理 21.1, 定理 1.2, 命題 22.1 | `stable_E`、`terminates`、`R_wf` |
| `Bm4/Compute.lean` | 定義 5.1 | 外部実装との突き合わせ用の計算可能版 `expandC`（`test/compare.sh`） |

### コピー補題（`Bm4/CopyPaper/`）

定理 6.3 は論文の道筋どおりに証明されている。互いに参照し合う 6 つの主張 (C1)〜(C6)、
主張ごとに 1 本の局所補題、そして命題 6.11 の非循環な三段階の組み立て。

| ファイル | 論文 | 内容 |
|---|---|---|
| `Interval.lean` | 定義 6.1, 補題 6.2 | 区間内部の候補 `IntECand` と内部親 `IntPar`、6 主張の述語 `Claim1`〜`Claim6` |
| `L1.lean` | 補題 6.4 | (C1)ₖ を h < k の (C1)ₕ から |
| `L3.lean` | 補題 6.5 | (C3)ₖ（k < m₀）を (C1)ₖ と (C3)ₖ₋₁ から |
| `L5.lean` | 補題 6.6 | (C5)ₖ を (C1)ₕ, (C5)ₕ (h < k)、(C1)ₖ、(C3)ₖ または (C4) から |
| `L2.lean` | 補題 6.7 | (C2)ₖ を (C2)ₕ (h < k)、(C1)ₖ、(C5)ₖ、(C3)ₖ または (C4) から |
| `L6.lean` | (6.16), 補題 6.8 | 通過性、(C6)ₖ を (C1)ₖ, (C5)ₖ、(C3)ₖ または (C4) から |
| `L4.lean` | 補題 6.9, 6.10 | (C4)。m₀ = 0 なら無条件、m₀ > 0 なら (C3)_{m₀-1}, (C6)_{m₀-1} から |
| `Assemble.lean` | 命題 6.11, 定理 6.3, 系 6.12 | 三段階の組み立て、全行の 6 主張、隣接コピーの系 |
| `Char.lean` | 定理 6.3 | 下流が使う界面 `anc_tA_iff`、`anc_tA_cases`、`hasParent_tA_of_parForm` を 6 主張から導く |

同じ界面のより短い証明が、ブランチ `feature/closed-form` の `Bm4/CopyClosed.lean` にある。
親と祖先の関係を単一の閉形式で表し、行に関する 1 本の帰納法で済ませるもので、m の行最大性を
使わないため命題 6.11 の順位付けも要らない。`CopyPaper/Char.lean` と `CopyClosed.lean` の
どちらか一方だけがビルドに入る。

### Part III（`Bm4/SetTheory/`）

| ファイル | 論文 | 内容 |
|---|---|---|
| `Fm.lean` | §12 | 名前付き変数の論理式、領域上の充足、Δ₀ 絶対性、Σ̂q/Π̂q、双対化、padding、併合 |
| `Defin.lean` | §8〜15 | Lévy 定義可能性の浅い埋め込み（`Delta0Def` / `SigmaDef` / `PiDef`）と閉包補題 |
| `L.lean` | §9 | 構成可能階層 `L` |
| `Adm.lean`, `HF.lean` | §10 | 許容順序数、遺伝的有限集合、Δ₀ 定義可能な集合演算 |
| `Rel.lean` | — | 論理式と定義可能述語の相対化 |
| `Recur.lean`, `Recursion.lean` | §10 | `L θ` の内部での Σ₁ 収集と順序数に沿った Σ₁ 再帰 |
| `BF.lean`, `BFConv.lean` | §12 | ブロック式 `BF`、クラス `BF.Sig` / `BF.Pi`、`Fm` への翻訳 |
| `Code.lean`, `BFCode.lean` | §8, §12 | 論理式とブロック式の符号、Δ₀ 認識子 |
| `CodeFV.lean` | §8, §11 | `NotFreeW`。「この変数は符号化された式に自由に現れない」の Δ₀ 認識子 |
| `SatCode.lean` | 定義 8.3, 補題 8.4 | 充足コード、正しさ、一意性、存在 |
| `SatInL.lean` | 補題 10.5(1) | 許容な `L θ` の**内部**に充足コードが存在する |
| `LCode.lean`, `LCodeEx.lean` | 定義 9.1, 補題 9.2, 10.5(2) | L 階層の内部コード、健全性と存在 |
| `Blk.lean` | §12 | 代入のブロック同時更新 |
| `Truth.lean`, `TrCorrect.lean`, `BaseOK.lean` | §13 | 真理述語の Δ₀ 基底（定義 13.2）と補題 13.3 |
| `Elem.lean` | §14 | `≺*q`、有限段の Tarski–Vaught 判定 |
| `KPAx.lean`, `KPSat.lean`, `AdmKP.lean` | 定義 11.1, 補題 11.2 | **論文の**内部許容性述語。KP 公理のコード `KPAxCode`、その `L θ` での真理、`AdmKP` と `admKP_iff` |
| `BlkP.lean` | §12 | 論文どおり定義域を**穴埋め**するブロック更新 |
| `BFCodeD.lean` | 定義 12.1 | 論文どおりブロック変数の**相異性**を要求するコード認識子 |
| `TrP.lean`, `TrPV.lean`, `StRelP.lean`, `StKP.lean` | §13〜15 | 定義 13.4 の真理述語 `Tr_{Σ̂q}` / `Tr_{Π̂q}`（§12 の穴埋め付きブロック更新の上）、補題 13.5（複雑度）、定理 13.6（正しさ。`TrPV.lean` が外部宇宙版）、`TV_q`・`St_k`・`Rel_k` とその正しさ（補題 15.3, 15.5） |
| `StKP.lean` | 定義 15.2, 15.4, 補題 15.3, 15.5 | 穴埋め経路の `St_k` と `Rel_k`、その複雑度と正しさ |
| `Omega1.lean`, `Skolem.lean`, `AdmTrans.lean` | §16 | ω₁ 未満の `L γ` の可算性、ω₁ の許容性、初期対 `L Λ ≺ L ω₁` |
| `Good.lean`, `Stable.lean` | §15 | `GoodOrd` 界面、ラベルとしての許容順序数、`◁ₖ` |
| `Reflect.lean` | §17, §18〜22 | **定理 17.1**（有限行反映）、`LabelSystem` の実体、無条件形の主定理 |

## 設計メモ

- `Arr r` は対 `(len, col : ℕ → ℕ → ℕ)`。親も祖先も `len` を読まないので、補題 3.1（接頭部分の
  不変性）は一般化された `anc_congr_iff`（位置 ≤ i で一致する 2 配列は i の祖先が一致）になる。
- コピー補題は論文どおり。6 主張を局所補題 6.4〜6.10 で証明し、命題 6.11 の段階順で組み立てる。
  論文の辞書式順位 (0,k,·) < (1,0,0) < (2,k,·) はこの段階順に対応する。`CopyPaper/Char.lean` が
  そこから `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` の親・祖先の関係を読み取り、`Expand.lean`、`Standard.lean`、
  `Label.lean` が使う `ParForm` / `AncForm` の形にする。
- Part III も論文どおり。`Update` は新しい空所を書き込む値で埋め、代入は (8.4) の適切さ条件
  `Asn_A` を持つ（`SatCode.lean`）。ブロック更新は定義域を穴埋めする（`BlkP.lean`）。Σ̂q クラスと
  そのコード認識子はブロック変数の相異性を要求する（`Fm.lean`、`BFCodeD.lean`）。真理述語は定義
  13.2・13.4 の `Form` 判定を持つ（`Truth.lean`、`TrP.lean`）。補題 15.3 は真理述語の正しさから
  証明する（`StRelP.lean`）。内部許容性は空代入での KP 公理の真理で、スキーマのインスタンスは
  全称閉包の形で認識される（`KPAx.lean`、`AdmKP.lean`）。
- §12〜§15 はかつて二重に形式化されていた（∅ 穴埋めを持たないブロック更新に基づく緩い版と、
  論文どおりの版）。主定理が緩い版を使っていないことを `sorry` 注入で確かめたうえで、
  緩い版（`TV.lean`、`StRel.lean` の後半、`Truth.lean` の `TrSigS`/`TrPiS`、`Blk.lean` の
  `IsBlkUpd`、`AdmP.lean`、`AdmPOK.lean`）は削除した。残るのは論文どおりの一本だけである。
- 定理 21.1 は論文どおり、選択公理と ω-再帰、そしてラベルの高さの集合の最小元で証明する。
  命題 22.1 は高さの帰納法で証明し直さず、定理 1.2 から導く。
- `LabelSystem` は Part IV が Part III から使うものだけを束ねている。ラベルの整礎全順序、
  関係 `rel k`（◁ₖ、補題 15.1）、初期対（補題 16.2）、行数 r で抑えた有限行反映（定理 17.1）。

## 自明として扱っている背景

論文は ZFC の中で書かれ、構成可能階層・許容順序数・Lévy 階層の標準理論を使う。その大半は
import せず**ここで作っている**。`L`、`IsAdmissible`、Lévy クラス、Δ₀ 絶対性、充足コード、
Tarski–Vaught 判定、ω₁ 未満の `L γ` の可算性は、いずれも専用のファイルを持つ。

証明せず Mathlib から取っているものと、その標準的な出典は次のとおり。

| Mathlib から取るもの | 用途 | 標準的な出典 |
|---|---|---|
| `ZFSet` — ZF のモデル | Part III 全体 | Jech, *Set Theory*, 3rd ed. |
| `Ordinal`, `Cardinal`, `Order.IsSuccLimit` | 順序数と極限 | Jech, ch. 2–3 |
| `Cardinal.isRegular_aleph_one` — ω₁ の正則性 | 補題 16.2（`Omega1.lean`） | Jech, ch. 3 |
| `Cardinal.aleph 1`, `Cardinal.lt_aleph_one_iff` | 補題 16.1（`Omega1.lean`） | Jech, ch. 3 |
| `Ordinal.lsub` と正則性による評価 | 補題 16.2 | Jech, ch. 3 |
| `WellFounded`, `Acc`, `WellFoundedLT`, `Relation.TransGen` | Part V（`Main.lean`） | Jech, ch. 2 |
| `Classical.choice` | 定理 21.1 と命題 22.1。論文と同じ | — |

論文が前提とする許容集合論（Barwise, *Admissible Sets and Structures*）は取り込んでいない。
`Adm.lean`、`KPAx.lean`、`KPSat.lean` が定義から必要な分を作る。論文が前提とするモデル論
（Chang–Keisler, *Model Theory*）も同様で、有限段の Tarski–Vaught 判定は `Elem.lean`、
Skolem 包は `Skolem.lean` で証明している。

## 確認方法

```sh
lake exe cache get     # Mathlib のビルド済みキャッシュを取得
lake build             # 全体をビルド。90 秒程度
lake env lean Bm4/CopyPaper/Assemble.lean          # 単一ファイル
BMS=<外部実装のパス> LEANPROJ=. test/compare.sh     # 定義 5.1 との突き合わせ、58 例
```

主定理が使う公理の確認:

```sh
echo 'import Bm4
#print axioms BM4.ST.terminates_unconditional
#print axioms BM4.ST.R_wf_unconditional' > Check.lean
lake env lean Check.lean
rm Check.lean
```
