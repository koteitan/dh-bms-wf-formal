[← Back](../README.md)

# 形式化で使っている定義の棚卸し

論文以外の定義をどこで使っているかの一覧。3 分類する。

- 1. 標準数学 — 論文が「既知」として使い、証明しないもの
- 2. 形式化の道具 — 論文に無く、Lean で証明を書くためだけに導入したもの
- 3. 改変 — 論文の定義を意図的に変えた箇所

主定理の主張自体は論文の語彙だけでできている。

```
terminates_unconditional (A : Arr r) (hA : Reachable r A) (n : ℕ → ℕ) : ∃ T, (seq A n T).len = 0
R_wf_unconditional (r : ℕ) : WellFounded (R r)
```

`Arr` は定義 1.1、`Reachable` と `seq` は定義 5.1、`R` は §22 のもの。`WellFounded` だけが
Mathlib。

## 1. 標準数学（Mathlib から借りたもの）

| 使うもの | どこで | 論文での扱い |
|---|---|---|
| `ZFSet` | Part III 全体 | ZFC の集合。論文は地の理論として使う |
| `Ordinal` | Part III 全体 | 順序数 |
| `Cardinal.aleph 1` (= ω₁) | `Omega1.lean`, `Skolem.lean` | §16 |
| `Cardinal.isRegular_aleph_one` | 補題 16.2 | ω₁ の正則性。論文は既知として使う |
| `Ordinal.lsub` | 補題 16.2 | 上限 |
| `Order.IsSuccLimit` | `Adm.lean` ほか | 極限順序数 |
| `Relation.TransGen` | `Defs.lean` | 祖先関係の推移閉包 |
| `WellFounded`, `Acc`, `WellFoundedLT` | `Main.lean` | 整礎性 |
| `Countable`, `Set.Countable` | 補題 16.1 | 可算性 |
| `Classical.choice` | 全体 | 選択公理 |

論文が定義する概念（L、許容順序数、Δ₀、Σ̂q / Π̂q、KP、≺*q、St_k、Rel_k）は全部こちらで書き直して
あり、Mathlib からは持ってきていない。

## 2. 形式化の道具（論文に無い定義）

証明の内側でしか使わず、定理の主張には現れない。

### Part III と Part IV の接続

| 定義 | 場所 | 何のため |
|---|---|---|
| `LabelSystem` | `Label.lean` | Part IV/V が Part III から使うものだけを束ねた界面。論文は Part III の結果を直に使う |
| `GoodOrd` | `Good.lean` | 「良い順序数」の条件をまとめたもの |
| `AdmOrd`, `RelAdm` | `Reflect.lean` | 許容順序数の型と ◁ₖ |

### Lévy 階層の浅い埋め込み

| 定義 | 場所 |
|---|---|
| `Pred`, `Delta0Def`, `SigmaDef`, `PiDef` | `Defin.lean` |

論文は「この論理式は Δ₀ である」と構文で言う。こちらは述語 `Pred` に対する性質として書く。構文
（`Fm`）と浅い埋め込みの両方を持ち、`Rel.lean` で繋いでいる。

### コード化の機械

`Fm.code`, `Fm.der`, `DerSeqW`, `IsCodeW`, `IsAtomicCodeW`, `IsDelta0CodeW`, `IsSigCodeW`,
`IsPiCodeW`, `natZ`, `ωZ`, `kprodZ`, `nestZ`, `cEq`〜`cBex`, `D0C`, `D0Sh`, `DerSeqBW`,
`IsCodeBW`, `IsInjSeq`, `IsNeSeqW`

論文は「ゲーデル数を取る」で済ませる部分。こちらは遺伝的有限集合としてコードを組み、認識述語が Δ₀
であることを一つずつ証明している。

### 代入と列の帳簿

`IsSeqA`, `SeqVal`, `IsFunc`, `IsDom`, `IsRan`, `IsUpdate`, `IsRestrict`, `IsUpdSeq`, `WClosed`,
`BaseCorrect`, `GoodAsn`, `GoodAsnP`, `GoodAsnQ`, `TransDom`, `GoodDom`, `natBound`

### 配列まわりの細部

`HasParent`, `LastHasParent`, `dropLast`, `toBadRoot`, `parentRel`, `IntECand`, `Asc`, `Aq`

`IntECand` は定義 6.1 を区間の左端で表したもの。他は論文が言葉で済ませる部分。

### テスト専用（定理は一切使わない）

`expandC`, `Mat`, `parseMat`, `showMat`, `run` — `Compute.lean`。yaBMS との突き合わせ用。

### 閉形式（`main` には無い）

`ParForm`, `AncForm` は `Copy.lean` に残っている（関係を書く型として下流が使う）。証明そのもの
（`CandForm`, `CandHyp`, `AncFormX`, `parent_tA_iff'` ほか）はブランチ `feature/closed-form` の
`Bm4/CopyClosed.lean` にある。

## 3. 改変（論文の定義を意図的に変えた箇所）

方針に従って分類した。索引だけ置く。

### 直した（原文忠実になった）

| もとの改変 | 論文の箇所 | どう直したか |
|---|---|---|
| コピー補題を閉形式で証明 | 定理 6.3 | 6 つの局所補題と命題 6.11 に（`Bm4/CopyPaper/`） |
| 補題 15.3 を複雑度経由で証明 | 補題 15.3 | `tvqP_iff_elemHat` に |
| 内部の許容性を `CollTrue` で | 定義 11.1 | `AdmKP` に |
| ブロック更新が定義域を伸ばさない | §12 BlkUpd | `BlkP.lean` に |
| ブロック変数の相異性を課さない | 定義 12.1 | `BFCodeD.lean` に |
| `AdmKP` に Δ₀ の連言 2 つを追加 | 定義 11.1 | 削除。極限性は KP の真理から導出 |
| `KPTrue` が全代入を回す | 定義 11.1 | `⟨d, ∅⟩ ∈ S` に。スキーマは全称閉包で認識 |
| 分出・収集の副条件を強めた | §11 | `NotFreeW` で「x, y が φ に自由でない」に |
| 定理 21.1 を整礎帰納で証明 | 定理 21.1 | Choice + ω-再帰 + 高さ集合の最小元に |
| 命題 22.1 を高さの帰納で証明 | 命題 22.1 | 定理 1.2 から導く形に |
| 補題 2.2(3) の主張が無い | 補題 2.2(3) | `ancEq_single_finite_chain` を追加 |
| 定義 6.1 の `IntPar` が無い | 定義 6.1 | `IntPar` と補題 6.2(1)(3) を追加 |
| 命題 19.1 の (e)(f) が別の筋 | 命題 19.1 | (C6)+補題 3.1 と系 6.12 に |
| `TVqP` に余分な連言 4 つ | 定義 14.2 | 削除（含意の仮定へ、D-9） |
| 定理 14.4 が q = k+2 のみ | 定理 14.4 | 全ての q ≥ 1 に |
| `RelKP` に Ord/順序の連言が無い | 定義 15.4 | 復活 |
| 補題 15.5(1) が無い | 補題 15.5 | `relKP_iff_ext` を追加 |

### 直さない（迂回）

`plan/formalization-detours.md` の D-1 〜 D-13 を参照。

| §8.1 `Update` が空所を ∅ で埋める | §8.1 | x で埋め、代入に (8.4) の適切さ条件 `Asn_A` を復活 |
| `SatCode` に論文に無い `∅ ∈ A` の節 | 定義 8.3 | 削除 |
| 定義 9.1 に論文に無い節、ξ ≠ 0 の制限 | 定義 9.1 | 削除。条件 3〜5 が ξ = 0 も覆う |
| 補題 12.2(4) が二項連言のみ | 補題 12.2(4) | 選言と有限族版を追加 |
| Σ̂q クラスにブロック内相異性が無い | 定義 12.1 | `IsSigma` / `IsPi` に追加 |
| BlkUpd の ν に相異性・有限列性が無い | §12 | 追加 |
| 補題 8.2 の第一主張が無い | 補題 8.2 | 追加 |
| 補題 10.3 が graph の帰属だけ | 補題 10.3 | 一意存在の形に |
| 真理述語にコード判定が無い | 定義 13.2, 13.4 | `Form` の連言を追加 |
| 補題 13.3 / 定理 13.6 の外部宇宙版が無い | §13 | 追加 |
| `LCode` の配置が論文と違う | 定義 9.1 | `FourCode` と 5 条件で書き直し |

### 未着手

**なし。**

## 分類の方針と置き場所

| 見つかったもの | どうするか | 置き場所 |
|---|---|---|
| 原文の間違い、修正しないと証明できない部分 | 修正案を書く | `plan/paper-corrections.md` A |
| 原文に足りない部分 | 放置。大きいものだけ補足 | `plan/paper-corrections.md` B |
| 原文にあるが必要ない部分 | メモ | `plan/paper-redundancies.md` |
| こちらの都合で迂回した部分 | メモ | `plan/formalization-detours.md` |
| 原文忠実に直せる部分 | 直す | — |
| 自明として扱っている大きな部分 | 参考文献として記録 | `lean/README.md` |
