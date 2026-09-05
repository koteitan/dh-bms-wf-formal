[← Back](../README.md)

# 論文の方式に合わせる作業 (branch `paper-faithful`, 2026-09-04)

## 目的

形式化が論文と道の違う箇所のうち、次の 3 つを論文どおりにし、**本線に載せる**。

- 差分 2: 補題 15.3 の片方向を、複雑度の迂回ではなく真理述語の正しさから証明する
- 差分 4: 内部の許容性を、Δ₀ 収集の直接内部化ではなく KP 公理コードの真理で定義する（定義 11.1）
- 差分 5: ブロック更新の穴埋め（§12 BlkUpd）とブロック変数の相異性（定義 12.1）を課す

## 判断の根拠

論文に誤りは無い。差は形式化側にあった。

- 論文の定義 12.1 はブロック変数が相異なることを要求するが、`IsNeSeqW` は課していなかった。
- 論文の §12 BlkUpd は定義域を伸ばす（穴埋めする）が、`IsBlkUpd` は伸ばさなかった。
- この 2 つの欠落のため補題 15.3 の片方向で真理述語の正しさが使えず、複雑度経由の別証明
  (`trSigS_transfer`) を使っていた。
- 論文の定義 11.1 は KP の公理コードを使うが、`CollTrue` は充足集合経由で Δ₀ 収集を直接
  内部化していた。

## 作ったファイル

| ファイル | 行 | 内容 |
|---|---|---|
| `BlkP.lean` | 465 | 論文の BlkUpd（穴埋めあり）、Δ₀ 性、存在（定義域の仮定なし） |
| `BFCodeD.lean` | 266 | ブロック変数の相異性を課したコード認識述語 `IsSigCodeWD` / `IsPiCodeWD` |
| `TrP.lean` | 375 | 穴埋め版の上の真理述語と定理 13.6（`GoodAsnP` は条件が 1 つ少ない） |
| `StRelP.lean` | 404 | `TVqP` と `tvqP_iff_elemHat`（補題 15.3 の橋を論文の道で） |
| `KPAx.lean` | 716 | KP の公理を `Fm` として書き、コード認識述語 `KPAxCode` を Δ₀ で定義 |
| `KPSat.lean` | 339 | 許容 θ で `L θ` が KP を満たすこと、およびその逆 |
| `AdmKP.lean` | 174 | 論文の定義 11.1 (`AdmKP`) と補題 11.2 (`admKP_iff`) |
| `StKP.lean` | 146 | `StKP` / `RelKP` と複雑度・正しさ（補題 15.3, 15.5） |

## 本線への繋ぎ込み

`Reflect.lean` の識別子を置き換えただけで通った。証明本体の変更はゼロ。

| 旧 | 新 |
|---|---|
| `AdmP` | `AdmKP` |
| `sigmaDef_admP` | `sigmaDef_admKP` |
| `admP_iff'` | `admKP_iff` |
| `StK` / `piDef_StK` / `stK_iff` | `StKP` / `piDef_StKP` / `stKP_iff` |
| `RelK` / `sigmaDef_RelK` / `relK_iff` | `RelKP` / `sigmaDef_RelKP` / `relKP_iff` |

## 本当に本線に載ったかの検査

Lean 4.30 のこの構成では olean に定理本体が入らないため、証明項を辿るメタプログラムは使えない
(`ConstantInfo.value?` が `none`)。代わりに次の検査をした。

旧経路の `stK_iff`, `relK_iff`, `admP_iff'` の証明を一時的に `sorry` に置き換えてビルドし、

```
'BM4.ST.stK_iff'                  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'BM4.ST.terminates_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'BM4.ST.R_wf_unconditional'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorry` は生きているのに主定理は汚染されない。よって主定理は旧経路に依存しない。検査後
3 ファイルは復元した。

## 残した但し書き

1. `AdmKP` は KP 公理の真理に加えて Δ₀ の 2 連言 `w ∈ η ∧ (∀ ζ ∈ η, ζ+1 ∈ η)` を持つ。
   KP の真理だけから η の極限性を出す補題が無いため。`AdmP` も同じ形なので不利ではない。
2. 分出・収集スキーマの副条件は「x, y が φ に自由でない」ではなく、より強く Δ₀ 判定可能な
   「φ の全変数 < N ≤ x, y」。認識されるのは束縛変数を φ の全変数より上に取り直した
   インスタンスのみで、rename up to では完全。
3. `satIn_kpAx` は付値が `L θ` 内に落ちることを要求する。無条件形は ZFC で決定不能
   （V=L の無矛盾性）なので強制的。`KPTrue` は M 上の列を回すので内部では影響しない。
4. 旧ファイル `AdmP.lean` / `AdmPOK.lean` / `TV.lean` / `StRel.lean` は残してある。
   論文経路がそれらの補助補題の上に建っているため。

## git の扱い

1. `Bm4/CopyPaper/*` を `paper-copy-lemma` にコミット（済、`8c2c6a7`）
2. `git checkout -b paper-faithful main`（8 ファイルは未追跡なので付いてくる）（済）
3. 8 ファイルと `Reflect.lean` / `Bm4.lean` / `README.md` を `paper-faithful` にコミット
4. `paper-faithful` を `main` と `paper-copy-lemma` の両方へマージ
