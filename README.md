[English](README-en.md) | [Japanese](README.md)

# dh-bms-wf-formal

DH 氏が BM4（バシク行列システム ver. 4）の停止性と展開関係の整礎性の証明を証明し、 2026 年 9 月 4 日にその論文「[Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB:BM4(%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D).pdf)」を[巨大数研究 Wiki](https://googology.fandom.com/ja/wiki/%E5%B7%A8%E5%A4%A7%E6%95%B0%E7%A0%94%E7%A9%B6Wiki) に[発表した](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:DeltaEta22223/BM4%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E)。

このリポジトリは、その証明の Lean 4 による形式化である。

## 経緯
- 2026 年 9 月 4 日: DH 氏が論文を巨大数研究 Wiki に発表した。
- 2026 年 9 月 5 日: 形式化が完了し、github に公開した。

## 目的

BM4（バシク行列システム ver. 4）について、次の 2 つを Lean 4 で証明する。

- **定理 1.2（停止性）**: BM4 の任意の配列から始まる任意の展開列は、有限回で空配列に到達する。
- **命題 22.1（整礎性）**: 一段展開関係 R は整礎である。

```lean
theorem BM4.ST.terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A)
    (n : ℕ → ℕ) : ∃ T, (BM4.seq A n T).len = 0
theorem BM4.ST.R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r)
```

**論文全体が形式化済みで、`sorry` は 0 件。** 証明された全ての宣言が依存する公理は
`propext`、`Classical.choice`、`Quot.sound` の 3 つだけ。

形式化は**原文に忠実であること**を第一の方針としている。証明が短くなることや仮定が弱くなる
ことよりも、論文の定義・主張・証明の筋をそのまま写すことを優先する。

## ディレクトリ構成

```
.
├── README.md                  このファイル
├── paper-corrections.md       論文への修正案（形式化して見つかったもの）
├── diff/                      形式化差異（論文の命題ごとに原文・Lean・理由）
│   ├── README.md              目次
│   ├── rule.md                書き方のルール
│   └── P-01.md 〜 P-14.md
├── plan/
│   ├── fidelity-audit.md      原文忠実性の監査結果（節ごとに独立監査）
│   ├── fidelity-audit-fix.md  監査が挙げた U（迂回）74 件の修正作業の記録
│   └── U2P.md                 U と論文中の命題の対応表
├── VERSION
├── lean/                      Lean 4 プロジェクト
│   ├── README.md              形式化の詳細（ファイルと論文の対応表）
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Bm4.lean               ルートモジュール
│   ├── Bm4/
│   │   ├── Defs.lean          定義 1.1, 2.1, 5.1（配列・親・祖先・展開）
│   │   ├── Basic.lean         補題 2.2, 3.1, 4.1
│   │   ├── Copy.lean          §6 の設定（bad root、位置、成分）
│   │   ├── CopyPaper/         定理 6.3（コピー補題）を論文の 6 主張で証明
│   │   ├── Expand.lean        定義 5.1 と bad root の接続
│   │   ├── Standard.lean      命題 7.1（標準性不変量）
│   │   ├── Label.lean         定義 18.1, 命題 19.1（安定ラベルと高さの降下）
│   │   ├── Main.lean          補題 20.1, 定理 21.1, 定理 1.2, 命題 22.1
│   │   ├── Compute.lean       定義 5.1 の計算可能版（試験用、定理は使わない）
│   │   └── SetTheory/         Part III（§8〜§17）
│   └── test/                  外部実装との突き合わせ（58 例）
└── plan/                      作業メモ（日本語のみ）
    ├── README.md              plan/ の各文書の説明
    ├── definitions-audit.md   定義の棚卸し（標準数学 / 形式化の道具 / 改変）
    ├── paper-redundancies.md  原文にあるが必要なかった部分
    ├── formalization-detours.md  こちらの都合で迂回した部分
    └── paper-copy-lemma.md    コピー補題を論文の道筋で証明した記録
```

## 形式化差異

原文どおりに書けなかった箇所は、論文の命題ごとに 1 ページを立てて記録している。
各ページは原文の命題と証明、Lean での命題と証明、そして原文どおりに書けなかった理由を
並べる。目次は [diff/README.md](diff/README.md)。

`lean/Bm4/SetTheory/` が全体の約 77% を占める。集合論の道具（構成可能階層 L、許容順序数、
Δ₀ 論理式のコード化、充足コード、交代ブロック真理述語、有限行反映）を一から作っている。
各ファイルと論文の節の対応は [lean/README.md](lean/README.md) の表を参照。

## ビルド環境

| | |
|---|---|
| Lean | v4.30.0 |
| Mathlib | v4.30.0 タグ |
| ビルドツール | Lake |

`lean/lean-toolchain` と `lean/lakefile.toml` に固定してある。Mathlib 以外の依存は無い。

## ビルド方法

```sh
cd lean
lake exe cache get     # Mathlib のビルド済みキャッシュを取得
lake build             # 全体をビルド
```

Mathlib のキャッシュがあれば、この形式化自体のビルドは 90 秒程度（8533 ジョブ、58 モジュール）。

単一ファイルの確認:

```sh
cd lean
lake env lean Bm4/CopyPaper/Assemble.lean
```

主定理が使う公理の確認:

```sh
cd lean
echo 'import Bm4
#print axioms BM4.ST.terminates_unconditional
#print axioms BM4.ST.R_wf_unconditional' > Check.lean
lake env lean Check.lean
rm Check.lean
```

定義 5.1 と外部実装の突き合わせ（58 例）:

```sh
cd lean
BMS=<外部実装のパス> LEANPROJ=. test/compare.sh
```

## 参考文献

（原文の書誌情報は後で追記）

形式化が自分で証明せず Mathlib から取っている背景知識と、その標準的な出典は
[lean/README.md](lean/README.md) の "Background taken as standard" を参照。
