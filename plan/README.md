[← Back](../README.md)

# plan/ の中身

形式化の作業メモ。日本語のみ。

論文と形式化のずれについて調べた結果は、次の 4 分類で置き場所を決めている。

| 見つかったもの | どうするか | 置き場所 |
|---|---|---|
| 原文の間違い、修正しないと証明できない部分 | 修正案を書く | [../paper-corrections.md](../paper-corrections.md) A |
| 原文に足りない部分 | 放置。大きいものだけ補足 | [../paper-corrections.md](../paper-corrections.md) B |
| 原文にあるが必要ない部分 | メモ | [paper-redundancies.md](paper-redundancies.md) |
| こちらの都合で迂回した部分 | メモ | [formalization-detours.md](formalization-detours.md) |
| 原文忠実に直せる部分 | 直す | — |
| 自明として扱っている大きな部分 | 参考文献として記録 | [../lean/README.md](../lean/README.md) |

## 調査の結果

| ファイル | 何の文章か |
|---|---|
| [definitions-audit.md](definitions-audit.md) | 形式化で使っている定義の棚卸し。1. 標準数学（Mathlib から取ったもの）、2. 形式化の道具（論文に無く、証明のためだけに導入したもの）、3. 改変（論文の定義を意図的に変えた箇所）の 3 分類。3 は直したものと直さないものの索引になっている |
| [paper-redundancies.md](paper-redundancies.md) | 論文にあるが形式化には要らなかった箇所。補題 6.5 の区間内部の親、補題 6.7 の `E ∈ G`、通過性 (6.16) の (C1)ₖ、定理 17.1 の場合分け、定理 21.1 の r = 0、分出・収集の副条件の `x`、補題 20.1 の r ≥ 1 など |
| [formalization-detours.md](formalization-detours.md) | 論文どおりに書けず別の道を通った箇所と、その理由。補題 10.5(1) を `L θ` 版にしたこと、命題 22.1 の最小コードを選択公理で代用したこと、`Arr` を総関数で表したこと、Lévy 階層の浅い埋め込み、`LabelSystem` による抽象化など |

論文への修正案だけは結果としてルートに置いてある → [../paper-corrections.md](../paper-corrections.md)

## 作業の記録

| ファイル | 何の文章か |
|---|---|
| [requirements.md](requirements.md) | 最初の依頼。論文を Lean 4 で形式化すること、ZFC と Lean の公理系の差から生じる問題があれば報告すること |
| [lean-formalization-study.md](lean-formalization-study.md) | 着手前の実現可能性調査。Lean + Mathlib で論文全体が形式化できるかの見積もりと、Part III の設計 |
| [phaseB-tasks.md](phaseB-tasks.md) | Part III（§8〜§17）の作業分解 |
| [paper-copy-lemma.md](paper-copy-lemma.md) | コピー補題（定理 6.3）を論文の 6 主張と命題 6.11 で証明し直した記録。主張の一覧、局所補題の依存表、閉形式からの独立性の検査方法 |
| [paper-faithful-plan.md](paper-faithful-plan.md) | Part III のうち、ブロック更新の穴埋め・コード変数の相異性・内部許容性の 3 点を論文どおりに直した記録。旧経路に依存していないことの検査方法（旧補題を `sorry` に置き換えて主定理が `sorryAx` を拾わないことを見る）も書いてある |

## その他の md

| ファイル | 何の文章か |
|---|---|
| [../README.md](../README.md) | リポジトリの入口。目的、ディレクトリ構成、ビルド環境、ビルド方法、参考文献。英語版 `README-en.md` あり |
| [../paper-corrections.md](../paper-corrections.md) | 論文への修正案。書かれたとおりでは証明が通らない箇所だけを置く |
| [../lean/README.md](../lean/README.md) | 形式化の詳細。ファイルと論文の節の対応表、設計メモ、自明として扱っている背景と出典、ビルド確認の方法。英語版 `README-en.md` あり |
