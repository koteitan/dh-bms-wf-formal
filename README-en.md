[English](README-en.md) | [Japanese](README.md)

# dh-bms-wf-formal

DH proved the termination of BM4 (Bashicu Matrix System version 4) and the well-foundedness of
its expansion relation, and on 4 September 2026 [published](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:DeltaEta22223/BM4%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E)
the paper [*"Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性"*](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB:BM4(%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D).pdf)
(Termination of the Bashicu Matrix System version 4 and well-foundedness of its expansion
relation) on the [Japanese Googology Wiki](https://googology.fandom.com/ja/wiki/%E5%B7%A8%E5%A4%A7%E6%95%B0%E7%A0%94%E7%A9%B6Wiki).

This repository is a Lean 4 formalization of that proof.

## History
- 4 September 2026: DH published the paper on the Japanese Googology Wiki.
- 5 September 2026: the formalization was completed and published on GitHub.

## Purpose

To prove two statements about BM4 (Bashicu Matrix System version 4) in Lean 4:

- **Theorem 1.2 (termination)**: every expansion sequence starting from any array of BM4 reaches
  the empty array in finitely many steps.
- **Proposition 22.1 (well-foundedness)**: the one-step expansion relation R is well-founded.

```lean
theorem BM4.ST.terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A)
    (n : ℕ → ℕ) : ∃ T, (BM4.seq A n T).len = 0
theorem BM4.ST.R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r)
```

**The whole paper is formalized, without `sorry`.** Every proved declaration depends only on
`propext`, `Classical.choice` and `Quot.sound`.

The guiding principle is **fidelity to the paper**. Reproducing the paper's definitions,
statements and lines of argument takes priority over shorter proofs or weaker hypotheses.

## Directory layout

```
.
├── README.md                  this file (Japanese)
├── README-en.md               this file (English)
├── paper-corrections.md       corrections proposed to the paper, found while formalizing
├── diff/                      formalization gaps, one page per proposition of the paper
│   ├── README.md              index
│   ├── rule.md                how to write these pages
│   └── P-01.md .. P-14.md
├── plan/
│   ├── fidelity-audit.md      the fidelity audit, one independent agent per section
│   ├── fidelity-audit-fix.md  the repair log for the 74 U (detour) findings
│   └── U2P.md                 which U belongs to which proposition
├── VERSION
├── lean/                      the Lean 4 project
│   ├── README.md              details: which file corresponds to which section
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── Bm4.lean               root module
│   ├── Bm4/
│   │   ├── Defs.lean          Def. 1.1, 2.1, 5.1 (arrays, parents, ancestors, expansion)
│   │   ├── Basic.lean         Lemmas 2.2, 3.1, 4.1
│   │   ├── Copy.lean          the §6 setup (bad root, positions, entries)
│   │   ├── CopyPaper/         Theorem 6.3 (the copy lemma) by the paper's six claims
│   │   ├── Expand.lean        links Definition 5.1 with the bad-root data
│   │   ├── Standard.lean      Proposition 7.1 (the standardness invariant)
│   │   ├── Label.lean         Def. 18.1, Prop. 19.1 (stable labels and height descent)
│   │   ├── Main.lean          Lemma 20.1, Thm 21.1, Thm 1.2, Prop. 22.1
│   │   ├── Compute.lean       a computable form of Definition 5.1 (testing only)
│   │   └── SetTheory/         Part III (§8-§17)
│   └── test/                  comparison against an external implementation (58 cases)
└── plan/                      working notes (Japanese only)
    ├── README.md              what each document under plan/ is
    ├── definitions-audit.md   inventory: standard maths / formalization tools / deviations
    ├── paper-redundancies.md  parts of the paper that turned out to be unnecessary
    ├── formalization-detours.md  places we could not follow the paper, and why
    └── paper-copy-lemma.md    record of proving the copy lemma the paper's way
```

## Formalization gaps

Where the Lean text could not follow the paper literally, there is one page per proposition
of the paper: the paper's statement and proof, the Lean statement and proof, and why it could
not be written the paper's way. Index: [diff/README.md](diff/README.md).

`lean/Bm4/SetTheory/` is about 77% of the whole. It builds the set theory from scratch: the
constructible hierarchy `L`, admissible ordinals, codes of Δ₀ formulas, satisfaction codes, the
alternating-block truth predicates and finite pattern reflection. See the table in
[lean/README-en.md](lean/README-en.md) for the file-to-section correspondence.

## Build environment

| | |
|---|---|
| Lean | v4.30.0 |
| Mathlib | tag v4.30.0 |
| Build tool | Lake |

Pinned in `lean/lean-toolchain` and `lean/lakefile.toml`. There is no dependency other than
Mathlib.

## How to build

```sh
cd lean
lake exe cache get     # fetch the prebuilt Mathlib cache
lake build             # build everything
```

With the Mathlib cache in place, this development itself builds in about 90 seconds
(8533 jobs, 58 modules).

To check a single file:

```sh
cd lean
lake env lean Bm4/CopyPaper/Assemble.lean
```

To check which axioms the main theorems use:

```sh
cd lean
echo 'import Bm4
#print axioms BM4.ST.terminates_unconditional
#print axioms BM4.ST.R_wf_unconditional' > Check.lean
lake env lean Check.lean
rm Check.lean
```

To compare Definition 5.1 against an external implementation (58 cases):

```sh
cd lean
BMS=<path to the external implementation> LEANPROJ=. test/compare.sh
```

## References

(bibliographic details of the paper to be added)

For the background results this development takes from Mathlib rather than proving, and where
they are found in the literature, see "Background taken as standard" in
[lean/README-en.md](lean/README-en.md).
