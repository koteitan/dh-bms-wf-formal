[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# Lean 4 formalization of the BM4 termination proof

Formalization of the paper "Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性" (DH).
Lean 4 v4.30.0, Mathlib (May 2026).

## Status

**The whole paper is formalized, without `sorry`.** The main theorems:

```lean
theorem BM4.ST.terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A)
    (n : ℕ → ℕ) : ∃ T, (BM4.seq A n T).len = 0        -- Theorem 1.2
theorem BM4.ST.R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r)   -- Proposition 22.1
```

All proved declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

Parts I, II, IV, V are proved relative to the abstract interface `LabelSystem` (`Bm4/Label.lean`);
Part III constructs an instance of it (`Bm4/SetTheory/`), so the theorems above are unconditional.

## Files

| file | paper | content |
|---|---|---|
| `Bm4/Defs.lean` | Def. 1.1, 2.1, 5.1 | arrays `Arr r`, parents, ancestors, `tildeCol`, `expand`, `E r`, `Reachable`, `seq`, `R` |
| `Bm4/Basic.lean` | Lemma 2.2, 3.1, 4.1 | basic ancestor facts, prefix invariance (`anc_congr_iff`), convexity (`convex`) |
| `Bm4/Copy.lean` | §6 | the bad-root data `BadRoot`, its positions and entries, and the shapes `ParForm` / `AncForm` in which the copied array's relations are described |
| `Bm4/Expand.lean` | Def. 5.1 | link between `expand` and the bad-root data `BadRoot` |
| `Bm4/Standard.lean` | Prop. 7.1, Rem. 7.2 | standardness invariant `standard_invariant`; official rule `expandOfficial` and `expandOfficial_eq_expand` |
| `Bm4/Label.lean` | Def. 18.1, Prop. 19.1 | `LabelSystem` interface, stable labels `Stable`, height descent `descent` |
| `Bm4/Main.lean` | Lemma 20.1, Thm 21.1, Thm 1.2, Prop. 22.1 | `stable_E`, `terminates`, `R_wf` |
| `Bm4/Compute.lean` | Def. 5.1 | computable `expandC` for testing against an external implementation (`test/compare.sh`) |

### The copy lemma (`Bm4/CopyPaper/`)

Theorem 6.3 is proved the way the paper does it: six mutually referring claims `(C1)`–`(C6)`,
one local lemma per claim, and the acyclic three-stage assembly of Proposition 6.11.

| file | paper | content |
|---|---|---|
| `Interval.lean` | Def. 6.1, Lemma 6.2 | interval-internal candidates `IntECand` and their parent lemmas; the six claims as predicates `Claim1`…`Claim6` |
| `L1.lean` | Lemma 6.4 | `(C1)ₖ` from `(C1)ₕ` for `h < k` |
| `L3.lean` | Lemma 6.5 | `(C3)ₖ` (`k < m₀`) from `(C1)ₖ` and `(C3)ₖ₋₁` |
| `L5.lean` | Lemma 6.6 | `(C5)ₖ` from `(C1)ₕ`, `(C5)ₕ` (`h < k`), `(C1)ₖ` and `(C3)ₖ` / `(C4)` |
| `L2.lean` | Lemma 6.7 | `(C2)ₖ` from `(C2)ₕ` (`h < k`), `(C1)ₖ`, `(C5)ₖ` and `(C3)ₖ` / `(C4)` |
| `L6.lean` | (6.16), Lemma 6.8 | the passing property; `(C6)ₖ` from `(C1)ₖ`, `(C5)ₖ` and `(C3)ₖ` / `(C4)` |
| `L4.lean` | Lemmas 6.9, 6.10 | `(C4)`, for `m₀ = 0` outright and for `m₀ > 0` from `(C3)_{m₀-1}`, `(C6)_{m₀-1}` |
| `Assemble.lean` | Prop. 6.11, Thm 6.3, Cor. 6.12 | the three stages, the six claims for every row, and the adjacent-copy corollary |
| `Char.lean` | Thm 6.3 | the interface the rest of the development uses — `anc_tA_iff`, `anc_tA_cases`, `hasParent_tA_of_parForm` — derived from the six claims |

A shorter proof of the same interface, by a single closed form for the parent and ancestor
relations (one induction on the row, no maximality of `m`, so no ranking argument), lives on the
branch `feature/closed-form` as `Bm4/CopyClosed.lean`. Exactly one of `CopyPaper/Char.lean` and
`CopyClosed.lean` is part of a build.

### Part III (`Bm4/SetTheory/`)

| file | paper | content |
|---|---|---|
| `Fm.lean` | §12 | formulas with named variables, satisfaction over a domain, Δ₀ absoluteness, Σ̂q/Π̂q, dualization, padding, merging |
| `Defin.lean` | §8–15 | shallow Lévy definability (`Delta0Def` / `SigmaDef` / `PiDef`) and its closure lemmas |
| `L.lean` | §9 | the constructible hierarchy `L` |
| `Adm.lean`, `HF.lean` | §10 | admissible ordinals, hereditarily finite sets, Δ₀-definable set operations |
| `Rel.lean` | — | relativization of formulas and of definable predicates |
| `Recur.lean`, `Recursion.lean` | §10 | Σ₁-collection and Σ₁-recursion along ordinals inside `L θ` |
| `BF.lean`, `BFConv.lean` | §12 | block formulas `BF`, the classes `BF.Sig` / `BF.Pi`, and their translation to `Fm` |
| `Code.lean`, `BFCode.lean` | §8, §12 | codes of formulas and of block formulas, Δ₀ recognizers |
| `CodeFV.lean` | §8, §11 | `NotFreeW`, a Δ₀ recognizer for "this variable is not free in the coded formula" |
| `SatCode.lean` | Def. 8.3, Lem. 8.4 | satisfaction codes, correctness, uniqueness, existence |
| `SatInL.lean` | Lem. 10.5(1) | satisfaction codes exist **inside** an admissible `L θ` |
| `LCode.lean`, `LCodeEx.lean` | Def. 9.1, Lem. 9.2, 10.5(2) | internal codes for the `L`-hierarchy, soundness and existence |
| `Blk.lean` | §12 | simultaneous block updates of assignments |
| `Truth.lean`, `TrCorrect.lean`, `BaseOK.lean` | §13 | the Δ₀ base of the truth predicates (Definition 13.2) and Lemma 13.3 |
| `Elem.lean` | §14 | `≺*q`, the finite-stage Tarski–Vaught criterion |
| `KPAx.lean`, `KPSat.lean`, `AdmKP.lean` | Def. 11.1, Lem. 11.2 | **the paper's** internal admissibility predicate: the KP axioms as codes (`KPAxCode`), their truth in `L θ`, and `AdmKP` with `admKP_iff` |
| `BlkP.lean` | §12 | block updates that **pad** the domain, as the paper prescribes |
| `BFCodeD.lean` | Def. 12.1 | code recognizers requiring the block variables to be **distinct**, as the paper prescribes |
| `TrP.lean`, `TrPV.lean`, `StRelP.lean`, `StKP.lean` | §13–15 | the truth predicates `Tr_{Σ̂q}` / `Tr_{Π̂q}` of Definition 13.4 (over §12's padded block update), Lemma 13.5 (complexity), Theorem 13.6 (correctness; `TrPV.lean` is its external-universe half), and `TV_q`, `St_k`, `Rel_k` with their correctness (Lemmas 15.3 and 15.5) |
| `StKP.lean` | Def. 15.2, 15.4, Lem. 15.3, 15.5 | `St_k` and `Rel_k` over the padded route, their complexity and correctness |
| `Omega1.lean`, `Skolem.lean`, `AdmTrans.lean` | §16 | countability of `L γ` below `ω₁`, admissibility of `ω₁`, the initial pair `L Λ ≺ L ω₁` |
| `Good.lean`, `Stable.lean` | §15 | the `GoodOrd` interface, admissible ordinals as labels, `◁ₖ` |
| `Reflect.lean` | §17, §18–22 | **Theorem 17.1** (finite pattern reflection), the `LabelSystem` instance, and the unconditional main theorems |

## Design notes

- `Arr r` is a pair `(len, col : ℕ → ℕ → ℕ)`. Parents and ancestors never read `len`, so
  Lemma 3.1 (prefix invariance) is the general `anc_congr_iff`: arrays agreeing on positions
  `≤ i` have the same ancestors of `i`.
- The copy lemma follows the paper: the six claims are proved by the local lemmas 6.4–6.10 and
  assembled by the stage order of Proposition 6.11, which is where the paper's lexicographic
  ranking `(0,k,·) < (1,0,0) < (2,k,·)` is discharged. `Bm4/CopyPaper/Char.lean` then reads the
  parent and ancestor relations of `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` off the claims, in the shapes `ParForm`
  and `AncForm` that `Expand.lean`, `Standard.lean` and `Label.lean` consume.
- Part III follows the paper: `Update` fills new slots with the value being written and
  assignments carry the appropriateness condition `Asn_A` of (8.4) (`SatCode.lean`); block
  updates pad the domain (`BlkP.lean`); the Σ̂q classes and their code recognizers require
  distinct block variables (`Fm.lean`, `BFCodeD.lean`); the truth predicates carry the `Form`
  guard of Definitions 13.2 and 13.4 (`Truth.lean`, `TrP.lean`); Lemma 15.3 is proved from the
  correctness of the truth predicate (`StRelP.lean`); and internal admissibility is the truth of
  the KP axioms at the empty assignment, the schema instances being recognized in universally
  closed form (`KPAx.lean`, `AdmKP.lean`).
- §12–§15 used to be formalized twice: once over a block update without the `∅` padding, and
  once the paper's way.  Injecting `sorry` confirmed that the main theorems never used the
  former, so it was deleted (`TV.lean`, the tail of `StRel.lean`, `TrSigS`/`TrPiS` of
  `Truth.lean`, `IsBlkUpd` of `Blk.lean`, `AdmP.lean` and `AdmPOK.lean`).  Only the paper's
  route remains.
- Theorem 21.1 is proved the paper's way — choice, ω-recursion and the least element of the set
  of label heights — and Proposition 22.1 is derived from Theorem 1.2, not reproved by induction
  on heights.
- `LabelSystem` bundles exactly what Part IV uses from Part III: a well-founded linear order of
  labels, relations `rel k` (`◁ₖ`, Lemma 15.1), an initial pair (Lemma 16.2), and finite pattern
  reflection bounded by a row count `r` (Theorem 17.1).

## Background taken as standard

The paper works inside ZFC and uses the standard theory of the constructible hierarchy,
admissible ordinals and the Lévy hierarchy. Most of that theory is *built here* rather than
imported: `L`, `IsAdmissible`, the Lévy classes, Δ₀-absoluteness, satisfaction codes, the
Tarski–Vaught criterion and the countability of `L γ` below `ω₁` all have their own files.

What is taken from Mathlib without proof, and where it is found in the literature:

| taken from Mathlib | used for | standard reference |
|---|---|---|
| `ZFSet` — a model of ZF | the whole of Part III | Jech, *Set Theory*, 3rd ed. |
| `Ordinal`, `Cardinal`, `Order.IsSuccLimit` | ordinals and limits throughout | Jech, ch. 2–3 |
| `Cardinal.isRegular_aleph_one` — `ω₁` is regular | Lemma 16.2 (`Omega1.lean`) | Jech, ch. 3 |
| `Cardinal.aleph 1`, `Cardinal.lt_aleph_one_iff` | Lemma 16.1 (`Omega1.lean`) | Jech, ch. 3 |
| `Ordinal.lsub` and its regularity bound | Lemma 16.2 | Jech, ch. 3 |
| `WellFounded`, `Acc`, `WellFoundedLT`, `Relation.TransGen` | Part V (`Main.lean`) | Jech, ch. 2 |
| `Classical.choice` | Theorem 21.1 and Proposition 22.1, as in the paper | — |

The background on admissible sets and KP that the paper assumes (Barwise, *Admissible Sets and
Structures*) is not imported: `Adm.lean`, `KPAx.lean` and `KPSat.lean` develop what is needed
from the definition. Likewise the model theory the paper assumes (Chang–Keisler, *Model
Theory*) — the finite-level Tarski–Vaught criterion is proved in `Elem.lean` and the Skolem hull
in `Skolem.lean`.

## Checking

```sh
lake exe cache get     # fetch the prebuilt Mathlib cache
lake build             # build everything, about 90 seconds
lake env lean Bm4/CopyPaper/Assemble.lean          # a single file
BMS=<external implementation> LEANPROJ=. test/compare.sh   # Def. 5.1 against it, 58 cases
```

To see which axioms the main theorems use:

```sh
echo 'import Bm4
#print axioms BM4.ST.terminates_unconditional
#print axioms BM4.ST.R_wf_unconditional' > Check.lean
lake env lean Check.lean
rm Check.lean
```
