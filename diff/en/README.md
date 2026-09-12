[← Back](../../README_en.md) | [English](README.md) | [Japanese](../README.md)

# Formalization differences

For each proposition of the paper, a page that puts side by side **the statement and proof in
the paper**, **the statement and proof in Lean**, and **the reason it could not be written
exactly as in the paper**. No Lean code is shown; everything is written in mathematical
notation.

The writing rules are fixed in [rule.md](rule.md).
The correspondence between the places listed in
[plan/fidelity-audit-fix.md](../../plan/fidelity-audit-fix.md) and the propositions is in
[plan/U2P.md](../../plan/U2P.md).

## Contents

| P | Proposition in the paper | Section |
|---|---|---|
| [P-01](P-01.md) | (8.2) the well-formedness code $\mathrm{Form}(e)$ | §8 |
| [P-02](P-02.md) | (8.3) the graph $G_F$ of a syntactic operation | §8 |
| [P-03](P-03.md) | Definition 9.1 the $L$-hierarchy code | §9 |
| [P-04](P-04.md) | opening of §10, $\mathrm{KP}$ and admissible ordinals | §10 |
| [P-05](P-05.md) | Corollary 10.2 functional $\Sigma_1$-Replacement | §10 |
| [P-06](P-06.md) | Lemma 10.3 $\Sigma_1$-recursion on the ordinals in $\mathrm{KP}$ | §10 |
| [P-07](P-07.md) | Lemma 10.4 finite codes and closure inside $\mathrm{KP}$ | §10 |
| [P-08](P-08.md) | Lemma 10.5 satisfaction codes and $L$-codes inside $\mathrm{KP}$ | §10 |
| [P-09](P-09.md) | Definition 11.1 the $\hat\Sigma_1$ form of admissibility | §11 |
| [P-10](P-10.md) | Lemma 12.2 safe syntactic operations | §12 |
| [P-11](P-11.md) | Lemma 13.3 correctness of $\Delta_0$ truth | §13 |
| [P-12](P-12.md) | Definition 13.4 the partial truth predicate | §13 |
| [P-13](P-13.md) | Definition 14.2 the Tarski–Vaught formula | §14 |
| [P-14](P-14.md) | Lemma 15.5 correctness of $\mathrm{Rel}_k$ | §15 |

## Roots of the differences

Almost every difference reduces to one of three roots.

| Root | Content | P |
|---|---|---|
| **B** | The medium of coding. The paper takes codes to be natural numbers and pairs them with the Cantor pairing function $\pi$, whereas Lean takes hereditarily finite sets with Kuratowski pairs, that is, elements of $L_\omega$ | P-01, P-02, P-03, P-09 |
| **C** | The absence of $\mathrm{KP} \vdash$. Section 10 of the paper makes the syntactic claim "$\mathrm{KP}$ proves the following", but Lean has no proof system, so the semantic claim "inside $L_\theta$ for admissible $\theta$" is used instead | P-04, P-05, P-06, P-07, P-08, P-14 |
| **D** | The absence of function symbols. The paper writes a $\Delta_0$-definable function in term position, whereas Lean writes it as a relation and quantifies the output | P-10, P-12 |

P-13 belongs to none of the roots; it is an isolated difference. P-11 is written exactly as in
the paper, and only the difference in the line of the proof is recorded.
