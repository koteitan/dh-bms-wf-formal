[← Back](README.md) | [English](rule.md) | [Japanese](../rule.md)

# Working rules for diff/

Rules for writing `diff/P-xx.md`.

## 1. Section layout

```
# P-(proposition number): (title)

## The paper

### Statement
(the proposition number in the paper)
(the statement)

### Proof
(the proof as printed in the paper, quoted as it stands)

## Lean

### The statement in Lean
(the proposition Lean proves, written in MathJax rather than in the Lean language)

### The proof in Lean
(the Lean proof, written in MathJax rather than in the Lean language)

### Correspondence with Lean
(a table matching the formulas above to the Lean declarations. Lean identifiers may be
written here and nowhere else)

## Why it could not be written as in the paper
(the reason it could not be written as in the paper)
```

Do not change the wording or the nesting of the headings.

## 2. Do not write an outline (most important)

**What is wanted is not an outline but the detail of the proof.**

When turning a Lean proof into formulas, do not write only a summary of the shape "the proof
here goes roughly like this" and drop the details. Turn every small formula written in Lean
into mathematics, so that the result can be **matched against the proof in the paper line by
line**.

### Bad example

> Apply Lemma 8.4 to obtain the correctness of the satisfaction code. By $\Delta_0$
> absoluteness it also holds externally, so the equivalence of the positive form follows.
> The negative form is the same.

Which lemma was applied to what, which set was taken, and from which inclusion absoluteness
follows are all missing.

### Good example

> Take a transitive set $A$ containing the range of $a$. Concretely, let $\rho$ be an ordinal
> with $\omega + 1 < \rho < \theta$ and $\rho + 1 < \theta$, and put $A = L_\rho$. Then $A$ is
> transitive, $\mathrm{ran}(a) \subseteq A$, and $A \in L_{\rho+1} \subseteq W$. Next apply
> Lemma 10.5(1) inside $W$ to $A$ and take $U, T \in W$ with
> $W \models \mathrm{SatCode}(A,U,T)$. Since $\mathrm{SatCode}$ is $\Delta_0$ and $W$ is
> transitive, $\Delta_0$ absoluteness gives $\mathrm{SatCode}(A,U,T)$ externally as well.
> Lemma 8.4 then gives $\langle e,a\rangle \in T \iff (A,\in) \models \delta[a]$. …

### Asymmetry in length is allowed

If the proof in the paper is three lines and the Lean proof is two hundred, then **write two
hundred lines' worth of content on the Lean side**. "The paper is short, so Lean should be
short" is wrong. The purpose of these pages is to show the differences, so the more something
differs, the more detail it gets.

Conversely, where the paper and Lean run along the same line, it is enough to write "the same
as the paper" and be brief. But state explicitly how far they agree and where they part.

## 3. Do not write Lean code (with one exception, the last section)

"The statement in Lean" and "The proof in Lean" are written in mathematics. Write neither Lean
identifiers nor file names. When a name is needed, use the notation of the paper, or, if the
paper has none, a plain descriptive name.

- Bad: $\mathrm{IsCodeW}\ h\ w\ e$
- Good: $\mathrm{Form}(e)$, or "the well-formedness test"

**The one exception is the section "### Correspondence with Lean".** Identifiers and file
names go there. Formulas alone do not tell the reader where to look in Lean, so one
correspondence table is placed at the end.

### How to write "Correspondence with Lean"

Make a table with the **names of the formulas** that appeared in the two sections above on the
left and the corresponding Lean declarations on the right, in the order they appeared.

| Formula | Lean | File |
|---|---|---|
| $\mathrm{Form}(e)$ | `IsCodeW h w e` | `Bm4/SetTheory/Code.lean` |
| $\mathrm{Last}(s) = e$ | `IsLastW w s e` | same |
| $\mathrm{Form}$ is $\Delta_0$ | `delta0_isCodeW` | same |
| $\mathrm{Form}(e) \iff \exists\varphi\,(e = \ulcorner\varphi\urcorner)$ | `isCodeW_iff` | same |

- Write the file as a path relative to `lean/`.
- **Do not write line numbers.** They go stale at once.
- A lemma used only inside the proof still goes in the table if its name appears in the
  description of the proof.
- For a formula with no counterpart, write "none" on the right, and say why there is none
  under "Why it could not be written as in the paper".

## 4. Quote the paper as it stands

As "the proof as printed in the paper, quoted as it stands" says, do not summarize. Where the
paper omits something, leave it omitted, and make clear that what fills the gap is on the Lean
side.

Transcribe the formulas into MathJax in the notation of the paper. Do not substitute symbols
(do not turn $\hat\Sigma_q$ into $\Sigma_q$, or $\prec^*_q$ into $\prec_q$).

### Do not use `>` for the quotation

Do not use the Markdown blockquote (`>` at the start of a line). Write the text plainly. The
whole of the `## The paper` section is the paper, so there is no need to mark it off.

- Bad:

```
> A derivation of a well-formed formula is a finite sequence $s$ of naturals each of whose
> terms is an atomic formula code of (8.1), or
>
> $$\mathrm{Form}(e) \ :\Longleftrightarrow\ \exists s \in \omega\ (\cdots)$$
>
> is the definition.
```

- Good:

```
A derivation of a well-formed formula is a finite sequence $s$ of naturals each of whose
terms is an atomic formula code of (8.1), or

$$\mathrm{Form}(e) \ :\Longleftrightarrow\ \exists s \in \omega\ (\cdots)$$

is the definition.
```

## 5. Do not write the history of the audit

The reader wants only two things: **the difference between the current Lean and the paper**,
and **why it still cannot be written as in the paper**. The route that led there is not
written.

Not written:

- references to audit numbers such as "the point raised in audit U-30 had two parts" or
  "U-48 is resolved"
- change history such as "it used to be …", "it was changed to …", "… was newly added"
- a section named "what has been resolved"
- work status such as "not started", "reverted", "postponed"

Written:

- what the current Lean does and where it differs from the paper
- why that difference cannot be removed (a structural obstacle), or what work removing it
  would take and how large that work is

For an item where the difference is gone, simply write "written as in the paper". Do not write
what was fixed or how.

## 6. When there is no counterpart, say so

For something in the paper with no counterpart in Lean, write "no counterpart" explicitly and
say what stands in its place instead. Do not paper over the gap with "in substance this
corresponds to it".

## 7. When a proposition has several parts

A proposition split into (1)(2)(3), such as Lemma 10.4, is written part by part on both the
paper side and the Lean side. The state of the parts (resolved, partial, open) can differ, so
do not merge them.

## 8. Update the table of contents

When a page is added or renamed, fix the table of contents in [README.md](README.md) and the
correspondence table in [plan/U2P.md](../../plan/U2P.md) at the same time.

## 9. What may be mentioned

Do not mention the name or the content of any file outside this repository. Do not mention
anything under `tmp/` either. Refer to the paper only as "the paper".

## 10. Notation

Follow the notation of the paper.

| Meaning | Notation |
|---|---|
| the constructible hierarchy | $L_\xi$ |
| admissible ordinals | $\theta,\ \eta,\ \xi$ |
| the alternating block hierarchy | $\hat\Sigma_q,\ \hat\Pi_q$ |
| alternating block elementarity | $M \prec^*_q N$ |
| the stability relation | $\alpha \lhd_k \beta$ |
| a code | $\ulcorner \varphi \urcorner$ |
| an ordered pair | $\langle x, y \rangle$ |
| relativization | $\varphi^M$ |
