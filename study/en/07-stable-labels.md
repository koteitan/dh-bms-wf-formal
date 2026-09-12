[← Back](README.md) | [English](07-stable-labels.md) | [Japanese](../07-stable-labels.md)

# Stable labels and height descent (Part IV)

Prerequisites

| Note | Terms used from it |
|---|---|
| [The strict alternating block hierarchy and the stability relation](04-alternating-blocks.md) | **$`\lhd_k`$ (3.1)**, transitivity in Lemma 15.1(2) |
| [Finite pattern reflection (Theorem 17.1)](06-finite-reflection.md) | **(17.1)–(17.4) of Theorem 17.1 (3.1)** |

The prerequisites of those two notes are needed as well.

## 0. What is used from Parts I and II

Part IV is written in combinatorial language. Only what is used is listed here; the proofs are
in Parts I and II of the paper.

### 0.1 Arrays, parents, ancestors

An **array** with $`r`$ rows and length $`\ell`$ is
$`A = (A_0, \dots, A_{\ell-1}) \in (\mathbb{N}^r)^\ell`$. We write $`A_i(k)`$ for the $`k`$-th
component of the $`i`$-th column, and set the position set to
$`\mathrm{Pos}(A) = \{0, \dots, \ell-1\}`$.

**Definition 2.1.** Let $`i \in \mathrm{Pos}(A)`$ and $`k \lt r`$. We say $`j \lt i`$ is a
**structural $`k`$-parent candidate** of $`i`$ if, for $`k = 0`$, simply $`j \lt i`$, and for
$`k \gt 0`$, $`j`$ is a strict $`(k-1)`$-ancestor of $`i`$. A structural candidate further
satisfying $`A_j(k) \lt A_i(k)`$ is called a **valid candidate**. If the valid candidates have
a greatest column index, that index is the **$`k`$-parent** of $`i`$.

$`j \prec^A_k i`$ means that $`j`$ is reached from $`i`$ by following parents finitely many
times. $`j \preceq^A_k i`$ means $`j = i`$ or $`j \prec^A_k i`$.

**The parts of Lemma 2.2 that are used.**

1. If $`j \prec^A_k i`$ then $`j \lt i`$ and $`A_j(k) \lt A_i(k)`$
2. If $`h \lt k`$ and $`j \prec^A_k i`$ then $`j \prec^A_h i`$
3. If $`u, v`$ are both $`k`$-ancestors of $`w`$ and $`u \lt v`$ then $`u \prec^A_k v`$

### 0.2 Expansion (Definition 5.1)

If $`\ell = 0`$ then $`A[N] = A`$. Let $`\ell \gt 0`$, write $`c = \ell-1`$ for the index of the
last column and $`C = A_c`$ for that column.

If $`c`$ has no parent in any row, then $`A[N]`$ is the prefix $`A \restriction c`$ obtained by
deleting $`C`$.

If $`c`$ has a parent, write $`m_0`$ for its **greatest parent row**, $`p`$ for the
$`m_0`$-parent of $`c`$ and $`P = A_p`$ for that column.

```math
G = (A_0, \dots, A_{p-1}), \qquad
B_0 = (A_p, \dots, A_{\ell-2}) = (D_0, \dots, D_{s-1})
```

where $`D_0 = P`$ and $`s = \ell - 1 - p`$. Since $`p \prec^A_{m_0} c`$, we have
$`\Delta_k = C(k) - P(k) \gt 0`$ for $`k \lt m_0`$.

For $`k \lt m_0`$, we say $`D_j`$ **rises** if $`p \preceq^A_k (p+j)`$ holds. For
$`q = 0, \dots, N`$ define the copies $`B_q = (D_0^{(q)}, \dots, D_{s-1}^{(q)})`$ by

```math
D_j^{(q)}(k) =
\begin{cases}
D_j(k) + q\Delta_k & (k \lt m_0 \text{ and } D_j \text{ rises}) \cr
D_j(k) & (\text{otherwise})
\end{cases}
```

and put $`A[N] = G \frown B_0 \frown \cdots \frown B_N`$. This operation does not change the
number of rows $`r`$.

### 0.3 Prefix invariance (Lemma 3.1)

For two positions belonging to a prefix $`A \restriction m`$, the $`k`$-parent and
$`k`$-ancestor relations are the same whether computed in the prefix or in the whole array.

### 0.4 The copy lemma (Theorem 6.3)

It rewrites the ancestor relation in $`A[N]`$ in terms of the relation in the original array
$`A`$. Part IV uses the following three together with one corollary. A $`\prec_k`$ without a
superscript denotes the relation in $`A[N]`$.

```math
\text{(C1)} \qquad D_i^{(q)} \prec_k D_j^{(q)} \iff D_i^{(0)} \prec^A_k D_j^{(0)}
```
```math
\text{(C2)} \qquad \text{for } E \in G, \quad E \prec_k D_j^{(q)} \iff E \prec^A_k D_j^{(0)}
```
```math
\text{(C6)} \qquad \text{for } 0 \le a \lt b \lt N, \quad
D_i^{(a)} \prec_k D_j^{(b)} \iff D_i^{(a)} \prec_k D_j^{(b+1)}
```

**Corollary 6.12 (ancestors crossing adjacent copies).** If
$`D_i^{(q)} \prec_k D_j^{(q+1)}`$ then

```math
k \lt m_0, \qquad D_i^{(0)} \prec^A_k C, \qquad P \preceq^A_k D_j^{(0)} . \tag{6.24}
```

## 1. Stable labels (Definition 18.1)

**Definition.** Let $`A`$ be an array with $`r`$ rows and length $`\ell`$. A **stable label**
is a function on the positions of the columns,

```math
f : \{0, \dots, \ell-1\} \longrightarrow \mathrm{Ord}
```

satisfying the following three conditions.

1. Each $`f(i)`$ is an admissible ordinal
2. If $`i \lt j`$ then $`f(i) \lt f(j)`$
3. If $`i \prec^A_k j`$ then $`f(i) \lhd_k f(j)`$

The empty array is assigned the empty function.

**Meaning.** An admissible ordinal is attached to each column position of the array, and the
order of the positions and the parent-child relation are translated into the order of the
ordinals and the stability relation $`\lhd_k`$. Condition 3 is the point of contact with Part
III.

Even if the same column vector occurs at two positions, those two positions carry separate
labels. So one never writes $`f(C)`$; a label is always specified by a column position.

## 2. Height

**Definition.** If $`A`$ is nonempty, then

```math
\mathrm{ht}(f) = f(\ell-1)
```

is called the **height** of $`f`$. It is the label of the last column position.

By condition 2, the height is the largest of the values of $`f`$.

## 3. Proposition 19.1 (height descent)

### 3.1 Statement

Let a nonempty array $`A`$ with a fixed number of rows $`r`$ have a stable label $`f`$. For any
$`N \in \mathbb{N}`$, if $`A[N]`$ is nonempty then it has a stable label $`g`$ with

```math
\mathrm{ht}(g) \lt \mathrm{ht}(f) . \tag{19.1}
```

That is, one expansion in the sense of Definition 5.1 strictly lowers the height of a stable
label.

Below put $`c = \ell-1`$, $`C = A_c`$ and $`\beta = f(c) = \mathrm{ht}(f)`$.

### 3.2 Case 1: C has no parent in any row

In this case $`A[N] = A \restriction c`$. By Lemma 3.1, the parent and ancestor relations
remaining in the prefix are the same as in the original $`A`$, so $`f \restriction c`$ is a
stable label. If the prefix is nonempty, its last position is smaller than $`c`$, so by
condition 2 the height is smaller than $`f(c) = \beta`$.

### 3.3 Case 2: the setting

Suppose the greatest parent row $`m_0`$ exists. Using the notation of 0.2, set the labels by
position to be

```math
\alpha = f(p), \qquad y_i = f(p+i) \quad (0 \le i \lt s).
```

From $`p \lt p+1 \lt \cdots \lt p+s-1 \lt c`$ and condition 2,

```math
\alpha = y_0 \lt y_1 \lt \cdots \lt y_{s-1} \lt \beta . \tag{19.2}
```

Also $`p \prec^A_{m_0} c`$, so condition 3 gives

```math
\alpha \lhd_{m_0} \beta . \tag{19.3}
```

This is what the hypothesis of Theorem 17.1 amounts to.

### 3.4 The inductive construction

For $`q = 0, \dots, N`$ put

```math
A_q = G \frown B_0 \frown \cdots \frown B_q .
```

Construct a stable label $`f_q`$ on $`A_q`$ satisfying the following two invariants.

| | Invariant |
|---|---|
| (I1) | the label of the $`i`$-th column of the last copy $`B_q`$ is $`y_i`$ |
| (I2) | every column before $`B_q`$ has a label smaller than $`\alpha`$ |

**When $`q = 0`$:** $`A_0 = A \restriction c`$. By Lemma 3.1, $`f_0 = f \restriction c`$ is a
stable label. The labels of $`B_0`$ are $`y_i`$ by definition, and $`G`$ lies before position
$`p`$, so by condition 2 all its labels are smaller than $`f(p) = \alpha`$.

**From $`q`$ to $`q+1`$:** let the set of labels occurring before $`B_q`$ be

```math
X = \{\, f_q(u) : u \text{ a position before } B_q \,\}.
```

This is a finite set of admissible ordinals, and (I2) gives $`X \subseteq \alpha`$. Also

```math
Y = \{y_0 \lt \cdots \lt y_{s-1}\} \subseteq [\alpha, \beta)
```

is a nonempty finite set of admissible ordinals. By $`m_0 \lt r`$ and (19.3), Theorem 17.1 can
be applied with

```math
n = m_0, \qquad (\alpha, \beta, X, Y).
```

The result is admissible ordinals $`y'_0, \dots, y'_{s-1}`$ satisfying

```math
y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha \tag{19.4}
```

and

```math
\max(X \cup \{\omega\}) \lt y'_0 \tag{19.5}
```

and moreover (17.2)–(17.4). Define the function $`f_{q+1}`$ on $`A_{q+1}`$ as follows.

1. Before $`B_q`$, keep the same values as $`f_q`$
2. Change the label of the $`i`$-th column of $`B_q`$ from $`y_i`$ to $`y'_i`$
3. Assign the original value $`y_i`$ to the $`i`$-th column of the new $`B_{q+1}`$

The construction is: **push down, and put the original values back in the space that was
freed**.

### 3.5 Strict increase

We check condition 2.

| Interval | Ground |
|---|---|
| last before $`B_q`$ $`\to`$ head of $`B_q`$ | $`\max X \lt y'_0`$ by (19.5) |
| inside $`B_q`$ | $`y'_0 \lt \cdots \lt y'_{s-1}`$ of (19.4) |
| end of $`B_q`$ $`\to`$ head of $`B_{q+1}`$ | $`y'_{s-1} \lt \alpha`$ of (19.4) and $`\alpha = y_0`$ |
| inside $`B_{q+1}`$ | $`y_0 \lt \cdots \lt y_{s-1}`$ of (19.2) |

It increases strictly throughout. The new last copy carries $`y_i`$, so (I1) holds, and every
earlier label is below $`\alpha`$, so (I2) holds too.

### 3.6 The six cases of the ancestor condition

What remains is condition 3. An ancestor always lies to the left of its target column. Splitting
on the positions of the target column and the ancestor, the following six cases are exhaustive.

| | Position of the ancestor | Position of the target | Result used |
|---|---|---|---|
| (a) | inside $`A_q`$ | before $`B_q`$ | Lemma 3.1 |
| (b) | inside $`A_q`$ | the old last copy $`B_q`$ | (17.2), (17.3) |
| (c) | the new $`B_{q+1}`$ | the new $`B_{q+1}`$ | (C1) |
| (d) | $`G`$ | the new $`B_{q+1}`$ | (C2) |
| (e) | $`B_a`$ ($`a \lt q`$) | the new $`B_{q+1}`$ | (C6) and Lemma 3.1 |
| (f) | the old last copy $`B_q`$ | the new $`B_{q+1}`$ | Corollary 6.12 |

**(a).** Both the target column and its ancestor lie in the prefix $`A_q`$, before $`B_q`$.
Since $`A_q`$ is a prefix of $`A_{q+1}`$, Lemma 3.1 says the ancestor relation is unchanged,
and the labels were not changed either. The stability of $`f_q`$ applies as it stands.

**(b).** Let the target be $`D_j^{(q)}`$. The target and all its ancestors belong to $`A_q`$,
so by Lemma 3.1 the ancestor relation in $`A_{q+1}`$ is identical with the one in $`A_q`$.

- if the ancestor lies before $`B_q`$ and its current label is $`x \in X`$, then stability of
  $`f_q`$ gives $`x \lhd_k y_j`$, and (17.2) preserves this as $`x \lhd_k y'_j`$
- if the ancestor is $`D_i^{(q)}`$ inside $`B_q`$, then stability before the change gives
  $`y_i \lhd_k y_j`$, and (17.3) gives $`y'_i \lhd_k y'_j`$

**(c).** Let $`D_i^{(q+1)} \prec_k D_j^{(q+1)}`$. Applying (C1) to the array $`A_{q+1}`$ with
$`q+1`$ copies gives $`D_i^{(0)} \prec^A_k D_j^{(0)}`$. The original stable label $`f`$ gives
$`y_i \lhd_k y_j`$, and the labels of the new copy are $`y_i, y_j`$, so the required relation
holds.

**(d).** Take $`E \in G`$ with $`E \prec_k D_j^{(q+1)}`$. (C2) gives
$`E \prec^A_k D_j^{(0)}`$. The labels of $`G`$ and of the new copy are the same as in the
original $`f`$, so the original stability applies as it stands.

**(e).** Let $`D_i^{(a)} \prec_k D_j^{(q+1)}`$. Applying (C6) with $`q+1`$ copies and $`b = q`$
gives $`D_i^{(a)} \prec_k D_j^{(q)}`$. Both columns belong to the prefix $`A_q`$, so by Lemma
3.1 this is equivalent to the relation in $`A_q`$. Applying the stability of $`f_q`$ and
writing $`z`$ for the current label of the ancestor gives $`z \lhd_k y_j`$. The labels of
$`B_a`$ are not changed at this stage and the new target's label is $`y_j`$, so the required
relation holds.

**(f).** Let $`D_i^{(q)} \prec_k D_j^{(q+1)}`$. Corollary 6.12 gives

```math
k \lt m_0, \qquad D_i^{(0)} \prec^A_k C, \qquad P \preceq^A_k D_j^{(0)} . \tag{19.10}
```

The first ancestor relation together with the stability of the original $`f`$ gives

```math
y_i \lhd_k \beta . \tag{19.11}
```

Since $`k \lt m_0 = n`$, applying (17.4) of Theorem 17.1 to (19.11) gives

```math
y'_i \lhd_k \alpha . \tag{19.12}
```

- if $`j = 0`$, the new target's label is $`y_0 = \alpha`$, and (19.12) is exactly the required
  relation
- if $`j \gt 0`$, then $`P`$ and $`D_j^{(0)}`$ are different positions, so the last, non-strict
  relation in (19.10) is strict. The original stability gives $`\alpha \lhd_k y_j`$. Joining
  this with (19.12) by the transitivity of Lemma 15.1(2) gives $`y'_i \lhd_k y_j`$

These six cases show that $`f_{q+1}`$ is a stable label.

### 3.7 Conclusion

Finite induction on $`q`$ gives $`f_N`$. By (I1), the labels of the last copy $`B_N`$ are
always $`y_0, \dots, y_{s-1}`$, so (19.2) gives

```math
\mathrm{ht}(f_N) = y_{s-1} \lt \beta = \mathrm{ht}(f) .
```

$`\square`$

## 4. Remark 19.2

Organizing the parts of the copy lemma used in the inductive step:

| Placement of the ancestor | Result used |
|---|---|
| inside the new copy | (C1) |
| from $`G`$ to the new copy | (C2) |
| from a copy two or more back to the new copy | (C6) and prefix invariance |
| between adjacent copies | Corollary 6.12, hence (C1), (C3), (C4), (C5) |

In the proof of Proposition 19.1 the copy lemma is used only after Theorem 6.3 is established.
So the dependence between the two is one-way.

## 5. How it is used in the paper

| Place | Use |
|---|---|
| Definition 18.1 | stable labels |
| Proposition 19.1 | one expansion strictly lowers the height |
| Lemma 20.1 | build a stable label for $`E_r`$ from the $`\Lambda, \Theta`$ of (16.2) |
| Theorem 21.1 | no infinite descending sequence of heights, hence no infinite expansion sequence |
| Theorem 1.2 | termination |
| Proposition 22.1 | well-foundedness of the expansion relation |

## 6. Correspondence in Lean

| Concept | Lean | File |
|---|---|---|
| array | `Arr r` | `Bm4/Defs.lean` |
| $`k`$-parent | `parent A k j i` | same |
| $`j \prec^A_k i`$ | `anc A k j i` | same |
| $`j \preceq^A_k i`$ | `ancEq A k j i` | same |
| Lemma 2.2(1) | `anc_lt_and_val_lt` | `Bm4/Basic.lean` |
| Lemma 3.1 | `anc_congr_iff` | same |
| the label interface | `LabelSystem` | `Bm4/Label.lean` |
| Definition 18.1 | `Stable S A f` | same |
| height | `ht A f` | same |
| condition 2 of Definition 18.1 | `Stable.mono` | same |
| condition 3 of Definition 18.1 | `Stable.rel` | same |
| 3.2 (Case 1) | `descent_drop` | same |
| Lemma 3.1 for $`A_q`$ | `anc_Aq_iff` | same |
| (I1), (I2) | `Inv` | same |
| $`q = 0`$ in 3.4 | `inv_zero` | same |
| $`q \to q+1`$ in 3.4 | `inv_succ` | same |
| the six-case split of 3.6 | `region_cases` | same |
| the finite induction of 3.7 | `inv_exists` | same |
| Proposition 19.1 | `descent` | same |
| the interface for (C1), (C2), (C6) and Corollary 6.12 | `Bm4/CopyPaper/Char.lean` | same |
