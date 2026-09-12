[← Back](README.md) | [English](05-truth-predicates.md) | [Japanese](../05-truth-predicates.md)

# Partial truth predicates and finite-level Tarski–Vaught

Prerequisites

| Note | Terms used from here |
|---|---|
| [The constructible hierarchy L](01-constructible-hierarchy.md) | formula, structure $`(X,\in)`$, assignment $`\bar a`$, satisfaction $`\models`$, transitive, $`L_\xi`$ |
| [The Levy hierarchy and absoluteness](02-levy-hierarchy.md) | bounded quantifier, block, $`\Delta_0`$, $`\Delta_0`$ absoluteness |
| [KP and admissible ordinals](03-kp-admissible.md) | KP, admissible ordinal, $`\mathrm{SatCode}`$, $`\mathrm{LCode}`$, code, $`\langle e, a \rangle`$ |
| [The strict alternating block hierarchy and the stability relation](04-alternating-blocks.md) | **$`\hat\Sigma_q`$, $`\hat\Pi_q`$ (1.1)**, matrix, padding and finite combination (1.5), $`\prec^*_q`$, $`\lhd_k`$ |

## 1. Why partial truth predicates are needed

### 1.1 The aim of this note

**What we want to show.** Theorem 17.1 of the next note is roughly this claim.

> Finitely many admissible ordinals $`Y`$ lying in $`[\alpha, \beta)`$ can be replaced by $`Y'`$ below
> $`\alpha`$ with the $`\lhd`$ relations preserved.

This $`Y'`$ is what is used to lower the height of the stable labels (stable-label note 3.4).
The problem is how to show that such a $`Y'`$ exists.

**The only thing available as a hypothesis is $`\alpha \lhd_n \beta`$.** As in 3.1 of the
alternating-block note, this is $`L_\alpha \prec^*_{n+2} L_\beta`$, that is,

```math
\text{for sentences } \varphi \text{ of complexity } \hat\Sigma_{n+2} \text{ or below} \quad
L_\beta \models \varphi \iff L_\alpha \models \varphi
```

It is an equivalence about sentences, and it says nothing else.

**So the procedure is forced.** To use this equivalence one has no choice but the following four steps.

1. Write down what we want to show as a $`\hat\Sigma_{n+2}`$ sentence $`\varphi`$
2. Check $`L_\beta \models \varphi`$
3. Get $`L_\alpha \models \varphi`$ from the equivalence
4. Take the witnesses of $`\varphi`$ in $`L_\alpha`$ as $`Y'`$

What has to be written down is

```math
\exists u_0 \cdots \exists u_{s-1}\ \bigl(u_0, \dots, u_{s-1}
\text{ are admissible and the } \lhd \text{ relations are as follows}\bigr)
```

Unless the content of these parentheses can be written as a formula of the language $`\{\in\}`$, the
existence of $`Y'`$ cannot be derived even with $`\alpha \lhd_n \beta`$ as a hypothesis.

**What is missing for writing the content.** That sentence contains conditions of the form
"$`u \lhd_k v`$". The definition of $`\lhd_k`$ is

```math
u \lhd_k v \quad\iff\quad L_u \prec^*_{k+2} L_v
\quad\iff\quad \text{the truth values of } \hat\Sigma_j \text{ formulas agree in } L_u \text{ and } L_v
```

so we have to express the truth of **both** $`L_u`$ and $`L_v`$ inside $`L_\beta`$, the place where
the sentence is written. Here the partner $`v`$ comes in two kinds.

| partner $`v`$ | $`L_v`$ inside $`L_\beta`$ | how to express truth inside $`L_v`$ |
|---|---|---|
| an ordinal inside $`L_\beta`$ | **is a set** | expressible by $`\mathrm{SatCode}`$ of KP note §7 |
| $`\beta`$ itself | **is not a set** | not expressible by $`\mathrm{SatCode}`$ |

From $`L_\beta \cap \mathrm{Ord} = \beta`$ (constructible hierarchy note §9) we get
$`\beta \notin L_\beta`$, hence $`L_\beta \notin L_\beta`$. A universe cannot be a set inside itself.
**Only when the partner is "the universe we are in itself" is it inexpressible by
$`\mathrm{SatCode}`$.**

Why conditions of that form are needed is seen in 3.3 of the finite-row-reflection note. It is exactly
because they have that form that $`\beta`$ gets replaced by $`\alpha`$ in Theorem 17.1.

**This note builds a way to express the inexpressible side.** That is, it provides something saying

> $`\varphi_e[a]`$ is true in the universe I am in now

There are two straightforward approaches, and neither works.

| Approach | Result | Where discussed |
|---|---|---|
| hold it as a set (the way $`\mathrm{SatCode}`$ does) | unusable, because the universe is not a set | 1.2 |
| write it as a single formula | unusable, by Tarski's undefinability of truth | 1.3 |
| make a separate formula for each alternation count $`q`$ | this is the one we take | 1.4 |

1.2 and 1.3 rule out separate approaches; neither reinforces the other.
It is because both fail that the shape in 1.4 is forced.

### 1.2 Why SatCode is not enough

In §7 of the KP and admissible ordinals note, satisfaction for a set $`A`$ could be held as a set $`T`$.

```math
\langle e, a \rangle \in T \quad\iff\quad (A, \in) \models \varphi_e[a]
```

This was possible because $`A`$ is a set and the recursion for satisfaction over it could be written down
as a collection of finitely many pairs. The universe is not a set, so the same move is unavailable.

### 1.3 Tarski's undefinability of truth

It cannot be written as a single formula. Suppose there were a single formula $`\mathrm{Tr}`$ with

```math
\mathrm{Tr}(e, a) \quad\iff\quad \varphi_e[a] \text{ is true}
```

for all formula codes $`e`$ and assignments $`a`$. Then diagonalization produces a sentence saying
"I am false", a contradiction. It has the same shape as the liar paradox.

### 1.4 The way out: cut by alternation count

We cannot put everything into one formula, but **fixing the alternation count makes it writable**.
For each $`q`$ we build separate formulas

```math
\mathrm{Tr}_{\hat\Sigma_q}, \qquad \mathrm{Tr}_{\hat\Pi_q}
```

These are the **partial** truth predicates. Why there is no contradiction is seen in 3.3.

$`\hat\Sigma_q`$ and $`\hat\Pi_q`$ are the strict alternating block hierarchy defined in 1.1 of the
alternating-block note (the paper, Definition 12.1).

### 1.5 Three kinds of truth

| Truth of what | How written | Where |
|---|---|---|
| truth inside a set $`A`$ | a **set** $`T`$ ($`\mathrm{SatCode}`$) | KP note §7 |
| $`\Delta_0`$ truth of the whole universe | **formulas** $`\mathrm{Tr}^+_{\Delta_0}`$, $`\mathrm{Tr}^-_{\Delta_0}`$ | the paper, Definition 13.2 |
| $`\hat\Sigma_q`$ truth of the whole universe | **formulas** $`\mathrm{Tr}_{\hat\Sigma_q}`$, $`\mathrm{Tr}_{\hat\Pi_q}`$ | the paper, Definition 13.4 |

The bottom two are formulas, not sets. That is the difference from $`\mathrm{SatCode}`$.

## 2. Positive and negative representations of Δ₀ truth

### 2.1 Definition 13.2

Let $`\mathrm{Asn}_A(e,a)`$ be the $`\Delta_0`$ predicate "$`a`$ is an $`A`$-valued assignment covering all
free variables of $`e`$" (the paper, (8.4)).

**Positive representation.** $`\mathrm{Tr}^+_{\Delta_0}(e, a)`$ holds when $`e`$ is a $`\Delta_0`$ formula
code and **there exist** $`A, U, T`$ with

```math
A \text{ is transitive} \ \wedge\ \mathrm{Asn}_A(e,a) \ \wedge\ a \in U
\ \wedge\ \mathrm{SatCode}(A,U,T) \ \wedge\ \langle e,a \rangle \in T
```

**Negative representation.** $`\mathrm{Tr}^-_{\Delta_0}(e, a)`$ holds when $`e`$ is a $`\Delta_0`$ formula
code and **for all** $`A, U, T`$

```math
\bigl(A \text{ is transitive} \wedge \mathrm{Asn}_A(e,a) \wedge a \in U \wedge \mathrm{SatCode}(A,U,T)\bigr)
\ \Longrightarrow\ \langle e,a \rangle \in T
```

**How to read them.** Both say "take a transitive $`A`$ containing all values of $`a`$ and look at the
truth value there". The positive one says "there is at least one such $`A`$ and it is true there"; the
negative one says "it is true in all such $`A`$".

### 2.2 Complexity (13.1)

**Definition (matrix).** What remains after removing the leading quantifier block from each of the two
predicates of 2.1 is called the **matrix** of that predicate (alternating-block note 1.1). Written out,
they are as follows.

The matrix of $`\mathrm{Tr}^+_{\Delta_0}`$.

```math
A \text{ is transitive} \ \wedge\ \mathrm{Asn}_A(e,a) \ \wedge\ a \in U
\ \wedge\ \mathrm{SatCode}(A,U,T) \ \wedge\ \langle e,a \rangle \in T
```

The matrix of $`\mathrm{Tr}^-_{\Delta_0}`$.

```math
\bigl(A \text{ is transitive} \wedge \mathrm{Asn}_A(e,a) \wedge a \in U \wedge \mathrm{SatCode}(A,U,T)\bigr)
\ \to\ \langle e,a \rangle \in T
```

The positive one is a conjunction, the negative one an implication. The leading "$`e`$ is a $`\Delta_0`$
formula code" sits outside the quantifier block, so it is not part of the matrix.

**The matrices are $`\Delta_0`$.** Look at the parts one by one.

| Part | Why it is $`\Delta_0`$ |
|---|---|
| "$`A`$ is transitive" | $`\forall y \in A\ \forall z \in y\ (z \in A)`$. Levy hierarchy note 2.2 |
| $`\mathrm{Asn}_A(e,a)`$ | the paper (8.4). Quantifiers bounded by $`\omega, a, A`$ |
| $`a \in U`$ | atomic |
| $`\mathrm{SatCode}(A,U,T)`$ | the paper, formula (8.5) |
| $`\langle e,a \rangle \in T`$ | ordered pair and $`\in`$. KP note 8.2 |

$`\Delta_0`$ is closed under $`\wedge`$ and $`\to`$ (Levy hierarchy note 2.1), so both matrices are
$`\Delta_0`$. The leading "$`e`$ is a $`\Delta_0`$ formula code" is $`\Delta_0`$ as well (end of KP note
7.2). Hence

```math
\mathrm{Tr}^+_{\Delta_0} \in \hat\Sigma_1, \qquad
\mathrm{Tr}^-_{\Delta_0} \in \hat\Pi_1 .
```

In the positive one $`\exists A\, \exists U\, \exists T`$ is a single block; in the negative one
$`\forall A\, \forall U\, \forall T`$ is a single block.

### 2.3 Example

The computation in §7.4 of the KP and admissible ordinals note applies directly.

Take $`e = \ulcorner v_0 \in v_1 \urcorner = 8`$ and $`a = (\emptyset, \{\emptyset\})`$. Taking
$`A = L_2`$,

- $`L_2`$ is transitive
- the values $`\emptyset`$ and $`\{\emptyset\}`$ of $`a`$ are elements of $`L_2`$
- from the second row of the table in §7.4, $`\langle 8, (\emptyset,\{\emptyset\}) \rangle \in T`$

So $`\mathrm{Tr}^+_{\Delta_0}(8, (\emptyset,\{\emptyset\}))`$ holds.

Replacing $`A`$ by $`L_3`$ or by $`L_\omega`$ does not change the answer, because $`v_0 \in v_1`$ is
$`\Delta_0`$ and the truth value of a $`\Delta_0`$ formula agrees inside and outside a transitive set
(Levy hierarchy note §3). The positive and negative representations agree for the same reason.

### 2.4 Lemma 13.3 (correctness)

Let $`\theta`$ be admissible and $`W = L_\theta`$. If $`e, a \in W`$, $`e`$ codes a $`\Delta_0`$ formula
$`\delta`$, and $`a`$ is an appropriate assignment, then

```math
W \models \mathrm{Tr}^+_{\Delta_0}(e, a)
\ \iff\ W \models \mathrm{Tr}^-_{\Delta_0}(e, a)
\ \iff\ W \models \delta[a] . \tag{13.2}
```

The same equivalences hold in the external universe $`V`$.

**Sketch of the proof (the paper).**

1. Inside $`W`$, take $`A = L_\rho`$ containing all values of $`a`$, with $`\rho`$ satisfying
   $`\omega + 1 \lt \rho \lt \theta`$ and $`\rho + 1 \lt \theta`$.
   Then $`A \in L_{\rho+1} \subseteq W`$
2. Since $`W \models \mathrm{KP}`$, apply Lemma 10.5(1) to $`A`$ inside $`W`$ and take
   $`U, T \in W`$ with $`\mathrm{SatCode}(A,U,T)`$
3. $`\mathrm{SatCode}`$ is $`\Delta_0`$ and $`W`$ is transitive, so $`\mathrm{SatCode}(A,U,T)`$ holds
   outside too
4. By Lemma 8.4, $`\langle e,a \rangle \in T \iff (A,\in) \models \delta[a]`$
5. $`A \subseteq W`$ are both transitive and $`\delta`$ is $`\Delta_0`$, so
   $`(A,\in) \models \delta[a] \iff W \models \delta[a]`$

Steps 3 to 5 give the equivalence for the positive representation. For the negative one, when
$`W \not\models \delta[a]`$ the $`A, U, T`$ built in step 1 are a counterexample to the universal
condition. $`\square`$

### 2.5 Why two are needed

Because the $`\hat\Sigma`$ side and the $`\hat\Pi`$ side each need their own base. As seen in §3,

```math
\mathrm{Tr}_{\hat\Sigma_1} \text{ stacks an } \exists \text{ block on } \mathrm{Tr}^+_{\Delta_0}\ (\hat\Sigma_1)
```
```math
\mathrm{Tr}_{\hat\Pi_1} \text{ stacks a } \forall \text{ block on } \mathrm{Tr}^-_{\Delta_0}\ (\hat\Pi_1)
```

The same polarities stack, so each gets away with a single block. Building the $`\hat\Pi`$ side out of the
positive representation alone would put an $`\exists`$ inside a $`\forall`$, raising the alternation count
by 1 and breaking the complexity in 3.3.

## 3. Higher alternation counts

### 3.1 Simultaneous block update

**Definition (the paper §12).** For a finite assignment $`a`$, a finite sequence $`\nu`$ of pairwise
distinct variable numbers, and a value sequence $`t`$ of the same length, define
$`\mathrm{BlkUpd}(a, \nu, t, b)`$ as follows. Let $`m`$ be the maximum of $`\mathrm{dom}(a)`$ and
$`\{\nu(i) + 1 : i \in \mathrm{dom}(\nu)\}`$, and let $`\mathrm{dom}(b) = m`$ with

```math
b(j) = \begin{cases}
t(i) & \text{when there is an } i \text{ with } \nu(i) = j \cr
a(j) & \text{when } j \in \mathrm{dom}(a) \text{ and the above does not apply} \cr
\emptyset & \text{otherwise}
\end{cases}
```

Roughly, "$`b`$ is $`a`$ with its $`\nu(i)`$-th variable replaced by $`t(i)`$".

**Uniqueness.** The values of $`\nu`$ are pairwise distinct, so there is at most one $`i`$ in the first
case, and $`b`$ is uniquely determined. That the values of $`\nu`$ are pairwise distinct is condition 2 of
1.1 of the alternating-block note.

**Complexity.** The quantifiers can be bounded by $`a, \nu, t, b, \omega`$ and finitely many unions of
them, so $`\mathrm{BlkUpd}`$ is $`\Delta_0`$.

When $`t`$ is not a finite sequence of the same length as $`\nu`$, $`\mathrm{BlkUpd}`$ is taken to be
false.

### 3.2 Definition 13.4

**Symbols defined here.** Two: the formulas $`\mathrm{Tr}_{\hat\Sigma_q}(e,a)`$ and
$`\mathrm{Tr}_{\hat\Pi_q}(e,a)`$. One pair for each $`q \ge 1`$.

**Symbols already available.**

| Symbol | What it is | Where |
|---|---|---|
| $`\mathrm{Tr}^+_{\Delta_0}(e,a)`$, $`\mathrm{Tr}^-_{\Delta_0}(e,a)`$ | positive and negative representations of $`\Delta_0`$ truth | 2.1 |
| $`\mathrm{BlkUpd}(a,\nu,t,b)`$ | simultaneous block update | 3.1 |
| $`\mathrm{Vars}(e)`$ | the sequence of variable numbers of the outermost block of the formula $`e`$ denotes | the paper §12 |
| $`\mathrm{Body}(e)`$ | the code of the body of the formula $`e`$ denotes, with the outermost block removed | the paper §12 |
| $`\mathrm{Form}_{\hat\Sigma_q}(e)`$, $`\mathrm{Form}_{\hat\Pi_q}(e)`$ | "$`e`$ is the code of a $`\hat\Sigma_q`$ ($`\hat\Pi_q`$) formula". $`\Delta_0`$ | the paper §12 |

Below put $`\nu = \mathrm{Vars}(e)`$ and $`d = \mathrm{Body}(e)`$.

**Definition.** Define $`\mathrm{Tr}_{\hat\Sigma_q}`$ and $`\mathrm{Tr}_{\hat\Pi_q}`$ by recursion on
$`q`$ as the formulas satisfying the following.

For $`q = 1`$,

```math
\mathrm{Tr}_{\hat\Sigma_1}(e,a) \iff
\mathrm{Form}_{\hat\Sigma_1}(e) \wedge
\exists t\, \exists b\ \bigl(\mathrm{BlkUpd}(a,\nu,t,b) \wedge \mathrm{Tr}^+_{\Delta_0}(d,b)\bigr)
```
```math
\mathrm{Tr}_{\hat\Pi_1}(e,a) \iff
\mathrm{Form}_{\hat\Pi_1}(e) \wedge
\forall t\, \forall b\ \bigl(\mathrm{BlkUpd}(a,\nu,t,b) \to \mathrm{Tr}^-_{\Delta_0}(d,b)\bigr)
```

For $`q \ge 1`$,

```math
\mathrm{Tr}_{\hat\Sigma_{q+1}}(e,a) \iff
\mathrm{Form}_{\hat\Sigma_{q+1}}(e) \wedge
\exists t\, \exists b\ \bigl(\mathrm{BlkUpd}(a,\nu,t,b) \wedge \mathrm{Tr}_{\hat\Pi_q}(d,b)\bigr)
```
```math
\mathrm{Tr}_{\hat\Pi_{q+1}}(e,a) \iff
\mathrm{Form}_{\hat\Pi_{q+1}}(e) \wedge
\forall t\, \forall b\ \bigl(\mathrm{BlkUpd}(a,\nu,t,b) \to \mathrm{Tr}_{\hat\Sigma_q}(d,b)\bigr)
```

**How to read it.** The right-hand side calls the truth predicate one level lower on the body $`d`$
obtained by removing one outermost block. The sequence of values given to the block is $`t`$, and
$`\mathrm{BlkUpd}`$ writes it into the assignment $`a`$ to make $`b`$. $`\hat\Pi`$ appears in the
definition of $`\hat\Sigma`$ and $`\hat\Sigma`$ in the definition of $`\hat\Pi`$, so the two are defined
simultaneously.

### 3.3 Lemma 13.5 (complexity)

For every $`q \ge 1`$,

```math
\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q, \qquad
\mathrm{Tr}_{\hat\Pi_q} \in \hat\Pi_q . \tag{13.5}
```

**Sketch of the proof.** For $`q = 1`$, $`\mathrm{BlkUpd}`$ is $`\Delta_0`$ and
$`\mathrm{Tr}^+_{\Delta_0}`$ has one existential block (2.2). Merging $`t, b`$ into that existential block
makes the whole thing one block, so it is $`\hat\Sigma_1`$. On the negative side, merge
$`\forall t \forall b`$ with the universal block of $`\mathrm{Tr}^-_{\Delta_0}`$ to get $`\hat\Pi_1`$.

From $`q`$ to $`q+1`$: $`\mathrm{Tr}_{\hat\Sigma_{q+1}}`$ has the shape of a $`\hat\Pi_q`$ formula placed
inside a new existential block $`\exists t \exists b`$, so it is $`\hat\Sigma_{q+1}`$. The dual is the
same. $`\mathrm{Vars}`$ and $`\mathrm{Body}`$ are $`\Delta_0`$-definable function symbols, and
$`\mathrm{Form}`$ and $`\mathrm{BlkUpd}`$ are $`\Delta_0`$, so they do not raise the alternation count.
$`\square`$

**This is where the contradiction of 1.2 is avoided.** The predicate that speaks of $`\hat\Sigma_q`$ truth
stays inside $`\hat\Sigma_q`$, so any sentence produced by diagonalization stays inside $`\hat\Sigma_q`$
as well. Its negation is $`\hat\Pi_q`$, which falls outside the range covered by
$`\mathrm{Tr}_{\hat\Sigma_q}`$. So the liar sentence does not close up. Trying to merge everything into
one formula erases this staircase and produces the contradiction.

### 3.4 Theorem 13.6 (correctness)

Let $`\theta`$ be admissible and $`W = L_\theta`$. If $`q \ge 1`$, $`e, a \in W`$, $`e`$ codes a
$`\hat\Sigma_q`$ formula $`\varphi`$ or a $`\hat\Pi_q`$ formula $`\psi`$, and $`a`$ is an appropriate
assignment, then

```math
W \models \mathrm{Tr}_{\hat\Sigma_q}(e,a) \iff W \models \varphi[a], \qquad
W \models \mathrm{Tr}_{\hat\Pi_q}(e,a) \iff W \models \psi[a] .
```

The same equivalences hold in the external universe $`V`$.

**Sketch of the proof.** Simultaneous induction on $`q`$ for $`\hat\Sigma`$ and $`\hat\Pi`$.
The base $`q = 1`$ is Lemma 13.3. In the induction step one checks that giving a value sequence $`t`$ to
the outermost block agrees with the usual semantics. Since $`W \models \mathrm{KP}`$ has Pairing and
Union, a value sequence $`t`$ of finitely many elements of $`W`$ and the updated assignment $`b`$ exist as
elements of $`W`$. $`\square`$

## 4. Finite-level Tarski–Vaught

### 4.1 Relativization

Write $`\mathrm{Tr}^M_{\hat\Sigma_j}(e,a)`$ for the fixed formula $`\mathrm{Tr}_{\hat\Sigma_j}`$ with
every unbounded quantifier restricted to $`M`$. Since all quantifiers are bounded by $`M`$, this is a
$`\Delta_0`$ formula with $`M`$ as a parameter.

The difference in meaning is here.

```
Tr_{Σ̂j}(e,a)     φ_e[a] is true in the universe we are in
Tr^M_{Σ̂j}(e,a)   φ_e[a] is true inside M
```

### 4.2 Definition 14.2

For $`q \ge 1`$, let $`\mathrm{TV}_q(M)`$ be one canonical $`\hat\Pi_q`$ representation, via Lemma 12.2, of
the following finite conjunction.

```math
\bigwedge_{1 \le j \le q}
\forall e \in \omega\ \forall a \in M\
\bigl(\mathrm{Form}_{\hat\Sigma_j}(e) \wedge \mathrm{Asn}_M(e,a)
\wedge \mathrm{Tr}_{\hat\Sigma_j}(e,a) \ \to\ \mathrm{Tr}^M_{\hat\Sigma_j}(e,a)\bigr)
\tag{14.1}
```

**How to read it.** It collects, for $`j = 1, \dots, q`$, the statement "if a $`\hat\Sigma_j`$ formula
written with parameters from $`M`$ is true in the universe, it is true inside $`M`$ as well". This is the
Tarski–Vaught test cut at alternation count $`q`$.

### 4.3 Lemma 14.3 (complexity)

```math
\mathrm{TV}_q \in \hat\Pi_q .
```

**Sketch of the proof.** For a fixed $`j`$, the implication is a disjunction of the $`\hat\Pi_j`$ formula
$`\neg \mathrm{Tr}_{\hat\Sigma_j}`$ and a $`\Delta_0`$ formula, so it collects into $`\hat\Pi_j`$. The
outer $`\forall e \in \omega`$ and $`\forall a \in M`$ are bounded universal quantifiers and merely merge
into the existing leading universal block, so they do not raise the alternation count. Pad each term up to
$`\hat\Pi_q`$ and combine the finite conjunction into one (alternating-block note 1.5, items 3 and 4).
$`\square`$

### 4.4 Theorem 14.4 (finite-level Tarski–Vaught)

If $`\xi \lt \theta`$ are both admissible then

```math
L_\theta \models \mathrm{TV}_q(L_\xi) \quad\iff\quad L_\xi \prec^*_q L_\theta . \tag{14.2}
```

**Sketch of the proof.** First, by Theorem 13.6 and the definition of relativization, (14.1) inside
$`L_\theta`$ means the following. When $`e`$ is a $`\hat\Sigma_j`$ formula and $`a`$ is an
$`L_\xi`$-valued assignment,

```math
L_\theta \models \varphi_e[a] \ \Longrightarrow\ L_\xi \models \varphi_e[a] . \tag{14.3}
```

Assuming $`L_\xi \prec^*_q L_\theta`$, (14.3) is immediate, so we get
$`L_\theta \models \mathrm{TV}_q(L_\xi)`$.

Conversely assume $`L_\theta \models \mathrm{TV}_q(L_\xi)`$. By induction on
$`j = 0, 1, \dots, q`$, show simultaneously that all $`\hat\Sigma_j`$ and $`\hat\Pi_j`$ formulas have the
same truth value in both structures.

- $`j = 0`$ is $`\Delta_0`$ absoluteness
- For $`j \ge 1`$, write a $`\hat\Sigma_j`$ formula as $`\exists \vec x\ \psi(\vec x, \bar a)`$ with
  $`\psi \in \hat\Pi_{j-1}`$ and $`\bar a \in L_\xi`$. If it is true in $`L_\theta`$ it is true in
  $`L_\xi`$ by (14.3). Conversely if it is true in $`L_\xi`$, there are witnesses $`\bar b \in L_\xi`$
  with $`L_\xi \models \psi(\bar b, \bar a)`$. By the induction hypothesis
  $`L_\theta \models \psi(\bar b, \bar a)`$, so the original formula is true in $`L_\theta`$ as well
- For a $`\hat\Pi_j`$ formula $`\chi`$, dualization (alternating-block note 1.5, item 2) gives a
  $`\hat\Sigma_j`$ formula $`\chi^\perp`$ equivalent to $`\neg\chi`$, and the already established
  agreement for $`\hat\Sigma_j`$ applies

$`\square`$

### 4.5 What this buys us

$`\prec^*_q`$ was a relation seen from the outside (alternating-block note §2). Theorem 14.4
**replaces it by a predicate writable inside $`L_\theta`$**.

```
relation seen from outside    L_ξ ≺*_q L_θ
predicate writable inside     L_θ ⊨ TV_q(L_ξ)
```

This lets us speak of $`\lhd_k`$ inside $`L_\theta`$. $`\mathrm{St}_k`$ of §15 of the paper has that
shape.

```math
\mathrm{St}_k(\xi) \ :\iff\ \forall M\, \forall c\ \bigl(\mathrm{LCode}(\xi,M,c) \to \mathrm{TV}_{k+2}(M)\bigr)
\tag{15.2}
```

By Lemma 9.2 the only $`M`$ for $`\mathrm{LCode}`$ is $`L_\xi`$, so $`\mathrm{St}_k(\xi)`$ is equivalent to
$`\mathrm{TV}_{k+2}(L_\xi)`$. Hence Lemma 15.3's

```math
L_\theta \models \mathrm{St}_k(\xi) \quad\iff\quad \xi \lhd_k \theta
```

follows from Theorem 14.4. Lemma 14.3 gives $`\mathrm{St}_k \in \hat\Pi_{k+2}`$, and this is the part that
enters the complexity computation of Theorem 17.1 (alternating-block note 3.3).

## 5. How it is used in the paper

| Place | Use |
|---|---|
| Definition 13.2 | $`\mathrm{Tr}^+_{\Delta_0}`$, $`\mathrm{Tr}^-_{\Delta_0}`$ |
| (13.1) | the positive representation is $`\hat\Sigma_1`$, the negative one $`\hat\Pi_1`$ |
| Lemma 13.3 | correctness of $`\Delta_0`$ truth. The base of Theorem 13.6 |
| Definition 13.4 | $`\mathrm{Tr}_{\hat\Sigma_q}`$, $`\mathrm{Tr}_{\hat\Pi_q}`$ |
| Lemma 13.5 | $`\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q`$ |
| Theorem 13.6 | correctness of the partial truth predicates |
| Definition 14.2, Lemma 14.3 | $`\mathrm{TV}_q(M) \in \hat\Pi_q`$ |
| Theorem 14.4 | $`L_\theta \models \mathrm{TV}_q(L_\xi) \iff L_\xi \prec^*_q L_\theta`$ |
| Definition 15.2, Lemma 15.3 | $`\mathrm{St}_k`$ and its correctness |
| Definition 15.4, Lemma 15.5 | $`\mathrm{Rel}_k`$ and its correctness |
| Theorem 17.1 | uses that a $`\hat\Sigma_{n+2}`$ sentence assembled from the above parts, true in $`L_\beta`$, is true in $`L_\alpha`$ |

## 6. Counterparts in Lean

| Concept | Lean | File |
|---|---|---|
| the matrix of Definition 13.2 | `TrD0Mat` | `Bm4/SetTheory/Truth.lean` |
| $`\mathrm{Tr}^+_{\Delta_0}`$ | `TrD0P` | same |
| $`\mathrm{Tr}^-_{\Delta_0}`$ | `TrD0N` | same |
| the $`\hat\Sigma_1`$ of (13.1) | `sigmaDef_trD0P` | same |
| the $`\hat\Pi_1`$ of (13.1) | `piDef_trD0N` | same |
| Lemma 13.3 (inside $`L_\theta`$) | `baseCorrect_L` | `Bm4/SetTheory/BaseOK.lean` |
| Lemma 13.3 (external universe $`V`$) | `baseCorrect_V` | same |
| $`\mathrm{BlkUpd}`$ | `IsBlkUpdP` | `Bm4/SetTheory/BlkP.lean` |
| $`\mathrm{Tr}_{\hat\Sigma_q}`$ of Definition 13.4 | `TrSigP` | `Bm4/SetTheory/TrP.lean` |
| $`\mathrm{Tr}_{\hat\Pi_q}`$ of Definition 13.4 | `TrPiP` | same |
| Theorem 13.6 | `trSigQ_correct`, `trPiQ_correct` | `Bm4/SetTheory/StRelP.lean` |
| Theorem 13.6 (external universe $`V`$) | `trSigPiQ_correct_V` | `Bm4/SetTheory/TrPV.lean` |
| each term of (14.1) | `TVBodyP` | `Bm4/SetTheory/StRelP.lean` |
| the finite conjunction of (14.1) | `TVConjP` | same |
| $`\mathrm{TV}_q(M)`$ | `TVqP` | same |
| the semantic version of Theorem 14.4 | `elemHat_of_downward` | `Bm4/SetTheory/Elem.lean` |
| $`\mathrm{St}_k`$ of Definition 15.2 | `StKP` | `Bm4/SetTheory/StKP.lean` |
| the complexity in Lemma 15.3 | `piDef_StKP` | same |
| $`\mathrm{Rel}_k`$ of Definition 15.4 | `RelKP` | same |
| the complexity in Lemma 15.5 | `sigmaDef_RelKP` | same |
