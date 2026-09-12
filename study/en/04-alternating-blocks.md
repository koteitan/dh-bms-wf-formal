[← Back](README.md) | [English](04-alternating-blocks.md) | [Japanese](../04-alternating-blocks.md)

# The strict alternating block hierarchy and the stability relation

Prerequisites

| Note | Terms used from it |
|---|---|
| [The constructible hierarchy L](01-constructible-hierarchy.md) | formula, structure $`(X,\in)`$, assignment $`\bar a`$, satisfaction $`\models`$, transitive, $`L_\xi`$ |
| [The Lévy hierarchy and absoluteness](02-levy-hierarchy.md) | bounded quantification, **block**, $`\Delta_0`$, $`\Delta_0`$ absoluteness, $`\Sigma_1`$, $`\Pi_1`$ |
| [KP and admissible ordinals](03-kp-admissible.md) | KP, **admissible ordinal**, $`\mathrm{SatCode}`$, $`\mathrm{LCode}`$ |

## 1. Σ̂q and Π̂q

### 1.1 Definition

**Definition (Definition 12.1 of the paper).** Put
$`\hat\Sigma_0 = \hat\Pi_0 = \Delta_0`$. For $`q \ge 1`$, the formulas of the forms

```math
\hat\Sigma_q : \ \exists \vec x_1\, \forall \vec x_2\, \exists \vec x_3 \cdots Q_q \vec x_q\ \delta,
\qquad
\hat\Pi_q : \ \forall \vec x_1\, \exists \vec x_2\, \forall \vec x_3 \cdots Q_q \vec x_q\ \delta
```

are called $`\hat\Sigma_q`$ and $`\hat\Pi_q`$ respectively. Here $`\delta \in \Delta_0`$ and
each $`\vec x_i`$ is a block of unbounded quantifiers (§4.1 of the Lévy hierarchy note)
satisfying the following four conditions.

1. Each $`\vec x_i`$ is nonempty
2. The variables inside one block are distinct
3. Adjacent blocks have opposite polarity
4. The free variables do not clash with the bound variables inside the blocks

The remainder $`\delta`$ after removing all the leading blocks is called the **matrix** of the
formula. The objects treated in Part I of the paper are called "arrays", and are a different
thing from this "matrix".

### 1.2 What the four conditions do

**Condition 3 is what "strict" means.** If two blocks of the same polarity are adjacent, they
merge into one.

```math
\exists \vec x_1\, \exists \vec x_2\, \forall \vec x_3\ \delta
\quad\text{can be rewritten as}\quad
\exists (\vec x_1, \vec x_2)\, \forall \vec x_3\ \delta
```

which is $`\hat\Sigma_2`$. Imposing 3 makes $`q`$ equal to "the number of polarity switches
$`+\, 1`$".

**Condition 1 makes $`q`$ meaningful.** If empty blocks were allowed, then for instance

```math
\exists ()\, \forall x\ \delta
```

would look like two blocks, but its content is $`\forall x\ \delta`$, which is $`\hat\Pi_1`$.
Condition 1 forbids this.

**Condition 2 makes substitution unique.** The simultaneous block update
$`\mathrm{BlkUpd}(a, \nu, t, b)`$ of §12 of the paper is the operation rewriting the positions
of the list of variable indices $`\nu`$ all at once by the list of values $`t`$. If the same
index occurred twice in $`\nu`$, it would not be determined which value to assign. This is the
condition behind the paper's "the values of $`\nu`$ are distinct, so it is unique".

**Condition 4 keeps substitution from capturing variables.** If a block bound a free variable
$`y`$ by $`\forall y`$, then the operation assigning a value to $`y`$ would change the meaning.

### 1.3 Examples

| Formula | Class |
|---|---|
| $`x \in y`$ | $`\Delta_0 = \hat\Sigma_0 = \hat\Pi_0`$ |
| $`x \subseteq y`$, that is, $`\forall z \in x\,(z \in y)`$ | $`\Delta_0`$ |
| $`\exists z\,(x \in z)`$ | $`\hat\Sigma_1`$ |
| $`\forall w\,(w \subseteq x \to w \in z)`$ | $`\hat\Pi_1`$ |
| $`\exists u_1\,\exists u_2\,\forall v\ \delta`$ | $`\hat\Sigma_2`$ (the $`\exists`$ form one block) |
| $`\forall v\,\exists u\ \delta`$ | $`\hat\Pi_2`$ |
| $`\mathrm{Adm}(\eta)`$ (Definition 11.1 of the paper) | $`\hat\Sigma_1`$ |

The last row holds because, as seen in §8 of the KP and admissible ordinals note,
$`\mathrm{Adm}(\eta)`$ is a conjunction of three $`\Delta_0`$ predicates with one block
$`\exists M, c, U, S`$ on top.

### 1.4 How it differs from the Lévy hierarchy

For $`q = 1`$ they agree.

```math
\hat\Sigma_1 = \Sigma_1, \qquad \hat\Pi_1 = \Pi_1
```

For $`q \ge 2`$ they differ. Lévy's $`\Sigma_2`$ only says "the unbounded quantifiers alternate
twice", and bounded quantifiers may be mixed in anywhere. $`\hat\Sigma_2`$ is restricted to the
prenex form $`\exists \vec x\, \forall \vec y\ \delta`$ with $`\delta \in \Delta_0`$.

So a transformation into prenex form is needed, and sometimes it cannot be done. The example in
Remark 12.3 of the paper is

```math
\forall u \in a\ \exists x\ \delta(u,x).
```

Moving $`\forall u \in a`$ outside the unbounded $`\exists x`$ to get a $`\Sigma_1`$ prenex form
requires the equivalence with

```math
\exists b\ \forall u \in a\ \exists x \in b\ \delta(u,x)
```

and that is Collection (§2 of the KP and admissible ordinals note). Without assuming
Collection, this rewriting cannot be done.

The paper avoids this transformation and works only with formulas in alternating block form
from the start. Both the truth predicates (§13) and the sentences used for reflection (§17) are
built in a form that does not need this move.

### 1.5 Safe syntactic operations (Lemma 12.2 of the paper)

The following operations have $`\Delta_0`$ graphs under the fixed coding.

1. Variable renaming, substitution, avoidance of bound variable capture, relativization,
   prefixing an alternating block
2. Dualization of $`\hat\Sigma_q`$ and $`\hat\Pi_q`$
3. **padding**: for $`j \le q`$, moving a $`\hat\Sigma_j`$ formula to an equivalent
   $`\hat\Sigma_q`$ formula and a $`\hat\Pi_j`$ formula to an equivalent $`\hat\Pi_q`$ formula
4. Collecting a finite conjunction or disjunction of formulas of the same alternation type into
   one formula of the same alternation type

**How padding works.** Put as many idle blocks as needed at the innermost position, quantifying
variables that do not occur in the formula. In a nonempty structure, if the variable $`z`$ does
not occur in $`\varphi`$ then

```math
\exists z\ \varphi \leftrightarrow \varphi, \qquad \forall z\ \varphi \leftrightarrow \varphi
```

so the meaning is unchanged.

**How finite joining works.** After renaming the bound variables of the two formulas apart, for
two formulas with the same polarity list $`Q_1, \dots, Q_q`$,

```math
Q_1 \vec x_1 \cdots Q_q \vec x_q\ \delta, \qquad
Q_1 \vec u_1 \cdots Q_q \vec u_q\ \varepsilon
```

take, for $`\star \in \{\wedge, \vee\}`$,

```math
Q_1 (\vec x_1, \vec u_1) \cdots Q_q (\vec x_q, \vec u_q)\ (\delta \star \varepsilon).
```

This merely merges two blocks of the same polarity over mutually independent variables into
one.

Items 3 and 4 are used in the complexity computation of §3.3.

## 2. ≺*q

### 2.1 Definition

**Definition (Definition 14.1 of the paper).** For transitive sets $`M \subseteq N`$ and
$`q \ge 1`$,

```math
M \prec^*_q N \quad :\iff\quad
\begin{aligned}
&\text{for every } j\ (1 \le j \le q)\text{, every } \hat\Sigma_j \text{ and } \hat\Pi_j \text{ formula } \varphi\text{,} \cr
&\text{and every assignment } \bar a \text{ with values in } M, \cr
&(M,\in) \models \varphi[\bar a] \iff (N,\in) \models \varphi[\bar a]
\end{aligned}
```

**Meaning.** Ordinary elementarity $`M \prec N`$ says that the truth values agree for every
formula. $`\prec^*_q`$ caps that at alternation number $`q`$. The larger $`q`$ is, the stronger
the condition.

### 2.2 The Δ₀ level comes for free

The definition has $`1 \le j`$, so it does not require agreement at $`j = 0`$, that is, for
$`\Delta_0`$. But if $`M`$ and $`N`$ are transitive and $`M \subseteq N`$, agreement for
$`\Delta_0`$ follows automatically from §3 of the Lévy hierarchy note. So in fact they agree at
every $`0 \le j \le q`$.

### 2.3 An example where ≺*₁ fails

Take $`\psi(x) \equiv \exists z\,(x \in z)`$. As in 1.3, it is $`\hat\Sigma_1`$.

Let $`M = L_2 = \{\emptyset, \{\emptyset\}\}`$ and $`N = L_3`$. Both are transitive and
$`L_2 \subseteq L_3`$. Take the assignment $`\bar a(x) = \{\emptyset\}`$.

From the $`\exists`$ line of the definition of satisfaction (§2 of the constructible hierarchy
note), for a transitive set $`W`$,

```math
(W, \in) \models \psi[\bar a]
\quad\iff\quad
\text{there is } c \in W \text{ with } \bar a(x) \in c.
```

That is, it asks whether a set having $`\{\emptyset\}`$ as an element is in $`W`$. We compute
this for $`W = L_2`$ and $`W = L_3`$.

**When $`W = L_2`$:** the candidates $`c`$ are the two sets $`\emptyset`$ and
$`\{\emptyset\}`$. Neither $`\{\emptyset\} \in \emptyset`$ nor
$`\{\emptyset\} \in \{\emptyset\}`$ holds. Hence

```math
(L_2, \in) \models \psi[\bar a] \quad \text{is false}.
```

**When $`W = L_3`$:**
$`L_3 = \{\emptyset, \{\emptyset\}, \{\{\emptyset\}\}, \{\emptyset,\{\emptyset\}\}\}`$, and
$`c = \{\{\emptyset\}\}`$ satisfies $`\{\emptyset\} \in \{\{\emptyset\}\}`$. Hence

```math
(L_3, \in) \models \psi[\bar a] \quad \text{is true}.
```

Here $`\psi`$ is $`\hat\Sigma_1`$, the value of $`\bar a`$ is an element of $`L_2`$, and the
truth values disagree. So the condition of 2.1 fails at $`j = 1`$ and

```math
L_2 \not\prec^*_1 L_3 .
```

### 2.4 Monotone in q, and transitive

**Monotonicity.** If $`1 \le h \le k`$ and $`M \prec^*_k N`$ then $`M \prec^*_h N`$, because
the required range $`1 \le j \le h`$ is part of $`1 \le j \le k`$.

**Transitivity.** If $`M \prec^*_q N`$ and $`N \prec^*_q P`$ then $`M \prec^*_q P`$. Since
$`M \subseteq N \subseteq P`$, fixing $`j`$ and $`\bar a`$ and applying the two hypotheses in
turn gives

```math
(M,\in) \models \varphi[\bar a] \iff (N,\in) \models \varphi[\bar a] \iff (P,\in) \models \varphi[\bar a].
```

## 3. ◁k

### 3.1 Definition

**Definition (equation (15.1) of the paper).** For admissible ordinals
$`\alpha \lt \beta`$ and $`k \in \mathbb{N}`$,

```math
\alpha \lhd_k \beta \quad :\iff\quad L_\alpha \prec^*_{k+2} L_\beta .
```

**Meaning.** $`L_\alpha`$ and $`L_\beta`$ return the same truth value, parameters from
$`L_\alpha`$ included, for every formula of alternation number at most $`k+2`$.

### 3.2 Lemma 15.1

**(1) Monotonicity.** If $`h \lt k`$ and $`\alpha \lhd_k \beta`$ then
$`\alpha \lhd_h \beta`$.

**Proof.** $`\alpha \lhd_k \beta`$ is $`L_\alpha \prec^*_{k+2} L_\beta`$. If $`h \lt k`$ then
$`h+2 \lt k+2`$, so monotonicity in 2.4 gives $`L_\alpha \prec^*_{h+2} L_\beta`$, that is,
$`\alpha \lhd_h \beta`$. $`\square`$

**(2) Transitivity.** If $`\alpha \lhd_k \beta`$ and $`\beta \lhd_k \gamma`$ then
$`\alpha \lhd_k \gamma`$.

**Proof.** Use transitivity in 2.4 with $`q = k+2`$. $`\square`$

### 3.3 Why +2

Because the sentence written in $`L_\beta`$ in the proof of Theorem 17.1 turns out to be
exactly $`\hat\Sigma_{n+2}`$. Getting ahead of ourselves, here is the breakdown. Three kinds of
predicate are used.

| Predicate | Role | Complexity |
|---|---|---|
| $`\mathrm{Adm}(\eta)`$ (Definition 11.1) | $`\eta`$ is an admissible ordinal | $`\hat\Sigma_1`$ |
| $`\mathrm{Rel}_k(\xi,\eta)`$ (Definition 15.4) | the internal form of $`\xi \lhd_k \eta`$ | $`\hat\Sigma_1`$ |
| $`\mathrm{St}_m(\xi)`$ (Definition 15.2) | the internal form of "$`\xi \lhd_m`$ the universe we are in" | $`\hat\Pi_{m+2}`$ |

With $`n`$ the bound on the number of rows, only $`\mathrm{St}_m`$ with $`m \lt n`$ is used, so
$`\hat\Pi_{m+2} \le \hat\Pi_{n+1}`$.

A $`\hat\Sigma_1`$ formula $`\exists \vec z\ \delta`$ is equivalent, in a nonempty structure, to

```math
\forall w\ \exists \vec z\ (w = w \wedge \delta)
```

so it can be regarded as $`\hat\Pi_2`$ and raised to $`\hat\Pi_{n+1}`$ by the padding of 1.5.

Collecting everything into one $`\hat\Pi_{n+1}`$ formula $`\Phi(\vec u)`$ by the finite joining
of 1.5 and putting one block $`\exists u_0 \cdots \exists u_{s-1}`$ on the outside gives

```math
\exists \vec u\ \Phi(\vec u) \ \in\ \hat\Sigma_{n+2}.
```

The hypothesis needed to conclude that this sentence, true in $`L_\beta`$, is also true in
$`L_\alpha`$ is exactly $`L_\alpha \prec^*_{n+2} L_\beta`$, that is,
$`\alpha \lhd_n \beta`$.

The $`2`$ in $`+2`$ is the $`1`$ for raising to $`\hat\Pi_{n+1}`$ plus the $`1`$ for the outer
$`\exists`$ block.

### 3.4 Relation to full elementarity

Lemma 16.2 of the paper produces a pair of admissible ordinals
$`\Lambda \lt \Theta`$ with

```math
L_\Lambda \prec L_\Theta
```

(elementarity with no restriction on the alternation number). Since there is no restriction,

```math
\Lambda \lhd_k \Theta \tag{16.2}
```

holds for every $`k`$. This is the starting point of the stable labels (Lemma 20.1).

## 4. How it is used in the paper

| Place | Use |
|---|---|
| Definition 12.1 | $`\hat\Sigma_q`$, $`\hat\Pi_q`$ |
| Lemma 12.2 | safe syntactic operations; padding and finite joining |
| Definition 13.4 | the partial truth predicates $`\mathrm{Tr}_{\hat\Sigma_q}`$, $`\mathrm{Tr}_{\hat\Pi_q}`$ |
| Lemma 13.5 | $`\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q`$, $`\mathrm{Tr}_{\hat\Pi_q} \in \hat\Pi_q`$ |
| Definition 14.1 | $`\prec^*_q`$ |
| Definition 14.2, Lemma 14.3 | the Tarski–Vaught formula $`\mathrm{TV}_q(M) \in \hat\Pi_q`$ |
| Theorem 14.4 | $`L_\theta \models \mathrm{TV}_q(L_\xi) \iff L_\xi \prec^*_q L_\theta`$ |
| equation (15.1) | $`\lhd_k`$ |
| Lemma 15.1 | monotonicity and transitivity |
| Theorem 17.1 | finite pattern reflection; uses the complexity computation of 3.3 |
| Definition 18.1 | stable labels; if $`i \prec_k j`$ then $`f(i) \lhd_k f(j)`$ |

## 5. Correspondence in Lean

| Concept | Lean | File |
|---|---|---|
| $`\hat\Sigma_q`$ | `IsSigma q φ` | `Bm4/SetTheory/Fm.lean` |
| $`\hat\Pi_q`$ | `IsPi q φ` | same |
| condition 1 of 1.1 (blocks are nonempty) | `hl : l ≠ []` in `IsSigma.succ` | same |
| condition 2 of 1.1 (variables are distinct) | `hnd : l.Nodup` in `IsSigma.succ` | same |
| block formulas and dualization | `BF`, `BF.dual`, `sat_dual` | `Bm4/SetTheory/BF.lean` |
| padding | `BF.padSig`, `BF.padPi`, `Sig.padSig`, `Pi.padPi` | `Bm4/SetTheory/BFPad.lean` |
| $`M \prec^*_q N`$ | `ElemHat q M N` | `Bm4/SetTheory/Elem.lean` |
| 2.2 (the $`\Delta_0`$ level comes for free) | `ElemHat.delta0` | same |
| agreement at $`j \le q`$ | `ElemHat.sigma`, `ElemHat.pi` | same |
| monotonicity in 2.4 | `ElemHat.mono` | same |
| transitivity in 2.4 | `ElemHat.trans` | same |
| the type of admissible ordinals | `AdmOrd` | `Bm4/SetTheory/Stable.lean` |
| $`\alpha \lhd_k \beta`$ | `RelAdm k α β` | same |
| Lemma 15.1(1) | `relAdm_mono` | same |
| Lemma 15.1(2) | `relAdm_trans` | same |
| full elementarity | `ElemFull` | `Bm4/SetTheory/AdmTrans.lean` |
| the initial pair of (16.2) | `exists_relAdm_all` | `Bm4/SetTheory/Stable.lean` |

The formalized $`\mathrm{RelAdm}`$ includes $`\alpha \lt \beta`$ as a conjunct. Equation (15.1)
of the paper puts $`\alpha \lt \beta`$ as a standing hypothesis, so the content is the same.
$`\mathrm{ElemHat}`$ likewise includes $`1 \le q`$, transitivity of $`M`$ and $`N`$, and
$`M \subseteq N`$ as conjuncts.
