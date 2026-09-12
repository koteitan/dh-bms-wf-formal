[← Back](README.md) | [English](06-finite-reflection.md) | [Japanese](../06-finite-reflection.md)

# Finite Row Reflection (Theorem 17.1)

Prerequisites

| Note | Terms used from here |
|---|---|
| [The constructible hierarchy L](01-constructible-hierarchy.md) | $`L_\xi`$, $`L_\xi \cap \mathrm{Ord} = \xi`$ (§9) |
| [The Levy hierarchy and absoluteness](02-levy-hierarchy.md) | $`\Delta_0`$, $`\Delta_0`$ absoluteness |
| [KP and admissible ordinals](03-kp-admissible.md) | KP, admissible ordinal, $`\mathrm{SatCode}`$, $`\mathrm{LCode}`$, Corollary 10.6 |
| [The strict alternating block hierarchy and the stability relation](04-alternating-blocks.md) | **$`\hat\Sigma_q`$, $`\hat\Pi_q`$ (1.1)**, $`\prec^*_q`$, $`\lhd_k`$, Lemma 15.1, why +2 (3.3) |
| [Partial truth predicates and finite-level Tarski–Vaught](05-truth-predicates.md) | $`\mathrm{TV}_q`$, Lemma 14.3, Theorem 14.4 |

## 1. Internal representations

### 1.1 Why they are needed

Both $`\lhd_k`$ and "$`\eta`$ is admissible" have so far been conditions stated from the outside.
In the proof of Theorem 17.1 they are turned into **sentences written inside** $`L_\beta`$.
From the truth of such a sentence in $`L_\beta`$ we derive its truth in $`L_\alpha`$.
Three predicates are prepared for this.

### 1.2 Adm(η) (Definition 11.1)

**Symbols defined here.** Two: $`\mathrm{KPTrue}(M,U,S)`$ and $`\mathrm{Adm}(\eta)`$.

**Symbols already available.**

| Symbol | What it is | Where |
|---|---|---|
| $`\mathrm{KPAx}(d)`$ | "$`d`$ is the code of an axiom of KP or of one instance of an axiom schema". $`\Delta_0`$ | the paper §11 |
| $`\mathrm{LCode}(\eta,M,c)`$ | $`L`$-hierarchy code | KP note §8 |
| $`\mathrm{SatCode}(M,U,S)`$ | satisfaction code | KP note §7 |

**Definition (the paper, Definition 11.1).** Define $`\mathrm{KPTrue}`$ and $`\mathrm{Adm}`$ as the
formulas satisfying the following.

```math
\mathrm{KPTrue}(M,U,S) \ :\iff\ \forall d \in \omega\ \bigl(\mathrm{KPAx}(d) \to \langle d, \emptyset \rangle \in S\bigr)
```
```math
\mathrm{Adm}(\eta) \ :\iff\ \exists M, c, U, S\ \bigl(
\mathrm{LCode}(\eta,M,c) \wedge \mathrm{SatCode}(M,U,S) \wedge \mathrm{KPTrue}(M,U,S)\bigr)
```

**How to read it.** "Build a code for $`L_\eta`$, build its satisfaction code, and every axiom of KP is
true there." That is, $`L_\eta \models \mathrm{KP}`$ rewritten in the language of codes.

The assignment is $`\emptyset`$ because what $`\mathrm{KPAx}`$ recognizes is sentences, that is, codes with
no free variables. A sentence needs no assignment (KP note 1).

**Complexity.** $`\mathrm{LCode}`$, $`\mathrm{SatCode}`$ and $`\mathrm{KPTrue}`$ are all $`\Delta_0`$, and
$`\exists M, c, U, S`$ is a single block. Hence

```math
\mathrm{Adm} \in \hat\Sigma_1 .
```

**Lemma 11.2 (correctness).** If $`\theta`$ is admissible and $`\eta \lt \theta`$ then

```math
L_\theta \models \mathrm{Adm}(\eta) \quad\iff\quad L_\eta \models \mathrm{KP} .
```

Right to left is by Corollary 10.6, which gives a code for $`L_\eta`$ inside $`L_\theta`$, together with
the existence of a satisfaction code inside $`L_\theta`$ (Lemma 10.5(1)).
Left to right is by the $`\Delta_0`$ absoluteness of $`\mathrm{LCode}`$, $`\mathrm{SatCode}`$,
$`\mathrm{KPTrue}`$ and by Lemmas 9.2 and 8.4.

### 1.3 St_k(ξ) (Definition 15.2)

**Definition (the paper, Definition 15.2).** Define $`\mathrm{St}_k(\xi)`$ as the formula satisfying the
following. $`\mathrm{TV}_q(M)`$ is the one from 4.2 of the truth-predicate note.

```math
\mathrm{St}_k(\xi) \ :\iff\ \forall M\, \forall c\ \bigl(\mathrm{LCode}(\xi,M,c) \to \mathrm{TV}_{k+2}(M)\bigr)
\tag{15.2}
```

**How to read it.** It is the predicate saying "$`\xi \lhd_k`$ the universe we are in", stated inside the
universe we are in. The second argument is "myself", so one argument suffices.

**Complexity.** From $`\mathrm{TV}_{k+2} \in \hat\Pi_{k+2}`$ (Lemma 14.3),

```math
\mathrm{St}_k \in \hat\Pi_{k+2} .
```

**Lemma 15.3 (correctness).** If $`\xi \lt \theta`$ are both admissible then

```math
L_\theta \models \mathrm{St}_k(\xi) \quad\iff\quad \xi \lhd_k \theta . \tag{15.3}
```

By Corollary 10.6 there is a correct code for $`L_\xi`$ inside $`L_\theta`$, and the set represented by
any such code is $`L_\xi`$ by Lemma 9.2. Hence $`\mathrm{St}_k(\xi)`$ is equivalent to
$`\mathrm{TV}_{k+2}(L_\xi)`$, and Theorem 14.4 applies.

### 1.4 Rel_k(ξ,η) (Definition 15.4)

**Relativization.** Let $`\mathrm{St}_k(\xi)^M`$ be the formula obtained from $`\mathrm{St}_k(\xi)`$ by
restricting every unbounded quantifier to $`M`$. Since all quantifiers are bounded by $`M`$, this is
$`\Delta_0`$.

**Definition (the paper, Definition 15.4).** Define $`\mathrm{Rel}_k(\xi,\eta)`$ as the formula satisfying
the following. $`\mathrm{Ord}(\xi)`$ is the $`\Delta_0`$ predicate "$`\xi`$ is an ordinal"
(Levy hierarchy note 2.2).

```math
\mathrm{Rel}_k(\xi,\eta) \ :\iff\
\mathrm{Ord}(\xi) \wedge \mathrm{Ord}(\eta) \wedge \xi \lt \eta
\wedge \exists M\, \exists c\ \bigl(\mathrm{LCode}(\eta,M,c) \wedge \mathrm{St}_k(\xi)^M\bigr)
\tag{15.4}
```

**How to read it.** It is the two-argument version of $`\mathrm{St}_k`$, with "myself" replaced by
$`\eta`$. Relativizing $`\mathrm{St}_k(\xi)`$ to $`M = L_\eta`$ lets us say "$`\mathrm{St}_k(\xi)`$ inside
$`L_\eta`$" from the outside as a single formula.

**Complexity.** The relativized $`\mathrm{St}_k(\xi)^M`$ is $`\Delta_0`$, $`\mathrm{LCode}`$ is $`\Delta_0`$,
and $`\mathrm{Ord}`$ and $`\xi \lt \eta`$ are $`\Delta_0`$ as well. Since $`\exists M \exists c`$ is a
single block,

```math
\mathrm{Rel}_k \in \hat\Sigma_1 .
```

No matter how large $`k`$ is, it stays $`\hat\Sigma_1`$, because the result of the relativization is
$`\Delta_0`$ independently of $`k`$. This is what matters in 3.4.

**Lemma 15.5 (correctness).**

1. If $`\xi \lt \eta`$ are both admissible then $`\mathrm{Rel}_k(\xi,\eta) \iff \xi \lhd_k \eta`$
2. If $`\xi \lt \eta \lt \theta`$ are all admissible then
   $`L_\theta \models \mathrm{Rel}_k(\xi,\eta) \iff \xi \lhd_k \eta`$

For (1), taking a code satisfying $`\mathrm{LCode}(\eta,M,c)`$ in the external universe gives $`M = L_\eta`$
by Lemma 9.2, and $`\mathrm{St}_k(\xi)^{L_\eta}`$ is the same as $`L_\eta \models \mathrm{St}_k(\xi)`$, so
apply Lemma 15.3 with $`\theta = \eta`$. For (2), the internal witness code is also correct outside by
$`\Delta_0`$ absoluteness, and again $`M = L_\eta`$.

### 1.5 The three side by side

| Predicate | Meaning | Complexity |
|---|---|---|
| $`\mathrm{Adm}(\eta)`$ | $`\eta`$ is admissible | $`\hat\Sigma_1`$ |
| $`\mathrm{Rel}_k(\xi,\eta)`$ | $`\xi \lhd_k \eta`$ | $`\hat\Sigma_1`$ |
| $`\mathrm{St}_k(\xi)`$ | $`\xi \lhd_k`$ the universe we are in | $`\hat\Pi_{k+2}`$ |

Only $`\mathrm{St}_k`$ has a complexity depending on $`k`$, because it carries $`\mathrm{TV}_{k+2}`$ as it is.
$`\mathrm{Rel}_k`$ gets away with $`\hat\Sigma_1`$ because it only relativizes that $`\mathrm{St}_k`$ to
$`M`$, making it $`\Delta_0`$, and then prefixes $`\exists M \exists c`$.

## 2. The first stable pair (§16)

Theorem 17.1 has $`\alpha \lhd_n \beta`$ as a hypothesis. §16 is what says such a pair exists.

### 2.1 Terms and facts used

**Definition ($`\omega_1^V`$).** Write $`\omega_1^V`$ for the least uncountable ordinal in the external
universe $`V`$.

**Definition (regular).** An ordinal $`\kappa`$ is **regular** if every $`A \subseteq \kappa`$ with
$`|A| \lt |\kappa|`$ satisfies $`\sup A \lt \kappa`$.

**Fact.** $`\omega_1`$ is regular. That is, the supremum of a countable set of ordinals below
$`\omega_1`$ is below $`\omega_1`$.

**Definition ($`\lt_L`$).** By transfinite recursion along $`\xi`$, build a well-ordering $`\lt_\xi`$ of
$`L_\xi`$.

**When $`\xi = 0`$:** $`L_0 = \emptyset`$, so the empty order.

**When $`\xi + 1`$:** The elements of $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ are carved out from pairs
$`\langle e, a \rangle`$ ($`e`$ a formula code, $`a`$ a finite sequence of elements of $`L_\xi`$)
(constructible hierarchy note §4). First order these pairs.

- Finite sequences $`a`$ and $`a'`$: if their lengths differ, the shorter is smaller; if the lengths are
  equal, compare the first component where they differ using $`\lt_\xi`$
- Pairs $`\langle e,a \rangle`$ and $`\langle e',a' \rangle`$: if $`e \ne e'`$, compare $`e`$ and $`e'`$ as
  natural numbers; if $`e = e'`$, compare $`a`$ and $`a'`$ by the rule above

One element can be carved out from several pairs (constructible hierarchy note 4.2), so for
$`y \in L_{\xi+1} \setminus L_\xi`$ let $`p(y)`$ be the least of the pairs carving out $`y`$.
Then, for $`x, y \in L_{\xi+1}`$,

```math
x \lt_{\xi+1} y \iff
\begin{cases}
\text{true} & x \in L_\xi \text{ and } y \notin L_\xi \cr
x \lt_\xi y & x, y \in L_\xi \cr
p(x) \lt p(y) & x, y \notin L_\xi \cr
\text{false} & x \notin L_\xi \text{ and } y \in L_\xi
\end{cases}
```

**When $`\lambda`$ is a limit:** set $`\lt_\lambda = \bigcup_{\xi \lt \lambda} \lt_\xi`$.
The $`\lt_\xi`$ do not conflict with each other, so this is an order.

Finally set $`\lt_L = \bigcup_\xi \lt_\xi`$.

**Fact.** $`\lt_L`$ is a well-ordering of all of $`L`$ and is definable inside $`L`$. Hence one can
specify "the $`\lt_L`$-least element satisfying a condition" without using the axiom of choice.

**Definition (Skolem function).** For a structure $`N`$ and a formula $`\exists x\, \varphi(x, \bar y)`$, a
function that takes $`\bar y`$ and returns one witness $`x`$ for $`\varphi`$ is called a **Skolem
function**. When $`N \subseteq L`$, returning the $`\lt_L`$-least witness makes it unique.

**Fact (Tarski–Vaught test).** For transitive $`M \subseteq N`$, if every $`\exists x\, \varphi(x, \bar a)`$
($`\bar a \in M`$) true in $`N`$ always has a witness inside $`M`$, then $`M \prec N`$. This is the
finite-level version in §4 of the truth-predicate note with the restriction on the number of
alternations removed.

### 2.2 Lemma 16.1

If $`\gamma \lt \omega_1^V`$ then $`L_\gamma`$ is countable in the external universe $`V`$.

By transfinite induction on $`\gamma`$. At successor stages there are countably many formula codes and
finite parameter sequences; at countable limit stages it is a union of countably many countable sets.

### 2.3 Lemma 16.2

There exist admissible ordinals $`\Lambda, \Theta`$ with

```math
\omega \lt \Lambda \lt \Theta, \qquad L_\Lambda \prec L_\Theta . \tag{16.1}
```

**Sketch of the proof.** Put $`\Theta = \omega_1^V`$.

First show $`L_\Theta \models \mathrm{KP}`$.

| Axiom | Reason |
|---|---|
| Extensionality, Empty Set, Pairing, Union, Infinity | because $`\Theta`$ is a limit greater than $`\omega`$ (KP note 6.2) |
| Set Induction | from external Foundation. If some instance failed, external Separation would build a counterexample set, and taking its $`\in`$-least element gives a contradiction |
| $`\Delta_0`$-Separation | from $`\Delta_0`$ absoluteness between a sufficiently large $`L_{\gamma_0}`$ containing the parameters and $`L_\Theta`$ |
| $`\Delta_0`$-Collection | below |

$`\Delta_0`$-Collection goes as follows. Suppose
$`L_\Theta \models \forall x \in a\ \exists y\ \delta(x,y,p)`$ with $`\delta \in \Delta_0`$.
By Lemma 16.1, $`a`$ is countable externally. For each $`x \in a`$ take the $`\lt_L`$-least witness
$`y_x`$ and take the supremum of all their $`L`$-ranks. By the regularity of $`\omega_1^V`$ the supremum
is below $`\Theta`$, and a single $`L_\rho \in L_\Theta`$ containing all witnesses is the collection set.

Next build $`\Lambda`$. Fix externally the $`\lt_L`$-least Skolem functions for all first-order formulas of
$`(L_\Theta, \in)`$. For a countable $`\gamma \lt \Theta`$, the set of values obtained by applying all
Skolem functions to finite parameters from $`L_\gamma`$ is countable. Hence one can take
$`L_{h(\gamma)}`$ containing them, for some $`h(\gamma) \lt \Theta`$. Starting from a countable limit
$`\gamma_0 \gt \omega`$, take successive countable limits with

```math
\gamma_{s+1} \gt \max\{\gamma_s,\ h(\gamma_s)\}
```

and put $`\Lambda = \sup_{s \lt \omega} \gamma_s`$.

Any finite parameters from $`L_\Lambda`$ lie in some $`L_{\gamma_s}`$, and their Skolem values lie in
$`L_{h(\gamma_s)} \subseteq L_{\gamma_{s+1}} \subseteq L_\Lambda`$.
Hence $`L_\Lambda`$ is closed under all Skolem functions, and by the Tarski–Vaught test
$`L_\Lambda \prec L_\Theta`$. Being a full elementary submodel, $`L_\Lambda \models \mathrm{KP}`$ as well.
$`\square`$

### 2.4 (16.2)

$`L_\Lambda \prec L_\Theta`$ has no restriction on the number of alternations, so for every
$`k \in \mathbb{N}`$

```math
\Lambda \lhd_k \Theta . \tag{16.2}
```

This is the starting point for the stable labels (Lemma 20.1).

## 3. Theorem 17.1

### 3.1 Statement

Let $`r, n \in \mathbb{N}`$ with $`n \lt r`$. Let $`\alpha, \beta`$ be admissible with
$`\alpha \lhd_n \beta`$. Let $`X \subseteq \alpha`$ be a finite set of admissible ordinals, and let

```math
Y = \{y_0 \lt \cdots \lt y_{s-1}\} \subseteq [\alpha, \beta)
```

be a nonempty finite set of admissible ordinals. Then there exists a set of admissible ordinals

```math
Y' = \{y'_0 \lt \cdots \lt y'_{s-1}\} \subseteq \alpha
```

satisfying all of the following (17.1)–(17.4).

```math
\max(X \cup \{\omega\}) \lt y'_0 \tag{17.1}
```
```math
\forall x \in X\ \forall i \lt s\ \forall k \lt r\ \bigl(x \lhd_k y_i \Longrightarrow x \lhd_k y'_i\bigr) \tag{17.2}
```
```math
\forall i \lt s\ \forall j \lt s\ \forall k \lt r\ \bigl(y_i \lhd_k y_j \Longrightarrow y'_i \lhd_k y'_j\bigr) \tag{17.3}
```
```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lhd_m \beta \Longrightarrow y'_i \lhd_m \alpha\bigr) \tag{17.4}
```

**How to read it.** Finitely many admissible ordinals $`Y`$ lying in $`[\alpha, \beta)`$ can be pushed
down below $`\alpha`$ with all the $`\lhd`$ relations preserved.

### 3.2 The proof

Inside $`L_\beta`$, impose the following finitely many conditions on variables
$`u_0, \dots, u_{s-1}`$.

| Group | Condition |
|---|---|
| 1 | $`\mathrm{Adm}(u_i)`$, $`x \lt u_0`$ for each $`x \in X`$, and $`\omega \lt u_0 \lt \cdots \lt u_{s-1}`$ |
| 2 | $`\mathrm{Rel}_k(x, u_i)`$ for each $`x \lhd_k y_i`$ true externally |
| 3 | $`\mathrm{Rel}_k(u_i, u_j)`$ for each $`y_i \lhd_k y_j`$ true externally |
| 4 | $`\mathrm{St}_m(u_i)`$ for each $`y_i \lhd_m \beta`$ ($`m \lt n`$) true externally |

Let $`\Phi(\vec u)`$ be the finite conjunction of these. As in 3.3 of the alternating-block note,

```math
\exists u_0 \cdots \exists u_{s-1}\ \Phi(\vec u) \ \in\ \hat\Sigma_{n+2} . \tag{17.5}
```

In $`L_\beta`$, $`u_i = y_i`$ are witnesses. By Lemmas 11.2, 15.3 and 15.5, $`L_\beta`$ recognizes the four
groups of conditions correctly. By the hypothesis $`L_\alpha \prec^*_{n+2} L_\beta`$, (17.5) is true in
$`L_\alpha`$ as well. Let $`y'_0, \dots, y'_{s-1}`$ be its witnesses.

The rest is just reading off.

| What we get | Grounds |
|---|---|
| each $`y'_i`$ is admissible externally too | $`L_\alpha \models \mathrm{Adm}(y'_i)`$ and Lemma 11.2 |
| $`y'_i \lt \alpha`$ | $`y'_i \in L_\alpha \cap \mathrm{Ord} = \alpha`$ (constructible hierarchy note §9) |
| (17.1) | the order conditions of group 1 |
| (17.2), (17.3) | the $`\mathrm{Rel}_k`$ conditions inside $`L_\alpha`$ and Lemma 15.5(2) |
| (17.4) | $`L_\alpha \models \mathrm{St}_m(y'_i)`$ and Lemma 15.3 |

$`\square`$

### 3.3 Why only group 4 uses St

Groups 2 and 3 use $`\mathrm{Rel}_k`$, and only group 4 uses $`\mathrm{St}_m`$. The reason lies in how
$`\beta`$ is handled.

One would like to write $`\mathrm{Rel}_m(u_i, \beta)`$, but one cannot.
Since $`L_\beta \cap \mathrm{Ord} = \beta`$ we have $`\beta \notin L_\beta`$, so $`\beta`$ has no name
inside $`L_\beta`$.

$`\mathrm{St}_m(u_i)`$ means "$`u_i \lhd_m`$ the universe we are in" (1.3). So

```
read inside L_β    y_i ◁_m β
read inside L_α    y'_i ◁_m α
```

The same single formula swaps its partner depending on where it is read. This is what the push-down in
(17.4) really is.

### 3.4 The role of n < r

Only group 4 matters for the complexity computation.

- The $`k`$ in groups 2 and 3 ranges over $`k \lt r`$, but $`\mathrm{Rel}_k`$ is $`\hat\Sigma_1`$
  independently of $`k`$ (1.4). So the complexity does not rise however large $`r`$ is
- The $`\mathrm{St}_m`$ of group 4 is $`\hat\Pi_{m+2}`$, and $`m \lt n`$, so it fits inside
  $`\hat\Pi_{n+1}`$

As a result (17.5) is $`\hat\Sigma_{n+2}`$, which matches the hypothesis $`\alpha \lhd_n \beta`$ exactly.
$`n \lt r`$ is the condition needed to use $`n = m_0`$ (the largest parent row) and $`r`$ as the number of
rows in Proposition 19.1.

### 3.5 How it is used in Proposition 19.1

In the induction step showing that one expansion lowers the height, it is applied as follows
(the paper §19).

```
n = m_0        the largest parent row
α = f(p)       the label at the position of the m_0-parent
β = f(c)       the label of the last column
X              all labels of columns before the copy interval
Y              the labels of the copy interval, y_0 < … < y_{s-1}
```

From $`p \prec^A_{m_0} c`$ and the stable-label conditions we get $`\alpha \lhd_{m_0} \beta`$, so
Theorem 17.1 applies. Replacing the labels of the old copy by the resulting $`Y'`$ lets us reassign the
original $`y_i`$ to the new copy.

## 4. How it is used in the paper

| Place | Use |
|---|---|
| Definition 11.1, Lemma 11.2 | $`\mathrm{Adm}`$ and its correctness |
| Definition 15.2, Lemma 15.3 | $`\mathrm{St}_k`$ and its correctness |
| Definition 15.4, Lemma 15.5 | $`\mathrm{Rel}_k`$ and its correctness |
| Lemma 16.1 | $`L_\gamma`$ is countable when $`\gamma \lt \omega_1^V`$ |
| Lemma 16.2, (16.2) | the initial pair $`\Lambda \lhd_k \Theta`$ |
| Theorem 17.1 | finite row reflection |
| Lemma 20.1 | uses (16.2) to build the stable labels of $`E_r`$ |
| Proposition 19.1 | uses Theorem 17.1 with $`n = m_0`$ to lower the height |

## 5. Counterparts in Lean

| Concept | Lean | File |
|---|---|---|
| $`\mathrm{KPTrue}`$ of Definition 11.1 | `KPTrue` | `Bm4/SetTheory/AdmKP.lean` |
| $`\mathrm{Adm}`$ of Definition 11.1 | `AdmKP` | same |
| $`\mathrm{KPAx}`$ | `KPAxCode` | `Bm4/SetTheory/KPAx.lean` |
| $`\mathrm{Adm} \in \hat\Sigma_1`$ | `sigmaDef_admKP` | `Bm4/SetTheory/AdmKP.lean` |
| Lemma 11.2 | `admKP_iff` | same |
| $`\mathrm{St}_k`$ of Definition 15.2 | `StKP` | `Bm4/SetTheory/StKP.lean` |
| $`\mathrm{St}_k \in \hat\Pi_{k+2}`$ | `piDef_StKP` | same |
| Lemma 15.3 | `stKP_iff` | same |
| $`\mathrm{Rel}_k`$ of Definition 15.4 | `RelKP` | same |
| $`\mathrm{Rel}_k \in \hat\Sigma_1`$ | `sigmaDef_RelKP` | same |
| Lemma 15.5(2) | `relKP_iff` | same |
| Lemma 15.5(1) | `relKP_iff_ext` | same |
| Lemma 16.1 | `L_countable` | `Bm4/SetTheory/Omega1.lean` |
| $`\omega_1`$ is admissible | `isAdmissible_omega1` | same |
| Skolem hull | `Bm4/SetTheory/Skolem.lean` | same |
| Lemma 16.2 | `exists_admissible_elemFull_pair` | `Bm4/SetTheory/AdmTrans.lean` |
| (16.2) | `exists_relAdm_all` | `Bm4/SetTheory/Stable.lean` |
| Theorem 17.1 | `reflect_pattern` | `Bm4/SetTheory/Reflect.lean` |
| the complexity computation of (17.5) | `sigmaDef_blk`, `sigmaDef_bigAnd`, `PiDef.toSigma` | same |
