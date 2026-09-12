[← Back](README.md) | [English](02-levy-hierarchy.md) | [Japanese](../02-levy-hierarchy.md)

# The Lévy hierarchy and absoluteness

Prerequisite: [The constructible hierarchy L](01-constructible-hierarchy.md) (formulas, the
structure $`(X,\in)`$, satisfaction $`\models`$, transitive sets)

## 1. Bounded and unbounded quantification

**Definition (unbounded quantification).** An $`\exists z`$ or $`\forall z`$ occurring in a
formula, in that bare form, is called **unbounded quantification**.

**Meaning.** There is no restriction on the range of $`z`$. It runs over every set in the
universe.

**Definition (bounded quantification).** For a variable $`z`$ and a variable $`y`$ different
from $`z`$, we use the following abbreviations.

```math
\exists z \in y\ \varphi \ \equiv\ \exists z\,(z \in y \wedge \varphi), \qquad
\forall z \in y\ \varphi \ \equiv\ \forall z\,(z \in y \to \varphi)
```

Here $`y`$ is assumed not to be bound by $`z`$ inside $`\varphi`$. This form is called
**bounded quantification**.

**Meaning.** The range of $`z`$ is restricted to the elements of $`y`$. The range in which
$`z`$ is sought is specified in advance by the variable $`y`$.

**How to tell them apart.** Expanding a bounded quantifier out of its abbreviation produces an
$`\exists z`$, but it always comes paired with $`z \in y \wedge \cdots`$. A bare $`\exists z`$
or $`\forall z`$ that is not in such a pair is unbounded quantification.

| Formula | Kind |
|---|---|
| $`\forall z \in x\ (z \in y)`$ | one bounded |
| $`\forall y \in x\ \forall z \in y\ (z \in x)`$ | two bounded |
| $`\exists z\ (x \in z)`$ | one unbounded |
| $`\forall w\,(w \subseteq x \to w \in z)`$ | one unbounded; the inside of $`w \subseteq x`$ is bounded |

The difference between bounded and unbounded is what matters in §3 below.

## 2. Δ₀ formulas

### 2.1 Definition

A formula $`\varphi`$ is $`\Delta_0`$ if **every quantifier occurring in $`\varphi`$ is
bounded**.

Atomic formulas ($`x = y`$ and $`x \in y`$) have no quantifiers, so they are $`\Delta_0`$.
$`\Delta_0`$ formulas joined by $`\neg, \wedge, \vee, \to`$ are $`\Delta_0`$, and a $`\Delta_0`$
formula with a bounded quantifier put on it is $`\Delta_0`$. That is the whole collection.

### 2.2 Examples writable in Δ₀

| Meaning | $`\Delta_0`$ formula |
|---|---|
| $`x \subseteq y`$ | $`\forall z \in x\ (z \in y)`$ |
| $`x = \emptyset`$ | $`\neg \exists z \in x\ (z = z)`$ |
| $`x`$ is transitive | $`\forall y \in x\ \forall z \in y\ (z \in x)`$ |
| $`x`$ is an ordinal | $`x`$ is transitive $`\wedge\ \forall y \in x\ (y`$ is transitive$`)`$ |
| $`z = \{x, y\}`$ | $`x \in z \wedge y \in z \wedge \forall w \in z\ (w = x \vee w = y)`$ |
| $`z = x \cup y`$ | $`\forall w \in z\,(w \in x \vee w \in y) \wedge \forall w \in x\,(w \in z) \wedge \forall w \in y\,(w \in z)`$ |
| $`z = \bigcup x`$ | $`\forall w \in z\ \exists u \in x\ (w \in u) \wedge \forall u \in x\ \forall w \in u\ (w \in z)`$ |
| $`x`$ is a limit ordinal | $`x`$ is an ordinal $`\wedge\ \neg(x = \emptyset) \wedge \forall y \in x\ \exists z \in x\ (y \in z)`$ |
| $`x = \omega`$ | $`x`$ is a limit ordinal $`\wedge\ \forall y \in x\ \neg(y`$ is a limit ordinal$`)`$ |

The ordered pair $`z = \langle x, y \rangle = \{\{x\},\{x,y\}\}`$ is $`\Delta_0`$ too. The
elements of $`z`$ are just the two sets $`\{x\}`$ and $`\{x,y\}`$, so one bounds by
$`\exists u \in z`$ and $`\exists v \in z`$ and uses the row for $`z = \{x,y\}`$ above.

Finite sequences, finite functions, and their lengths, components and concatenations come out
$`\Delta_0`$ in the same way. This is what the paper means when it repeats in §8 that "these
are $`\Delta_0`$".

### 2.3 Examples that do not look writable in Δ₀

A bounded quantifier $`\exists z \in y`$ means "search only among the elements of $`y`$". So to
make a quantifier bounded, **a set containing everything one is searching for must already be
at hand as a variable**. "At hand" means the free variables and whatever the operations of 2.2
reach from them.

Here are three examples where that fails.

**$`z = P(x)`$.** What one wants to say is "every subset of $`x`$ is in $`z`$". The $`w`$ one
wants to range over is all subsets of $`x`$, and the only set containing them is $`P(x)`$. But
$`P(x)`$ is precisely what one is trying to define as $`z`$. Writing $`\forall w \in z`$ only
lets one speak "about what is already in $`z`$", and the essential "everything is in" cannot be
said.

Ranging over the elements of $`x`$ does not reach them either, because $`\in`$ and
$`\subseteq`$ are different.

| | Content | Number |
|---|---|---|
| elements of $`x = \{0,1\}`$ | $`0,\ 1`$ | 2 |
| subsets of $`x`$ | $`\emptyset,\ \{0\},\ \{1\},\ \{0,1\}`$ | 4 |

The lower row is not made of elements of $`x`$, so $`\forall w \in x`$ cannot pick it up.

**$`x`$ is countable.** One wants to say that a bijection $`f : x \to \omega`$ exists. Such an
$`f`$ is a set of $`\langle a, n \rangle`$, that is, a subset of $`x \times \omega`$. The range
one wants is $`P(x \times \omega)`$, which no amount of looking at the elements of $`x`$ and
$`\omega`$ produces.

**$`x`$ is a cardinal.** One wants to say "there is no surjection from $`\alpha \lt x`$ onto
$`x`$". Again there is no range for $`f`$.

All of this is about "no way of writing it comes to mind". A proof that it *cannot* be written
is given in §3.5. The names for the complexities are given in §4.5.

## 3. Δ₀ absoluteness

This is the main point of the note.

### 3.1 Statement

**Theorem ($`\Delta_0`$ absoluteness).** Let $`M`$ be a transitive set, $`\varphi`$ a
$`\Delta_0`$ formula and $`\bar a`$ an assignment with values in $`M`$. Then

```math
(M, \in) \models \varphi[\bar a] \quad\iff\quad \varphi[\bar a] .
```

The right-hand side means "it really holds in the whole universe".

That is, **the truth value of a $`\Delta_0`$ formula is the same whether measured inside or
outside a transitive set**.

### 3.2 Proof

By induction on how $`\varphi`$ is built.

**Atomic formulas.** $`(M,\in) \models (x \in y)[\bar a]`$ means
$`\bar a(x) \in \bar a(y)`$, and $`(x \in y)[\bar a]`$ also means
$`\bar a(x) \in \bar a(y)`$. The same. $`x = y`$ likewise.

**Connectives.** $`\neg`$, $`\wedge`$, $`\vee`$, $`\to`$ are determined on both sides by the
same rule from the truth values of the subformulas. Just use the induction hypothesis.

**Bounded existential quantification.** Let $`\varphi = \exists z \in y\ \psi`$. From the
definition of satisfaction,

```math
(M,\in) \models \varphi[\bar a]
\iff \text{there is } c \in M \text{ with } c \in \bar a(y) \text{ and }
(M,\in) \models \psi[\bar a(z \mapsto c)].
```

The induction hypothesis replaces the last part by $`\psi[\bar a(z \mapsto c)]`$. On the
outside,

```math
\varphi[\bar a]
\iff \text{there is } c \text{ with } c \in \bar a(y) \text{ and } \psi[\bar a(z \mapsto c)].
```

The only difference is whether $`c`$ is taken from $`M`$ or from the whole universe. But
$`\bar a(y) \in M`$ and $`M`$ is transitive, so

```math
\bar a(y) \subseteq M .
```

Hence $`c \in \bar a(y)`$ automatically gives $`c \in M`$. The two conditions coincide.

**Bounded universal quantification.**
$`\forall z \in y\ \psi \equiv \neg \exists z \in y\ \neg\psi`$ reduces it to the above.
$`\square`$

Transitivity was used in exactly one place, the bounded quantifier. That "the elements of
$`\bar a(y)`$ are automatically elements of $`M`$" can be said there is the whole of this
theorem.

### 3.3 Transitivity cannot be dropped

Let $`M = \{\emptyset, \{\{\emptyset\}\}\}`$. This is not transitive: indeed
$`\{\emptyset\} \in \{\{\emptyset\}\} \in M`$ but $`\{\emptyset\} \notin M`$.

Take $`\varphi(x) \equiv \exists z \in x\ (z = z)`$ ("$`x`$ is nonempty"). It is
$`\Delta_0`$. Take the assignment $`\bar a(x) = \{\{\emptyset\}\}`$.

- In $`(M,\in)`$ one looks for $`c \in M`$ with $`c \in \{\{\emptyset\}\}`$. The candidates are
  $`\emptyset`$ and $`\{\{\emptyset\}\}`$, and neither is an element of $`\{\{\emptyset\}\}`$.
  So it is **false**
- Outside, $`\{\emptyset\} \in \{\{\emptyset\}\}`$, so it is **true**

They disagree even though the formula is $`\Delta_0`$. That is why transitivity is needed.

### 3.4 What this buys

In §2 of the previous note we made an example where $`(X,\in) \models`$ and "really holds"
differ. This theorem says that for $`\Delta_0`$ they do not differ.

In other words:

> If you search with a $`\Delta_0`$ condition, what you find inside a transitive set is the
> real thing.

The paper uses it repeatedly in this form.

- $`\mathrm{SatCode}(A,U,T)`$ is $`\Delta_0`$ (equation 8.5). So if one finds $`U, T`$
  satisfying $`\mathrm{SatCode}`$ inside $`L_\theta`$, they are a genuine satisfaction code
  seen from outside as well
- $`\mathrm{LCode}(\eta,M,c)`$ is $`\Delta_0`$ (equation 9.4). So an $`L`$-hierarchy code found
  inside $`L_\theta`$ is correct outside too, and Lemma 9.2 gives $`M = L_\eta`$ outside as
  well (Corollary 10.6)

The converse direction comes at the same time: if it is true outside then it is true inside.

### 3.5 How to show that something is not writable in Δ₀

Take the contrapositive of §3.1. Since

```math
\varphi \in \Delta_0 \ \Longrightarrow\ \text{absolute for transitive sets}
```

we get:

> If there is a transitive set $`M`$ and an assignment $`\bar a`$ with values in $`M`$ for
> which $`(M,\in) \models \varphi[\bar a]`$ and $`\varphi[\bar a]`$ disagree, then $`\varphi`$
> is not $`\Delta_0`$.

**Example.**

```math
\psi(x) \ \equiv\ \exists z\ (x \in z)
```

meaning "$`x`$ is an element of something". It is a formula that looks simple, with just one
unbounded quantifier.

Take $`M = L_2 = \{\emptyset, \{\emptyset\}\}`$. This is transitive, because $`\emptyset`$ has
no elements and the only element $`\emptyset`$ of $`\{\emptyset\}`$ belongs to $`M`$. Take the
assignment $`\bar a(x) = \{\emptyset\}`$.

- In $`(M,\in)`$ the candidates $`z`$ are just $`\emptyset`$ and $`\{\emptyset\}`$. Neither
  $`\{\emptyset\} \in \emptyset`$ nor $`\{\emptyset\} \in \{\emptyset\}`$ holds, so it is
  **false**
- Outside, $`\{\emptyset\} \in \{\{\emptyset\}\}`$, so it is **true**

They disagree, so $`\psi`$ is not $`\Delta_0`$.

**The number of quantifiers is irrelevant.** This example also shows that being $`\Delta_0`$ is
not a matter of the number of quantifiers. The $`x = \omega`$ of §2.2 has a dozen or so bounded
quantifiers when expanded and is $`\Delta_0`$, whereas the $`\psi`$ here has only one unbounded
quantifier and is not $`\Delta_0`$. What matters is not the number but whether a set bounding
the quantifier is at hand.

The three examples of §2.3 can be shown not to be $`\Delta_0`$ by the same method. But building
an $`M`$ where the truth values disagree is heavier than in the example above and needs an
argument taking a countable transitive model, which is omitted here.

## 4. Σ₁ and Π₁

### 4.1 Blocks

**Definition.** Among the unbounded quantifiers lined up at the front of a formula, **a run of
consecutive quantifiers of the same kind** is called a **block**. A block ends where the kind
changes from $`\exists`$ to $`\forall`$ or from $`\forall`$ to $`\exists`$.

**Meaning.** However many quantifiers of the same kind are lined up, they are one block. What
is counted is not the number of quantifiers but the number of times the kind switches.

**Examples.**

| Formula | How the blocks split | Number of blocks |
|---|---|---|
| $`\exists x_1\, \exists x_2\, \exists x_3\ \delta`$ | $`\exists x_1 \exists x_2 \exists x_3`$ | 1 |
| $`\forall x_1\, \forall x_2\ \delta`$ | $`\forall x_1 \forall x_2`$ | 1 |
| $`\exists x_1\, \exists x_2\, \forall y_1\ \delta`$ | $`\exists x_1 \exists x_2`$ \| $`\forall y_1`$ | 2 |
| $`\exists x\, \forall y\, \exists z\ \delta`$ | $`\exists x`$ \| $`\forall y`$ \| $`\exists z`$ | 3 |

### 4.2 Definition of Σ₁ and Π₁

**Definition.** Let $`\delta`$ be a $`\Delta_0`$ formula. The formulas of the forms

```math
\Sigma_1 :\ \exists x_1 \cdots \exists x_n\ \delta, \qquad
\Pi_1 :\ \forall x_1 \cdots \forall x_n\ \delta
```

are called $`\Sigma_1`$ and $`\Pi_1`$ respectively. The leading $`\exists x_i`$ and
$`\forall x_i`$ carry no $`\in y`$, so they are unbounded quantification (§1).

**$`\Delta_0`$ is included.** Reading $`n = 0`$, that is, the block being empty, a $`\Delta_0`$
formula is itself both $`\Sigma_1`$ and $`\Pi_1`$.

### 4.3 One-sided absoluteness

**Theorem.** Let $`M`$ be a transitive set and $`\bar a`$ an assignment with values in $`M`$.

```math
\varphi \in \Sigma_1 \ \Longrightarrow\
\bigl[\ (M,\in) \models \varphi[\bar a] \ \Longrightarrow\ \varphi[\bar a]\ \bigr]
```

```math
\psi \in \Pi_1 \ \Longrightarrow\
\bigl[\ \psi[\bar a] \ \Longrightarrow\ (M,\in) \models \psi[\bar a]\ \bigr]
```

The former is called **upward absolute**, the latter **downward absolute**.

**Proof.** Let $`\varphi = \exists \bar x\ \delta`$. If
$`(M,\in) \models \varphi[\bar a]`$ then there are witnesses $`\bar c \in M`$ with
$`(M,\in) \models \delta[\bar c, \bar a]`$. Since $`\delta`$ is $`\Delta_0`$, §3 makes
$`\delta[\bar c, \bar a]`$ really true, hence $`\exists \bar x\ \delta`$ is true.

Let $`\psi = \forall \bar x\ \delta`$. If $`\psi[\bar a]`$ is true then in particular
$`\delta[\bar c, \bar a]`$ is true for elements $`\bar c`$ of $`M`$. By §3,
$`(M,\in) \models \delta[\bar c, \bar a]`$. Since $`\bar c`$ was an arbitrary element of $`M`$,
$`(M,\in) \models \psi[\bar a]`$. $`\square`$

### 4.4 An example where the converse fails

Look again at

```math
\psi(x) \ \equiv\ \exists z\ (x \in z)
```

from §3.5. $`x \in z`$ is atomic, hence $`\Delta_0`$, with one $`\exists`$ block $`\exists z`$
in front of it. So it has the form of 4.2 and is $`\Sigma_1`$.

The computation with $`M = L_2`$ and $`\bar a(x) = \{\emptyset\}`$ is as in §3.5: **true**
outside, **false** inside. The converse of upward absoluteness for $`\Sigma_1`$ fails, because
the witness $`\{\{\emptyset\}\}`$ lies outside $`M`$.

For $`\Pi_1`$ it is the other way round: if a counterexample lies outside $`M`$, the formula can
be true inside but false outside.

### 4.5 The complexity of the examples of §2.3

Now that $`\Sigma_1`$ and $`\Pi_1`$ are defined, the three things that could not be written in
$`\Delta_0`$ in §2.3 can be named.

| Meaning | Shape of the formula | Complexity |
|---|---|---|
| $`z = P(x)`$ | $`\forall w\,(w \subseteq x \to w \in z) \wedge \forall w \in z\,(w \subseteq x)`$ | $`\Pi_1`$ |
| $`x`$ is countable | $`\exists f\,\exists w\,(w = \omega \wedge f`$ is a bijection from $`x`$ to $`w`$$`)`$ | $`\Sigma_1`$ |
| $`x`$ is a cardinal | $`x`$ is an ordinal $`\wedge\ \forall f\,\forall \alpha \in x\,(f`$ is not a surjection from $`\alpha`$ onto $`x`$$`)`$ | $`\Pi_1`$ |

In every row, what is left after removing the leading unbounded block is $`\Delta_0`$:
$`w \subseteq x`$, $`w = \omega`$ and "$`f`$ is a bijection" can all be written in the style of
2.2. The $`\forall \alpha \in x`$ in the third row is bounded, so the only unbounded block is
$`\forall f`$.

By §4.3, $`z = P(x)`$ and "$`x`$ is a cardinal" are downward absolute, and "$`x`$ is countable"
is upward absolute.

## 5. Higher levels of the hierarchy

Stacking blocks gives a hierarchy. $`\Sigma_{n+1}`$ is a $`\Pi_n`$ formula with an unbounded
$`\exists`$ block in front, and $`\Pi_{n+1}`$ is a $`\Sigma_n`$ formula with an unbounded
$`\forall`$ block in front. This is called the **Lévy hierarchy**.

The paper does not use general Lévy formulas with $`n \ge 2`$. Instead it defines in §12 the
**strict alternating block hierarchy** $`\hat\Sigma_q, \hat\Pi_q`$ and uses that, because
turning a general Lévy formula into a simple prenex form can require Collection, which it wants
to avoid (Remark 12.3 of the paper).

For $`q = 1`$ the two agree.

```math
\hat\Sigma_1 = \Sigma_1, \qquad \hat\Pi_1 = \Pi_1
```

They start to differ from $`q \ge 2`$. $`\hat\Sigma_q`$ gets its own note.

## 6. How it is used in the paper

The places where the paper claims "this is $`\Delta_0`$" are as follows. All of them are there
in order to use "what you find inside is the real thing" from §3.4.

| Place | Claim |
|---|---|
| §8 (8.3) | the graph $`G_F`$ of a syntactic operation is $`\Delta_0`$ |
| §8 (8.4) | appropriateness of an assignment, $`\mathrm{Asn}_A`$, is $`\Delta_0`$ |
| §8 (8.5) | $`\mathrm{SatCode}`$ is $`\Delta_0`$ |
| §9 | $`\mathrm{FourCode}`$ and $`\mathrm{DefInp}`$ are $`\Delta_0`$ |
| §9 (9.4) | $`\mathrm{LCode}`$ is $`\Delta_0`$ |
| §11 | $`\mathrm{KPAx}`$ is $`\Delta_0`$ |
| §12 | $`\mathrm{BlkUpd}`$ is $`\Delta_0`$, and so are the syntactic operations of Lemma 12.2 |
| §14 | the relativized $`\mathrm{Tr}^M_{\hat\Sigma_j}`$ is $`\Delta_0`$ with $`M`$ as a parameter |
| §15 | the relativized $`\mathrm{St}_k(\xi)^M`$ is $`\Delta_0`$ |

$`\Sigma_1`$ appears, for instance, in equation (13.1) as
$`\mathrm{Tr}^+_{\Delta_0} \in \hat\Sigma_1`$ and
$`\mathrm{Tr}^-_{\Delta_0} \in \hat\Pi_1`$.

Incidentally, $`\Delta_0`$ also appears in the axiom system KP itself, defined in §10 of the
paper, namely in $`\Delta_0`$-Separation and $`\Delta_0`$-Collection. That is treated in the
next note.

## 7. Correspondence in Lean

| Concept | Lean | File |
|---|---|---|
| bounded universal $`\forall z \in y`$ | `Fm.ball i j φ` | `Bm4/SetTheory/Fm.lean` |
| bounded existential $`\exists z \in y`$ | `Fm.bex i j φ` | same |
| $`\Delta_0`$ formula | `IsDelta0` | same |
| $`\Delta_0`$ absoluteness (transitive quantification domain) | `IsDelta0.sat_iff_satV` | same |
| $`\Delta_0`$ absoluteness (transitive set $`W`$) | `IsDelta0.satIn_iff_satV` | same |
| absoluteness between two transitive sets | `IsDelta0.satIn_iff_satIn` | same |
| $`\hat\Sigma_q`$ / $`\hat\Pi_q`$ formula | `IsSigma q φ` / `IsPi q φ` | same |
| transitive quantification domain | `TransDom` | `Bm4/SetTheory/Defin.lean` |
| nonempty transitive quantification domain | `GoodDom` | same |
| $`\Delta_0`$-definable predicate | `Delta0Def s P` | same |
| $`\hat\Sigma_q`$ / $`\hat\Pi_q`$-definable predicate | `SigmaDef q s P` / `PiDef q s P` | same |
| closure under bounded quantification | `Delta0Def.ball`, `Delta0Def.bex` | same |
