[← Back](README.md) | [English](03-kp-admissible.md) | [Japanese](../03-kp-admissible.md)

# KP and admissible ordinals

Prerequisites

| Note | Terms used from here |
|---|---|
| [The constructible hierarchy L](01-constructible-hierarchy.md) | formula, structure $`(X,\in)`$, assignment $`\bar a`$, satisfaction $`\models`$, transitive, $`\mathrm{Def}`$, $`L_\xi`$ |
| [The Levy hierarchy and absoluteness](02-levy-hierarchy.md) | bounded quantifier, $`\Delta_0`$, $`\Delta_0`$ absoluteness, $`\Sigma_1`$, $`\Pi_1`$ |

## 1. Sentences, axiom systems, models

**Definition (sentence).** A formula with no free variables is called a **sentence**.

**Meaning.** A sentence has a truth value without being handed an assignment. So instead of
$`(M, \in) \models \varphi[\bar a]`$ one can write

```math
(M, \in) \models \varphi
```

Below this is abbreviated $`M \models \varphi`$.

**Definition (schema).** A rule associating one sentence to each formula $`\varphi`$ is called a
**schema**. There are infinitely many formulas, so one schema denotes infinitely many sentences.

**Definition (axiom system, model).** A collection $`T`$ of sentences is called an **axiom system**.
When a set $`M`$ satisfies

```math
M \models T \quad :\iff\quad M \models \varphi \text{ for every } \varphi \in T
```

$`M`$ is called a **model** of $`T`$.

## 2. The axioms of KP

**Definition.** **KP** (Kripke–Platek set theory) is the axiom system consisting of the following eight
(the paper, start of §10). The last three are schemas.

### Extensionality

```math
\forall x\,\forall y\,\bigl(\forall z\,(z \in x \leftrightarrow z \in y) \to x = y\bigr)
```

Two sets with the same elements are equal.

### Empty Set

```math
\exists x\,\forall z\,\neg(z \in x)
```

There is a set with no elements.

### Pairing

```math
\forall x\,\forall y\,\exists z\,(x \in z \wedge y \in z)
```

There is a set $`z`$ containing both $`x`$ and $`y`$. $`z`$ may have extra elements.
When exactly $`\{x,y\}`$ is needed, carve it out of $`z`$ by $`\Delta_0`$-Separation.

### Union

```math
\forall x\,\exists z\,\forall y \in x\,\forall w \in y\,(w \in z)
```

There is a set $`z`$ containing all elements of elements of $`x`$. This too may have extras;
exactly $`\bigcup x`$ is obtained by $`\Delta_0`$-Separation.

### Infinity

```math
\exists x\,\bigl(\exists e \in x\,(e = \emptyset)
\ \wedge\ \forall y \in x\,\exists s \in x\,(s = y \cup \{y\})\bigr)
```

There is an **inductive set**, that is, a set containing $`\emptyset`$ and containing $`y \cup \{y\}`$
whenever it contains $`y`$. This $`x`$ contains all of
$`\emptyset, \{\emptyset\}, \{\emptyset,\{\emptyset\}\}, \dots`$, so it is infinite.
In §5, $`L_\omega`$ fails to be a model of KP precisely because this axiom fails.

### Δ₀-Separation

For each $`\Delta_0`$ formula $`\varphi(z, \bar p)`$,

```math
\forall a\,\forall \bar p\,\exists b\,\forall z\,\bigl(z \in b \leftrightarrow (z \in a \wedge \varphi(z, \bar p))\bigr)
```

From an existing $`a`$, one can carve out just the elements satisfying the condition $`\varphi`$.
The difference from ZF is that the carving condition is restricted to $`\Delta_0`$.

### Δ₀-Collection

For each $`\Delta_0`$ formula $`\varphi(x, y, \bar p)`$,

```math
\forall a\,\forall \bar p\,\Bigl(\forall x \in a\,\exists y\ \varphi(x,y,\bar p)
\ \to\ \exists b\,\forall x \in a\,\exists y \in b\ \varphi(x,y,\bar p)\Bigr)
```

Read the antecedent and the consequent separately.

**Antecedent** $`\ \forall x \in a\ \exists y\ \varphi(x,y,\bar p)`$

For every element $`x`$ of $`a`$ there is a $`y`$ satisfying $`\varphi(x,y,\bar p)`$.
This $`\exists y`$ is unbounded, so $`y`$ may be anywhere in the universe.

**Consequent** $`\ \exists b\ \forall x \in a\ \exists y \in b\ \varphi(x,y,\bar p)`$

There is a set $`b`$ containing at least one such $`y`$ for every $`x`$ in $`a`$.
$`b`$ may contain extra elements.

**What it says.** The $`y`$'s, which existed separately for each $`x`$, can be captured together in a
single set $`b`$. This "antecedent $`\to`$ consequent" shape is called **Collection**.
A version with a higher-complexity condition $`\varphi`$ appears in §9.

**Why it is not trivial.** The antecedent says only "for each $`x`$ there is a $`y`$". If the $`y`$'s
grow larger and larger with $`x`$, there might be no set containing all of them. Collection asserts that
this does not happen.

**It is the special axiom.** As seen in §6.2, the other seven axioms hold automatically in $`L_\theta`$
whenever $`\theta`$ is a limit greater than $`\omega`$. This is the only one that is not automatic, and
it is effectively the single condition for admissibility (§6.3).

### Set Induction

For each formula $`\varphi`$,

```math
\forall x\,\bigl((\forall y \in x\ \varphi(y)) \to \varphi(x)\bigr) \ \to\ \forall x\ \varphi(x)
```

If "whenever $`\varphi`$ holds for all elements of $`x`$ it holds for $`x`$" can be shown, then
$`\varphi`$ holds for every $`x`$. It is induction along $`\in`$.

## 3. What was dropped from ZF

| Axiom | ZF | KP |
|---|---|---|
| Extensionality, Empty Set, Pairing, Union, Infinity | yes | yes |
| Foundation / Set Induction | yes | yes |
| **Power Set** | yes | **absent** |
| Separation | arbitrary formulas | **$`\Delta_0`$ only** |
| Replacement / Collection | arbitrary formulas | **$`\Delta_0`$ only** |

There is a single reason for the removals: what does not fit inside $`\Delta_0`$ is excluded.

- Power Set: as in §4.5 of the Levy hierarchy note, $`z = P(x)`$ is $`\Pi_1`$ and cannot be written
  $`\Delta_0`$
- Restricting Separation and Replacement to $`\Delta_0`$ is for the same reason

Keeping only $`\Delta_0`$ lets §3.4 of the Levy hierarchy note,

> if you search using a $`\Delta_0`$ condition, what you find inside a transitive set is the real thing

apply as it stands. Being weaker, KP can be satisfied by a smaller $`L_\theta`$. The paper uses exactly
this strength: "small, yet enough for the constructions needed".

## 4. Admissible ordinals

**Definition.** An ordinal $`\theta`$ is **admissible** if

```math
L_\theta \models \mathrm{KP}
```

holds.

**Meaning.** It says $`L_\theta`$ is "large enough to be usable as set theory". The measure of largeness
is $`\mathrm{KP}`$.

## 5. ω is not admissible

Look at which axioms of KP are satisfied by $`L_\omega = \mathrm{HF}`$ (all hereditarily finite sets).

| Axiom | Does it hold in $`L_\omega`$? |
|---|---|
| Extensionality | yes |
| Empty Set | yes, $`\emptyset \in \mathrm{HF}`$ |
| Pairing | yes, if $`x, y`$ are hereditarily finite so is $`\{x,y\}`$ |
| Union | yes, likewise |
| $`\Delta_0`$-Separation | yes, a subset of a finite set is hereditarily finite |
| $`\Delta_0`$-Collection | yes |
| Set Induction | yes |
| **Infinity** | **no** |

Only Infinity fails. An inductive set $`x`$ contains all of
$`\emptyset, \{\emptyset\}, \{\emptyset,\{\emptyset\}\}, \dots`$, so it is infinite. But every element of
$`L_\omega`$ is finite (constructible hierarchy note §7). So $`L_\omega`$ has no inductive set.

```math
L_\omega \not\models \mathrm{KP}
```

Hence $`\omega`$ is not admissible.

## 6. The substantive condition is Δ₀-Collection alone

Look from both directions at what follows when $`\theta`$ is admissible.

### 6.1 Admissible implies θ is a limit greater than ω (the paper, Lemma 13.1)

**Lemma 13.1.** If $`\theta`$ is admissible then $`\theta \gt \omega`$ and $`\theta`$ is a limit ordinal.
Also $`\omega \in L_\theta`$.

**Proof.** $`L_\theta \models \mathrm{KP}`$ satisfies Infinity, so there is an inductive set inside
$`L_\theta`$. $`L_\theta`$ is transitive, so the least inductive set obtained there by
$`\Delta_0`$-Separation coincides with the external $`\omega`$. Hence $`\omega \in L_\theta`$.
From $`L_\theta \cap \mathrm{Ord} = \theta`$ (constructible hierarchy note §9), $`\omega \lt \theta`$.

Next take any $`\xi \lt \theta`$. Then $`\xi \in L_\theta`$. Using Pairing and Union inside $`L_\theta`$
gives $`\xi + 1 = \xi \cup \{\xi\} \in L_\theta`$. Hence $`\xi + 1 \lt \theta`$, and $`\theta`$ is a limit
ordinal. $`\square`$

### 6.2 Conversely, for a limit greater than ω the seven axioms are automatic

If $`\omega \lt \theta`$ and $`\theta`$ is a limit ordinal, the seven axioms other than
$`\Delta_0`$-Collection hold automatically in $`L_\theta`$.

| Axiom | Reason |
|---|---|
| Extensionality, Set Induction | $`L_\theta`$ is transitive and they hold in the outer universe |
| Empty Set, Pairing, Union | a set built from $`a, b \in L_\xi`$ lies in $`\mathrm{Def}(L_\xi) = L_{\xi+1}`$. $`\theta`$ is a limit, so $`\xi + 1 \lt \theta`$ |
| $`\Delta_0`$-Separation | what is carved out is a subset of $`a`$ and is definable over $`L_\xi`$; again it lies in $`L_{\xi+1}`$ |
| Infinity | $`\omega \lt \theta`$ gives $`\omega \in L_\theta`$. $`\omega`$ itself is an inductive set |

### 6.3 Summary

Combining 6.1 and 6.2,

```math
\theta \text{ is admissible}
\quad\iff\quad
\omega \lt \theta \ \wedge\ \theta \text{ is a limit ordinal} \ \wedge\
\Delta_0\text{-Collection holds in } L_\theta
```

**The substantive condition is $`\Delta_0`$-Collection alone.** The formalization takes this right-hand
side as the definition (§12).

## 7. Satisfaction codes SatCode

This is the content of Definition 8.3 and Lemma 8.4 of the paper. Used in §8 and §9.

### 7.1 The three arguments

$`\mathrm{SatCode}(A, U, T)`$ of Definition 8.3 of the paper is a three-argument $`\Delta_0`$ predicate
(the paper, formula 8.5). The definition itself is long, so only what each argument is is given here.
A **code** is a formula represented as a natural number (the coding is in 7.2).

| Argument | What it is |
|---|---|
| $`A`$ | the object whose truth is measured. It is the domain of the structure $`(A, \in)`$ |
| $`T`$ | the **truth part**. A set of pairs $`\langle e, a \rangle`$, where $`e`$ is a formula code and $`a`$ an assignment. Only the true ones are in it |
| $`U`$ | the **workspace**. An auxiliary set where formula codes and assignments live. Transitive and closed under pairing and union |

On that basis, $`\mathrm{SatCode}(A, U, T)`$ is read as

> $`T`$ correctly codes the satisfaction relation of the structure $`(A, \in)`$, and $`U`$ is the
> workspace for it

The content of "correctly" is Lemma 8.4 of the paper: writing $`\varphi_e`$ for the formula denoted by
the code $`e`$,

```math
\langle e, a \rangle \in T \quad\iff\quad (A, \in) \models \varphi_e[a]
```

$`T`$ is uniquely determined by $`A`$ and does not depend on the choice of $`U`$.

That is, $`\mathrm{SatCode}`$ is the recursion for $`\models`$, given from outside in §2 of the
constructible hierarchy note, **held instead as a single set $`T`$**. Being a set, formula codes $`e`$ can
be quantified over. That is why Definition 11.1 can be written as "for every KP axiom code $`d`$,
$`\langle d, \emptyset \rangle \in S`$".

### 7.2 Computing codes

The coding of §8 of the paper uses the Cantor pairing function

```math
\pi(m,n) = \frac{(m+n)(m+n+1)}{2} + n
```

and is defined as follows.

```math
\ulcorner v_i = v_j \urcorner = \pi(0, \pi(i,j)), \qquad
\ulcorner v_i \in v_j \urcorner = \pi(1, \pi(i,j))
```
```math
\ulcorner \neg\varphi \urcorner = \pi(2, \ulcorner\varphi\urcorner), \qquad
\ulcorner \varphi \wedge \psi \urcorner = \pi(3, \pi(\ulcorner\varphi\urcorner, \ulcorner\psi\urcorner)), \qquad
\ulcorner \exists v_i\,\varphi \urcorner = \pi(4, \pi(i, \ulcorner\varphi\urcorner))
```

Computing gives the following.

```math
\begin{aligned}
\ulcorner v_0 = v_0 \urcorner &= 0 \cr
\ulcorner \neg(v_0 = v_0) \urcorner &= 3 \cr
\ulcorner v_0 = v_1 \urcorner &= 5 \cr
\ulcorner \exists v_1\,(v_1 \in v_0) \urcorner &= 295 \cr
\ulcorner \neg\exists v_1\,(v_1 \in v_0) \urcorner &= 44548
\end{aligned}
```

**Claim.** "$`e`$ is the code of a well-formed formula" and "$`e`$ is the code of a $`\Delta_0`$ formula"
are both $`\Delta_0`$ predicates (the paper §8).

**Reason.** As a witness, take a record of how $`e`$ is built, that is, a finite sequence $`s`$ of
natural numbers in which each term is either an atomic formula code or the result of applying one
constructor to earlier terms, with the last term equal to $`e`$. A finite sequence is itself a single
natural number via $`\pi`$, so $`s \in \omega`$ and one can write it **boundedly** as

```math
\mathrm{Form}(e) \ :\iff\ \exists s \in \omega\ (s \text{ is a record of how } e \text{ is built})
\tag{8.2}
```

Checking the record only looks at the tag and projections of each term, and is bounded by $`s, e, \omega`$.
Whether it is a $`\Delta_0`$ formula can be read off by checking whether each $`\exists`$ in the record
has the form $`\exists v_i\,(v_i \in v_j \wedge \cdots)`$, that is, the expanded form of a bounded
quantifier, and this is bounded too.

### 7.3 How assignments are written

This follows the usage in §9.1 of the paper. Take $`v_0`$ as "the variable being carved out" and
$`v_1, v_2, \dots`$ as parameter variables, with $`a`$ the sequence of parameter values.
Write $`a_x`$ for the complete assignment obtained by assigning $`x`$ to $`v_0`$ and appending $`a`$
after it. It is $`a_x`$ that goes into $`T`$.
Following the paper, brackets $`\langle\ ,\ \rangle`$ are used for ordered pairs and $`(\ ,\ )`$ for
finite sequences.

| Name $`\langle e, a \rangle`$ | The formula $`e`$ denotes | Meaning |
|---|---|---|
| $`\langle 3, () \rangle`$ | $`\neg(v_0 = v_0)`$ | always false |
| $`\langle 0, () \rangle`$ | $`v_0 = v_0`$ | always true |
| $`\langle 44548, () \rangle`$ | $`\neg\exists v_1\,(v_1 \in v_0)`$ | $`v_0`$ is empty |
| $`\langle 295, () \rangle`$ | $`\exists v_1\,(v_1 \in v_0)`$ | $`v_0`$ is nonempty |
| $`\langle 5, (1) \rangle`$ | $`v_0 = v_1`$, with $`1`$ substituted for $`v_1`$ | $`v_0`$ is $`1`$ |

### 7.4 Computing with A = L_2

In von Neumann naturals, $`L_2 = \{\emptyset, \{\emptyset\}\} = \{0, 1\}`$.

Look at $`\langle 295, () \rangle`$. Here $`a_x = (x)`$, so only $`v_0`$ gets a value.

- $`x = 0 = \emptyset`$. There is no $`c \in L_2`$ with $`c \in \emptyset`$. **false**
- $`x = 1 = \{\emptyset\}`$. $`c = \emptyset`$ satisfies $`\emptyset \in \{\emptyset\}`$. **true**

```math
\langle 295,\ (0) \rangle \notin T, \qquad \langle 295,\ (1) \rangle \in T
```

Look at $`\langle 5, (1) \rangle`$. Here $`a_x = (x, 1)`$, with $`x`$ at $`v_0`$ and $`1`$ at $`v_1`$.

```math
\langle 5,\ (0, 1) \rangle \notin T \quad (0 \ne 1), \qquad
\langle 5,\ (1, 1) \rangle \in T \quad (1 = 1)
```

**The subsets carved out by the five rows.** For each $`\langle e, a \rangle`$, collect
$`\{x \in L_2 : \langle e, a_x \rangle \in T\}`$.

| $`\langle e, a \rangle`$ | Subset carved out |
|---|---|
| $`\langle 3, () \rangle`$ | $`\emptyset`$ |
| $`\langle 0, () \rangle`$ | $`\{0, 1\} = L_2`$ |
| $`\langle 44548, () \rangle`$ | $`\{0\} = \{\emptyset\}`$ |
| $`\langle 295, () \rangle`$ | $`\{1\} = \{\{\emptyset\}\}`$ |
| $`\langle 5, (1) \rangle`$ | $`\{1\} = \{\{\emptyset\}\}`$ |

The first four rows produce all four subsets of $`L_2`$. This is the same as the stage-3 table in §7 of
the constructible hierarchy note, and it is the content of $`\mathrm{Def}(L_2) = L_3`$.

The last two rows produce the same subset from different codes. What $`\mathrm{Def}`$ collects is subsets,
not codes, so duplication is fine.

**Note** that the $`\exists v_1`$ of $`\exists v_1\,(v_1 \in v_0)`$ is unbounded, but the formula is
equivalent to $`\exists v_1 \in v_0\,(v_1 = v_1)`$, which is $`\Delta_0`$.
So the answer to "is it nonempty" is the same whether measured inside $`L_2`$ or outside
(Levy hierarchy note §3).

For $`U`$ it suffices to take a transitive set containing $`A`$, $`\omega`$, $`T`$ and all the
assignments. Here the assignments are finite functions, so an $`L_\xi`$ a little above $`L_\omega`$ is
enough.

## 8. L-hierarchy codes LCode

This is the content of Definition 9.1 and Lemma 9.2 of the paper.

Inside the definition of $`\mathrm{LCode}`$, the $`\mathrm{SatCode}`$ of §7 appears as it is.
One $`\mathrm{SatCode}`$ is required for each stage of the hierarchy being built (condition 3 of
Definition 9.1 of the paper). Its shape is written in 8.2.

### 8.1 The three arguments

$`\mathrm{LCode}(\eta, M, c)`$ is also a three-argument $`\Delta_0`$ predicate (the paper, formula 9.4).

| Argument | Role | What it is | Counterpart in $`\mathrm{SatCode}(A, U, T)`$ of §7 |
|---|---|---|---|
| $`\eta`$ | input | the ordinal specifying how far the hierarchy is built | $`A`$ (input; the domain of the structure) |
| $`M`$ | result | the top stage of the finished hierarchy | $`T`$ (result; the truth part) |
| $`c`$ | auxiliary | the whole working data, with 4 components (8.2) | $`U`$ (auxiliary; the workspace) |

On that basis, $`\mathrm{LCode}(\eta, M, c)`$ is read as

> $`c`$ is a record of building $`L_0`$ up to $`L_\eta`$ in order by $`\mathrm{Def}`$, and $`M`$ is its
> top stage

The content of "correctly" is Lemma 9.2 of the paper,

```math
\mathrm{LCode}(\eta, M, c) \ \Longrightarrow\ M = L_\eta
```

$`M`$ is uniquely determined by $`\eta`$ and does not depend on the choice of $`c`$.

**The argument order is swapped relative to §7.** The roles correspond, but the positions do not.

```
SatCode ( input , auxiliary , result )
LCode   ( input , result , auxiliary )
```

This is the paper's order, so it is used as is. Since the roles correspond, the statements correspond too.

| | §7 $`\mathrm{SatCode}`$ | §8 $`\mathrm{LCode}`$ |
|---|---|---|
| result unique from the input | Lemma 8.4 ($`T`$ unique from $`A`$) | Lemma 9.2 ($`M = L_\eta`$) |
| the predicate is $`\Delta_0`$ | the paper, formula (8.5) | the paper, formula (9.4) |
| how it is used | finding $`U, T`$ inside $`L_\theta`$ makes $`T`$ the real truth part | finding $`M, c`$ inside $`L_\theta`$ makes $`M`$ the real $`L_\eta`$ |

However $`c`$ holds more than $`U`$. $`U`$ itself sits as the 0th component of $`c`$, and there are
additionally the construction records $`H, S, D`$ (8.2).

### 8.2 The four components of c

**Definition (function, domain, range).** A set $`f`$ is a **function** if all elements of $`f`$ are
ordered pairs and

```math
\langle x, y \rangle \in f \ \wedge\ \langle x, y' \rangle \in f
\ \Longrightarrow\ y = y'
```

holds. Then

```math
\mathrm{dom}\, f = \{\, x : \exists y\ \langle x,y \rangle \in f \,\}, \qquad
\mathrm{ran}\, f = \{\, y : \exists x\ \langle x,y \rangle \in f \,\}
```

are called the **domain** and the **range** of $`f`$. When $`\langle x,y \rangle \in f`$, write $`y`$ as
$`f(x)`$.

**Meaning.** A function is the set of ordered pairs itself and carries no information about "which set it
maps into". Hence $`\mathrm{ran}\, f`$ is exactly the set of values $`f`$ actually takes.

**Definition (components of $`c`$).** $`c`$ is a function with domain $`\{0,1,2,3\}`$, with
$`c(0) = U`$, $`c(1) = H`$, $`c(2) = S`$, $`c(3) = D`$ (the paper's $`\mathrm{FourCode}`$).

| Component | Domain | Content |
|---|---|---|
| $`H`$ | $`\eta + 1`$ | the hierarchy itself. $`H(\xi) = L_\xi`$ |
| $`S`$ | $`\eta`$ | truth parts. $`\mathrm{SatCode}(H(\xi), U, S(\xi))`$ holds |
| $`D`$ | $`\eta`$ | an enumeration of the definable subsets. Its type is fixed below |
| $`U`$ | — | not a function. Transitive, closed under pairing and union, and containing all of $`\eta, M, H, S, D, \omega`$ |

$`S(\xi)`$ is exactly the third argument of the $`\mathrm{SatCode}`$ of §7. There is one for each stage.

**Definition (the type of $`D`$).** $`D`$ is a function with domain $`\eta`$. For each $`\xi \lt \eta`$,
the value $`D(\xi)`$ is **again a function**, whose domain is the set of all pairs of the form
$`\langle e, a \rangle`$. Here $`e`$ is a formula code and $`a`$ a parameter sequence as in §7.3, whose
values all lie in $`H(\xi)`$. The value $`b = D(\xi)(e,a)`$ is a subset of $`H(\xi)`$ satisfying, for
every $`x \in H(\xi)`$,

```math
x \in b \quad\iff\quad \langle e, a_x \rangle \in S(\xi)
```

(condition 4 of Definition 9.1 of the paper, formula (9.1)).

**Notation.** $`D(\xi)`$ is itself a function, so two sets of parentheses line up. $`D(\xi)(e,a)`$ is
shorthand for $`D(\xi)(\langle e,a \rangle)`$, the value of $`D(\xi)`$ applied to the single argument
$`\langle e,a \rangle`$ (the paper's notation). The values of $`H(\xi)`$ and $`S(\xi)`$ are sets, so the
parentheses stop at one.

| Expression | What it is |
|---|---|
| $`H(2)`$ | a set. $`L_2`$ |
| $`S(2)`$ | a set. The truth part of $`L_2`$ |
| $`D(2)`$ | a **function** |
| $`D(2)(295, ())`$ | a set. $`\{1\}`$ |

### 8.3 How the stages are built

$`H`$ is determined by the following three conditions (conditions 2 and 5 of Definition 9.1 of the
paper). $`\mathrm{ran}\, D(\xi)`$ means $`\mathrm{ran}(D(\xi))`$, the range of the inner function
$`D(\xi)`$ (8.2). It is not the range of $`D`$.

```math
H(0) = \emptyset, \qquad
H(\xi+1) = \mathrm{ran}\, D(\xi), \qquad
H(\lambda) = \bigcup_{\xi<\lambda} H(\xi) \quad (\lambda \text{ a limit})
```

Finally set $`M = H(\eta)`$.

The middle one is the point. $`D(\xi)`$ is a function listing the definable subsets of $`L_\xi`$ without
omission, so its range coincides exactly with $`\mathrm{Def}(L_\xi)`$. That is,

```math
H(\xi+1) = \mathrm{ran}\, D(\xi) = \mathrm{Def}(H(\xi))
```

which reproduces $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ of §5 of the constructible hierarchy note.

"Without omission" holds because condition 4 of Definition 9.1 of the paper specifies the domain of
$`D(\xi)`$ **exactly** as the set of all $`\langle e, a \rangle`$, and specifies the values by (9.1),

```math
x \in b \quad\iff\quad \langle e, a_x \rangle \in S(\xi)
```

This is exactly the computation carried out in §7.4.

### 8.4 Computing with η = 3

Continuing §7.4, build $`\eta = 3`$. The domain of $`H`$ is $`\eta+1 = 4`$, and the domains of $`S`$ and
$`D`$ are $`\eta = 3`$.

| $`\xi`$ | $`H(\xi)`$ | Number of elements |
|---|---|---|
| $`0`$ | $`\emptyset`$ | 0 |
| $`1`$ | $`\{\emptyset\}`$ | 1 |
| $`2`$ | $`\{\emptyset, \{\emptyset\}\}`$ | 2 |
| $`3`$ | $`L_3`$ | 4 |

Write out $`D(2)`$. The five rows of §7.4 become the values directly.

| $`\langle e, a \rangle`$ | $`D(2)(e,a)`$ |
|---|---|
| $`\langle 3, () \rangle`$ | $`\emptyset`$ |
| $`\langle 0, () \rangle`$ | $`\{0, 1\}`$ |
| $`\langle 44548, () \rangle`$ | $`\{0\}`$ |
| $`\langle 295, () \rangle`$ | $`\{1\}`$ |
| $`\langle 5, (1) \rangle`$ | $`\{1\}`$ |

The domain of $`D(2)`$ is not just these five but all $`\langle e,a \rangle`$ over $`L_2`$.
There are only four distinct values, however, so the range is

```math
\mathrm{ran}\, D(2) = \{\, \emptyset,\ \{0\},\ \{1\},\ \{0,1\} \,\} = L_3 = H(3)
```

which satisfies the successor-stage condition of 8.3. Finally $`M = H(3) = L_3`$, as in Lemma 9.2.

### 8.5 Why being Δ₀ matters

$`\mathrm{LCode}(\eta, M, c)`$ is $`\Delta_0`$ (the paper, formula 9.4). So by §3.4 of the Levy hierarchy
note, if $`M, c`$ satisfying $`\mathrm{LCode}`$ are found inside the transitive $`L_\theta`$, they are the
real thing seen from outside. Applying Lemma 9.2 outside gives $`M = L_\eta`$ outside as well. This
becomes Corollary 10.6 of §9.

## 9. What can be done inside KP

§10 of the paper derives the needed lemmas from KP in order. The chain is as follows.

**Lemma 10.1 ($`\Sigma_1`$-Collection).** The $`\Delta_0`$-Collection of §2 with the condition replaced by
a $`\Sigma_1`$ formula $`\psi`$ is also provable from KP. That is, under KP,

```math
\forall x \in a\ \exists y\ \psi(x,y) \ \Longrightarrow\ \exists b\ \forall x \in a\ \exists y \in b\ \psi(x,y)
\qquad (\psi \in \Sigma_1)
```

holds. $`\Sigma_1`$-Collection is not an axiom of KP but a theorem derived from KP.

The mechanism is to bundle the witnesses $`y`$ and $`z`$ of $`\psi = \exists z\,\delta`$ into an ordered
pair $`w = \langle y, z\rangle`$. "$`w`$ is a witness pair for $`x`$" is then $`\Delta_0`$, so
$`\Delta_0`$-Collection applies.

**Corollary 10.2 (functional $`\Sigma_1`$-Replacement).** Strengthening the antecedent of Lemma 10.1 to
"there is **exactly one** $`y`$" (written $`\exists!y`$) yields not just a set $`b`$ but a function.
That is, under KP, from $`\psi \in \Sigma_1`$ and

```math
\forall x \in a\ \exists!y\ \psi(x,y)
```

there exists a function $`F`$ with $`\mathrm{dom}(F) = a`$ satisfying $`\psi(x, F(x))`$ for every
$`x \in a`$. Since the $`y`$ for each $`x`$ is uniquely determined, $`x \mapsto y`$ is a function; that is
all.

**Lemma 10.3 (ordinal $`\Sigma_1`$-recursion).** A recursion whose value at each stage is uniquely
determined by a $`\Sigma_1`$ condition can be carried out to the end inside KP and yields a single
function. The same holds for $`\omega`$-recursion.

**Lemma 10.4 (finite coding and closure).** KP proves the following.

1. For any $`A`$, the set $`A^{\lt\omega}`$ of all finite sequences from $`A`$ exists
2. For any $`X`$, the least transitive set $`\mathrm{TC}(X)`$ containing $`X`$ exists
3. For any $`X`$, there is a $`U`$ with $`X \subseteq U`$ that is transitive and closed under pairing and
   union

**Lemma 10.5 (existence of satisfaction codes and L-codes).** Uses the $`\mathrm{SatCode}`$ of §7.
KP proves the following.

1. For any set $`A`$ there are $`U, T`$ satisfying $`\mathrm{SatCode}(A, U, T)`$.
   The truth part $`T`$ is uniquely determined by $`A`$
2. For any ordinal $`\eta`$ there are $`M, c`$ satisfying $`\mathrm{LCode}(\eta, M, c)`$

**Corollary 10.6.** If $`\theta`$ is admissible and $`\eta \lt \theta`$ then

```math
L_\theta \models \exists M\, \exists c\ \mathrm{LCode}(\eta, M, c)
```

and that $`M`$ is $`L_\eta`$ both internally and externally.

The last line is the point. $`\mathrm{LCode}`$ is $`\Delta_0`$ (the paper, formula 9.4), so by §3.4 of the
Levy hierarchy note a code found inside $`L_\theta`$ is the real thing outside as well, and
$`M = L_\eta`$ holds outside too. That is,

> Taking an admissible $`\theta`$, one can say inside $`L_\theta`$ that "$`L_\eta`$ exists"
> (for $`\eta \lt \theta`$).

This is the reason admissibility is required.

## 10. Aside: the least admissible ordinal

As in §5, $`\omega`$ is not admissible. So what is the least one?

It is the **Church–Kleene ordinal** $`\omega_1^{\mathrm{CK}}`$, the supremum of "ordinals representable by
a computable well-ordering". It is countable but far larger than $`\omega`$.

The paper does not use this ordinal. All it uses is that there are arbitrarily many admissible ordinals,
and the specific pair $`\Lambda \lt \Theta`$ built in Lemma 16.2.

## 11. How it is used in the paper

| Place | Use |
|---|---|
| Definition 18.1 | the values of the stable labels $`f(i)`$ are admissible ordinals |
| Formula (15.1) | $`\alpha \lhd_k \beta`$ is a relation between admissible ordinals $`\alpha \lt \beta`$ |
| Definition 11.1 | the predicate $`\mathrm{Adm}(\eta)`$ saying "$`\eta`$ is admissible" internally. It is $`\hat\Sigma_1`$ |
| Lemma 11.2 | its correctness. If $`\theta`$ is admissible and $`\eta \lt \theta`$ then $`L_\theta \models \mathrm{Adm}(\eta) \iff L_\eta \models \mathrm{KP}`$ |
| Lemma 16.2 | builds a pair of admissible ordinals $`\Lambda \lt \Theta`$ with $`L_\Lambda \prec L_\Theta`$ |
| Theorem 17.1 | pushes a finite set of admissible ordinals down below $`\alpha`$ |

That $`\mathrm{Adm}(\eta)`$ is $`\hat\Sigma_1`$ matters for the complexity computation of Theorem 17.1.
$`\hat\Sigma_q`$ is left to another note.

## 12. Counterparts in Lean

The formalization does not take $`L_\theta \models \mathrm{KP}`$ as the definition but instead uses the
right-hand side of §6.3 as the definition of `IsAdmissible`. This is because the file building the codes
of the KP axioms is downstream of `Adm.lean`; the equivalence is proved there.

| Concept | Lean | File |
|---|---|---|
| $`\Delta_0`$-Collection in $`L_\theta`$ | `Delta0Collection (L θ)` | `Bm4/SetTheory/Adm.lean` |
| $`\theta`$ is admissible (right-hand side of §6.3) | `IsAdmissible θ` | same |
| $`\theta \gt \omega`$ | `IsAdmissible.omega_lt` | same |
| $`\theta`$ is a limit ordinal | `IsAdmissible.isSuccLimit` | same |
| $`\omega \in L_\theta`$ | `IsAdmissible.omega_mem` | same |
| codes of the KP axioms | `KPAxCode` | `Bm4/SetTheory/KPAx.lean` |
| the §6.2 direction (right-hand side $`\Rightarrow`$ all KP axioms true) | `KPSat.satIn_kpAx` | `Bm4/SetTheory/KPSat.lean` |
| the §6.1 direction (all KP axioms true $`\Rightarrow`$ right-hand side) | `KPSat.isAdmissible_of_kpTrue`, `AdmKP.omega_lt_of_kpTrue`, `AdmKP.isSuccLimit_of_kpTrue` | same, `Bm4/SetTheory/AdmKP.lean` |
| $`\mathrm{Adm}(\eta)`$ of Definition 11.1 | `AdmKP D h w η` | `Bm4/SetTheory/AdmKP.lean` |
| Lemma 11.2 | `admKP_iff` | same |
| Lemmas 10.1, 10.3 ($`\Sigma_1`$ collection and ordinal recursion) | `Bm4/SetTheory/Recur.lean`, `Recursion.lean` | same |
| Lemma 10.5(1) (existence of satisfaction codes) | `Bm4/SetTheory/SatInL.lean` | same |
| $`\mathrm{SatCode}(A,U,T)`$ of §7 | `SatCode h w M U S` | `Bm4/SetTheory/SatCode.lean` |
| Lemma 8.4 (correctness of satisfaction codes) | `satCode_correct` | same |
| $`\mathrm{LCode}(\eta,M,c)`$ of §8 | `LCode h w η M c` | `Bm4/SetTheory/LCode.lean` |
| formula (9.4) ($`\mathrm{LCode}`$ is $`\Delta_0`$) | `delta0_lcode` | same |
| Lemma 9.2 ($`M = L_\eta`$) | `lcode_sound` | same |
| Lemma 10.5(2), Corollary 10.6 (existence of L-codes) | `lcode_exists_in_L` | `Bm4/SetTheory/LCodeEx.lean` |
