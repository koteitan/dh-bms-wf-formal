[← Back](README.md) | [English](01-constructible-hierarchy.md) | [Japanese](../01-constructible-hierarchy.md)

# The constructible hierarchy L

## 1. Formulas of the language {∈}

The only symbols used are these.

| Kind | Symbols |
|---|---|
| variables | $`x, y, z, w, \dots`$ |
| atomic formulas | $`x = y`$, $`x \in y`$ |
| connectives | $`\neg`$ (not), $`\wedge`$ (and), $`\vee`$ (or), $`\to`$ (implies) |
| quantifiers | $`\exists z`$ (there exists $`z`$), $`\forall z`$ (for all $`z`$) |

A finite combination of these is called a **formula**. There are no function symbols and no constant
symbols. Symbols such as $`\subseteq`$ and $`\emptyset`$ are abbreviations and can be written out with
$`\in`$ and $`=`$.

```math
x \subseteq y \ \equiv\ \forall z\,(z \in x \to z \in y), \qquad
x = \emptyset \ \equiv\ \neg\exists z\,(z \in x)
```

A variable not bound by a quantifier is called a **free variable**. For instance, in

```math
\varphi(x, y) \ \equiv\ \exists z\,(z \in x \wedge z \in y)
```

$`z`$ is bound by $`\exists z`$ and is not free, while $`x`$ and $`y`$ are the free variables.
To ask whether a formula is true or false, one has to fix values for all of its free variables.
A value assigned to a free variable is called a **parameter**.

## 2. The structure (X, ∈) and satisfaction

**Definition (structure).** For a set $`X`$, the **structure** $`(X, \in)`$ is the pair in which the
underlying domain is $`X`$ and the symbol $`\in`$ is read as the real membership relation restricted to
$`X`$.

**Meaning.** It is the stage on which formulas are read. Variables denote only elements of $`X`$, and the
symbol $`\in`$ denotes membership between elements of $`X`$.

**Definition (assignment).** An **assignment** is a function $`\bar a`$ from all variables to $`X`$.
Write $`\bar a(x) \in X`$ for the value at the variable $`x`$.

**Meaning.** It is what assigns concrete values from $`X`$ to the variables of a formula. As seen in §1,
all that is needed to ask for a truth value are the values of the free variables; indeed
$`(X,\in) \models \varphi[\bar a]`$ is determined by the values of $`\bar a`$ at the free variables of
$`\varphi`$ alone and does not depend on the values at other variables. The domain is taken to be all
variables so that the $`\bar a(z \mapsto c)`$ below always makes sense.

**Definition (substitution).** For an assignment $`\bar a`$, a variable $`z`$, and a value $`c \in X`$,
define the assignment $`\bar a(z \mapsto c)`$ by

```math
\bar a(z \mapsto c)(z) = c, \qquad
\bar a(z \mapsto c)(u) = \bar a(u) \quad (u \ne z)
```

**Meaning.** It is the assignment with only the value of $`z`$ replaced by $`c`$, everything else kept.

**Definition (satisfaction).** Define $`(X, \in) \models \varphi[\bar a]`$ by recursion on the shape of
$`\varphi`$ as follows.

```math
\begin{aligned}
(X,\in) &\models (x = y)[\bar a]
  &&\iff\ \bar a(x) = \bar a(y) \cr
(X,\in) &\models (x \in y)[\bar a]
  &&\iff\ \bar a(x) \in \bar a(y) \cr
(X,\in) &\models (\neg\varphi)[\bar a]
  &&\iff\ \text{not } (X,\in) \models \varphi[\bar a] \cr
(X,\in) &\models (\varphi \wedge \psi)[\bar a]
  &&\iff\ \text{both hold} \cr
(X,\in) &\models (\exists z\,\varphi)[\bar a]
  &&\iff\ \text{for some } c \in X,\ (X,\in) \models \varphi[\bar a(z \mapsto c)] \cr
(X,\in) &\models (\forall z\,\varphi)[\bar a]
  &&\iff\ \text{for all } c \in X,\ (X,\in) \models \varphi[\bar a(z \mapsto c)]
\end{aligned}
```

**Meaning.** Read it as "$`\varphi`$ is true in the structure $`(X,\in)`$ under the assignment
$`\bar a`$". $`\models`$ is the symbol read "satisfies".

The most important point is the last two lines. **The quantifiers $`\exists z`$ and $`\forall z`$ range
over elements of $`X`$ only.** They do not range over the whole universe.

**Definition (witness).** When $`(X,\in) \models (\exists z\,\varphi)[\bar a]`$ holds, the $`c \in X`$
appearing on the right-hand side of the definition above, that is, a $`c`$ with

```math
(X,\in) \models \varphi[\bar a(z \mapsto c)]
```

is called a **witness** of this existential claim.

**Meaning.** It is the concrete value that makes $`\exists z\,\varphi`$ true. There need not be only
one; there may be several. When existential quantifiers line up as
$`\exists z_1 \cdots \exists z_m\,\varphi`$, a tuple of values $`(c_1, \dots, c_m)`$ is called a witness.

### Example

Take $`X = \{\emptyset, \{\emptyset\}\}`$ and $`\varphi(x) \equiv \exists z\,(z \in x)`$, which means
"$`x`$ has an element".

- When $`\bar a(x) = \emptyset`$. There is no $`c \in X`$ with $`c \in \emptyset`$, so **false**
- When $`\bar a(x) = \{\emptyset\}`$. $`c = \emptyset`$ is an element of $`X`$ and
  $`\emptyset \in \{\emptyset\}`$, so **true**

Hence

```math
\{\, x \in X : (X,\in) \models \varphi[x] \,\} = \{\{\emptyset\}\}.
```

### What confining the quantifiers to X does

With the same $`X = \{\emptyset, \{\emptyset\}\}`$ take $`\psi(x) \equiv \exists z\,(x \in z)`$, which
means "$`x`$ is an element of something". Take the assignment $`\bar a(x) = \{\emptyset\}`$.

- In the structure $`(X,\in)`$ there are only two candidates $`z`$, namely $`\emptyset`$ and
  $`\{\emptyset\}`$. Neither $`\{\emptyset\} \in \emptyset`$ nor $`\{\emptyset\} \in \{\emptyset\}`$
  holds, so **false**
- Seen in the whole universe, $`\{\emptyset\} \in \{\{\emptyset\}\}`$, so **true**

For the same formula, $`(X,\in) \models`$ and "really holds" differ. This difference matters throughout
what follows.

## 3. Two terms used later

**Transitive.** A set $`X`$ is **transitive** if

```math
x \in y \in X \ \Longrightarrow\ x \in X
```

holds. Equivalently, every element of $`X`$ is a subset of $`X`$.

**Von Neumann naturals.** Define the natural numbers as sets by

```math
0 = \emptyset, \quad 1 = \{0\}, \quad 2 = \{0, 1\}, \quad \dots, \quad n = \{0, 1, \dots, n-1\}
```

$`n`$ is "the set of all naturals smaller than itself". All of them are transitive.

## 4. The definable power set Def

### 4.1 Definable

Take a set $`X`$ and a subset $`b \subseteq X`$. $`b`$ is **definable over $`X`$** if there are a formula
$`\varphi(x, y_1, \dots, y_n)`$ and parameters $`p_1, \dots, p_n \in X`$ with

```math
b = \{\, x \in X : (X, \in) \models \varphi[x, p_1, \dots, p_n] \,\}
```

As in §2, the quantifiers of $`\varphi`$ range only inside $`X`$.

#### Example

Look at $`X = \{\emptyset, \{\emptyset\}\}`$.

$`b = \{\{\emptyset\}\}`$ is definable. Taking $`\varphi(x) \equiv \exists z\,(z \in x)`$, as computed in
§2,

```math
\{\, x \in X : (X,\in) \models \varphi[x] \,\} = \{\{\emptyset\}\} = b .
```

No parameters are used ($`n = 0`$).

$`b = \{\emptyset\}`$ is definable as well. This one uses a parameter.
Taking $`\varphi(x, y) \equiv (x = y)`$ and the parameter $`p_1 = \emptyset \in X`$,

```math
\{\, x \in X : (X,\in) \models \varphi[x, \emptyset] \,\}
= \{\, x \in X : x = \emptyset \,\} = \{\emptyset\} = b .
```

One can also write it without a parameter as $`\varphi(x) \equiv \neg\exists z\,(z \in x)`$
("$`x`$ is empty").

The remaining two are definable too.

| $`b`$ | $`\varphi`$ | parameters |
|---|---|---|
| $`\emptyset`$ | $`x \ne x`$ | none |
| $`\{\emptyset\}`$ | $`\neg\exists z\,(z \in x)`$ | none |
| $`\{\{\emptyset\}\}`$ | $`\exists z\,(z \in x)`$ | none |
| $`\{\emptyset, \{\emptyset\}\}`$ | $`x = x`$ | none |

This $`X`$ is finite, so all four subsets turned out definable. This is no accident: it is always so for
finite sets (§6). Non-definable subsets appear only once $`X`$ is infinite, and the first example shows
up at stage ω+1 in §7.

### 4.2 Def(X)

Write $`\mathrm{Def}(X)`$ for the collection of all definable $`b`$.

```math
\mathrm{Def}(X) = \{\, b \subseteq X : b \text{ is definable over } X \,\}
```

Whereas the power set $`P(X)`$ collects all subsets, $`\mathrm{Def}(X)`$ collects only "those specifiable
by a formula and finitely many parameters". Hence

```math
\mathrm{Def}(X) \subseteq P(X).
```

The computation in 4.1 shows that for $`X = \{\emptyset, \{\emptyset\}\}`$,

```math
\mathrm{Def}(X) = P(X)
= \bigl\{\ \emptyset,\ \ \{\emptyset\},\ \ \{\{\emptyset\}\},\ \ \{\emptyset,\{\emptyset\}\}\ \bigr\}
```

### 4.3 Cardinality

There are only countably many formulas. Parameters are finite sequences of elements of $`X`$, so there
are $`|X|`$ of them when $`X`$ is infinite and finitely many when $`X`$ is finite. One pair
$`(\varphi, \bar p)`$ determines one $`b`$, so

```math
|\mathrm{Def}(X)| \le |X| + \aleph_0 .
```

Compared with $`P(X)`$ having size $`2^{|X|}`$, this is a large gap for infinite sets.

## 5. The constructible hierarchy

Iterate $`\mathrm{Def}`$ along the ordinals.

```math
L_0 = \emptyset, \qquad
L_{\xi+1} = \mathrm{Def}(L_\xi), \qquad
L_\lambda = \bigcup_{\xi < \lambda} L_\xi \quad (\lambda \text{ a limit})
```

and

```math
L = \bigcup_{\xi \in \mathrm{Ord}} L_\xi .
```

Elements of $`L`$ are called **constructible sets**. "Constructible" means "buildable from the stage below
by a formula".

For comparison, the von Neumann hierarchy has the same shape with $`\mathrm{Def}`$ replaced by $`P`$.

```math
V_0 = \emptyset, \qquad
V_{\xi+1} = P(V_\xi), \qquad
V_\lambda = \bigcup_{\xi<\lambda} V_\xi
```

## 6. At finite stages Def and P agree

**Lemma.** If $`X`$ is finite then $`\mathrm{Def}(X) = P(X)`$.

**Proof.** Let $`b \subseteq X`$. If $`b = \emptyset`$, take $`\varphi(x)`$ to be $`x \ne x`$.
If $`b = \{p_1, \dots, p_m\}`$ with $`m \ge 1`$, take $`p_1,\dots,p_m`$ as parameters and

```math
\varphi(x, y_1, \dots, y_m) \ \equiv\ (x = y_1 \vee \cdots \vee x = y_m)
```

so that $`b = \{x \in X : (X,\in) \models \varphi[x, \bar p]\}`$. $`\square`$

This is why $`L`$ and $`V`$ agree at finite stages. The difference appears only once infinite sets are
involved, where "list all elements of $`b`$ as parameters" is no longer possible.

## 7. Computing the small stages

### Stage 0

```math
L_0 = \emptyset
```

0 elements.

### Stage 1

The only subset of $`L_0 = \emptyset`$ is $`\emptyset`$, writable by $`\varphi(x) \equiv (x \ne x)`$.

```math
L_1 = \mathrm{Def}(\emptyset) = \{\emptyset\}
```

1 element.

### Stage 2

$`L_1 = \{\emptyset\}`$ has two subsets, $`\emptyset`$ and $`\{\emptyset\}`$.

- $`\emptyset`$ … $`\varphi(x) \equiv (x \ne x)`$
- $`\{\emptyset\}`$ … $`\varphi(x) \equiv (x = x)`$, since it is all of $`L_1`$

```math
L_2 = \{\emptyset,\ \{\emptyset\}\}
```

2 elements. This is the von Neumann natural $`2 = \{0, 1\}`$.

### Stage 3

$`L_2 = \{\emptyset, \{\emptyset\}\}`$ has four subsets. Being finite, all are definable.

| Subset | Formula |
|---|---|
| $`\emptyset`$ | $`x \ne x`$ |
| $`\{\emptyset\}`$ | $`\neg \exists z\,(z \in x)`$ ("$`x`$ is empty") |
| $`\{\{\emptyset\}\}`$ | $`\exists z\,(z \in x)`$ (the example in §2) |
| $`\{\emptyset, \{\emptyset\}\}`$ | $`x = x`$ |

```math
L_3 = \bigl\{\ \emptyset,\ \ \{\emptyset\},\ \ \{\{\emptyset\}\},\ \ \{\emptyset,\{\emptyset\}\}\ \bigr\}
```

4 elements. With parameters one could instead produce $`\{\emptyset\}`$ from
$`\varphi(x,y) \equiv (x = y)`$ with the parameter $`y = \emptyset`$.

### Stage 4 and beyond

$`|L_3| = 4`$, so by the finite-stage lemma $`L_4 = P(L_3)`$ and

```math
|L_4| = 2^4 = 16 .
```

Thereafter $`|L_{n+1}| = 2^{|L_n|}`$, so

| $`n`$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| $`\lvert L_n \rvert`$ | 0 | 1 | 2 | 4 | 16 | 65536 | $`2^{65536}`$ |

They quickly become impossible to write down, but throughout $`n \lt \omega`$

```math
L_n = V_n
```

### Stage ω

```math
L_\omega = \bigcup_{n<\omega} L_n = \bigcup_{n<\omega} V_n = V_\omega
```

This is the **hereditarily finite sets** $`\mathrm{HF}`$, that is, all sets that are finite, whose
elements are finite, and so on all the way down. $`L_\omega`$ is countable.

#### Nothing new enters

$`\omega`$ is a limit ordinal, so stage ω is a union. Hence if $`a \in L_\omega`$ then $`a \in L_n`$ for
some $`n \lt \omega`$.

```math
L_\omega \setminus \bigcup_{n<\omega} L_n = \emptyset
```

That is, stage ω itself creates no new elements. The new elements are created at each finite stage, and
stage ω merely collects them all. Every limit stage is like this.

#### Examples of elements

Each of them entered as new at some finite stage.

| Element | Expanded | Stage where it entered |
|---|---|---|
| $`0`$ | $`\emptyset`$ | $`L_1`$ |
| $`1`$ | $`\{\emptyset\}`$ | $`L_2`$ |
| $`2`$ | $`\{\emptyset,\{\emptyset\}\}`$ | $`L_3`$ |
| $`\{1\}`$ | $`\{\{\emptyset\}\}`$ | $`L_3`$ |
| $`\{2\}`$ | $`\{\{\emptyset,\{\emptyset\}\}\}`$ | $`L_4`$ |
| $`\{1,2\}`$ | $`\{\{\emptyset\},\{\emptyset,\{\emptyset\}\}\}`$ | $`L_4`$ |

All the von Neumann naturals $`0, 1, 2, \dots`$ belong. $`n`$ enters as new at $`L_{n+1}`$.

Ordered pairs belong as well. Coding $`\langle x, y \rangle = \{\{x\},\{x,y\}\}`$,

```math
\langle 0, 1 \rangle = \{\{0\},\{0,1\}\} = \{\{\emptyset\},\{\emptyset,\{\emptyset\}\}\}
```

which is the same set as $`\{1,2\}`$ in the table above. Likewise finite sequences and finite graphs can
be coded inside $`\mathrm{HF}`$. All of finite combinatorics fits in here.

$`\omega`$ itself is infinite, so it does not belong.

#### Note: things that are not elements of ω are mixed in

The elements of $`\omega`$ are only the naturals. $`\{1\}`$ in the table above is an element of $`L_3`$,
hence of $`L_\omega`$, but it is not a natural, so it is not an element of $`\omega`$.
The same goes for $`\{2\}`$, $`\{1,2\}`$ and $`\langle 0,1 \rangle`$. Hence

```math
\omega \subsetneq L_\omega .
```

The inclusion holds, because $`n \in L_{n+1} \subseteq L_\omega`$ for each $`n`$. Equality does not.

Two things are easy to confuse. Both agree, but as sets they are different objects.

- Looking only at ordinals they agree: $`L_\omega \cap \mathrm{Ord} = \omega`$ (§9)
- The cardinalities agree too: $`|L_\omega| = |\omega| = \aleph_0`$

### Stage ω+1

Here is where $`\mathrm{Def}`$ and $`P`$ first part ways.

```math
L_{\omega+1} = \mathrm{Def}(L_\omega), \qquad V_{\omega+1} = P(V_\omega)
```

$`L_\omega = V_\omega`$ is countable, so

```math
|V_{\omega+1}| = 2^{\aleph_0} \quad(\text{uncountable}), \qquad
|L_{\omega+1}| = \aleph_0 \quad(\text{countable})
```

#### What enters as new

The elements of $`L_{\omega+1}`$ are subsets of $`L_\omega`$. If $`b \subseteq L_\omega`$ is **finite**,
then all elements of $`b`$ are hereditarily finite, so $`b`$ itself is hereditarily finite and
$`b \in L_\omega`$, that is, it was there already. So the newcomers are only the infinite ones, and

```math
L_{\omega+1} \setminus L_\omega
= \{\, b \subseteq L_\omega : b \text{ is definable and infinite} \,\}.
```

#### Examples of what enters as new

| New element | Formula | Parameters |
|---|---|---|
| $`\omega = \{0,1,2,\dots\}`$ | "$`x`$ is transitive and so are its elements" | none |
| $`L_\omega`$ itself | $`x = x`$ | none |
| $`L_\omega \setminus \omega`$ (all finite sets that are not naturals) | the negation of the above | none |
| all singletons $`\{\{a\} : a \in L_\omega\}`$ | $`\exists z\,(z \in x) \wedge \forall z\,\forall w\,(z \in x \wedge w \in x \to z = w)`$ | none |
| $`\omega \setminus (n+1) = \{n+1, n+2, \dots\}`$ | "$`x`$ is an ordinal" $`\wedge\ y \in x`$ | $`y = n`$ |
| all even numbers $`\{0,2,4,\dots\}`$, all primes | arithmetic written out. Omitted, being long | none |

Writing out the formula for $`\omega`$,

```math
\forall y \in x\,\forall z \in y\,(z \in x)
\ \wedge\ \forall y \in x\,\forall z \in y\,\forall w \in z\,(w \in y)
```

($`x`$ is transitive and so are its elements). The only elements of $`L_\omega`$ satisfying this are the
von Neumann naturals, so the set carved out is exactly $`\omega`$. Since $`\omega \notin L_\omega`$, it is
indeed a new element.

The fifth row alone, with $`n`$ varying as the parameter, yields infinitely many newcomers
$`\omega \setminus 1, \omega \setminus 2, \dots`$. The total number of newcomers is countably infinite,
since $`\mathrm{Def}(L_\omega)`$ is countable.

#### Examples of what does not enter

There are $`2^{\aleph_0}`$ subsets of $`\omega`$, but $`L_{\omega+1}`$ is countable, so almost none of
them enter. In fact $`L_{\omega+1} \cap P(\omega)`$ is exactly the sets definable over
$`(V_\omega, \in)`$, that is, exactly the arithmetical sets. Sets above the degree of the halting problem
(for example $`0^{(\omega)}`$) do not enter.

This is the gap between $`\mathrm{Def}`$ and $`P`$. In $`V_{\omega+1} = P(V_\omega)`$ all
$`2^{\aleph_0}`$ subsets of $`\omega`$ enter.

#### Note: restricted to ordinals, the only newcomer is ω

```math
L_\omega \cap \mathrm{Ord} = \omega, \qquad
L_{\omega+1} \cap \mathrm{Ord} = \omega+1
```

The difference is the single $`\{\omega\}`$. The property $`L_\xi \cap \mathrm{Ord} = \xi`$ in §9 says
only this; it is not a statement about how $`L_\xi`$ itself grows. Looking at all elements, countably
infinitely many enter as new, as above.

## 8. The size of a general stage

If $`\xi \ge \omega`$ then

```math
|L_\xi| = |\xi| .
```

In particular, if $`\xi`$ is a countable ordinal then $`L_\xi`$ is a countable set.

This follows by transfinite induction on $`\xi`$ from the fact that one application of $`\mathrm{Def}`$
raises the size only up to $`|X| + \aleph_0`$ (the cardinality estimate of §4) and that a limit stage is a
union of $`|\lambda|`$ many stages. For $`V_\xi`$, which uses $`P`$, the estimate fails, since
$`|V_{\omega+n}|`$ jumps exponentially with each $`n`$.

## 9. Basic properties

| Property | Content |
|---|---|
| transitivity | each $`L_\xi`$ is transitive |
| monotonicity | $`\xi \le \eta \Rightarrow L_\xi \subseteq L_\eta`$ |
| itself | $`L_\xi \in L_{\xi+1}`$ |
| ordinals | $`L_\xi \cap \mathrm{Ord} = \xi`$ |
| rank | $`x \in L_\xi \Rightarrow \mathrm{rank}(x) \lt \xi`$ |

**Reason for transitivity and monotonicity.** If $`X`$ is transitive then $`X \subseteq \mathrm{Def}(X)`$.
Indeed, for $`a \in X`$, taking $`\varphi(x,y) \equiv (x \in y)`$ with the parameter $`y = a`$ gives
$`\{x \in X : x \in a\} = a \cap X = a`$ (by transitivity $`a \subseteq X`$). This yields
$`L_\xi \subseteq L_{\xi+1}`$. Also, if $`b \in \mathrm{Def}(X)`$ then
$`b \subseteq X \subseteq \mathrm{Def}(X)`$, so $`\mathrm{Def}(X)`$ is transitive as well.

**Reason for "itself".** $`\varphi(x) \equiv (x = x)`$ carves out all of $`L_\xi`$.

**Reason for "ordinals".** Run the same argument as $`\omega \in L_{\omega+1}`$ of §7 at every stage.
$`\supseteq`$ comes from $`\zeta \in L_{\zeta+1} \subseteq L_\xi`$ for $`\zeta \lt \xi`$.
$`\subseteq`$ comes from the rank estimate.

## 10. Caution: V = L is not assumed

As in §5, elements of $`L`$ are called **constructible sets**. Now, the claim that every set is
constructible,

```math
V = L
```

is a separate axiom independent of $`\mathrm{ZFC}`$. Neither this note nor the paper assumes it.

The reason it need not be assumed is that the definition of $`L_\xi`$ (§5) can be written down inside
$`\mathrm{ZFC}`$ as it stands. It only iterates $`\mathrm{Def}`$ along the ordinals, so $`L`$ and its
hierarchy $`L_\xi`$ exist without $`V = L`$. $`V = L`$ is the axiom claiming "that is all of them", which
is a separate matter from whether $`L`$ can be built.

The paper too builds $`L`$ inside $`\mathrm{ZFC}`$ and merely uses ordinals in it as labels for the array.
Indeed, Lemma 16.2 takes $`\omega_1^V`$ of the external universe, distinguishing $`V`$ from $`L`$.

## 11. Counterparts in Lean

| Concept | Lean | File |
|---|---|---|
| formula | `Fm` | `Bm4/SetTheory/Fm.lean` |
| $`(X,\in) \models \varphi[\bar a]`$ | `SatIn W v φ` | same |
| satisfaction with a specified quantifier domain | `Sat D v φ` | same |
| $`b`$ is definable over $`X`$ | `DefinableOver M X` | `Bm4/SetTheory/L.lean` |
| $`\mathrm{Def}(X)`$ | `Def M` | same |
| $`L_\xi`$ | `L o` | same |
| $`L_0 = \emptyset`$ | `L_zero` | same |
| $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ | `L_succ` | same |
| the union at a limit stage | `L_limit`, `mem_L_limit` | same |
| $`\mathrm{Def}(X) \subseteq P(X)`$ | `subset_of_mem_Def` | same |
| $`X \subseteq \mathrm{Def}(X)`$ ($`X`$ transitive) | `subset_Def` | same |
| $`X \in \mathrm{Def}(X)`$ | `self_mem_Def` | same |
| transitivity of $`\mathrm{Def}(X)`$ | `Def_transitive` | same |
| transitivity of $`L_\xi`$ | `L_transitive` | same |
| $`\xi \le \eta \Rightarrow L_\xi \subseteq L_\eta`$ | `L_mono` | same |
| $`L_\xi \in L_{\xi+1}`$ | `L_mem_L_succ` | same |
| $`L_\xi \cap \mathrm{Ord} = \xi`$ | `toZFSet_mem_L_iff` | same |
| $`x \in L_\xi \Rightarrow \mathrm{rank}(x) \lt \xi`$ | `rank_lt_of_mem_L` | same |
