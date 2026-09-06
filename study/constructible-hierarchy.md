[← Back](README.md)

# 構成可能階層 L

## 1. 言語 {∈} の論理式

使う記号は次だけである。

| 種類 | 記号 |
|---|---|
| 変数 | $`x, y, z, w, \dots`$ |
| 原子式 | $`x = y`$、$`x \in y`$ |
| 結合子 | $`\neg`$（でない）、$`\wedge`$（かつ）、$`\vee`$（または）、$`\to`$（ならば） |
| 量化子 | $`\exists z`$（ある $`z`$ が存在して）、$`\forall z`$（全ての $`z`$ について） |

これらを有限回組み合わせたものを **論理式** と呼ぶ。関数記号も定数記号も無い。
$`\subseteq`$ や $`\emptyset`$ のような記号は略記であって、$`\in`$ と $`=`$ に書き下せる。

```math
x \subseteq y \ \equiv\ \forall z\,(z \in x \to z \in y), \qquad
x = \emptyset \ \equiv\ \neg\exists z\,(z \in x)
```

量化子に縛られていない変数を **自由変数** と呼ぶ。たとえば

```math
\varphi(x, y) \ \equiv\ \exists z\,(z \in x \wedge z \in y)
```

では $`z`$ は $`\exists z`$ に縛られていて自由でなく、$`x`$ と $`y`$ が自由変数である。
論理式に値を入れて真偽を問うには、自由変数の全部に値を決めてやる必要がある。
自由変数に入れる値を **パラメータ** と呼ぶ。

## 2. 構造 (X, ∈) と充足

**定義（構造）.** 集合 $`X`$ に対し、**構造** $`(X, \in)`$ とは、土台を $`X`$ とし、
記号 $`\in`$ を本物の帰属関係の $`X`$ への制限として読む、と決めた組のことである。

**意味.** 論理式を読むときの舞台である。変数は $`X`$ の元だけを表し、記号 $`\in`$ は
$`X`$ の元どうしの帰属を表す。

**定義（割り当て）.** **割り当て** とは、変数全体から $`X`$ への関数 $`\bar a`$ のことである。
変数 $`x`$ に対する値を $`\bar a(x) \in X`$ と書く。

**意味.** 論理式の変数へ $`X`$ の中の具体的な値を入れる係である。§1 で見たとおり、
真偽を問うのに要るのは自由変数の値だけで、実際 $`(X,\in) \models \varphi[\bar a]`$ は
$`\varphi`$ の自由変数における $`\bar a`$ の値だけで決まり、他の変数の値には依らない。
定義域を変数全体にしておくのは、次の $`\bar a(z \mapsto c)`$ がいつでも意味を持つようにするためである。

**定義（差し替え）.** 割り当て $`\bar a`$、変数 $`z`$、値 $`c \in X`$ に対し、
割り当て $`\bar a(z \mapsto c)`$ を次で定める。

```math
\bar a(z \mapsto c)(z) = c, \qquad
\bar a(z \mapsto c)(u) = \bar a(u) \quad (u \ne z)
```

**意味.** 変数 $`z`$ の値だけを $`c`$ に取り替え、他はそのままにした割り当てである。

**定義（充足）.** $`(X, \in) \models \varphi[\bar a]`$ を、$`\varphi`$ の形に沿って次で定める。

```math
\begin{aligned}
(X,\in) &\models (x = y)[\bar a]
  &&\iff\ \bar a(x) = \bar a(y) \cr
(X,\in) &\models (x \in y)[\bar a]
  &&\iff\ \bar a(x) \in \bar a(y) \cr
(X,\in) &\models (\neg\varphi)[\bar a]
  &&\iff\ (X,\in) \models \varphi[\bar a] \text{ でない} \cr
(X,\in) &\models (\varphi \wedge \psi)[\bar a]
  &&\iff\ \text{両方が成立} \cr
(X,\in) &\models (\exists z\,\varphi)[\bar a]
  &&\iff\ \text{ある } c \in X \text{ について } (X,\in) \models \varphi[\bar a(z \mapsto c)] \cr
(X,\in) &\models (\forall z\,\varphi)[\bar a]
  &&\iff\ \text{全ての } c \in X \text{ について } (X,\in) \models \varphi[\bar a(z \mapsto c)]
\end{aligned}
```

**意味.** 「割り当て $`\bar a`$ のもとで $`\varphi`$ は構造 $`(X,\in)`$ で真である」と読む。
$`\models`$ は「充足する」と読む記号である。

一番大事な点は最後の 2 行である。**量化子 $`\exists z`$、$`\forall z`$ は $`X`$ の元だけを走る。**
宇宙全体を走るのではない。

### 例

$`X = \{\emptyset, \{\emptyset\}\}`$ とし、$`\varphi(x) \equiv \exists z\,(z \in x)`$ を取る。
「$`x`$ は元を持つ」という意味である。

- $`x := \emptyset`$ のとき。$`z \in X`$ で $`z \in \emptyset`$ となるものは無いので **偽**
- $`x := \{\emptyset\}`$ のとき。$`z := \emptyset`$ は $`X`$ の元で $`\emptyset \in \{\emptyset\}`$
  なので **真**

よって

```math
\{\, x \in X : (X,\in) \models \varphi[x] \,\} = \{\{\emptyset\}\}.
```

### 量化子を X に閉じ込めることの効き目

同じ $`X = \{\emptyset, \{\emptyset\}\}`$ で $`\psi(x) \equiv \exists z\,(x \in z)`$ を取る。
「$`x`$ は何かの元である」という意味である。$`x := \{\emptyset\}`$ を入れる。

- 構造 $`(X,\in)`$ では、候補 $`z`$ は $`\emptyset`$ と $`\{\emptyset\}`$ の 2 つだけ。
  $`\{\emptyset\} \in \emptyset`$ も $`\{\emptyset\} \in \{\emptyset\}`$ も成立しないので **偽**
- 宇宙全体で見れば $`\{\emptyset\} \in \{\{\emptyset\}\}`$ なので **真**

同じ論理式でも、$`(X,\in) \models`$ と「本当に成立する」は違う。この違いがこの先ずっと効く。

## 3. あとで使う 2 つの言葉

**推移的.** 集合 $`X`$ が **推移的** とは

```math
x \in y \in X \ \Longrightarrow\ x \in X
```

が成り立つこと。言い換えると $`X`$ の元は全て $`X`$ の部分集合である。

**フォンノイマン自然数.** 自然数を集合として

```math
0 = \emptyset, \quad 1 = \{0\}, \quad 2 = \{0, 1\}, \quad \dots, \quad n = \{0, 1, \dots, n-1\}
```

と定める。$`n`$ は「自分より小さい自然数全部の集合」である。どれも推移的である。

## 4. 定義可能冪集合 Def

### 4.1 定義可能

集合 $`X`$ と、その部分集合 $`b \subseteq X`$ を取る。$`b`$ が **$`X`$ 上で定義可能** であるとは、
論理式 $`\varphi(x, y_1, \dots, y_n)`$ と、パラメータ $`p_1, \dots, p_n \in X`$ が存在して

```math
b = \{\, x \in X : (X, \in) \models \varphi[x, p_1, \dots, p_n] \,\}
```

と書けることをいう。$`\varphi`$ の量化子が $`X`$ の中だけを走ることは §2 のとおりである。

#### 例

$`X = \{\emptyset, \{\emptyset\}\}`$ で見る。

$`b = \{\{\emptyset\}\}`$ は定義可能である。$`\varphi(x) \equiv \exists z\,(z \in x)`$ と取ると、
§2 で計算したとおり

```math
\{\, x \in X : (X,\in) \models \varphi[x] \,\} = \{\{\emptyset\}\} = b .
```

パラメータは使っていない（$`n = 0`$）。

$`b = \{\emptyset\}`$ も定義可能である。こちらはパラメータを使う。
$`\varphi(x, y) \equiv (x = y)`$ と取り、$`p_1 := \emptyset \in X`$ を入れると

```math
\{\, x \in X : (X,\in) \models \varphi[x, \emptyset] \,\}
= \{\, x \in X : x = \emptyset \,\} = \{\emptyset\} = b .
```

パラメータを使わずに $`\varphi(x) \equiv \neg\exists z\,(z \in x)`$（「$`x`$ は空」）と書いてもよい。

残りの 2 つも定義可能である。

| $`b`$ | $`\varphi`$ | パラメータ |
|---|---|---|
| $`\emptyset`$ | $`x \ne x`$ | なし |
| $`\{\emptyset\}`$ | $`\neg\exists z\,(z \in x)`$ | なし |
| $`\{\{\emptyset\}\}`$ | $`\exists z\,(z \in x)`$ | なし |
| $`\{\emptyset, \{\emptyset\}\}`$ | $`x = x`$ | なし |

この $`X`$ は有限なので、部分集合 4 つが全部定義可能になった。これは偶然ではなく、
有限集合では常にそうなる（§6）。定義可能でない部分集合が現れるのは $`X`$ が無限になってからで、
最初の例は §7 の第 ω+1 段に出てくる。

### 4.2 Def(X)

定義可能な $`b`$ を全部集めたものを $`\mathrm{Def}(X)`$ と書く。

```math
\mathrm{Def}(X) = \{\, b \subseteq X : b \text{ は } X \text{ 上で定義可能} \,\}
```

冪集合 $`P(X)`$ が部分集合を全部集めるのに対し、$`\mathrm{Def}(X)`$ は
「論理式と有限個のパラメータで指定できるもの」だけを集める。従って

```math
\mathrm{Def}(X) \subseteq P(X).
```

4.1 の計算は、$`X = \{\emptyset, \{\emptyset\}\}`$ について

```math
\mathrm{Def}(X) = P(X)
= \bigl\{\ \emptyset,\ \ \{\emptyset\},\ \ \{\{\emptyset\}\},\ \ \{\emptyset,\{\emptyset\}\}\ \bigr\}
```

であることを示している。

### 4.3 個数

論理式は可算個しかない。パラメータは $`X`$ の元の有限列なので、$`X`$ が無限なら $`|X|`$ 個、
$`X`$ が有限なら有限個しかない。対 $`(\varphi, \bar p)`$ 一つが $`b`$ 一つを決めるので

```math
|\mathrm{Def}(X)| \le |X| + \aleph_0 .
```

$`P(X)`$ の大きさが $`2^{|X|}`$ であることと比べると、無限集合では大きな差になる。

## 5. 構成可能階層

順序数に沿って $`\mathrm{Def}`$ を繰り返す。

```math
L_0 = \emptyset, \qquad
L_{\xi+1} = \mathrm{Def}(L_\xi), \qquad
L_\lambda = \bigcup_{\xi < \lambda} L_\xi \quad (\lambda \text{ 極限})
```

そして

```math
L = \bigcup_{\xi \in \mathrm{Ord}} L_\xi .
```

$`L`$ の元を **構成可能集合** と呼ぶ。「構成可能」とは「下の段から論理式で作れる」の意である。

比較のため、フォンノイマン階層は同じ形で $`\mathrm{Def}`$ を $`P`$ に替えたものである。

```math
V_0 = \emptyset, \qquad
V_{\xi+1} = P(V_\xi), \qquad
V_\lambda = \bigcup_{\xi<\lambda} V_\xi
```

## 6. 有限段では Def と P が一致する

**補題.** $`X`$ が有限なら $`\mathrm{Def}(X) = P(X)`$。

**証明.** $`b \subseteq X`$ とする。$`b = \emptyset`$ なら $`\varphi(x)`$ を $`x \ne x`$ と取ればよい。
$`b = \{p_1, \dots, p_m\}`$（$`m \ge 1`$）なら $`p_1,\dots,p_m`$ をパラメータにして

```math
\varphi(x, y_1, \dots, y_m) \ \equiv\ (x = y_1 \vee \cdots \vee x = y_m)
```

と取れば $`b = \{x \in X : (X,\in) \models \varphi[x, \bar p]\}`$。$`\square`$

有限段で $`L`$ と $`V`$ が一致するのはこのためである。差が出るのは無限集合を相手にしてからで、
そこでは「$`b`$ の元を全部パラメータに並べる」ができなくなる。

## 7. 小さい段を計算する

### 第 0 段

```math
L_0 = \emptyset
```

元は 0 個。

### 第 1 段

$`L_0 = \emptyset`$ の部分集合は $`\emptyset`$ ただ一つで、$`\varphi(x) \equiv (x \ne x)`$ で書ける。

```math
L_1 = \mathrm{Def}(\emptyset) = \{\emptyset\}
```

元は 1 個。

### 第 2 段

$`L_1 = \{\emptyset\}`$ の部分集合は $`\emptyset`$ と $`\{\emptyset\}`$ の 2 つ。

- $`\emptyset`$ … $`\varphi(x) \equiv (x \ne x)`$
- $`\{\emptyset\}`$ … $`\varphi(x) \equiv (x = x)`$。$`L_1`$ 全体だから

```math
L_2 = \{\emptyset,\ \{\emptyset\}\}
```

元は 2 個。これはフォンノイマン自然数の $`2 = \{0, 1\}`$ である。

### 第 3 段

$`L_2 = \{\emptyset, \{\emptyset\}\}`$ の部分集合は 4 つ。有限なので全部定義可能。

| 部分集合 | 論理式 |
|---|---|
| $`\emptyset`$ | $`x \ne x`$ |
| $`\{\emptyset\}`$ | $`\neg \exists z\,(z \in x)`$（「$`x`$ は空」） |
| $`\{\{\emptyset\}\}`$ | $`\exists z\,(z \in x)`$（§2 の例） |
| $`\{\emptyset, \{\emptyset\}\}`$ | $`x = x`$ |

```math
L_3 = \bigl\{\ \emptyset,\ \ \{\emptyset\},\ \ \{\{\emptyset\}\},\ \ \{\emptyset,\{\emptyset\}\}\ \bigr\}
```

元は 4 個。パラメータを使えば $`\varphi(x,y) \equiv (x = y)`$ に $`y := \emptyset`$ を入れて
$`\{\emptyset\}`$ を出す、という書き方もできる。

### 第 4 段以降

$`|L_3| = 4`$ なので、有限段の補題から $`L_4 = P(L_3)`$ で

```math
|L_4| = 2^4 = 16 .
```

以下 $`|L_{n+1}| = 2^{|L_n|}`$ で、

| $`n`$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| $`\lvert L_n \rvert`$ | 0 | 1 | 2 | 4 | 16 | 65536 | $`2^{65536}`$ |

すぐ書き下せなくなるが、$`n \lt \omega`$ の間はずっと

```math
L_n = V_n
```

である。

### 第 ω 段

```math
L_\omega = \bigcup_{n<\omega} L_n = \bigcup_{n<\omega} V_n = V_\omega
```

これは **遺伝的有限集合** $`\mathrm{HF}`$、すなわち「有限で、その元も有限で、下までずっと有限」な
集合全体である。$`L_\omega`$ は可算である。

#### 新しく入るものは無い

$`\omega`$ は極限順序数なので、第 ω 段は合併である。従って $`a \in L_\omega`$ なら
ある $`n \lt \omega`$ について $`a \in L_n`$ である。

```math
L_\omega \setminus \bigcup_{n<\omega} L_n = \emptyset
```

つまり第 ω 段そのものは新しい元を作らない。新しい元は各有限段が作り、
第 ω 段はそれを全部集めるだけである。極限段は全てこうなる。

#### 元の例

どれも、ある有限段で新しく入ったものである。

| 元 | 展開した形 | 新しく入った段 |
|---|---|---|
| $`0`$ | $`\emptyset`$ | $`L_1`$ |
| $`1`$ | $`\{\emptyset\}`$ | $`L_2`$ |
| $`2`$ | $`\{\emptyset,\{\emptyset\}\}`$ | $`L_3`$ |
| $`\{1\}`$ | $`\{\{\emptyset\}\}`$ | $`L_3`$ |
| $`\{2\}`$ | $`\{\{\emptyset,\{\emptyset\}\}\}`$ | $`L_4`$ |
| $`\{1,2\}`$ | $`\{\{\emptyset\},\{\emptyset,\{\emptyset\}\}\}`$ | $`L_4`$ |

フォンノイマン自然数 $`0, 1, 2, \dots`$ は全て属する。$`n`$ が新しく入るのは $`L_{n+1}`$ である。

順序対も属する。$`\langle x, y \rangle = \{\{x\},\{x,y\}\}`$ と符号化すると

```math
\langle 0, 1 \rangle = \{\{0\},\{0,1\}\} = \{\{\emptyset\},\{\emptyset,\{\emptyset\}\}\}
```

で、これは上の表の $`\{1,2\}`$ と同じ集合である。同様に有限列も有限グラフも
$`\mathrm{HF}`$ の中に符号化できる。有限の組合せ論はまるごとここに入る。

$`\omega`$ 自身は無限なので属さない。

#### 付記：ω の元でないものが混ざっている

$`\omega`$ の元は自然数だけである。上の表の $`\{1\}`$ は $`L_3`$ の元、従って
$`L_\omega`$ の元だが、自然数ではないので $`\omega`$ の元ではない。
$`\{2\}`$、$`\{1,2\}`$、$`\langle 0,1 \rangle`$ も同じである。よって

```math
\omega \subsetneq L_\omega .
```

包含は成り立つ。各 $`n`$ について $`n \in L_{n+1} \subseteq L_\omega`$ だからである。
等号は成り立たない。

紛らわしいのは次の 2 点である。どちらも一致するが、集合としては別物である。

- 順序数だけを見れば一致する。$`L_\omega \cap \mathrm{Ord} = \omega`$（§9）
- 個数も一致する。$`|L_\omega| = |\omega| = \aleph_0`$

### 第 ω+1 段

ここで初めて $`\mathrm{Def}`$ と $`P`$ が分かれる。

```math
L_{\omega+1} = \mathrm{Def}(L_\omega), \qquad V_{\omega+1} = P(V_\omega)
```

$`L_\omega = V_\omega`$ は可算なので

```math
|V_{\omega+1}| = 2^{\aleph_0} \quad(\text{非可算}), \qquad
|L_{\omega+1}| = \aleph_0 \quad(\text{可算})
```

#### 何が新しく入るか

$`L_{\omega+1}`$ の元は $`L_\omega`$ の部分集合である。$`b \subseteq L_\omega`$ が
**有限** なら、$`b`$ の元は全て遺伝的有限だから $`b`$ 自身も遺伝的有限で、
$`b \in L_\omega`$。つまり前からある。従って新入りは無限なものだけで、

```math
L_{\omega+1} \setminus L_\omega
= \{\, b \subseteq L_\omega : b \text{ は定義可能かつ無限} \,\}.
```

#### 新しく入るものの例

| 新しい元 | 論理式 | パラメータ |
|---|---|---|
| $`\omega = \{0,1,2,\dots\}`$ | 「$`x`$ は推移的で、その元も推移的」 | なし |
| $`L_\omega`$ 自身 | $`x = x`$ | なし |
| $`L_\omega \setminus \omega`$（自然数でない有限集合全体） | 上の否定 | なし |
| 単集合全体 $`\{\{a\} : a \in L_\omega\}`$ | $`\exists z\,(z \in x) \wedge \forall z\,\forall w\,(z \in x \wedge w \in x \to z = w)`$ | なし |
| $`\omega \setminus (n+1) = \{n+1, n+2, \dots\}`$ | 「$`x`$ は順序数」$`\wedge\ y \in x`$ | $`y := n`$ |
| 偶数全体 $`\{0,2,4,\dots\}`$、素数全体 | 算術を書き下したもの。長いので略す | なし |

$`\omega`$ の論理式を書き下すと

```math
\forall y \in x\,\forall z \in y\,(z \in x)
\ \wedge\ \forall y \in x\,\forall z \in y\,\forall w \in z\,(w \in y)
```

である（$`x`$ は推移的で、その元も推移的）。$`L_\omega`$ の元でこれを満たすのは
フォンノイマン自然数だけなので、切り出される集合は $`\omega`$ ちょうどである。
$`\omega \notin L_\omega`$ だったので、確かに新しい元である。

$`n`$ をパラメータに変えた 5 行目だけで $`\omega \setminus 1, \omega \setminus 2, \dots`$ と
無限個の新入りが出る。新入りの総数は $`\mathrm{Def}(L_\omega)`$ が可算なので可算無限個である。

#### 新しく入らないものの例

$`\omega`$ の部分集合は $`2^{\aleph_0}`$ 個あるが、$`L_{\omega+1}`$ は可算なので、
ほとんど全部は入らない。実際 $`L_{\omega+1} \cap P(\omega)`$ は
$`(V_\omega, \in)`$ 上で定義可能な集合、すなわち算術的集合ちょうどである。
停止問題の次数より上にある集合（たとえば $`0^{(\omega)}`$）は入らない。

これが $`\mathrm{Def}`$ と $`P`$ の差である。$`V_{\omega+1} = P(V_\omega)`$ には
$`\omega`$ の部分集合が $`2^{\aleph_0}`$ 個すべて入る。

#### 付記：順序数に限れば新入りは ω だけ

```math
L_\omega \cap \mathrm{Ord} = \omega, \qquad
L_{\omega+1} \cap \mathrm{Ord} = \omega+1
```

差は $`\{\omega\}`$ ただ一つである。§9 の性質 $`L_\xi \cap \mathrm{Ord} = \xi`$ は
これを言っているだけで、$`L_\xi`$ そのものの増え方の話ではない。
元全体で見れば、上のとおり可算無限個が新しく入る。

## 8. 一般の段の大きさ

$`\xi \ge \omega`$ なら

```math
|L_\xi| = |\xi| .
```

とくに $`\xi`$ が可算順序数なら $`L_\xi`$ は可算集合である。

$`\mathrm{Def}`$ を一回適用しても大きさが $`|X| + \aleph_0`$ までしか増えないこと（§4 の個数評価）と、
極限段が $`|\lambda|`$ 個の合併であることから、$`\xi`$ に関する超限帰納法で従う。
$`P`$ を使う $`V_\xi`$ では $`|V_{\omega+n}|`$ が $`n`$ ごとに指数で跳ね上がるので、この評価は成り立たない。

## 9. 基本性質

| 性質 | 内容 |
|---|---|
| 推移性 | 各 $`L_\xi`$ は推移的 |
| 単調性 | $`\xi \le \eta \Rightarrow L_\xi \subseteq L_\eta`$ |
| 自分自身 | $`L_\xi \in L_{\xi+1}`$ |
| 順序数 | $`L_\xi \cap \mathrm{Ord} = \xi`$ |
| 階数 | $`x \in L_\xi \Rightarrow \mathrm{rank}(x) \lt \xi`$ |

**推移性と単調性の理由.** $`X`$ が推移的なら $`X \subseteq \mathrm{Def}(X)`$ である。実際
$`a \in X`$ に対し $`\varphi(x,y) \equiv (x \in y)`$、$`y := a`$ とすると
$`\{x \in X : x \in a\} = a \cap X = a`$（推移性より $`a \subseteq X`$）。これで
$`L_\xi \subseteq L_{\xi+1}`$ が出る。また $`b \in \mathrm{Def}(X)`$ なら
$`b \subseteq X \subseteq \mathrm{Def}(X)`$ なので $`\mathrm{Def}(X)`$ も推移的である。

**自分自身の理由.** $`\varphi(x) \equiv (x = x)`$ が $`L_\xi`$ 全体を切り出す。

**順序数の理由.** §7 の $`\omega \in L_{\omega+1}`$ と同じ議論を各段で行う。
$`\supseteq`$ は $`\zeta \lt \xi`$ に対し $`\zeta \in L_{\zeta+1} \subseteq L_\xi`$ から。
$`\subseteq`$ は階数の評価から。

## 10. 注意：V = L は仮定していない

§5 のとおり、$`L`$ の元を **構成可能集合** と呼ぶ。ここで、全ての集合が構成可能であるという主張

```math
V = L
```

は $`\mathrm{ZFC}`$ から独立した別の公理である。本ノートも原文もこれを仮定しない。

仮定しなくてよい理由は、$`L_\xi`$ の定義（§5）が $`\mathrm{ZFC}`$ の中でそのまま書けるからである。
$`\mathrm{Def}`$ を順序数に沿って繰り返すだけなので、$`V = L`$ がなくても
$`L`$ とその階層 $`L_\xi`$ は存在する。$`V = L`$ は「それで全部か」を主張する公理であって、
$`L`$ が作れるかどうかとは別である。

原文も $`\mathrm{ZFC}`$ の中で $`L`$ を作り、その中の順序数を配列のラベルとして使うだけである。
実際、補題 16.2 では外部宇宙の $`\omega_1^V`$ を取っており、$`V`$ と $`L`$ を区別して使っている。

## 11. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 論理式 | `Fm` | `Bm4/SetTheory/Fm.lean` |
| $`(X,\in) \models \varphi[\bar a]`$ | `SatIn W v φ` | 同上 |
| 量化域を指定した充足 | `Sat D v φ` | 同上 |
| $`b`$ が $`X`$ 上で定義可能 | `DefinableOver M X` | `Bm4/SetTheory/L.lean` |
| $`\mathrm{Def}(X)`$ | `Def M` | 同上 |
| $`L_\xi`$ | `L o` | 同上 |
| $`L_0 = \emptyset`$ | `L_zero` | 同上 |
| $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ | `L_succ` | 同上 |
| 極限段の合併 | `L_limit`, `mem_L_limit` | 同上 |
| $`\mathrm{Def}(X) \subseteq P(X)`$ | `subset_of_mem_Def` | 同上 |
| $`X \subseteq \mathrm{Def}(X)`$（$`X`$ 推移的） | `subset_Def` | 同上 |
| $`X \in \mathrm{Def}(X)`$ | `self_mem_Def` | 同上 |
| $`\mathrm{Def}(X)`$ の推移性 | `Def_transitive` | 同上 |
| $`L_\xi`$ の推移性 | `L_transitive` | 同上 |
| $`\xi \le \eta \Rightarrow L_\xi \subseteq L_\eta`$ | `L_mono` | 同上 |
| $`L_\xi \in L_{\xi+1}`$ | `L_mem_L_succ` | 同上 |
| $`L_\xi \cap \mathrm{Ord} = \xi`$ | `toZFSet_mem_L_iff` | 同上 |
| $`x \in L_\xi \Rightarrow \mathrm{rank}(x) \lt \xi`$ | `rank_lt_of_mem_L` | 同上 |
