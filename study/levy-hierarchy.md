[← Back](README.md)

# レヴィ階層と絶対性

前提: [構成可能階層 L](constructible-hierarchy.md)（論理式、構造 $`(X,\in)`$、充足 $`\models`$、推移的集合）

## 1. 有界量化と非有界量化

**定義（非有界量化）.** 論理式に現れる $`\exists z`$、$`\forall z`$ を、そのままの形で
**非有界量化** と呼ぶ。

**意味.** $`z`$ が動く範囲に制限がない。宇宙にある集合を全部走る。

**定義（有界量化）.** 変数 $`z`$ と、$`z`$ と異なる変数 $`y`$ に対し、次を略記とする。

```math
\exists z \in y\ \varphi \ \equiv\ \exists z\,(z \in y \wedge \varphi), \qquad
\forall z \in y\ \varphi \ \equiv\ \forall z\,(z \in y \to \varphi)
```

ただし $`y`$ は $`\varphi`$ の中で $`z`$ に束縛されていないものとする。
この形を **有界量化** と呼ぶ。

**意味.** $`z`$ が動く範囲が $`y`$ の元に限られる。探す範囲となる集合 $`y`$ を先に渡している。

**見分け方.** 有界量化を略記でなく展開すると $`\exists z`$ が現れるが、それは必ず
$`z \in y \wedge \cdots`$ と組になっている。この組になっていない裸の $`\exists z`$、$`\forall z`$ が
非有界量化である。

| 論理式 | 種類 |
|---|---|
| $`\forall z \in x\ (z \in y)`$ | 有界が 1 つ |
| $`\forall y \in x\ \forall z \in y\ (z \in x)`$ | 有界が 2 つ |
| $`\exists z\ (x \in z)`$ | 非有界が 1 つ |
| $`\forall w\,(w \subseteq x \to w \in z)`$ | 非有界が 1 つ。$`w \subseteq x`$ の中身は有界 |

有界と非有界の差は、あとの §3 で効いてくる。

## 2. Δ₀ 論理式

### 2.1 定義

論理式 $`\varphi`$ が $`\Delta_0`$ であるとは、**$`\varphi`$ に現れる量化子が全て有界** であることをいう。

原子式（$`x = y`$ と $`x \in y`$）は量化子を持たないので $`\Delta_0`$ である。
$`\Delta_0`$ 論理式を $`\neg, \wedge, \vee, \to`$ でつないだものも $`\Delta_0`$ であり、
$`\Delta_0`$ 論理式に有界量化を付けたものも $`\Delta_0`$ である。それだけの集まりである。

### 2.2 Δ₀ で書ける例

| 意味 | $`\Delta_0`$ 論理式 |
|---|---|
| $`x \subseteq y`$ | $`\forall z \in x\ (z \in y)`$ |
| $`x = \emptyset`$ | $`\neg \exists z \in x\ (z = z)`$ |
| $`x`$ は推移的 | $`\forall y \in x\ \forall z \in y\ (z \in x)`$ |
| $`x`$ は順序数 | $`x`$ は推移的 $`\wedge\ \forall y \in x\ (y`$ は推移的$`)`$ |
| $`z = \{x, y\}`$ | $`x \in z \wedge y \in z \wedge \forall w \in z\ (w = x \vee w = y)`$ |
| $`z = x \cup y`$ | $`\forall w \in z\,(w \in x \vee w \in y) \wedge \forall w \in x\,(w \in z) \wedge \forall w \in y\,(w \in z)`$ |
| $`z = \bigcup x`$ | $`\forall w \in z\ \exists u \in x\ (w \in u) \wedge \forall u \in x\ \forall w \in u\ (w \in z)`$ |
| $`x`$ は極限順序数 | $`x`$ は順序数 $`\wedge\ \neg(x = \emptyset) \wedge \forall y \in x\ \exists z \in x\ (y \in z)`$ |
| $`x = \omega`$ | $`x`$ は極限順序数 $`\wedge\ \forall y \in x\ \neg(y`$ は極限順序数$`)`$ |

順序対 $`z = \langle x, y \rangle = \{\{x\},\{x,y\}\}`$ も $`\Delta_0`$ である。
$`z`$ の元は $`\{x\}`$ と $`\{x,y\}`$ の 2 つだけなので、$`\exists u \in z`$、$`\exists v \in z`$ と
有界化して、上の $`z = \{x,y\}`$ の行を使えばよい。

有限列、有限関数、それらの長さ・成分・連結も同じ調子で $`\Delta_0`$ になる。
原文が §8 で「これらは $`\Delta_0`$ である」と繰り返すのはこの意味である。

### 2.3 Δ₀ で書けそうにない例

有界量化 $`\exists z \in y`$ は「$`y`$ の元の中だけを探す」という意味だった。だから量化子を
有界にするには、**探しているものを全部含む集合が、すでに変数として手元にある** 必要がある。
手元とは、自由変数と、そこから 2.2 の操作で届く範囲である。

これができない例を 3 つ挙げる。

**$`z = P(x)`$.** 言いたいのは「$`x`$ の部分集合は全部 $`z`$ に入る」である。走らせたい $`w`$ は
$`x`$ の部分集合全体だが、それを含む集合は $`P(x)`$ しかない。ところが $`P(x)`$ は、
今まさに $`z`$ として定義しようとしているものである。$`\forall w \in z`$ と書いてしまうと
「$`z`$ に入っているものについて」しか言えず、肝心の「全部入っている」が言えない。

$`x`$ の元を走らせても届かない。$`\in`$ と $`\subseteq`$ は違うからである。

| | 中身 | 個数 |
|---|---|---|
| $`x = \{0,1\}`$ の元 | $`0,\ 1`$ | 2 |
| $`x`$ の部分集合 | $`\emptyset,\ \{0\},\ \{1\},\ \{0,1\}`$ | 4 |

下の行は $`x`$ の元ではないので、$`\forall w \in x`$ では拾えない。

**$`x`$ は可算.** 全単射 $`f : x \to \omega`$ が存在することを言いたい。$`f`$ は
$`\langle a, n \rangle`$ を集めた集合、すなわち $`x \times \omega`$ の部分集合である。
走らせたい範囲は $`P(x \times \omega)`$ で、$`x`$ と $`\omega`$ の元をいくら見ても出てこない。

**$`x`$ は基数.** 「$`\alpha \lt x`$ から $`x`$ の上への全射は無い」を言いたい。
同じく $`f`$ を走らせる範囲がない。

以上は「書き方が思いつかない」という話である。「書けない」ことの証明は §3.5 で述べる。
複雑度の呼び名は §4.5 で与える。

## 3. Δ₀ 絶対性

このノートの主役である。

### 3.1 主張

**定理（$`\Delta_0`$ 絶対性）.** $`M`$ を推移的な集合、$`\varphi`$ を $`\Delta_0`$ 論理式、
$`\bar a`$ を $`M`$ の元からなる割り当てとする。このとき

```math
(M, \in) \models \varphi[\bar a] \quad\iff\quad \varphi[\bar a] .
```

右辺は「宇宙全体で本当に成立する」ことを表す。

つまり **$`\Delta_0`$ 論理式の真偽は、推移的集合の中で測っても外で測っても同じ** である。

### 3.2 証明

$`\varphi`$ の作られ方に関する帰納法で示す。

**原子式.** $`(M,\in) \models (x \in y)[\bar a]`$ は $`\bar a(x) \in \bar a(y)`$ のこと、
$`(x \in y)[\bar a]`$ も $`\bar a(x) \in \bar a(y)`$ のことである。同じ。$`x = y`$ も同様。

**結合子.** $`\neg`$、$`\wedge`$、$`\vee`$、$`\to`$ は、両辺とも部分論理式の真偽から同じ規則で決まる。
帰納法の仮定をそのまま使えばよい。

**有界存在量化.** $`\varphi = \exists z \in y\ \psi`$ とする。充足の定義から

```math
(M,\in) \models \varphi[\bar a]
\iff \text{ある } c \in M \text{ で } c \in \bar a(y) \text{ かつ }
(M,\in) \models \psi[\bar a(z \mapsto c)]
```

帰納法の仮定で右端を $`\psi[\bar a(z \mapsto c)]`$ に置き換えられる。一方、外側では

```math
\varphi[\bar a]
\iff \text{ある } c \text{ で } c \in \bar a(y) \text{ かつ } \psi[\bar a(z \mapsto c)]
```

違いは $`c`$ を $`M`$ から取るか宇宙全体から取るかだけである。ところが $`\bar a(y) \in M`$ で
$`M`$ は推移的だから

```math
\bar a(y) \subseteq M .
```

従って $`c \in \bar a(y)`$ なら自動的に $`c \in M`$ である。2 つの条件は一致する。

**有界全称量化.** $`\forall z \in y\ \psi \equiv \neg \exists z \in y\ \neg\psi`$ なので上に帰着する。
$`\square`$

推移性を使ったのは有界量化の 1 箇所だけである。そこで
「$`\bar a(y)`$ の元は自動的に $`M`$ の元」が言えることが、この定理の全てである。

### 3.3 推移性は落とせない

$`M = \{\emptyset, \{\{\emptyset\}\}\}`$ とする。これは推移的でない。実際
$`\{\emptyset\} \in \{\{\emptyset\}\} \in M`$ だが $`\{\emptyset\} \notin M`$ である。

$`\varphi(x) \equiv \exists z \in x\ (z = z)`$（「$`x`$ は空でない」）を取り、
$`x := \{\{\emptyset\}\}`$ を入れる。これは $`\Delta_0`$ である。

- $`(M,\in)`$ では、$`c \in M`$ で $`c \in \{\{\emptyset\}\}`$ となるものを探す。
  候補は $`\emptyset`$ と $`\{\{\emptyset\}\}`$ だが、どちらも $`\{\{\emptyset\}\}`$ の元ではない。
  よって **偽**
- 外では $`\{\emptyset\} \in \{\{\emptyset\}\}`$ なので **真**

$`\Delta_0`$ なのに食い違った。推移性が要る理由である。

### 3.4 何が嬉しいのか

前のノートの §2 で、$`(X,\in) \models`$ と「本当に成立する」は違う、という例を作った。
$`\Delta_0`$ のときだけは違わない、というのがこの定理である。

言い換えると

> $`\Delta_0`$ の条件で探し物をするなら、推移的集合の中で見つけたものは本物である。

原文はこの形で繰り返し使う。

- $`\mathrm{SatCode}(A,U,T)`$ は $`\Delta_0`$（式 8.5）。だから $`L_\theta`$ の中で
  $`\mathrm{SatCode}`$ を満たす $`U, T`$ を見つければ、外から見ても本物の充足コードである
- $`\mathrm{LCode}(\eta,M,c)`$ は $`\Delta_0`$（式 9.4）。だから $`L_\theta`$ の中で見つけた
  $`L`$-階層コードは外でも正しく、補題 9.2 から $`M = L_\eta`$ が外でも言える（系 10.6）

逆向きも同時に言える。外で真なら中でも真である。

### 3.5 Δ₀ で書けないことの示し方

§3.1 の対偶を取る。

```math
\varphi \in \Delta_0 \ \Longrightarrow\ \text{推移的集合で絶対}
```

だったので、次が言える。

> 推移的な集合 $`M`$ と $`M`$ の元からなる割り当て $`\bar a`$ があって、
> $`(M,\in) \models \varphi[\bar a]`$ と $`\varphi[\bar a]`$ の真偽が食い違うなら、
> $`\varphi`$ は $`\Delta_0`$ ではない。

**例.**

```math
\psi(x) \ \equiv\ \exists z\ (x \in z)
```

「$`x`$ は何かの元である」という意味である。非有界量化が 1 個あるだけの、見た目は簡単な論理式である。

$`M = L_2 = \{\emptyset, \{\emptyset\}\}`$ を取る。これは推移的である。
$`\emptyset`$ は元を持たず、$`\{\emptyset\}`$ の唯一の元 $`\emptyset`$ は $`M`$ に属するからである。
$`x := \{\emptyset\}`$ を入れる。

- $`(M,\in)`$ では、候補 $`z`$ は $`\emptyset`$ と $`\{\emptyset\}`$ の 2 つだけ。
  $`\{\emptyset\} \in \emptyset`$ も $`\{\emptyset\} \in \{\emptyset\}`$ も成立しないので **偽**
- 外では $`\{\emptyset\} \in \{\{\emptyset\}\}`$ なので **真**

食い違ったので $`\psi`$ は $`\Delta_0`$ ではない。

**量化子の個数は関係ない.** この例は、$`\Delta_0`$ かどうかが量化子の個数の問題ではないことも
示している。§2.2 の $`x = \omega`$ は展開すると有界量化を十数個持つが $`\Delta_0`$ であり、
ここの $`\psi`$ は非有界量化を 1 個しか持たないが $`\Delta_0`$ でない。
効くのは個数ではなく、量化子を抑える集合が手元にあるかである。

§2.3 の 3 つも同じ方法で $`\Delta_0`$ でないことが示せる。ただし真偽が食い違う $`M`$ の作り方は
上の例より重く、可算な推移的モデルを取る議論が要る。ここでは省く。

## 4. Σ₁ と Π₁

### 4.1 ブロック

**定義.** 論理式の先頭に並んだ非有界量化のうち、**同じ種類が連続しているひとかたまり** を
**ブロック** と呼ぶ。種類が $`\exists`$ から $`\forall`$ へ、または $`\forall`$ から
$`\exists`$ へ変わったところでブロックが切れる。

**意味.** 同じ種類がいくつ並んでいても 1 ブロックである。数えるのは量化子の個数ではなく、
種類が切り替わった回数である。

**例.**

| 論理式 | ブロックの切れ方 | ブロック数 |
|---|---|---|
| $`\exists x_1\, \exists x_2\, \exists x_3\ \delta`$ | $`\exists x_1 \exists x_2 \exists x_3`$ | 1 |
| $`\forall x_1\, \forall x_2\ \delta`$ | $`\forall x_1 \forall x_2`$ | 1 |
| $`\exists x_1\, \exists x_2\, \forall y_1\ \delta`$ | $`\exists x_1 \exists x_2`$ \| $`\forall y_1`$ | 2 |
| $`\exists x\, \forall y\, \exists z\ \delta`$ | $`\exists x`$ \| $`\forall y`$ \| $`\exists z`$ | 3 |

### 4.2 Σ₁ と Π₁ の定義

**定義.** $`\delta`$ を $`\Delta_0`$ 論理式とする。

```math
\Sigma_1 :\ \exists x_1 \cdots \exists x_n\ \delta, \qquad
\Pi_1 :\ \forall x_1 \cdots \forall x_n\ \delta
```

の形の論理式を、それぞれ $`\Sigma_1`$、$`\Pi_1`$ と呼ぶ。
先頭の $`\exists x_i`$、$`\forall x_i`$ は $`\in y`$ が付いていないので非有界量化である（§1）。

**$`\Delta_0`$ も入る.** $`n = 0`$、すなわちブロックが空の場合と読めば、
$`\Delta_0`$ 論理式自身も $`\Sigma_1`$ かつ $`\Pi_1`$ である。

### 4.3 片側だけの絶対性

**定理.** $`M`$ を推移的な集合、$`\bar a`$ を $`M`$ の元からなる割り当てとする。

```math
\varphi \in \Sigma_1 \ \Longrightarrow\
\bigl[\ (M,\in) \models \varphi[\bar a] \ \Longrightarrow\ \varphi[\bar a]\ \bigr]
```

```math
\psi \in \Pi_1 \ \Longrightarrow\
\bigl[\ \psi[\bar a] \ \Longrightarrow\ (M,\in) \models \psi[\bar a]\ \bigr]
```

前者を **上向き絶対**、後者を **下向き絶対** と呼ぶ。

**証明.** $`\varphi = \exists \bar x\ \delta`$ とする。$`(M,\in) \models \varphi[\bar a]`$ なら、
証人 $`\bar c \in M`$ があって $`(M,\in) \models \delta[\bar c, \bar a]`$。
$`\delta`$ は $`\Delta_0`$ なので §3 から $`\delta[\bar c, \bar a]`$ は本当に真。
従って $`\exists \bar x\ \delta`$ も真である。

$`\psi = \forall \bar x\ \delta`$ とする。$`\psi[\bar a]`$ が真なら、特に $`M`$ の元 $`\bar c`$ についても
$`\delta[\bar c, \bar a]`$ が真。§3 から $`(M,\in) \models \delta[\bar c, \bar a]`$。
$`\bar c`$ は $`M`$ の任意の元だったので $`(M,\in) \models \psi[\bar a]`$。$`\square`$

### 4.4 逆向きが言えない例

§3.5 で使った

```math
\psi(x) \ \equiv\ \exists z\ (x \in z)
```

をもう一度見る。$`x \in z`$ は原子式なので $`\Delta_0`$ であり、その前に $`\exists z`$ という
$`\exists`$ ブロックが 1 つ付いている。従って 4.2 の形なので $`\Sigma_1`$ である。

$`M = L_2`$、$`x := \{\emptyset\}`$ での計算は §3.5 のとおりで、外で **真**、中で **偽** だった。
$`\Sigma_1`$ の上向き絶対の逆は成り立たない。証人 $`\{\{\emptyset\}\}`$ が $`M`$ の
外にいるためである。

$`\Pi_1`$ では反対に、反例が $`M`$ の外にいると、中で真なのに外で偽になりうる。

### 4.5 §2.3 の例の複雑度

$`\Sigma_1`$ と $`\Pi_1`$ が定義できたので、§2.3 で $`\Delta_0`$ に書けなかった 3 つに
名前を付けられる。

| 意味 | 論理式の形 | 複雑度 |
|---|---|---|
| $`z = P(x)`$ | $`\forall w\,(w \subseteq x \to w \in z) \wedge \forall w \in z\,(w \subseteq x)`$ | $`\Pi_1`$ |
| $`x`$ は可算 | $`\exists f\,\exists w\,(w = \omega \wedge f`$ は $`x`$ から $`w`$ への全単射$`)`$ | $`\Sigma_1`$ |
| $`x`$ は基数 | $`x`$ は順序数 $`\wedge\ \forall f\,\forall \alpha \in x\,(f`$ は $`\alpha`$ から $`x`$ の上への全射でない$`)`$ | $`\Pi_1`$ |

どの行も、先頭の非有界ブロックを外したあとの中身は $`\Delta_0`$ である。
$`w \subseteq x`$、$`w = \omega`$、「$`f`$ は全単射」はいずれも 2.2 の形で書ける。
3 行目の $`\forall \alpha \in x`$ は有界なので、非有界ブロックは $`\forall f`$ だけである。

§4.3 から、$`z = P(x)`$ と「$`x`$ は基数」は下向き絶対、「$`x`$ は可算」は上向き絶対である。

## 5. 上の階層

ブロックを重ねると階層になる。$`\Sigma_{n+1}`$ は $`\Pi_n`$ 論理式の前に非有界 $`\exists`$ ブロックを
付けたもの、$`\Pi_{n+1}`$ は $`\Sigma_n`$ 論理式の前に非有界 $`\forall`$ ブロックを付けたものである。
これを **レヴィ階層** と呼ぶ。

原文は $`n \ge 2`$ の一般のレヴィ式を使わない。代わりに §12 で
**厳密交代ブロック階層** $`\hat\Sigma_q, \hat\Pi_q`$ を定義し、そちらを使う。
一般のレヴィ式を単純な前置形に直すには Collection が要ることがあり、それを避けるためである
（原文 備考 12.3）。

$`q = 1`$ では両者は一致する。

```math
\hat\Sigma_1 = \Sigma_1, \qquad \hat\Pi_1 = \Pi_1
```

差が出るのは $`q \ge 2`$ からである。$`\hat\Sigma_q`$ は別のノートにする。

## 6. 原文での使われ方

原文が「これは $`\Delta_0`$ である」と主張する箇所は次のとおりである。
どれも §3.4 の「中で見つけたものは本物」を使うためにある。

| 場所 | 主張 |
|---|---|
| §8 (8.3) | 構文操作のグラフ $`G_F`$ は $`\Delta_0`$ |
| §8 (8.4) | 代入の適切さ $`\mathrm{Asn}_A`$ は $`\Delta_0`$ |
| §8 (8.5) | $`\mathrm{SatCode}`$ は $`\Delta_0`$ |
| §9 | $`\mathrm{FourCode}`$、$`\mathrm{DefInp}`$ は $`\Delta_0`$ |
| §9 (9.4) | $`\mathrm{LCode}`$ は $`\Delta_0`$ |
| §11 | $`\mathrm{KPAx}`$ は $`\Delta_0`$ |
| §12 | $`\mathrm{BlkUpd}`$ は $`\Delta_0`$、補題 12.2 の構文操作も $`\Delta_0`$ |
| §14 | 相対化した $`\mathrm{Tr}^M_{\hat\Sigma_j}`$ は $`M`$ をパラメータとする $`\Delta_0`$ |
| §15 | 相対化した $`\mathrm{St}_k(\xi)^M`$ は $`\Delta_0`$ |

$`\Sigma_1`$ が出るのは、たとえば式 (13.1) の $`\mathrm{Tr}^+_{\Delta_0} \in \hat\Sigma_1`$、
$`\mathrm{Tr}^-_{\Delta_0} \in \hat\Pi_1`$ である。

なお、原文 §10 が定義する KP という公理系そのものにも $`\Delta_0`$ が現れる。
$`\Delta_0`$-Separation と $`\Delta_0`$-Collection である。これは次のノートで扱う。

## 7. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 有界全称 $`\forall z \in y`$ | `Fm.ball i j φ` | `Bm4/SetTheory/Fm.lean` |
| 有界存在 $`\exists z \in y`$ | `Fm.bex i j φ` | 同上 |
| $`\Delta_0`$ 論理式 | `IsDelta0` | 同上 |
| $`\Delta_0`$ 絶対性（推移的な量化域） | `IsDelta0.sat_iff_satV` | 同上 |
| $`\Delta_0`$ 絶対性（推移的集合 $`W`$） | `IsDelta0.satIn_iff_satV` | 同上 |
| 2 つの推移的集合の間の絶対性 | `IsDelta0.satIn_iff_satIn` | 同上 |
| $`\hat\Sigma_q`$ / $`\hat\Pi_q`$ 論理式 | `IsSigma q φ` / `IsPi q φ` | 同上 |
| 推移的な量化域 | `TransDom` | `Bm4/SetTheory/Defin.lean` |
| 空でない推移的な量化域 | `GoodDom` | 同上 |
| $`\Delta_0`$ 定義可能な述語 | `Delta0Def s P` | 同上 |
| $`\hat\Sigma_q`$ / $`\hat\Pi_q`$ 定義可能な述語 | `SigmaDef q s P` / `PiDef q s P` | 同上 |
| 有界量化で閉じること | `Delta0Def.ball`, `Delta0Def.bex` | 同上 |
