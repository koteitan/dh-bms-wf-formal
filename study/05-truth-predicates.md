[← Back](README.md) | [English](en/05-truth-predicates.md) | [Japanese](05-truth-predicates.md)

# 部分真理述語と有限段 Tarski–Vaught

前提

| ノート | ここから使う言葉 |
|---|---|
| [構成可能階層 L](01-constructible-hierarchy.md) | 論理式、構造 $`(X,\in)`$、割り当て $`\bar a`$、充足 $`\models`$、推移的、$`L_\xi`$ |
| [レヴィ階層と絶対性](02-levy-hierarchy.md) | 有界量化、ブロック、$`\Delta_0`$、$`\Delta_0`$ 絶対性 |
| [KP と許容順序数](03-kp-admissible.md) | KP、許容順序数、$`\mathrm{SatCode}`$、$`\mathrm{LCode}`$、コード、$`\langle e, a \rangle`$ |
| [厳密交代ブロック階層と安定関係](04-alternating-blocks.md) | **$`\hat\Sigma_q`$、$`\hat\Pi_q`$（1.1）**、行列、padding と有限結合（1.5）、$`\prec^*_q`$、$`\lhd_k`$ |

## 1. なぜ部分真理述語が要るのか

### 1.1 このノートの目的

**示したいこと.** 次のノートの定理 17.1 は、大まかにこういう主張である。

> $`[\alpha, \beta)`$ にある有限個の許容順序数 $`Y`$ を、$`\lhd`$ の関係を保ったまま
> $`\alpha`$ 未満の $`Y'`$ に取り替えられる。

この $`Y'`$ が、安定ラベルの高さを下げるのに使われる（安定ラベルのノート 3.4）。
問題は、そんな $`Y'`$ が存在することをどう示すか、である。

**仮定として使えるのは $`\alpha \lhd_n \beta`$ だけである.** 交代ブロックのノート 3.1 のとおり、
これは $`L_\alpha \prec^*_{n+2} L_\beta`$、すなわち

```math
\hat\Sigma_{n+2} \text{ 以下の文 } \varphi \text{ について } \quad
L_\beta \models \varphi \iff L_\alpha \models \varphi
```

という意味である。文についての同値であって、それ以外のことは言っていない。

**従って手順は 1 つに決まる.** この同値を使うには次の 4 段を踏むしかない。

1. 示したいことを $`\hat\Sigma_{n+2}`$ 文 $`\varphi`$ として書き下す
2. $`L_\beta \models \varphi`$ を確かめる
3. 同値から $`L_\alpha \models \varphi`$ を得る
4. $`L_\alpha`$ における $`\varphi`$ の証人を $`Y'`$ とする

書き下す対象は

```math
\exists u_0 \cdots \exists u_{s-1}\ \bigl(u_0, \dots, u_{s-1}
\text{ は許容順序数で、} \lhd \text{ の関係がこうなっている}\bigr)
```

である。この括弧の中身を言語 $`\{\in\}`$ の論理式として書けなければ、
$`\alpha \lhd_n \beta`$ を仮定していても $`Y'`$ の存在は導けない。

**中身を書くのに何が足りないか.** その文には「$`u \lhd_k v`$」という形の条件が入る。
$`\lhd_k`$ の定義は

```math
u \lhd_k v \quad\iff\quad L_u \prec^*_{k+2} L_v
\quad\iff\quad L_u \text{ と } L_v \text{ で } \hat\Sigma_j \text{ 式の真理値が一致する}
```

なので、$`L_u`$ と $`L_v`$ の**両方の真理**を、文を書く場所である $`L_\beta`$ の中で
表現することになる。ここで相手 $`v`$ には 2 通りある。

| 相手 $`v`$ | $`L_v`$ は $`L_\beta`$ の中で | $`L_v`$ の中の真理の表し方 |
|---|---|---|
| $`L_\beta`$ の中にある順序数 | **集合である** | KP ノート §7 の $`\mathrm{SatCode}`$ で表せる |
| $`\beta`$ 自身 | **集合でない** | $`\mathrm{SatCode}`$ では表せない |

構成可能階層のノート §9 の $`L_\beta \cap \mathrm{Ord} = \beta`$ から $`\beta \notin L_\beta`$、
従って $`L_\beta \notin L_\beta`$ である。自分自身は自分の中で集合になれない。
**相手が「いま居る宇宙自身」のときだけ、$`\mathrm{SatCode}`$ では表せない。**

そういう形の条件がなぜ要るのかは、有限行反映のノート 3.3 で見る。定理 17.1 で
$`\beta`$ が $`\alpha`$ に取り替わるのは、まさにこの形の条件だからである。

**このノートは、その表せない側を表す方法を作る.** すなわち

> いま自分がいる宇宙で $`\varphi_e[a]`$ が真である

を言うものを用意する。素直な方法が 2 つあるが、どちらも使えない。

| 方法 | 結果 | どこで見るか |
|---|---|---|
| 集合として持つ（$`\mathrm{SatCode}`$ と同じやり方） | 使えない。宇宙が集合でないから | 1.2 |
| 論理式 1 本で書く | 使えない。タルスキの真理定義不可能性による | 1.3 |
| 交代数 $`q`$ ごとに別の論理式を作る | これを採る | 1.4 |

1.2 と 1.3 は別々の方法を否定しており、一方が他方の補強ではない。
両方が使えないことから 1.4 の形に決まる。

### 1.2 SatCode で足りない理由

KP と許容順序数のノート §7 で、集合 $`A`$ に対する充足を集合 $`T`$ として持てた。

```math
\langle e, a \rangle \in T \quad\iff\quad (A, \in) \models \varphi_e[a]
```

これができたのは、$`A`$ が集合で、その上の充足の再帰を有限の対の集まりとして
書き下せたからである。宇宙は集合ではないので、同じ手が使えない。

### 1.3 タルスキの真理定義不可能性

1 本の論理式では書けない。仮に、全ての式コード $`e`$ と割り当て $`a`$ について

```math
\mathrm{Tr}(e, a) \quad\iff\quad \varphi_e[a] \text{ が真}
```

となる論理式 $`\mathrm{Tr}`$ が 1 本あったとする。すると対角化によって「自分は偽である」と
言う文が作れて矛盾する。嘘つきのパラドクスと同じ形である。

### 1.4 逃げ道：交代数で切る

全部まとめて 1 本にはできないが、**交代数を固定すれば書ける**。$`q`$ ごとに別の論理式

```math
\mathrm{Tr}_{\hat\Sigma_q}, \qquad \mathrm{Tr}_{\hat\Pi_q}
```

を作る。これが **部分** 真理述語である。矛盾しない理由は 3.3 で見る。

$`\hat\Sigma_q`$ と $`\hat\Pi_q`$ は、交代ブロックのノート 1.1（原文 定義 12.1）で定義した
厳密交代ブロック階層である。

### 1.5 3 種類の真理

| 何の真理か | 書き方 | どこ |
|---|---|---|
| 集合 $`A`$ の中の真理 | **集合** $`T`$（$`\mathrm{SatCode}`$） | KP ノート §7 |
| 宇宙全体の $`\Delta_0`$ の真理 | **論理式** $`\mathrm{Tr}^+_{\Delta_0}`$、$`\mathrm{Tr}^-_{\Delta_0}`$ | 原文 定義 13.2 |
| 宇宙全体の $`\hat\Sigma_q`$ の真理 | **論理式** $`\mathrm{Tr}_{\hat\Sigma_q}`$、$`\mathrm{Tr}_{\hat\Pi_q}`$ | 原文 定義 13.4 |

下 2 つは論理式であって集合ではない。ここが $`\mathrm{SatCode}`$ との違いである。

## 2. Δ₀ 真理の正表示と負表示

### 2.1 定義 13.2

$`\mathrm{Asn}_A(e,a)`$ を「$`a`$ は $`e`$ の自由変数を全部覆う $`A`$-値の割り当てである」という
$`\Delta_0`$ 述語とする（原文 (8.4)）。

**正表示.** $`\mathrm{Tr}^+_{\Delta_0}(e, a)`$ は、$`e`$ が $`\Delta_0`$ 式コードで、
**ある** $`A, U, T`$ が存在して

```math
A \text{ は推移的} \ \wedge\ \mathrm{Asn}_A(e,a) \ \wedge\ a \in U
\ \wedge\ \mathrm{SatCode}(A,U,T) \ \wedge\ \langle e,a \rangle \in T
```

となることとする。

**負表示.** $`\mathrm{Tr}^-_{\Delta_0}(e, a)`$ は、$`e`$ が $`\Delta_0`$ 式コードで、
**全ての** $`A, U, T`$ について

```math
\bigl(A \text{ は推移的} \wedge \mathrm{Asn}_A(e,a) \wedge a \in U \wedge \mathrm{SatCode}(A,U,T)\bigr)
\ \Longrightarrow\ \langle e,a \rangle \in T
```

となることとする。

**読み方.** どちらも「$`a`$ の値を全部含む推移的な $`A`$ を取って、そこでの真偽を見る」と
言っている。正表示は「そういう $`A`$ が 1 つでもあって真」、負表示は「そういう $`A`$ の全部で真」。

### 2.2 複雑度 (13.1)

**定義（行列）.** 2.1 の 2 つの述語から先頭の量化ブロックを取り除いた残りを、
その述語の **行列** と呼ぶ（交代ブロックのノート 1.1）。書き下すと次のとおりである。

$`\mathrm{Tr}^+_{\Delta_0}`$ の行列。

```math
A \text{ は推移的} \ \wedge\ \mathrm{Asn}_A(e,a) \ \wedge\ a \in U
\ \wedge\ \mathrm{SatCode}(A,U,T) \ \wedge\ \langle e,a \rangle \in T
```

$`\mathrm{Tr}^-_{\Delta_0}`$ の行列。

```math
\bigl(A \text{ は推移的} \wedge \mathrm{Asn}_A(e,a) \wedge a \in U \wedge \mathrm{SatCode}(A,U,T)\bigr)
\ \to\ \langle e,a \rangle \in T
```

正表示は連言、負表示は含意である。先頭にある「$`e`$ は $`\Delta_0`$ 式コードである」は
量化ブロックの外側にあるので、行列には入らない。

**行列は $`\Delta_0`$ である.** 部品を 1 つずつ見る。

| 部品 | なぜ $`\Delta_0`$ か |
|---|---|
| 「$`A`$ は推移的」 | $`\forall y \in A\ \forall z \in y\ (z \in A)`$。レヴィ階層のノート 2.2 |
| $`\mathrm{Asn}_A(e,a)`$ | 原文 (8.4)。量化が $`\omega, a, A`$ に有界 |
| $`a \in U`$ | 原子式 |
| $`\mathrm{SatCode}(A,U,T)`$ | 原文 式 (8.5) |
| $`\langle e,a \rangle \in T`$ | 順序対と $`\in`$。KP ノート 8.2 |

$`\Delta_0`$ は $`\wedge`$ と $`\to`$ で閉じている（レヴィ階層のノート 2.1）ので、
どちらの行列も $`\Delta_0`$ である。先頭の「$`e`$ は $`\Delta_0`$ 式コードである」も
$`\Delta_0`$ である（KP ノート 7.2 の末尾）。従って

```math
\mathrm{Tr}^+_{\Delta_0} \in \hat\Sigma_1, \qquad
\mathrm{Tr}^-_{\Delta_0} \in \hat\Pi_1 .
```

正表示は $`\exists A\, \exists U\, \exists T`$ が 1 ブロック、負表示は
$`\forall A\, \forall U\, \forall T`$ が 1 ブロックである。

### 2.3 例

KP と許容順序数のノート §7.4 の計算がそのまま使える。

$`e = \ulcorner v_0 \in v_1 \urcorner = 8`$、$`a = (\emptyset, \{\emptyset\})`$ とする。
$`A = L_2`$ を取ると

- $`L_2`$ は推移的である
- $`a`$ の値 $`\emptyset`$ と $`\{\emptyset\}`$ は $`L_2`$ の元である
- §7.4 の表の 2 行目から $`\langle 8, (\emptyset,\{\emptyset\}) \rangle \in T`$

よって $`\mathrm{Tr}^+_{\Delta_0}(8, (\emptyset,\{\emptyset\}))`$ が成り立つ。

$`A`$ を $`L_3`$ に取り替えても $`L_\omega`$ に取り替えても答えは変わらない。
$`v_0 \in v_1`$ は $`\Delta_0`$ で、$`\Delta_0`$ の真偽は推移的集合の中と外で一致するからである
（レヴィ階層のノート §3）。正表示と負表示が一致するのも同じ理由による。

### 2.4 補題 13.3（正しさ）

$`\theta`$ を許容順序数とし $`W = L_\theta`$ とする。$`e, a \in W`$ で、$`e`$ が $`\Delta_0`$ 式
$`\delta`$ を符号化し、$`a`$ が適切な割り当てなら

```math
W \models \mathrm{Tr}^+_{\Delta_0}(e, a)
\ \iff\ W \models \mathrm{Tr}^-_{\Delta_0}(e, a)
\ \iff\ W \models \delta[a] . \tag{13.2}
```

同じ同値は外部宇宙 $`V`$ でも成立する。

**証明の筋（原文）.**

1. $`W`$ の中で、$`a`$ の値を全部含む $`A = L_\rho`$ を取る。$`\rho`$ は
   $`\omega + 1 \lt \rho \lt \theta`$ かつ $`\rho + 1 \lt \theta`$ を満たすものとする。
   このとき $`A \in L_{\rho+1} \subseteq W`$
2. $`W \models \mathrm{KP}`$ なので、補題 10.5(1) を $`W`$ の中で $`A`$ に適用し、
   $`U, T \in W`$ で $`\mathrm{SatCode}(A,U,T)`$ となるものを取る
3. $`\mathrm{SatCode}`$ は $`\Delta_0`$ で $`W`$ は推移的だから、外でも $`\mathrm{SatCode}(A,U,T)`$
4. 補題 8.4 から $`\langle e,a \rangle \in T \iff (A,\in) \models \delta[a]`$
5. $`A \subseteq W`$ はどちらも推移的で $`\delta`$ は $`\Delta_0`$ だから
   $`(A,\in) \models \delta[a] \iff W \models \delta[a]`$

3 から 5 で正表示の同値を得る。負表示は、$`W \not\models \delta[a]`$ のときに 1 で作った
$`A, U, T`$ が全称条件の反例になることによる。$`\square`$

### 2.5 なぜ 2 つ要るのか

$`\hat\Sigma`$ 側と $`\hat\Pi`$ 側で別々の土台が要るからである。§3 で見るとおり

```math
\mathrm{Tr}_{\hat\Sigma_1} \text{ は } \mathrm{Tr}^+_{\Delta_0}\ (\hat\Sigma_1) \text{ の上に } \exists \text{ ブロックを重ねる}
```
```math
\mathrm{Tr}_{\hat\Pi_1} \text{ は } \mathrm{Tr}^-_{\Delta_0}\ (\hat\Pi_1) \text{ の上に } \forall \text{ ブロックを重ねる}
```

同じ極性が重なるので、どちらもブロックが 1 つのまま済む。正表示だけで $`\hat\Pi`$ 側を作ると
$`\forall`$ の内側に $`\exists`$ が来て交代数が 1 増え、3.3 の複雑度が壊れる。

## 3. 高い交代数

### 3.1 ブロック同時更新

**定義（原文 §12）.** 有限割り当て $`a`$、相異なる変数番号の有限列 $`\nu`$、
同じ長さの値列 $`t`$ に対し、$`\mathrm{BlkUpd}(a, \nu, t, b)`$ を次で定める。
$`m`$ を $`\mathrm{dom}(a)`$ と $`\{\nu(i) + 1 : i \in \mathrm{dom}(\nu)\}`$ の最大値とし、
$`\mathrm{dom}(b) = m`$ で

```math
b(j) = \begin{cases}
t(i) & \nu(i) = j \text{ となる } i \text{ があるとき} \cr
a(j) & j \in \mathrm{dom}(a) \text{ で上の場合でないとき} \cr
\emptyset & \text{それ以外}
\end{cases}
```

とする。「$`a`$ の $`\nu(i)`$ 番目の変数を $`t(i)`$ に置き換えたものが $`b`$ である」というような意味である。

**一意性.** $`\nu`$ の値は相異なるので、第 1 の場合の $`i`$ は高々 1 つであり、
$`b`$ は一意に定まる。$`\nu`$ の値が相異なることは交代ブロックのノート 1.1 の条件 2 である。

**複雑度.** 量化は $`a, \nu, t, b, \omega`$ とそれらの有限回の合併に有界化できるので、
$`\mathrm{BlkUpd}`$ は $`\Delta_0`$ である。

$`t`$ が $`\nu`$ と同じ長さの有限列でない場合、$`\mathrm{BlkUpd}`$ は偽とする。

### 3.2 定義 13.4

**ここで定義する記号.** 論理式 $`\mathrm{Tr}_{\hat\Sigma_q}(e,a)`$ と
$`\mathrm{Tr}_{\hat\Pi_q}(e,a)`$ の 2 つである。$`q \ge 1`$ ごとに 1 組ずつ作る。

**すでにある記号.**

| 記号 | 何か | どこ |
|---|---|---|
| $`\mathrm{Tr}^+_{\Delta_0}(e,a)`$、$`\mathrm{Tr}^-_{\Delta_0}(e,a)`$ | $`\Delta_0`$ 真理の正表示と負表示 | 2.1 |
| $`\mathrm{BlkUpd}(a,\nu,t,b)`$ | ブロック同時更新 | 3.1 |
| $`\mathrm{Vars}(e)`$ | $`e`$ が表す式の、最外ブロックの変数番号列 | 原文 §12 |
| $`\mathrm{Body}(e)`$ | $`e`$ が表す式から、最外ブロックを除いた本体のコード | 原文 §12 |
| $`\mathrm{Form}_{\hat\Sigma_q}(e)`$、$`\mathrm{Form}_{\hat\Pi_q}(e)`$ | 「$`e`$ は $`\hat\Sigma_q`$（$`\hat\Pi_q`$）式のコードである」。$`\Delta_0`$ | 原文 §12 |

以下 $`\nu = \mathrm{Vars}(e)`$、$`d = \mathrm{Body}(e)`$ と置く。

**定義.** $`\mathrm{Tr}_{\hat\Sigma_q}`$ と $`\mathrm{Tr}_{\hat\Pi_q}`$ を、下記を満たす論理式として
$`q`$ に関する再帰で定義する。

$`q = 1`$ について

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

$`q \ge 1`$ について

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

**読み方.** 右辺は、最外ブロックを 1 つ取り除いた本体 $`d`$ について、1 段低い真理述語を
呼んでいる。ブロックに与える値の列が $`t`$ で、$`\mathrm{BlkUpd}`$ がそれを割り当て $`a`$ に
書き込んで $`b`$ を作る。$`\hat\Sigma`$ の定義に $`\hat\Pi`$ が、$`\hat\Pi`$ の定義に
$`\hat\Sigma`$ が現れるので、2 つは同時に定義される。

### 3.3 補題 13.5（複雑度）

全ての $`q \ge 1`$ について

```math
\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q, \qquad
\mathrm{Tr}_{\hat\Pi_q} \in \hat\Pi_q . \tag{13.5}
```

**証明の筋.** $`q = 1`$ では、$`\mathrm{BlkUpd}`$ は $`\Delta_0`$、$`\mathrm{Tr}^+_{\Delta_0}`$ は
存在ブロックを 1 つ持つ（2.2）。$`t, b`$ をその存在ブロックへ併合すれば全体が 1 ブロックになり
$`\hat\Sigma_1`$ である。負表示側は $`\forall t \forall b`$ と $`\mathrm{Tr}^-_{\Delta_0}`$ の
全称ブロックを併合して $`\hat\Pi_1`$。

$`q`$ から $`q+1`$ へは、$`\mathrm{Tr}_{\hat\Sigma_{q+1}}`$ が新しい存在ブロック
$`\exists t \exists b`$ の内側に $`\hat\Pi_q`$ 式を置いた形なので $`\hat\Sigma_{q+1}`$ である。
双対も同じ。$`\mathrm{Vars}`$、$`\mathrm{Body}`$ は $`\Delta_0`$ 定義可能な関数記号、
$`\mathrm{Form}`$ と $`\mathrm{BlkUpd}`$ は $`\Delta_0`$ なので、交代数を増やさない。$`\square`$

**ここが 1.2 の矛盾を避けている場所である.** $`\hat\Sigma_q`$ の真理を語る述語が
$`\hat\Sigma_q`$ に留まるので、対角化で作れる文も $`\hat\Sigma_q`$ に留まる。
その否定は $`\hat\Pi_q`$ になり、$`\mathrm{Tr}_{\hat\Sigma_q}`$ の守備範囲の外へ出る。
だから嘘つきの文が閉じない。1 本にまとめようとすると、この階段が消えて矛盾する。

### 3.4 定理 13.6（正しさ）

$`\theta`$ を許容順序数とし $`W = L_\theta`$ とする。$`q \ge 1`$、$`e, a \in W`$ で、
$`e`$ が $`\hat\Sigma_q`$ 式 $`\varphi`$ または $`\hat\Pi_q`$ 式 $`\psi`$ を符号化し、
$`a`$ が適切な割り当てなら

```math
W \models \mathrm{Tr}_{\hat\Sigma_q}(e,a) \iff W \models \varphi[a], \qquad
W \models \mathrm{Tr}_{\hat\Pi_q}(e,a) \iff W \models \psi[a] .
```

同じ同値は外部宇宙 $`V`$ でも成立する。

**証明の筋.** $`q`$ に関する $`\hat\Sigma`$ と $`\hat\Pi`$ の同時帰納法である。
$`q = 1`$ の基底が補題 13.3。帰納段では、最外ブロックへ値の列 $`t`$ を与える操作が
通常の意味論と一致することを見る。$`W \models \mathrm{KP}`$ は Pairing と Union を持つので、
有限個の $`W`$ の元からなる値列 $`t`$ と更新後の割り当て $`b`$ が $`W`$ の元として存在する。
$`\square`$

## 4. 有限段 Tarski–Vaught

### 4.1 相対化

固定した論理式 $`\mathrm{Tr}_{\hat\Sigma_j}`$ の全ての非有界量化を $`M`$ に制限したものを
$`\mathrm{Tr}^M_{\hat\Sigma_j}(e,a)`$ と書く。量化子が全部 $`M`$ で抑えられるので、
これは $`M`$ をパラメータとする $`\Delta_0`$ 論理式である。

意味の差はここにある。

```
Tr_{Σ̂j}(e,a)     いま居る宇宙で φ_e[a] が真
Tr^M_{Σ̂j}(e,a)   M の中で φ_e[a] が真
```

### 4.2 定義 14.2

$`q \ge 1`$ に対し、$`\mathrm{TV}_q(M)`$ を次の有限連言の、補題 12.2 による 1 つの標準
$`\hat\Pi_q`$ 表示とする。

```math
\bigwedge_{1 \le j \le q}
\forall e \in \omega\ \forall a \in M\
\bigl(\mathrm{Form}_{\hat\Sigma_j}(e) \wedge \mathrm{Asn}_M(e,a)
\wedge \mathrm{Tr}_{\hat\Sigma_j}(e,a) \ \to\ \mathrm{Tr}^M_{\hat\Sigma_j}(e,a)\bigr)
\tag{14.1}
```

**読み方.** 「$`M`$ のパラメータで書いた $`\hat\Sigma_j`$ 式が宇宙で真なら、$`M`$ の中でも真」を
$`j = 1, \dots, q`$ について集めたものである。これが Tarski–Vaught テストを交代数 $`q`$ で
切ったものにあたる。

### 4.3 補題 14.3（複雑度）

```math
\mathrm{TV}_q \in \hat\Pi_q .
```

**証明の筋.** 固定した $`j`$ の含意は、$`\neg \mathrm{Tr}_{\hat\Sigma_j}`$ という $`\hat\Pi_j`$ 式と
$`\Delta_0`$ 式の選言なので $`\hat\Pi_j`$ にまとまる。外側の $`\forall e \in \omega`$、
$`\forall a \in M`$ は有界全称量化で、既存の先頭全称ブロックへ併合するだけなので交代数を増やさない。
padding で各項を $`\hat\Pi_q`$ へ上げ、有限連言を 1 つにまとめる
（交代ブロックのノート 1.5 の 3 と 4）。$`\square`$

### 4.4 定理 14.4（有限段 Tarski–Vaught）

$`\xi \lt \theta`$ がともに許容順序数なら

```math
L_\theta \models \mathrm{TV}_q(L_\xi) \quad\iff\quad L_\xi \prec^*_q L_\theta . \tag{14.2}
```

**証明の筋.** まず定理 13.6 と相対化の定義から、$`L_\theta`$ 内の (14.1) は次を意味する。
$`e`$ が $`\hat\Sigma_j`$ 式、$`a`$ が $`L_\xi`$-値の割り当てであるとき

```math
L_\theta \models \varphi_e[a] \ \Longrightarrow\ L_\xi \models \varphi_e[a] . \tag{14.3}
```

$`L_\xi \prec^*_q L_\theta`$ を仮定すれば (14.3) は明らかなので、$`L_\theta \models \mathrm{TV}_q(L_\xi)`$
を得る。

逆に $`L_\theta \models \mathrm{TV}_q(L_\xi)`$ を仮定する。$`j = 0, 1, \dots, q`$ に関する
帰納法で、$`\hat\Sigma_j`$ と $`\hat\Pi_j`$ の全式が両構造で同じ真理値を持つことを同時に示す。

- $`j = 0`$ は $`\Delta_0`$ 絶対性である
- $`j \ge 1`$ で $`\hat\Sigma_j`$ 式を $`\exists \vec x\ \psi(\vec x, \bar a)`$
  （$`\psi \in \hat\Pi_{j-1}`$、$`\bar a \in L_\xi`$）とする。$`L_\theta`$ で真なら (14.3) により
  $`L_\xi`$ で真。逆に $`L_\xi`$ で真なら、証人 $`\bar b \in L_\xi`$ があって
  $`L_\xi \models \psi(\bar b, \bar a)`$。帰納法の仮定から $`L_\theta \models \psi(\bar b, \bar a)`$ で、
  従って元の式も $`L_\theta`$ で真
- $`\hat\Pi_j`$ 式 $`\chi`$ は、双対化（交代ブロックのノート 1.5 の 2）で $`\neg\chi`$ と同値な
  $`\hat\Sigma_j`$ 式 $`\chi^\perp`$ を作り、既に示した $`\hat\Sigma_j`$ の一致を適用する

$`\square`$

### 4.5 何が嬉しいのか

$`\prec^*_q`$ は外側から見た関係だった（交代ブロックのノート §2）。定理 14.4 はそれを
**$`L_\theta`$ の中で書ける述語に置き換える**。

```
外から見た関係    L_ξ ≺*_q L_θ
中で書ける述語    L_θ ⊨ TV_q(L_ξ)
```

これで $`\lhd_k`$ を $`L_\theta`$ の内部で語れる。原文 §15 の $`\mathrm{St}_k`$ がその形である。

```math
\mathrm{St}_k(\xi) \ :\iff\ \forall M\, \forall c\ \bigl(\mathrm{LCode}(\xi,M,c) \to \mathrm{TV}_{k+2}(M)\bigr)
\tag{15.2}
```

補題 9.2 により $`\mathrm{LCode}`$ の $`M`$ は $`L_\xi`$ しかないので、$`\mathrm{St}_k(\xi)`$ は
$`\mathrm{TV}_{k+2}(L_\xi)`$ と同値である。従って補題 15.3 の

```math
L_\theta \models \mathrm{St}_k(\xi) \quad\iff\quad \xi \lhd_k \theta
```

が定理 14.4 から出る。補題 14.3 から $`\mathrm{St}_k \in \hat\Pi_{k+2}`$ であり、
これが定理 17.1 の複雑度計算に入る部品である（交代ブロックのノート 3.3）。

## 5. 原文での使われ方

| 場所 | 使い方 |
|---|---|
| 定義 13.2 | $`\mathrm{Tr}^+_{\Delta_0}`$、$`\mathrm{Tr}^-_{\Delta_0}`$ |
| (13.1) | 正表示は $`\hat\Sigma_1`$、負表示は $`\hat\Pi_1`$ |
| 補題 13.3 | $`\Delta_0`$ 真理の正しさ。定理 13.6 の基底 |
| 定義 13.4 | $`\mathrm{Tr}_{\hat\Sigma_q}`$、$`\mathrm{Tr}_{\hat\Pi_q}`$ |
| 補題 13.5 | $`\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q`$ |
| 定理 13.6 | 部分真理述語の正しさ |
| 定義 14.2、補題 14.3 | $`\mathrm{TV}_q(M) \in \hat\Pi_q`$ |
| 定理 14.4 | $`L_\theta \models \mathrm{TV}_q(L_\xi) \iff L_\xi \prec^*_q L_\theta`$ |
| 定義 15.2、補題 15.3 | $`\mathrm{St}_k`$ とその正しさ |
| 定義 15.4、補題 15.5 | $`\mathrm{Rel}_k`$ とその正しさ |
| 定理 17.1 | 上の部品を組んだ $`\hat\Sigma_{n+2}`$ 文が、$`L_\beta`$ で真なら $`L_\alpha`$ でも真であることを使う |

## 6. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 定義 13.2 の行列 | `TrD0Mat` | `Bm4/SetTheory/Truth.lean` |
| $`\mathrm{Tr}^+_{\Delta_0}`$ | `TrD0P` | 同上 |
| $`\mathrm{Tr}^-_{\Delta_0}`$ | `TrD0N` | 同上 |
| (13.1) の $`\hat\Sigma_1`$ | `sigmaDef_trD0P` | 同上 |
| (13.1) の $`\hat\Pi_1`$ | `piDef_trD0N` | 同上 |
| 補題 13.3（$`L_\theta`$ の中） | `baseCorrect_L` | `Bm4/SetTheory/BaseOK.lean` |
| 補題 13.3（外部宇宙 $`V`$） | `baseCorrect_V` | 同上 |
| $`\mathrm{BlkUpd}`$ | `IsBlkUpdP` | `Bm4/SetTheory/BlkP.lean` |
| 定義 13.4 の $`\mathrm{Tr}_{\hat\Sigma_q}`$ | `TrSigP` | `Bm4/SetTheory/TrP.lean` |
| 定義 13.4 の $`\mathrm{Tr}_{\hat\Pi_q}`$ | `TrPiP` | 同上 |
| 定理 13.6 | `trSigQ_correct`、`trPiQ_correct` | `Bm4/SetTheory/StRelP.lean` |
| 定理 13.6（外部宇宙 $`V`$） | `trSigPiQ_correct_V` | `Bm4/SetTheory/TrPV.lean` |
| (14.1) の各項 | `TVBodyP` | `Bm4/SetTheory/StRelP.lean` |
| (14.1) の有限連言 | `TVConjP` | 同上 |
| $`\mathrm{TV}_q(M)`$ | `TVqP` | 同上 |
| 定理 14.4 の意味論版 | `elemHat_of_downward` | `Bm4/SetTheory/Elem.lean` |
| 定義 15.2 の $`\mathrm{St}_k`$ | `StKP` | `Bm4/SetTheory/StKP.lean` |
| 補題 15.3 の複雑度 | `piDef_StKP` | 同上 |
| 定義 15.4 の $`\mathrm{Rel}_k`$ | `RelKP` | 同上 |
| 補題 15.5 の複雑度 | `sigmaDef_RelKP` | 同上 |
