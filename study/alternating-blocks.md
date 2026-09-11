[← Back](README.md)

# 厳密交代ブロック階層と安定関係

前提

| ノート | ここから使う言葉 |
|---|---|
| [構成可能階層 L](constructible-hierarchy.md) | 論理式、構造 $`(X,\in)`$、割り当て $`\bar a`$、充足 $`\models`$、推移的、$`L_\xi`$ |
| [レヴィ階層と絶対性](levy-hierarchy.md) | 有界量化、**ブロック**、$`\Delta_0`$、$`\Delta_0`$ 絶対性、$`\Sigma_1`$、$`\Pi_1`$ |
| [KP と許容順序数](kp-admissible.md) | KP、**許容順序数**、$`\mathrm{SatCode}`$、$`\mathrm{LCode}`$ |

## 1. Σ̂q と Π̂q

### 1.1 定義

**定義（原文 定義 12.1）.** $`\hat\Sigma_0 = \hat\Pi_0 = \Delta_0`$ とする。$`q \ge 1`$ に対し

```math
\hat\Sigma_q : \ \exists \vec x_1\, \forall \vec x_2\, \exists \vec x_3 \cdots Q_q \vec x_q\ \delta,
\qquad
\hat\Pi_q : \ \forall \vec x_1\, \exists \vec x_2\, \forall \vec x_3 \cdots Q_q \vec x_q\ \delta
```

の形の論理式をそれぞれ $`\hat\Sigma_q`$、$`\hat\Pi_q`$ と呼ぶ。ここで $`\delta \in \Delta_0`$ であり、
$`\vec x_i`$ は非有界量化のブロック（レヴィ階層のノート §4.1）で、次の 4 条件を満たす。

1. 各 $`\vec x_i`$ は空でない
2. 1 つのブロック内の変数は相異なる
3. 隣接するブロックの極性は逆である
4. 自由変数はブロック内の束縛変数と衝突しない

先頭のブロックを全部取り除いた残りの $`\delta`$ を、この式の **行列** と呼ぶ。
原文の第 I 部が扱う BM4 の対象は「配列」と呼ばれており、この「行列」とは別物である。

### 1.2 4 条件の意味

**3 が「厳密」の中身である.** 同じ極性が隣り合うと、それは 1 つのブロックにまとまる。

```math
\exists \vec x_1\, \exists \vec x_2\, \forall \vec x_3\ \delta
\quad\text{は}\quad
\exists (\vec x_1, \vec x_2)\, \forall \vec x_3\ \delta
```

と書き直せて $`\hat\Sigma_2`$ である。3 を課すと、$`q`$ は「極性が切り替わった回数 $`+\, 1`$」に
一致する。

**1 は $`q`$ を意味あるものにする.** 空のブロックを許すと、たとえば

```math
\exists ()\, \forall x\ \delta
```

が見かけ上 2 ブロックになるが、中身は $`\forall x\ \delta`$ で $`\hat\Pi_1`$ である。
1 はこれを禁じる。

**2 は代入を一意にする.** 原文 §12 のブロック同時更新 $`\mathrm{BlkUpd}(a, \nu, t, b)`$ は、
変数番号の列 $`\nu`$ の位置を値の列 $`t`$ で一斉に書き換える操作である。$`\nu`$ に同じ番号が
2 回現れると、どちらの値を割り当てるかが決まらない。原文が「$`\nu`$ の値は相異なるので一意である」と
書くのはこの条件による。

**4 は代入で変数が捕まらないようにする.** 自由変数 $`y`$ をブロックが $`\forall y`$ で
束縛していると、$`y`$ に値を割り当てる操作が意味を変えてしまう。

### 1.3 例

| 論理式 | クラス |
|---|---|
| $`x \in y`$ | $`\Delta_0 = \hat\Sigma_0 = \hat\Pi_0`$ |
| $`x \subseteq y`$、すなわち $`\forall z \in x\,(z \in y)`$ | $`\Delta_0`$ |
| $`\exists z\,(x \in z)`$ | $`\hat\Sigma_1`$ |
| $`\forall w\,(w \subseteq x \to w \in z)`$ | $`\hat\Pi_1`$ |
| $`\exists u_1\,\exists u_2\,\forall v\ \delta`$ | $`\hat\Sigma_2`$（$`\exists`$ が 1 ブロック） |
| $`\forall v\,\exists u\ \delta`$ | $`\hat\Pi_2`$ |
| $`\mathrm{Adm}(\eta)`$（原文 定義 11.1） | $`\hat\Sigma_1`$ |

最後の行は、KP と許容順序数のノート §8 で見たとおり、$`\mathrm{Adm}(\eta)`$ が
$`\Delta_0`$ 述語 3 つの連言に $`\exists M, c, U, S`$ を 1 ブロック付けた形だからである。

### 1.4 レヴィ階層との違い

$`q = 1`$ では一致する。

```math
\hat\Sigma_1 = \Sigma_1, \qquad \hat\Pi_1 = \Pi_1
```

$`q \ge 2`$ では違う。レヴィの $`\Sigma_2`$ は「非有界量化の交代が 2 段」というだけで、
有界量化がどこに混ざっていてもよい。$`\hat\Sigma_2`$ は
$`\exists \vec x\, \forall \vec y\ \delta`$（$`\delta \in \Delta_0`$）という前置形に限る。

前置形に直す変形が要るわけだが、それができない場合がある。原文 備考 12.3 の例は

```math
\forall u \in a\ \exists x\ \delta(u,x)
```

である。$`\forall u \in a`$ を非有界 $`\exists x`$ の外側へ出して $`\Sigma_1`$ 前置形にするには

```math
\exists b\ \forall u \in a\ \exists x \in b\ \delta(u,x)
```

との同値が要るが、これは Collection である（KP と許容順序数のノート §2）。
Collection を仮定しないと、この書き直しができない。

原文はこの変形を避け、最初から交代ブロック形の式だけを扱う。真理述語（§13）も
反射に使う文（§17）も、この移動が要らない形で作る。

### 1.5 安全な構文操作（原文 補題 12.2）

次の操作は、固定した符号化のもとでグラフが $`\Delta_0`$ である。

1. 変数改名、代入、束縛変数の衝突回避、相対化、交代ブロックの付加
2. $`\hat\Sigma_q`$ と $`\hat\Pi_q`$ の双対化
3. **padding**。$`j \le q`$ なら $`\hat\Sigma_j`$ 式を同値な $`\hat\Sigma_q`$ 式へ、
   $`\hat\Pi_j`$ 式を同値な $`\hat\Pi_q`$ 式へ移す
4. 同じ交代型の有限個の式の連言または選言を、同じ交代型の 1 式へまとめる

**padding の仕組み.** 式に現れない変数を量化する空回りのブロックを、最内側に必要な数だけ付ける。
非空な構造では、変数 $`z`$ が $`\varphi`$ に現れなければ

```math
\exists z\ \varphi \leftrightarrow \varphi, \qquad \forall z\ \varphi \leftrightarrow \varphi
```

なので意味が変わらない。

**有限結合の仕組み.** 2 式の束縛変数を互いに素に改名したうえで、同じ極性列
$`Q_1, \dots, Q_q`$ を持つ 2 式

```math
Q_1 \vec x_1 \cdots Q_q \vec x_q\ \delta, \qquad
Q_1 \vec u_1 \cdots Q_q \vec u_q\ \varepsilon
```

に対し、$`\star \in \{\wedge, \vee\}`$ について

```math
Q_1 (\vec x_1, \vec u_1) \cdots Q_q (\vec x_q, \vec u_q)\ (\delta \star \varepsilon)
```

を取る。同じ極性の 2 つのブロックを、互いに独立な変数について 1 つにまとめるだけである。

3 と 4 は §3.3 の複雑度計算で使う。

## 2. ≺*q

### 2.1 定義

**定義（原文 定義 14.1）.** 推移的な集合 $`M \subseteq N`$ と $`q \ge 1`$ に対し

```math
M \prec^*_q N \quad :\iff\quad
\begin{aligned}
&\text{全ての } j\ (1 \le j \le q)\text{、全ての } \hat\Sigma_j \text{ 式と } \hat\Pi_j \text{ 式 } \varphi\text{、} \cr
&\text{全ての } M \text{ の元からなる割り当て } \bar a \text{ について } \cr
&(M,\in) \models \varphi[\bar a] \iff (N,\in) \models \varphi[\bar a]
\end{aligned}
```

**意味.** 普通の初等部分 $`M \prec N`$ は、全ての論理式で真理値が一致することをいう。
$`\prec^*_q`$ はそれを交代数 $`q`$ で頭打ちにしたものである。$`q`$ が大きいほど強い条件になる。

### 2.2 Δ₀ の段は自動

定義は $`1 \le j`$ なので、$`j = 0`$、すなわち $`\Delta_0`$ の一致を要求していない。
しかし $`M`$ と $`N`$ が推移的で $`M \subseteq N`$ なら、$`\Delta_0`$ の一致は
レヴィ階層のノート §3 から自動で従う。だから実際には $`0 \le j \le q`$ の全部で一致する。

### 2.3 ≺*₁ が成り立たない例

$`\psi(x) \equiv \exists z\,(x \in z)`$ を取る。1.3 のとおり $`\hat\Sigma_1`$ である。

$`M = L_2 = \{\emptyset, \{\emptyset\}\}`$、$`N = L_3`$ とする。どちらも推移的で
$`L_2 \subseteq L_3`$ である。割り当てを $`\bar a(x) = \{\emptyset\}`$ と取る。

充足の定義（構成可能階層のノート §2）の $`\exists`$ の行から、推移的な集合 $`W`$ について

```math
(W, \in) \models \psi[\bar a]
\quad\iff\quad
\text{ある } c \in W \text{ について } \bar a(x) \in c
```

である。つまり「$`\{\emptyset\}`$ を元に持つ集合が $`W`$ の中にあるか」を問うている。
これを $`W = L_2`$ と $`W = L_3`$ で計算する。

**$`W = L_2`$ のとき:** 候補 $`c`$ は $`\emptyset`$ と $`\{\emptyset\}`$ の 2 つである。
$`\{\emptyset\} \in \emptyset`$ も $`\{\emptyset\} \in \{\emptyset\}`$ も成立しない。従って

```math
(L_2, \in) \models \psi[\bar a] \quad \text{は偽}
```

**$`W = L_3`$ のとき:** $`L_3 = \{\emptyset, \{\emptyset\}, \{\{\emptyset\}\}, \{\emptyset,\{\emptyset\}\}\}`$ で、
$`c = \{\{\emptyset\}\}`$ が $`\{\emptyset\} \in \{\{\emptyset\}\}`$ を満たす。従って

```math
(L_3, \in) \models \psi[\bar a] \quad \text{は真}
```

$`\psi`$ は $`\hat\Sigma_1`$ で、$`\bar a`$ の値は $`L_2`$ の元であり、真理値が食い違った。
従って $`j = 1`$ で 2.1 の条件が破れるので

```math
L_2 \not\prec^*_1 L_3 .
```

### 2.4 q について単調、そして推移的

**単調性.** $`1 \le h \le k`$ かつ $`M \prec^*_k N`$ なら $`M \prec^*_h N`$。
要求する範囲 $`1 \le j \le h`$ が $`1 \le j \le k`$ の部分だからである。

**推移性.** $`M \prec^*_q N`$ かつ $`N \prec^*_q P`$ なら $`M \prec^*_q P`$。
$`M \subseteq N \subseteq P`$ なので、$`j`$ と $`\bar a`$ を固定して 2 つの仮定を順に適用すれば

```math
(M,\in) \models \varphi[\bar a] \iff (N,\in) \models \varphi[\bar a] \iff (P,\in) \models \varphi[\bar a]
```

を得る。

## 3. ◁k

### 3.1 定義

**定義（原文 式 (15.1)）.** 許容順序数 $`\alpha \lt \beta`$ と $`k \in \mathbb{N}`$ に対し

```math
\alpha \lhd_k \beta \quad :\iff\quad L_\alpha \prec^*_{k+2} L_\beta .
```

**意味.** $`L_\alpha`$ と $`L_\beta`$ が、交代数 $`k+2`$ 以下の式について、
$`L_\alpha`$ のパラメータ込みで同じ真偽を返す、ということである。

### 3.2 補題 15.1

**(1) 単調性.** $`h \lt k`$ かつ $`\alpha \lhd_k \beta`$ なら $`\alpha \lhd_h \beta`$。

**証明.** $`\alpha \lhd_k \beta`$ は $`L_\alpha \prec^*_{k+2} L_\beta`$ である。
$`h \lt k`$ なら $`h+2 \lt k+2`$ なので、2.4 の単調性から $`L_\alpha \prec^*_{h+2} L_\beta`$、
すなわち $`\alpha \lhd_h \beta`$。$`\square`$

**(2) 推移性.** $`\alpha \lhd_k \beta`$ かつ $`\beta \lhd_k \gamma`$ なら $`\alpha \lhd_k \gamma`$。

**証明.** 2.4 の推移性を $`q = k+2`$ で使う。$`\square`$

### 3.3 なぜ +2 か

定理 17.1 の証明で $`L_\beta`$ に書く文が、ちょうど $`\hat\Sigma_{n+2}`$ になるからである。
先取りになるが内訳を書く。使う述語は 3 種類ある。

| 述語 | 役割 | 複雑度 |
|---|---|---|
| $`\mathrm{Adm}(\eta)`$（定義 11.1） | $`\eta`$ は許容順序数である | $`\hat\Sigma_1`$ |
| $`\mathrm{Rel}_k(\xi,\eta)`$（定義 15.4） | $`\xi \lhd_k \eta`$ の内部表示 | $`\hat\Sigma_1`$ |
| $`\mathrm{St}_m(\xi)`$（定義 15.2） | $`\xi \lhd_m`$「いま居る宇宙」の内部表示 | $`\hat\Pi_{m+2}`$ |

行数の上限を $`n`$ とすると、使うのは $`m \lt n`$ の $`\mathrm{St}_m`$ だけなので
$`\hat\Pi_{m+2} \le \hat\Pi_{n+1}`$ である。

$`\hat\Sigma_1`$ の式 $`\exists \vec z\ \delta`$ は、非空な構造で

```math
\forall w\ \exists \vec z\ (w = w \wedge \delta)
```

と同値なので $`\hat\Pi_2`$ とみなせ、1.5 の padding で $`\hat\Pi_{n+1}`$ へ上げられる。

1.5 の有限結合で全部を 1 つの $`\hat\Pi_{n+1}`$ 式 $`\Phi(\vec u)`$ にまとめ、
外側に $`\exists u_0 \cdots \exists u_{s-1}`$ を 1 ブロック付けると

```math
\exists \vec u\ \Phi(\vec u) \ \in\ \hat\Sigma_{n+2}
```

となる。この文が $`L_\beta`$ で真であることから $`L_\alpha`$ でも真であることを導くのに
必要な仮定が、まさに
$`L_\alpha \prec^*_{n+2} L_\beta`$、すなわち $`\alpha \lhd_n \beta`$ である。

$`+2`$ の $`2`$ は、$`\hat\Pi_{n+1}`$ へ上げるぶんの $`1`$ と、外側の $`\exists`$ ブロックの
$`1`$ である。

### 3.4 完全初等部分との関係

原文 補題 16.2 は、許容順序数の対 $`\Lambda \lt \Theta`$ で

```math
L_\Lambda \prec L_\Theta
```

（交代数の制限なしの初等部分）となるものを作る。制限が無いので、全ての $`k`$ について

```math
\Lambda \lhd_k \Theta \tag{16.2}
```

が成り立つ。これが安定ラベルの出発点になる（補題 20.1）。

## 4. 原文での使われ方

| 場所 | 使い方 |
|---|---|
| 定義 12.1 | $`\hat\Sigma_q`$、$`\hat\Pi_q`$ |
| 補題 12.2 | 安全な構文操作。padding と有限結合 |
| 定義 13.4 | 部分真理述語 $`\mathrm{Tr}_{\hat\Sigma_q}`$、$`\mathrm{Tr}_{\hat\Pi_q}`$ |
| 補題 13.5 | $`\mathrm{Tr}_{\hat\Sigma_q} \in \hat\Sigma_q`$、$`\mathrm{Tr}_{\hat\Pi_q} \in \hat\Pi_q`$ |
| 定義 14.1 | $`\prec^*_q`$ |
| 定義 14.2、補題 14.3 | Tarski–Vaught 公式 $`\mathrm{TV}_q(M) \in \hat\Pi_q`$ |
| 定理 14.4 | $`L_\theta \models \mathrm{TV}_q(L_\xi) \iff L_\xi \prec^*_q L_\theta`$ |
| 式 (15.1) | $`\lhd_k`$ |
| 補題 15.1 | 単調性と推移性 |
| 定理 17.1 | 有限行反映。3.3 の複雑度計算を使う |
| 定義 18.1 | 安定ラベル。$`i \prec_k j`$ なら $`f(i) \lhd_k f(j)`$ |

## 5. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| $`\hat\Sigma_q`$ | `IsSigma q φ` | `Bm4/SetTheory/Fm.lean` |
| $`\hat\Pi_q`$ | `IsPi q φ` | 同上 |
| 1.1 の条件 1（ブロックが空でない） | `IsSigma.succ` の `hl : l ≠ []` | 同上 |
| 1.1 の条件 2（変数が相異なる） | `IsSigma.succ` の `hnd : l.Nodup` | 同上 |
| ブロック式と双対化 | `BF`、`BF.dual`、`sat_dual` | `Bm4/SetTheory/BF.lean` |
| padding | `BF.padSig`、`BF.padPi`、`Sig.padSig`、`Pi.padPi` | `Bm4/SetTheory/BFPad.lean` |
| $`M \prec^*_q N`$ | `ElemHat q M N` | `Bm4/SetTheory/Elem.lean` |
| 2.2（$`\Delta_0`$ の段が自動） | `ElemHat.delta0` | 同上 |
| $`j \le q`$ での一致 | `ElemHat.sigma`、`ElemHat.pi` | 同上 |
| 2.4 の単調性 | `ElemHat.mono` | 同上 |
| 2.4 の推移性 | `ElemHat.trans` | 同上 |
| 許容順序数の型 | `AdmOrd` | `Bm4/SetTheory/Stable.lean` |
| $`\alpha \lhd_k \beta`$ | `RelAdm k α β` | 同上 |
| 補題 15.1(1) | `relAdm_mono` | 同上 |
| 補題 15.1(2) | `relAdm_trans` | 同上 |
| 完全初等部分 | `ElemFull` | `Bm4/SetTheory/AdmTrans.lean` |
| (16.2) の初期対 | `exists_relAdm_all` | `Bm4/SetTheory/Stable.lean` |

形式化の $`\mathrm{RelAdm}`$ は $`\alpha \lt \beta`$ を連言に含む。原文の (15.1) は
$`\alpha \lt \beta`$ を前置きの仮定として置いているので、内容は同じである。
$`\mathrm{ElemHat}`$ も同様に、$`1 \le q`$、$`M`$ と $`N`$ の推移性、$`M \subseteq N`$ を
連言に含んでいる。
