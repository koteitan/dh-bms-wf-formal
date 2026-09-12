[← Back](README.md) | [English](en/03-kp-admissible.md) | [Japanese](03-kp-admissible.md)

# KP と許容順序数

前提

| ノート | ここから使う言葉 |
|---|---|
| [構成可能階層 L](01-constructible-hierarchy.md) | 論理式、構造 $`(X,\in)`$、割り当て $`\bar a`$、充足 $`\models`$、推移的、$`\mathrm{Def}`$、$`L_\xi`$ |
| [レヴィ階層と絶対性](02-levy-hierarchy.md) | 有界量化、$`\Delta_0`$、$`\Delta_0`$ 絶対性、$`\Sigma_1`$、$`\Pi_1`$ |

## 1. 文、公理系、モデル

**定義（文）.** 自由変数を持たない論理式を **文** と呼ぶ。

**意味.** 文は割り当てを渡さなくても真偽が決まる。だから $`(M, \in) \models \varphi[\bar a]`$ ではなく

```math
(M, \in) \models \varphi
```

と書ける。以下これを $`M \models \varphi`$ と略記する。

**定義（スキーマ）.** 論理式 $`\varphi`$ ごとに 1 本の文を対応させる規則を **スキーマ** と呼ぶ。
論理式は無限にあるので、スキーマ 1 つは無限個の文を表す。

**定義（公理系・モデル）.** 文の集まり $`T`$ を **公理系** と呼ぶ。集合 $`M`$ が

```math
M \models T \quad :\iff\quad \text{全ての } \varphi \in T \text{ について } M \models \varphi
```

を満たすとき、$`M`$ は $`T`$ の **モデル** であるという。

## 2. KP の公理

**定義.** **KP**（Kripke–Platek 集合論）とは、次の 8 つからなる公理系である（原文 §10 冒頭）。
下 3 つはスキーマである。

### 外延性（Extensionality）

```math
\forall x\,\forall y\,\bigl(\forall z\,(z \in x \leftrightarrow z \in y) \to x = y\bigr)
```

同じ元を持つ 2 つの集合は等しい。

### 空集合（Empty Set）

```math
\exists x\,\forall z\,\neg(z \in x)
```

元を 1 つも持たない集合がある。

### 対（Pairing）

```math
\forall x\,\forall y\,\exists z\,(x \in z \wedge y \in z)
```

$`x`$ と $`y`$ を両方含む集合 $`z`$ がある。$`z`$ は余分な元を持ってよい。
$`\{x,y\}`$ ちょうどが要るときは、$`z`$ から $`\Delta_0`$-分出で切り出す。

### 和（Union）

```math
\forall x\,\exists z\,\forall y \in x\,\forall w \in y\,(w \in z)
```

$`x`$ の元の元を全部含む集合 $`z`$ がある。これも余分を持ってよく、
$`\bigcup x`$ ちょうどは $`\Delta_0`$-分出で取る。

### 無限（Infinity）

```math
\exists x\,\bigl(\exists e \in x\,(e = \emptyset)
\ \wedge\ \forall y \in x\,\exists s \in x\,(s = y \cup \{y\})\bigr)
```

**帰納的集合**、すなわち $`\emptyset`$ を含み、$`y`$ を含めば $`y \cup \{y\}`$ も含む集合がある。
この $`x`$ は $`\emptyset, \{\emptyset\}, \{\emptyset,\{\emptyset\}\}, \dots`$ を全部含むので無限である。
§5 で $`L_\omega`$ が KP のモデルにならないのは、この公理が成り立たないからである。

### Δ₀-分出（Δ₀-Separation）

各 $`\Delta_0`$ 論理式 $`\varphi(z, \bar p)`$ に対する

```math
\forall a\,\forall \bar p\,\exists b\,\forall z\,\bigl(z \in b \leftrightarrow (z \in a \wedge \varphi(z, \bar p))\bigr)
```

既にある $`a`$ から、条件 $`\varphi`$ を満たす元だけを切り出せる。
切り出す条件が $`\Delta_0`$ に限られているのが ZF との違いである。

### Δ₀-集合化（Δ₀-Collection）

各 $`\Delta_0`$ 論理式 $`\varphi(x, y, \bar p)`$ に対する

```math
\forall a\,\forall \bar p\,\Bigl(\forall x \in a\,\exists y\ \varphi(x,y,\bar p)
\ \to\ \exists b\,\forall x \in a\,\exists y \in b\ \varphi(x,y,\bar p)\Bigr)
```

前件と後件に分けて読む。

**前件** $`\ \forall x \in a\ \exists y\ \varphi(x,y,\bar p)`$

$`a`$ のどの元 $`x`$ についても、$`\varphi(x,y,\bar p)`$ を満たす $`y`$ が存在する。
この $`\exists y`$ は非有界なので、$`y`$ は宇宙のどこにあってもよい。

**後件** $`\ \exists b\ \forall x \in a\ \exists y \in b\ \varphi(x,y,\bar p)`$

そのような $`y`$ を、$`a`$ の全ての $`x`$ について少なくとも 1 つずつ含む集合 $`b`$ が存在する。
$`b`$ は余分な元を含んでよい。

**言っていること.** $`x`$ ごとにばらばらに存在していた $`y`$ を、
1 つの集合 $`b`$ にまとめて捕まえられる、ということである。
この「前件 $`\to`$ 後件」の形を **集合化**（Collection）と呼ぶ。
条件 $`\varphi`$ の複雑度を上げた版が §9 に出てくる。

**なぜ自明でないか.** 前件は「各 $`x`$ に $`y`$ がある」としか言っていない。
$`y`$ が $`x`$ ごとにどんどん大きくなると、それら全部を含む集合が無いかもしれない。
集合化は「そういうことは起きない」と主張している。

**特別な公理である.** §6.2 で見るとおり、他の 7 公理は $`\omega`$ より大きい極限 $`\theta`$ なら
$`L_\theta`$ で自動的に成立する。自動にならないのはこの公理だけで、
許容順序数であるための条件は実質これ 1 つである（§6.3）。

### ∈-帰納法（Set Induction）

各論理式 $`\varphi`$ に対する

```math
\forall x\,\bigl((\forall y \in x\ \varphi(y)) \to \varphi(x)\bigr) \ \to\ \forall x\ \varphi(x)
```

「$`x`$ の元すべてで $`\varphi`$ が成り立てば $`x`$ でも成り立つ」が言えれば、
全ての $`x`$ で $`\varphi`$ が成り立つ。$`\in`$ に沿った帰納法である。

## 3. ZF から何を外したか

| 公理 | ZF | KP |
|---|---|---|
| 外延性、空集合、対、和、無限 | ○ | ○ |
| 基礎 / $`\in`$-帰納法 | ○ | ○ |
| **冪集合** | ○ | **無し** |
| 分出 | 任意の論理式 | **$`\Delta_0`$ だけ** |
| 置換 / 集合化 | 任意の論理式 | **$`\Delta_0`$ だけ** |

外した理由は 1 つである。$`\Delta_0`$ に収まらないものを除いてある。

- 冪集合は、レヴィ階層のノート §4.5 のとおり $`z = P(x)`$ が $`\Pi_1`$ で $`\Delta_0`$ に書けない
- 分出と置換を $`\Delta_0`$ に制限するのも同じ理由である

$`\Delta_0`$ だけにしておくと、レヴィ階層のノート §3.4 の

> $`\Delta_0`$ の条件で探し物をするなら、推移的集合の中で見つけたものは本物である

がそのまま使える。KP は弱いぶん小さい $`L_\theta`$ でも満たせる。原文はこの
「小さくて、しかも必要な構成ができる」ちょうどの強さを使う。

## 4. 許容順序数

**定義.** 順序数 $`\theta`$ が **許容順序数**（admissible ordinal）であるとは

```math
L_\theta \models \mathrm{KP}
```

が成り立つことをいう。

**意味.** $`L_\theta`$ が「集合論として使える程度に大きい」ということである。
大きさの尺度が $`\mathrm{KP}`$ になっている。

## 5. ω は許容順序数でない

$`L_\omega = \mathrm{HF}`$（遺伝的有限集合全体）が KP のどれを満たすか見る。

| 公理 | $`L_\omega`$ で成立するか |
|---|---|
| 外延性 | ○ |
| 空集合 | ○ $`\emptyset \in \mathrm{HF}`$ |
| 対 | ○ $`x, y`$ が遺伝的有限なら $`\{x,y\}`$ も遺伝的有限 |
| 和 | ○ 同様 |
| $`\Delta_0`$-分出 | ○ 有限集合の部分集合は遺伝的有限 |
| $`\Delta_0`$-集合化 | ○ |
| $`\in`$-帰納法 | ○ |
| **無限** | **×** |

無限だけが成り立たない。帰納的集合 $`x`$ は $`\emptyset, \{\emptyset\}, \{\emptyset,\{\emptyset\}\}, \dots`$ を
全部含むので無限集合である。ところが $`L_\omega`$ の元は全部有限だった
（構成可能階層のノート §7）。だから $`L_\omega`$ に帰納的集合は無い。

```math
L_\omega \not\models \mathrm{KP}
```

よって $`\omega`$ は許容順序数でない。

## 6. 実質の条件は Δ₀-集合化だけ

$`\theta`$ が許容順序数のとき何が言えるかを、両方向から見る。

### 6.1 許容なら θ は ω より大きい極限（原文 補題 13.1）

**補題 13.1.** $`\theta`$ が許容順序数なら $`\theta \gt \omega`$ であり、$`\theta`$ は極限順序数である。
また $`\omega \in L_\theta`$。

**証明.** $`L_\theta \models \mathrm{KP}`$ は Infinity を満たすので、$`L_\theta`$ の中に帰納的集合がある。
$`L_\theta`$ は推移的なので、その中で $`\Delta_0`$-分出により得られる最小の帰納的集合は
外部の $`\omega`$ と一致する。従って $`\omega \in L_\theta`$。
構成可能階層のノート §9 の $`L_\theta \cap \mathrm{Ord} = \theta`$ から $`\omega \lt \theta`$。

次に任意の $`\xi \lt \theta`$ を取る。$`\xi \in L_\theta`$ である。Pairing と Union を
$`L_\theta`$ の中で使うと $`\xi + 1 = \xi \cup \{\xi\} \in L_\theta`$。従って $`\xi + 1 \lt \theta`$ で、
$`\theta`$ は極限順序数である。$`\square`$

### 6.2 逆に、ω より大きい極限なら 7 公理は自動

$`\omega \lt \theta`$ で $`\theta`$ が極限順序数なら、$`\Delta_0`$-集合化以外の 7 公理は
$`L_\theta`$ で自動的に成立する。

| 公理 | 理由 |
|---|---|
| 外延性、$`\in`$-帰納法 | $`L_\theta`$ が推移的で、外の宇宙で成立するから |
| 空集合、対、和 | $`a, b \in L_\xi`$ から作った集合は $`\mathrm{Def}(L_\xi) = L_{\xi+1}`$ に入る。$`\theta`$ が極限なので $`\xi + 1 \lt \theta`$ |
| $`\Delta_0`$-分出 | 切り出したものは $`a`$ の部分集合で、$`L_\xi`$ 上で定義可能。やはり $`L_{\xi+1}`$ に入る |
| 無限 | $`\omega \lt \theta`$ から $`\omega \in L_\theta`$。$`\omega`$ 自身が帰納的集合 |

### 6.3 まとめ

6.1 と 6.2 を合わせると

```math
\theta \text{ が許容順序数}
\quad\iff\quad
\omega \lt \theta \ \wedge\ \theta \text{ は極限順序数} \ \wedge\
L_\theta \text{ で } \Delta_0\text{-集合化が成立}
```

**実質の条件は $`\Delta_0`$-集合化だけ** である。形式化はこの右辺のほうを定義に採っている（§12）。

## 7. 充足コード SatCode

原文 定義 8.3 と補題 8.4 の内容である。§8 と §9 で使う。

### 7.1 3 つの引数

原文 定義 8.3 の $`\mathrm{SatCode}(A, U, T)`$ は
3 引数の $`\Delta_0`$ 述語である（原文 式 8.5）。定義そのものは長いので、
ここでは各引数が何かだけ書く。なお **コード** とは、論理式を自然数で表したものである
（符号化の仕方は 7.2）。

| 引数 | 何か |
|---|---|
| $`A`$ | 真偽を測る対象。構造 $`(A, \in)`$ の土台である |
| $`T`$ | **真理部分**。$`\langle e, a \rangle`$ という対を集めた集合で、$`e`$ は論理式のコード、$`a`$ は割り当てである。真であるものだけが入っている |
| $`U`$ | **作業場所**。論理式のコードと割り当てが住む補助集合。推移的で、対と和で閉じている |

そのうえで $`\mathrm{SatCode}(A, U, T)`$ は

> $`T`$ は構造 $`(A, \in)`$ の充足関係を正しく符号化しており、$`U`$ はそのための作業場所である

と読む。「正しく」の中身は原文 補題 8.4 で、コード $`e`$ が表す論理式を $`\varphi_e`$ と書くと

```math
\langle e, a \rangle \in T \quad\iff\quad (A, \in) \models \varphi_e[a]
```

である。$`T`$ は $`A`$ から一意に定まり、$`U`$ の取り方には依らない。

つまり $`\mathrm{SatCode}`$ は、構成可能階層のノート §2 で外から与えた $`\models`$ の再帰を、
**1 つの集合 $`T`$ として持ち直したもの** である。集合になっていると、論理式のコード $`e`$ を
量化できる。定義 11.1 が「全ての KP 公理コード $`d`$ について $`\langle d, \emptyset \rangle \in S`$」と
書けるのはこのためである。

### 7.2 コードの計算

原文 §8 の符号化は、カントール対関数

```math
\pi(m,n) = \frac{(m+n)(m+n+1)}{2} + n
```

を使って次のように定める。

```math
\ulcorner v_i = v_j \urcorner = \pi(0, \pi(i,j)), \qquad
\ulcorner v_i \in v_j \urcorner = \pi(1, \pi(i,j))
```
```math
\ulcorner \neg\varphi \urcorner = \pi(2, \ulcorner\varphi\urcorner), \qquad
\ulcorner \varphi \wedge \psi \urcorner = \pi(3, \pi(\ulcorner\varphi\urcorner, \ulcorner\psi\urcorner)), \qquad
\ulcorner \exists v_i\,\varphi \urcorner = \pi(4, \pi(i, \ulcorner\varphi\urcorner))
```

計算すると次のようになる。

```math
\begin{aligned}
\ulcorner v_0 = v_0 \urcorner &= 0 \cr
\ulcorner \neg(v_0 = v_0) \urcorner &= 3 \cr
\ulcorner v_0 = v_1 \urcorner &= 5 \cr
\ulcorner \exists v_1\,(v_1 \in v_0) \urcorner &= 295 \cr
\ulcorner \neg\exists v_1\,(v_1 \in v_0) \urcorner &= 44548
\end{aligned}
```

**主張.** 「$`e`$ は整式のコードである」「$`e`$ は $`\Delta_0`$ 式のコードである」は、
どちらも $`\Delta_0`$ 述語である（原文 §8）。

**理由.** 証拠として $`e`$ の作り方の記録、すなわち各項が原子式コードか、それ以前の項へ
構成子を 1 つ適用したもので、最後の項が $`e`$ である有限自然数列 $`s`$ を取る。
有限列も $`\pi`$ で 1 個の自然数になるので $`s \in \omega`$ であり

```math
\mathrm{Form}(e) \ :\iff\ \exists s \in \omega\ (s \text{ は } e \text{ の作り方の記録である})
\tag{8.2}
```

と**有界に**書ける。記録の検査も各項のタグと射影を見るだけで、$`s, e, \omega`$ に有界である。
$`\Delta_0`$ 式かどうかは、記録中の $`\exists`$ が $`\exists v_i\,(v_i \in v_j \wedge \cdots)`$
の形、すなわち有界量化の展開形かを見れば分かり、これも有界である。

### 7.3 割り当ての書き方

原文 §9.1 の使い方に合わせる。$`v_0`$ を「切り出す変数」、
$`v_1, v_2, \dots`$ をパラメータ変数とし、$`a`$ はパラメータの値の列とする。
$`v_0`$ に $`x`$ を割り当て、その後ろに $`a`$ を繋いだ完全な割り当てを $`a_x`$ と書く。
$`T`$ に入るのは $`a_x`$ のほうである。
括弧は原文に合わせ、$`\langle\ ,\ \rangle`$ を順序対、$`(\ ,\ )`$ を有限列に使う。

| 名前 $`\langle e, a \rangle`$ | $`e`$ が表す式 | 意味 |
|---|---|---|
| $`\langle 3, () \rangle`$ | $`\neg(v_0 = v_0)`$ | 常に偽 |
| $`\langle 0, () \rangle`$ | $`v_0 = v_0`$ | 常に真 |
| $`\langle 44548, () \rangle`$ | $`\neg\exists v_1\,(v_1 \in v_0)`$ | $`v_0`$ は空 |
| $`\langle 295, () \rangle`$ | $`\exists v_1\,(v_1 \in v_0)`$ | $`v_0`$ は空でない |
| $`\langle 5, (1) \rangle`$ | $`v_0 = v_1`$、$`v_1`$ に $`1`$ を代入 | $`v_0`$ は $`1`$ |

### 7.4 A = L_2 で計算する

フォンノイマン自然数で書くと
$`L_2 = \{\emptyset, \{\emptyset\}\} = \{0, 1\}`$ である。

$`\langle 295, () \rangle`$ を見る。$`a_x = (x)`$ で、$`v_0`$ にだけ値が入る。

- $`x = 0 = \emptyset`$。$`c \in L_2`$ で $`c \in \emptyset`$ となるものは無い。**偽**
- $`x = 1 = \{\emptyset\}`$。$`c = \emptyset`$ が $`\emptyset \in \{\emptyset\}`$ を満たす。**真**

```math
\langle 295,\ (0) \rangle \notin T, \qquad \langle 295,\ (1) \rangle \in T
```

$`\langle 5, (1) \rangle`$ を見る。$`a_x = (x, 1)`$ で、$`v_0`$ に $`x`$、$`v_1`$ に $`1`$ が入る。

```math
\langle 5,\ (0, 1) \rangle \notin T \quad (0 \ne 1), \qquad
\langle 5,\ (1, 1) \rangle \in T \quad (1 = 1)
```

**5 行が切り出す部分集合.** 各 $`\langle e, a \rangle`$ について $`\{x \in L_2 : \langle e, a_x \rangle \in T\}`$ を集める。

| $`\langle e, a \rangle`$ | 切り出される部分集合 |
|---|---|
| $`\langle 3, () \rangle`$ | $`\emptyset`$ |
| $`\langle 0, () \rangle`$ | $`\{0, 1\} = L_2`$ |
| $`\langle 44548, () \rangle`$ | $`\{0\} = \{\emptyset\}`$ |
| $`\langle 295, () \rangle`$ | $`\{1\} = \{\{\emptyset\}\}`$ |
| $`\langle 5, (1) \rangle`$ | $`\{1\} = \{\{\emptyset\}\}`$ |

上 4 行で $`L_2`$ の部分集合 4 つが全部出た。これは構成可能階層のノート §7 の
第 3 段の表と同じもので、$`\mathrm{Def}(L_2) = L_3`$ の中身である。

下 2 行は別のコードから同じ部分集合が出ている。$`\mathrm{Def}`$ が集めるのは
コードではなく部分集合なので、重複してよい。

**なお** $`\exists v_1\,(v_1 \in v_0)`$ の $`\exists v_1`$ は非有界だが、この式は
$`\exists v_1 \in v_0\,(v_1 = v_1)`$ と同値で、そちらは $`\Delta_0`$ である。
だから $`L_2`$ の中で測っても外で測っても「空でない」の答えは同じになる
（レヴィ階層のノート §3）。

$`U`$ は、$`A`$、$`\omega`$、$`T`$ と全ての割り当てを含む推移的な集合を取ればよい。
ここでは割り当てが有限関数なので、$`L_\omega`$ より少し上の $`L_\xi`$ で足りる。

## 8. L-階層コード LCode

原文 定義 9.1 と補題 9.2 の内容である。

$`\mathrm{LCode}`$ の定義の中には、§7 の $`\mathrm{SatCode}`$ がそのままの形で現れる。
作る階層の段 1 つにつき $`\mathrm{SatCode}`$ が 1 つ要求される（原文 定義 9.1 の条件 3）。
その形は 8.2 で書く。

### 8.1 3 つの引数

$`\mathrm{LCode}(\eta, M, c)`$ も 3 引数の $`\Delta_0`$ 述語である（原文 式 9.4）。

| 引数 | 役割 | 何か | §7 の $`\mathrm{SatCode}(A, U, T)`$ での対応 |
|---|---|---|---|
| $`\eta`$ | 入力 | どこまで階層を作るかを指定する順序数 | $`A`$（入力。構造の土台） |
| $`M`$ | 結果 | 作り終えた階層の最上段 | $`T`$（結果。真理部分） |
| $`c`$ | 補助 | 作業データ一式。4 成分からなる（8.2） | $`U`$（補助。作業場所） |

そのうえで $`\mathrm{LCode}(\eta, M, c)`$ は

> $`c`$ は $`L_0`$ から $`L_\eta`$ までを $`\mathrm{Def}`$ で順に作った記録であり、
> $`M`$ はその最上段である

と読む。「正しく」の中身は原文 補題 9.2 で

```math
\mathrm{LCode}(\eta, M, c) \ \Longrightarrow\ M = L_\eta
```

である。$`M`$ は $`\eta`$ から一意に定まり、$`c`$ の取り方には依らない。

**引数の並びは §7 と入れ替わっている.** 役割は対応しているが、位置は対応していない。

```
SatCode ( 入力 , 補助 , 結果 )
LCode   ( 入力 , 結果 , 補助 )
```

原文の並びなのでそのまま使う。役割が対応しているので、命題も対応する。

| | §7 $`\mathrm{SatCode}`$ | §8 $`\mathrm{LCode}`$ |
|---|---|---|
| 入力から結果が一意 | 補題 8.4（$`T`$ は $`A`$ から一意） | 補題 9.2（$`M = L_\eta`$） |
| 述語が $`\Delta_0`$ | 原文 式 (8.5) | 原文 式 (9.4) |
| 使い方 | $`L_\theta`$ の中で $`U, T`$ を見つければ $`T`$ は本物の真理部分 | $`L_\theta`$ の中で $`M, c`$ を見つければ $`M`$ は本物の $`L_\eta`$ |

ただし $`c`$ は $`U`$ より中身が多い。$`U`$ 自身が $`c`$ の第 0 成分として入っており、
さらに構成の記録 $`H, S, D`$ を持つ（8.2）。

### 8.2 c の 4 成分

**定義（関数、定義域、値域）.** 集合 $`f`$ が **関数** であるとは、$`f`$ の元が全て順序対であり、かつ

```math
\langle x, y \rangle \in f \ \wedge\ \langle x, y' \rangle \in f
\ \Longrightarrow\ y = y'
```

が成り立つことをいう。このとき

```math
\mathrm{dom}\, f = \{\, x : \exists y\ \langle x,y \rangle \in f \,\}, \qquad
\mathrm{ran}\, f = \{\, y : \exists x\ \langle x,y \rangle \in f \,\}
```

をそれぞれ $`f`$ の **定義域**、**値域** と呼ぶ。$`\langle x,y \rangle \in f`$ のとき
$`y`$ を $`f(x)`$ と書く。

**意味.** 関数は順序対の集合そのものであって、「どの集合へ写るか」という情報を持たない。
従って $`\mathrm{ran}\, f`$ は $`f`$ が実際に取る値の全体である。

**定義（$`c`$ の成分）.** $`c`$ は定義域 $`\{0,1,2,3\}`$ の関数で、$`c(0) = U`$、
$`c(1) = H`$、$`c(2) = S`$、$`c(3) = D`$ である（原文の $`\mathrm{FourCode}`$）。

| 成分 | 定義域 | 中身 |
|---|---|---|
| $`H`$ | $`\eta + 1`$ | 階層そのもの。$`H(\xi) = L_\xi`$ |
| $`S`$ | $`\eta`$ | 真理部分。$`\mathrm{SatCode}(H(\xi), U, S(\xi))`$ が成り立つ |
| $`D`$ | $`\eta`$ | 定義可能部分集合の枚挙。型は下で定める |
| $`U`$ | — | 関数ではない。推移的で対と和で閉じており、$`\eta, M, H, S, D, \omega`$ を全部含む |

$`S(\xi)`$ が §7 の $`\mathrm{SatCode}`$ の第 3 引数そのものである。各段ごとに 1 つずつ持つ。

**定義（$`D`$ の型）.** $`D`$ は定義域 $`\eta`$ の関数である。各 $`\xi \lt \eta`$ について、
値 $`D(\xi)`$ は **再び関数** であって、その定義域は $`\langle e, a \rangle`$ の形の対全体である。
ここで $`e`$ は式コード、$`a`$ は §7.3 のパラメータ列で、その値は全て $`H(\xi)`$ に属する。
値 $`b = D(\xi)(e,a)`$ は $`H(\xi)`$ の部分集合であって、全ての $`x \in H(\xi)`$ について

```math
x \in b \quad\iff\quad \langle e, a_x \rangle \in S(\xi)
```

を満たす（原文 定義 9.1 の条件 4、式 (9.1)）。

**記法.** $`D(\xi)`$ 自身が関数なので括弧が 2 つ並ぶ。$`D(\xi)(e,a)`$ は、引数 1 個の対
$`\langle e,a \rangle`$ に $`D(\xi)`$ を適用した値 $`D(\xi)(\langle e,a \rangle)`$ の略記である
（原文の書き方）。$`H(\xi)`$ と $`S(\xi)`$ の値は集合なので、括弧は 1 つで止まる。

| 式 | 何か |
|---|---|
| $`H(2)`$ | 集合。$`L_2`$ |
| $`S(2)`$ | 集合。$`L_2`$ の真理部分 |
| $`D(2)`$ | **関数** |
| $`D(2)(295, ())`$ | 集合。$`\{1\}`$ |

### 8.3 段の作り方

$`H`$ は次の 3 条件で決まる（原文 定義 9.1 の 2, 5）。
$`\mathrm{ran}\, D(\xi)`$ は $`\mathrm{ran}(D(\xi))`$、すなわち内側の関数 $`D(\xi)`$ の値域である
（8.2）。$`D`$ の値域ではない。

```math
H(0) = \emptyset, \qquad
H(\xi+1) = \mathrm{ran}\, D(\xi), \qquad
H(\lambda) = \bigcup_{\xi<\lambda} H(\xi) \quad (\lambda \text{ 極限})
```

最後に $`M = H(\eta)`$ とする。

真ん中が要点である。$`D(\xi)`$ は $`L_\xi`$ の定義可能部分集合を漏れなく並べた関数なので、
その値域が $`\mathrm{Def}(L_\xi)`$ にちょうど一致する。つまり

```math
H(\xi+1) = \mathrm{ran}\, D(\xi) = \mathrm{Def}(H(\xi))
```

で、構成可能階層のノート §5 の $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ が再現される。

「漏れなく並べた」ことは、原文 定義 9.1 の条件 4 が $`D(\xi)`$ の定義域を
$`\langle e, a \rangle`$ 全体と**正確に**指定し、値を (9.1) の

```math
x \in b \quad\iff\quad \langle e, a_x \rangle \in S(\xi)
```

で指定していることによる。これは §7.4 でやった計算そのものである。

### 8.4 η = 3 で計算する

§7.4 の続きとして $`\eta = 3`$ を作る。$`H`$ の定義域は $`\eta+1 = 4`$、
$`S`$ と $`D`$ の定義域は $`\eta = 3`$ である。

| $`\xi`$ | $`H(\xi)`$ | 元の個数 |
|---|---|---|
| $`0`$ | $`\emptyset`$ | 0 |
| $`1`$ | $`\{\emptyset\}`$ | 1 |
| $`2`$ | $`\{\emptyset, \{\emptyset\}\}`$ | 2 |
| $`3`$ | $`L_3`$ | 4 |

$`D(2)`$ を書き下す。§7.4 の 5 行がそのまま値になる。

| $`\langle e, a \rangle`$ | $`D(2)(e,a)`$ |
|---|---|
| $`\langle 3, () \rangle`$ | $`\emptyset`$ |
| $`\langle 0, () \rangle`$ | $`\{0, 1\}`$ |
| $`\langle 44548, () \rangle`$ | $`\{0\}`$ |
| $`\langle 295, () \rangle`$ | $`\{1\}`$ |
| $`\langle 5, (1) \rangle`$ | $`\{1\}`$ |

$`D(2)`$ の定義域はこの 5 つだけではなく、$`L_2`$ 上の $`\langle e,a \rangle`$ 全体である。
ただし値は 4 通りしかないので、値域は

```math
\mathrm{ran}\, D(2) = \{\, \emptyset,\ \{0\},\ \{1\},\ \{0,1\} \,\} = L_3 = H(3)
```

となり、8.3 の後続段の条件が満たされている。最後に $`M = H(3) = L_3`$ で、
補題 9.2 のとおりである。

### 8.5 なぜ Δ₀ であることが効くのか

$`\mathrm{LCode}(\eta, M, c)`$ は $`\Delta_0`$ である（原文 式 9.4）。だから
レヴィ階層のノート §3.4 により、推移的な $`L_\theta`$ の中で $`\mathrm{LCode}`$ を満たす
$`M, c`$ を見つければ、外から見てもそれは本物である。補題 9.2 を外で適用すれば
$`M = L_\eta`$ が外でも言える。これが §9 の系 10.6 になる。

## 9. KP の中で何ができるか

原文 §10 は、必要な補題を KP から順に導く。連鎖は次のとおりである。

**補題 10.1（$`\Sigma_1`$-集合化）.** §2 の $`\Delta_0`$-集合化で、条件を
$`\Sigma_1`$ 論理式 $`\psi`$ に取り替えた形も KP から証明できる。すなわち KP のもとで

```math
\forall x \in a\ \exists y\ \psi(x,y) \ \Longrightarrow\ \exists b\ \forall x \in a\ \exists y \in b\ \psi(x,y)
\qquad (\psi \in \Sigma_1)
```

が成り立つ。$`\Sigma_1`$-集合化は KP の公理ではなく、KP から導かれる定理である。

仕組みは、$`\psi = \exists z\,\delta`$ の証人 $`y`$ と $`z`$ を順序対 $`w = \langle y, z\rangle`$ に
まとめること。「$`w`$ は $`x`$ に対する証人対である」は $`\Delta_0`$ になるので、
$`\Delta_0`$-集合化が使える。

**系 10.2（機能的 $`\Sigma_1`$-置換）.** 補題 10.1 の前件を、$`y`$ が **ただ 1 つ** 存在する
（記号で $`\exists!y`$）に強めると、集合 $`b`$ どころか関数が取れる。すなわち KP のもとで、
$`\psi \in \Sigma_1`$ と

```math
\forall x \in a\ \exists!y\ \psi(x,y)
```

から、$`\mathrm{dom}(F) = a`$ かつ全ての $`x \in a`$ で $`\psi(x, F(x))`$ を満たす関数 $`F`$ が
存在する。$`x`$ に対する $`y`$ が 1 つに決まるので、$`x \mapsto y`$ が関数になる、というだけである。

**補題 10.3（順序数 $`\Sigma_1`$-再帰）.** 各段の値が $`\Sigma_1`$ で一意に決まる再帰は、
KP の中で最後まで実行できて 1 つの関数になる。$`\omega`$-再帰も同じ。

**補題 10.4（有限符号と閉包）.** KP は次を証明する。

1. 任意の $`A`$ について、$`A`$ の有限列全体 $`A^{\lt\omega}`$ が存在する
2. 任意の $`X`$ について、$`X`$ を含む最小の推移的集合 $`\mathrm{TC}(X)`$ が存在する
3. 任意の $`X`$ について、$`X \subseteq U`$ で $`U`$ が推移的、かつ対と和で閉じているものが存在する

**補題 10.5（充足コードと $`L`$-コードの存在）.** §7 の $`\mathrm{SatCode}`$ を使う。KP は次を証明する。

1. 任意の集合 $`A`$ について、$`\mathrm{SatCode}(A, U, T)`$ を満たす $`U, T`$ がある。
   真理部分 $`T`$ は $`A`$ から一意に定まる
2. 任意の順序数 $`\eta`$ について、$`\mathrm{LCode}(\eta, M, c)`$ を満たす $`M, c`$ がある

**系 10.6.** $`\theta`$ が許容順序数で $`\eta \lt \theta`$ なら

```math
L_\theta \models \exists M\, \exists c\ \mathrm{LCode}(\eta, M, c)
```

であり、その $`M`$ は内部でも外部でも $`L_\eta`$ である。

最後の 1 行が要点である。$`\mathrm{LCode}`$ は $`\Delta_0`$（原文 式 9.4）なので、
レヴィ階層のノート §3.4 により $`L_\theta`$ の中で見つけたコードは外でも本物であり、
$`M = L_\eta`$ が外でも言える。つまり

> 許容順序数 $`\theta`$ を取ると、$`L_\theta`$ の中で「$`L_\eta`$ が存在する」と言える（$`\eta \lt \theta`$）。

これが許容性を要求する理由である。

## 10. 参考：最小の許容順序数

§5 のとおり $`\omega`$ は許容順序数でない。では最小のものは何か。

**チャーチ・クリーネ順序数** $`\omega_1^{\mathrm{CK}}`$ である。これは
「計算可能な整列順序で表せる順序数」の上限で、可算だが $`\omega`$ よりはるかに大きい。

原文はこの順序数を使わない。使うのは、許容順序数がいくらでもあることと、
補題 16.2 で作る特定の対 $`\Lambda \lt \Theta`$ だけである。

## 11. 原文での使われ方

| 場所 | 使い方 |
|---|---|
| 定義 18.1 | 安定ラベル $`f(i)`$ の値は許容順序数である |
| 式 (15.1) | $`\alpha \lhd_k \beta`$ は許容順序数 $`\alpha \lt \beta`$ の間の関係である |
| 定義 11.1 | 内部で「$`\eta`$ は許容」と言う述語 $`\mathrm{Adm}(\eta)`$。$`\hat\Sigma_1`$ である |
| 補題 11.2 | その正しさ。$`\theta`$ 許容、$`\eta \lt \theta`$ なら $`L_\theta \models \mathrm{Adm}(\eta) \iff L_\eta \models \mathrm{KP}`$ |
| 補題 16.2 | 許容順序数の対 $`\Lambda \lt \Theta`$ で $`L_\Lambda \prec L_\Theta`$ となるものを作る |
| 定理 17.1 | 許容順序数からなる有限集合を $`\alpha`$ 未満へ押し下げる |

$`\mathrm{Adm}(\eta)`$ が $`\hat\Sigma_1`$ であることは定理 17.1 の複雑度計算に効く。
$`\hat\Sigma_q`$ は別のノートにする。

## 12. Lean での対応

形式化は $`L_\theta \models \mathrm{KP}`$ をそのまま定義に採らず、§6.3 の右辺のほうを
`IsAdmissible` の定義にしている。KP の公理のコードを作るファイルが `Adm.lean` より
下流にあるためで、同値性はそちらで証明されている。

| 概念 | Lean | ファイル |
|---|---|---|
| $`L_\theta`$ での $`\Delta_0`$-集合化 | `Delta0Collection (L θ)` | `Bm4/SetTheory/Adm.lean` |
| $`\theta`$ は許容順序数（§6.3 の右辺） | `IsAdmissible θ` | 同上 |
| $`\theta \gt \omega`$ | `IsAdmissible.omega_lt` | 同上 |
| $`\theta`$ は極限順序数 | `IsAdmissible.isSuccLimit` | 同上 |
| $`\omega \in L_\theta`$ | `IsAdmissible.omega_mem` | 同上 |
| KP の公理のコード | `KPAxCode` | `Bm4/SetTheory/KPAx.lean` |
| §6.2 の向き（右辺 $`\Rightarrow`$ KP の全公理が真） | `KPSat.satIn_kpAx` | `Bm4/SetTheory/KPSat.lean` |
| §6.1 の向き（KP の全公理が真 $`\Rightarrow`$ 右辺） | `KPSat.isAdmissible_of_kpTrue`, `AdmKP.omega_lt_of_kpTrue`, `AdmKP.isSuccLimit_of_kpTrue` | 同上、`Bm4/SetTheory/AdmKP.lean` |
| 定義 11.1 の $`\mathrm{Adm}(\eta)`$ | `AdmKP D h w η` | `Bm4/SetTheory/AdmKP.lean` |
| 補題 11.2 | `admKP_iff` | 同上 |
| 補題 10.1、10.3（$`\Sigma_1`$ 収集と順序数再帰） | `Bm4/SetTheory/Recur.lean`, `Recursion.lean` | 同上 |
| 補題 10.5(1)（充足コードの存在） | `Bm4/SetTheory/SatInL.lean` | 同上 |
| §7 の $`\mathrm{SatCode}(A,U,T)`$ | `SatCode h w M U S` | `Bm4/SetTheory/SatCode.lean` |
| 補題 8.4（充足コードの正しさ） | `satCode_correct` | 同上 |
| §8 の $`\mathrm{LCode}(\eta,M,c)`$ | `LCode h w η M c` | `Bm4/SetTheory/LCode.lean` |
| 式 (9.4)（$`\mathrm{LCode}`$ が $`\Delta_0`$） | `delta0_lcode` | 同上 |
| 補題 9.2（$`M = L_\eta`$） | `lcode_sound` | 同上 |
| 補題 10.5(2)、系 10.6（$`L`$-コードの存在） | `lcode_exists_in_L` | `Bm4/SetTheory/LCodeEx.lean` |
