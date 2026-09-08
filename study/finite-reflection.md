[← Back](README.md)

# 有限行反映（定理 17.1）

前提

| ノート | ここから使う言葉 |
|---|---|
| [構成可能階層 L](constructible-hierarchy.md) | $`L_\xi`$、$`L_\xi \cap \mathrm{Ord} = \xi`$（§9） |
| [レヴィ階層と絶対性](levy-hierarchy.md) | $`\Delta_0`$、$`\Delta_0`$ 絶対性 |
| [KP と許容順序数](kp-admissible.md) | KP、許容順序数、$`\mathrm{SatCode}`$、$`\mathrm{LCode}`$、系 10.6 |
| [厳密交代ブロック階層と安定関係](alternating-blocks.md) | **$`\hat\Sigma_q`$、$`\hat\Pi_q`$（1.1）**、$`\prec^*_q`$、$`\lhd_k`$、補題 15.1、なぜ +2 か（3.3） |
| [部分真理述語と有限段 Tarski–Vaught](truth-predicates.md) | $`\mathrm{TV}_q`$、補題 14.3、定理 14.4 |

## 1. 内部表示

### 1.1 なぜ要るのか

$`\lhd_k`$ も「$`\eta`$ は許容順序数」も、これまでは外から見た条件だった。
定理 17.1 の証明では、これらを $`L_\beta`$ の**中に書いた文**にする。
その文が $`L_\beta`$ で真であることから、$`L_\alpha`$ でも真であることを導く。
そのための述語を 3 つ用意する。

### 1.2 Adm(η)（定義 11.1）

**ここで定義する記号.** $`\mathrm{KPTrue}(M,U,S)`$ と $`\mathrm{Adm}(\eta)`$ の 2 つである。

**すでにある記号.**

| 記号 | 何か | どこ |
|---|---|---|
| $`\mathrm{KPAx}(d)`$ | 「$`d`$ は KP の公理または公理スキーマの 1 インスタンスのコードである」。$`\Delta_0`$ | 原文 §11 |
| $`\mathrm{LCode}(\eta,M,c)`$ | $`L`$-階層コード | KP ノート §8 |
| $`\mathrm{SatCode}(M,U,S)`$ | 充足コード | KP ノート §7 |

**定義（原文 定義 11.1）.** $`\mathrm{KPTrue}`$ と $`\mathrm{Adm}`$ を、下記を満たす論理式として
定義する。

```math
\mathrm{KPTrue}(M,U,S) \ :\iff\ \forall d \in \omega\ \bigl(\mathrm{KPAx}(d) \to \langle d, \emptyset \rangle \in S\bigr)
```
```math
\mathrm{Adm}(\eta) \ :\iff\ \exists M, c, U, S\ \bigl(
\mathrm{LCode}(\eta,M,c) \wedge \mathrm{SatCode}(M,U,S) \wedge \mathrm{KPTrue}(M,U,S)\bigr)
```

**読み方.** 「$`L_\eta`$ のコードを作り、その充足コードを作り、KP の全公理がそこで真」。
つまり $`L_\eta \models \mathrm{KP}`$ をコードの言葉で書き直したものである。

割り当てが $`\emptyset`$ なのは、$`\mathrm{KPAx}`$ が認識するのが文、すなわち自由変数を
持たないコードだけだからである。文には割り当てが要らない（KP ノート 1）。

**複雑度.** $`\mathrm{LCode}`$、$`\mathrm{SatCode}`$、$`\mathrm{KPTrue}`$ はどれも $`\Delta_0`$ で、
$`\exists M, c, U, S`$ が 1 ブロックである。従って

```math
\mathrm{Adm} \in \hat\Sigma_1 .
```

**補題 11.2（正しさ）.** $`\theta`$ が許容順序数で $`\eta \lt \theta`$ なら

```math
L_\theta \models \mathrm{Adm}(\eta) \quad\iff\quad L_\eta \models \mathrm{KP} .
```

右から左は、系 10.6 により $`L_\theta`$ の中に $`L_\eta`$ のコードがあること、および
$`L_\theta`$ の中に充足コードがあること（補題 10.5(1)）による。
左から右は、$`\mathrm{LCode}`$、$`\mathrm{SatCode}`$、$`\mathrm{KPTrue}`$ の $`\Delta_0`$ 絶対性と
補題 9.2、8.4 による。

### 1.3 St_k(ξ)（定義 15.2）

**定義（原文 定義 15.2）.** $`\mathrm{St}_k(\xi)`$ を、下記を満たす論理式として定義する。
$`\mathrm{TV}_q(M)`$ は部分真理述語のノート 4.2 のものである。

```math
\mathrm{St}_k(\xi) \ :\iff\ \forall M\, \forall c\ \bigl(\mathrm{LCode}(\xi,M,c) \to \mathrm{TV}_{k+2}(M)\bigr)
\tag{15.2}
```

**読み方.** 「$`\xi \lhd_k`$ いま居る宇宙」を、いま居る宇宙の中で言う述語である。
第 2 引数が「自分」なので 1 引数で済む。

**複雑度.** 補題 14.3 の $`\mathrm{TV}_{k+2} \in \hat\Pi_{k+2}`$ から

```math
\mathrm{St}_k \in \hat\Pi_{k+2} .
```

**補題 15.3（正しさ）.** $`\xi \lt \theta`$ がともに許容順序数なら

```math
L_\theta \models \mathrm{St}_k(\xi) \quad\iff\quad \xi \lhd_k \theta . \tag{15.3}
```

系 10.6 により $`L_\theta`$ の中に $`L_\xi`$ の正しいコードが存在し、どのコードが表す集合も
補題 9.2 により $`L_\xi`$ である。従って $`\mathrm{St}_k(\xi)`$ は $`\mathrm{TV}_{k+2}(L_\xi)`$ と
同値になり、定理 14.4 を適用すればよい。

### 1.4 Rel_k(ξ,η)（定義 15.4）

**相対化.** $`\mathrm{St}_k(\xi)^M`$ を、$`\mathrm{St}_k(\xi)`$ の全非有界量化を $`M`$ に
制限した論理式とする。量化子が全部 $`M`$ で抑えられるので、これは $`\Delta_0`$ である。

**定義（原文 定義 15.4）.** $`\mathrm{Rel}_k(\xi,\eta)`$ を、下記を満たす論理式として定義する。
$`\mathrm{Ord}(\xi)`$ は「$`\xi`$ は順序数である」という $`\Delta_0`$ 述語である
（レヴィ階層のノート 2.2）。

```math
\mathrm{Rel}_k(\xi,\eta) \ :\iff\
\mathrm{Ord}(\xi) \wedge \mathrm{Ord}(\eta) \wedge \xi \lt \eta
\wedge \exists M\, \exists c\ \bigl(\mathrm{LCode}(\eta,M,c) \wedge \mathrm{St}_k(\xi)^M\bigr)
\tag{15.4}
```

**読み方.** $`\mathrm{St}_k`$ の「自分」を $`\eta`$ に取り替えた 2 引数版である。
$`\mathrm{St}_k(\xi)`$ を $`M = L_\eta`$ へ相対化することで、「$`L_\eta`$ の中で $`\mathrm{St}_k(\xi)`$」を
外から 1 つの式として言える。

**複雑度.** 相対化した $`\mathrm{St}_k(\xi)^M`$ は $`\Delta_0`$、$`\mathrm{LCode}`$ も $`\Delta_0`$、
$`\mathrm{Ord}`$ と $`\xi \lt \eta`$ も $`\Delta_0`$ である。$`\exists M \exists c`$ が 1 ブロックなので

```math
\mathrm{Rel}_k \in \hat\Sigma_1 .
```

$`k`$ がいくら大きくても $`\hat\Sigma_1`$ のままである。相対化した結果が $`k`$ によらず
$`\Delta_0`$ だからである。ここが 3.4 で効く。

**補題 15.5（正しさ）.**

1. $`\xi \lt \eta`$ がともに許容順序数なら $`\mathrm{Rel}_k(\xi,\eta) \iff \xi \lhd_k \eta`$
2. $`\xi \lt \eta \lt \theta`$ が全て許容順序数なら
   $`L_\theta \models \mathrm{Rel}_k(\xi,\eta) \iff \xi \lhd_k \eta`$

(1) は、外部宇宙で $`\mathrm{LCode}(\eta,M,c)`$ を満たすコードを取れば補題 9.2 で $`M = L_\eta`$ となり、
$`\mathrm{St}_k(\xi)^{L_\eta}`$ が $`L_\eta \models \mathrm{St}_k(\xi)`$ と同じことなので、
補題 15.3 を $`\theta = \eta`$ で使えばよい。(2) は内部の証人コードも $`\Delta_0`$ 絶対性で
外で正しく、やはり $`M = L_\eta`$ であることによる。

### 1.5 3 つの並び

| 述語 | 意味 | 複雑度 |
|---|---|---|
| $`\mathrm{Adm}(\eta)`$ | $`\eta`$ は許容順序数である | $`\hat\Sigma_1`$ |
| $`\mathrm{Rel}_k(\xi,\eta)`$ | $`\xi \lhd_k \eta`$ | $`\hat\Sigma_1`$ |
| $`\mathrm{St}_k(\xi)`$ | $`\xi \lhd_k`$ いま居る宇宙 | $`\hat\Pi_{k+2}`$ |

$`\mathrm{St}_k`$ だけ複雑度が $`k`$ に依存する。$`\mathrm{TV}_{k+2}`$ をそのまま抱えているからである。
$`\mathrm{Rel}_k`$ が $`\hat\Sigma_1`$ で済むのは、その $`\mathrm{St}_k`$ を $`M`$ へ相対化して
$`\Delta_0`$ にしてから $`\exists M \exists c`$ を付けるだけだからである。

## 2. 最初の安定な対（§16）

定理 17.1 は $`\alpha \lhd_n \beta`$ を仮定に持つ。そういう対が存在することを言うのが §16 である。

### 2.1 使う言葉と事実

**定義（$`\omega_1^V`$）.** 外部宇宙 $`V`$ における最小の非可算順序数を $`\omega_1^V`$ と書く。

**定義（正則）.** 順序数 $`\kappa`$ が **正則** であるとは、$`A \subseteq \kappa`$ で
$`|A| \lt |\kappa|`$ なるものについて必ず $`\sup A \lt \kappa`$ となることをいう。

**事実.** $`\omega_1`$ は正則である。すなわち、$`\omega_1`$ 未満の順序数からなる可算集合の
上限は $`\omega_1`$ 未満である。

**定義（$`\lt_L`$）.** $`\xi`$ に沿った超限再帰で、$`L_\xi`$ の整列順序 $`\lt_\xi`$ を作る。

**$`\xi = 0`$.** $`L_0 = \emptyset`$ なので空の順序。

**$`\xi + 1`$.** $`L_{\xi+1} = \mathrm{Def}(L_\xi)`$ の元は、対 $`\langle e, a \rangle`$
（$`e`$ は論理式コード、$`a`$ は $`L_\xi`$ の元の有限列）から切り出される
（構成可能階層のノート §4）。まずこの対を並べる。

- 有限列 $`a`$ と $`a'`$ は、長さが違えば短い方を小さいとし、長さが同じなら
  最初に食い違う成分を $`\lt_\xi`$ で比べる
- 対 $`\langle e,a \rangle`$ と $`\langle e',a' \rangle`$ は、$`e \ne e'`$ なら $`e`$ と $`e'`$ を
  自然数として比べ、$`e = e'`$ なら $`a`$ と $`a'`$ を上の規則で比べる

1 つの元が複数の対から切り出されることがあるので（構成可能階層のノート 4.2）、
$`y \in L_{\xi+1} \setminus L_\xi`$ に対し、$`y`$ を切り出す対のうち最小のものを $`p(y)`$ とする。
そのうえで $`x, y \in L_{\xi+1}`$ について

```math
x \lt_{\xi+1} y \iff
\begin{cases}
\text{真} & x \in L_\xi \text{ かつ } y \notin L_\xi \cr
x \lt_\xi y & x, y \in L_\xi \cr
p(x) \lt p(y) & x, y \notin L_\xi \cr
\text{偽} & x \notin L_\xi \text{ かつ } y \in L_\xi
\end{cases}
```

**極限 $`\lambda`$.** $`\lt_\lambda = \bigcup_{\xi \lt \lambda} \lt_\xi`$ とする。
$`\lt_\xi`$ どうしは食い違わないので、これは順序になる。

最後に $`\lt_L = \bigcup_\xi \lt_\xi`$ とする。

**事実.** $`\lt_L`$ は $`L`$ 全体の整列順序であり、$`L`$ の中で定義可能である。
従って「条件を満たす $`\lt_L`$-最小の元」を、選択公理を使わずに指定できる。

**定義（Skolem 関数）.** 構造 $`N`$ と論理式 $`\exists x\, \varphi(x, \bar y)`$ に対し、
$`\bar y`$ を受け取って $`\varphi`$ の証人 $`x`$ を 1 つ返す関数を **Skolem 関数** と呼ぶ。
$`N \subseteq L`$ のときは $`\lt_L`$-最小の証人を返すことにすれば一意に決まる。

**事実（Tarski–Vaught test）.** 推移的な $`M \subseteq N`$ について、$`N`$ で真な
$`\exists x\, \varphi(x, \bar a)`$（$`\bar a \in M`$）が必ず $`M`$ の中に証人を持つなら、
$`M \prec N`$ である。部分真理述語のノート §4 の有限段版から、交代数の制限を外したものにあたる。

### 2.2 補題 16.1

$`\gamma \lt \omega_1^V`$ なら $`L_\gamma`$ は外部宇宙 $`V`$ で可算である。

$`\gamma`$ に関する超限帰納法による。後続段階では式コードと有限パラメータ列が可算個であり、
可算極限段階では可算個の可算集合の合併である。

### 2.3 補題 16.2

次を満たす許容順序数 $`\Lambda, \Theta`$ が存在する。

```math
\omega \lt \Lambda \lt \Theta, \qquad L_\Lambda \prec L_\Theta . \tag{16.1}
```

**証明の筋.** $`\Theta = \omega_1^V`$ と置く。

まず $`L_\Theta \models \mathrm{KP}`$ を示す。

| 公理 | 理由 |
|---|---|
| Extensionality, Empty Set, Pairing, Union, Infinity | $`\Theta`$ が $`\omega`$ より大きい極限であることから（KP ノート 6.2） |
| Set Induction | 外部 Foundation から。あるインスタンスが失敗すれば、外部 Separation で反例集合を作り、その $`\in`$-最小元を取れば矛盾する |
| $`\Delta_0`$-Separation | パラメータを含む十分大きい $`L_{\gamma_0}`$ と $`L_\Theta`$ の間の $`\Delta_0`$ 絶対性から |
| $`\Delta_0`$-Collection | 下記 |

$`\Delta_0`$-Collection は次のようにする。$`L_\Theta \models \forall x \in a\ \exists y\ \delta(x,y,p)`$
（$`\delta \in \Delta_0`$）とする。補題 16.1 により $`a`$ は外部で可算である。各 $`x \in a`$ に対して
$`\lt_L`$-最小証人 $`y_x`$ を取り、その $`L`$-階数全体の上限を取る。$`\omega_1^V`$ の正則性から
上限は $`\Theta`$ 未満であり、全証人を含む 1 つの $`L_\rho \in L_\Theta`$ が Collection 集合になる。

次に $`\Lambda`$ を作る。$`(L_\Theta, \in)`$ の全一階式に対する $`\lt_L`$-最小 Skolem 関数を
外部で固定する。可算な $`\gamma \lt \Theta`$ に対し、$`L_\gamma`$ の有限パラメータへ全 Skolem 関数を
適用した値全体は可算である。従って、それらを含む $`L_{h(\gamma)}`$ をある $`h(\gamma) \lt \Theta`$ に
対して取れる。可算極限 $`\gamma_0 \gt \omega`$ から始め

```math
\gamma_{s+1} \gt \max\{\gamma_s,\ h(\gamma_s)\}
```

となる可算極限を順に取り、$`\Lambda = \sup_{s \lt \omega} \gamma_s`$ と置く。

$`L_\Lambda`$ の有限パラメータはある $`L_{\gamma_s}`$ に含まれ、その Skolem 値は
$`L_{h(\gamma_s)} \subseteq L_{\gamma_{s+1}} \subseteq L_\Lambda`$ に入る。
従って $`L_\Lambda`$ は全 Skolem 関数で閉じており、Tarski–Vaught test により
$`L_\Lambda \prec L_\Theta`$ である。完全な初等部分なので $`L_\Lambda \models \mathrm{KP}`$ でもある。
$`\square`$

### 2.4 (16.2)

$`L_\Lambda \prec L_\Theta`$ には交代数の制限が無いので、全ての $`k \in \mathbb{N}`$ について

```math
\Lambda \lhd_k \Theta . \tag{16.2}
```

これが安定ラベルの出発点になる（補題 20.1）。

## 3. 定理 17.1

### 3.1 主張

$`r, n \in \mathbb{N}`$、$`n \lt r`$ とする。$`\alpha, \beta`$ を許容順序数とし
$`\alpha \lhd_n \beta`$ とする。$`X \subseteq \alpha`$ を許容順序数からなる有限集合、

```math
Y = \{y_0 \lt \cdots \lt y_{s-1}\} \subseteq [\alpha, \beta)
```

を許容順序数からなる非空有限集合とする。このとき、許容順序数からなる集合

```math
Y' = \{y'_0 \lt \cdots \lt y'_{s-1}\} \subseteq \alpha
```

で次を満たすものが存在する。

```math
\max(X \cup \{\omega\}) \lt y'_0 \tag{17.1}
```
```math
x \lhd_k y_i \ \Longrightarrow\ x \lhd_k y'_i \qquad (x \in X,\ k \lt r) \tag{17.2}
```
```math
y_i \lhd_k y_j \ \Longrightarrow\ y'_i \lhd_k y'_j \qquad (i, j \lt s,\ k \lt r) \tag{17.3}
```
```math
y_i \lhd_m \beta \ \Longrightarrow\ y'_i \lhd_m \alpha \qquad (i \lt s,\ m \lt n) \tag{17.4}
```

**読み方.** $`[\alpha, \beta)`$ にある有限個の許容順序数 $`Y`$ を $`\alpha`$ 未満へ押し下げても、
$`\lhd`$ の関係が全部保たれる、ということである。

### 3.2 証明

$`L_\beta`$ の中で、変数 $`u_0, \dots, u_{s-1}`$ に次の有限個の条件を課す。

| 群 | 条件 |
|---|---|
| 1 | $`\mathrm{Adm}(u_i)`$、各 $`x \in X`$ に対する $`x \lt u_0`$、および $`\omega \lt u_0 \lt \cdots \lt u_{s-1}`$ |
| 2 | 外部で真である各 $`x \lhd_k y_i`$ に対する $`\mathrm{Rel}_k(x, u_i)`$ |
| 3 | 外部で真である各 $`y_i \lhd_k y_j`$ に対する $`\mathrm{Rel}_k(u_i, u_j)`$ |
| 4 | 外部で真である各 $`y_i \lhd_m \beta`$（$`m \lt n`$）に対する $`\mathrm{St}_m(u_i)`$ |

これらの有限連言を $`\Phi(\vec u)`$ とする。交代ブロックのノート 3.3 のとおり

```math
\exists u_0 \cdots \exists u_{s-1}\ \Phi(\vec u) \ \in\ \hat\Sigma_{n+2} . \tag{17.5}
```

$`L_\beta`$ では $`u_i = y_i`$ が証人である。補題 11.2、15.3、15.5 により、
$`L_\beta`$ は 4 群の条件を正しく認識する。仮定 $`L_\alpha \prec^*_{n+2} L_\beta`$ により
(17.5) は $`L_\alpha`$ でも真である。その証人を $`y'_0, \dots, y'_{s-1}`$ とする。

あとは読み取るだけである。

| 得るもの | 根拠 |
|---|---|
| 各 $`y'_i`$ は外部でも許容順序数 | $`L_\alpha \models \mathrm{Adm}(y'_i)`$ と補題 11.2 |
| $`y'_i \lt \alpha`$ | $`y'_i \in L_\alpha \cap \mathrm{Ord} = \alpha`$（構成可能階層のノート §9） |
| (17.1) | 第 1 群の順序条件 |
| (17.2), (17.3) | $`L_\alpha`$ 内の $`\mathrm{Rel}_k`$ 条件と補題 15.5(2) |
| (17.4) | $`L_\alpha \models \mathrm{St}_m(y'_i)`$ と補題 15.3 |

$`\square`$

### 3.3 なぜ第 4 群だけ St か

第 2 群と第 3 群は $`\mathrm{Rel}_k`$、第 4 群だけ $`\mathrm{St}_m`$ を使う。理由は $`\beta`$ の扱いにある。

$`\mathrm{Rel}_m(u_i, \beta)`$ と書きたいところだが、書けない。
$`L_\beta \cap \mathrm{Ord} = \beta`$ なので $`\beta \notin L_\beta`$ であり、
$`\beta`$ は $`L_\beta`$ の中で名前を持たないからである。

$`\mathrm{St}_m(u_i)`$ は「$`u_i \lhd_m`$ いま居る宇宙」という意味だった（1.3）。だから

```
L_β の中で読むと    y_i ◁_m β
L_α の中で読むと    y'_i ◁_m α
```

となる。同じ 1 本の式が、居る場所によって相手を取り替える。これが (17.4) の押し下げの正体である。

### 3.4 n < r の役割

複雑度の計算に効くのは第 4 群だけである。

- 第 2 群と第 3 群の $`k`$ は $`k \lt r`$ を走るが、$`\mathrm{Rel}_k`$ は $`k`$ によらず
  $`\hat\Sigma_1`$ である（1.4）。だから $`r`$ がいくら大きくても複雑度は上がらない
- 第 4 群の $`\mathrm{St}_m`$ は $`\hat\Pi_{m+2}`$ で、$`m \lt n`$ なので $`\hat\Pi_{n+1}`$ に収まる

その結果 (17.5) が $`\hat\Sigma_{n+2}`$ になり、仮定 $`\alpha \lhd_n \beta`$ とちょうど噛み合う。
$`n \lt r`$ は、命題 19.1 で $`n = m_0`$（最大親行）、$`r`$ を行数として使うための条件である。

### 3.5 命題 19.1 での使い方

一回の展開で高さが下がることを示す帰納段で、次のように当てる（原文 §19）。

```
n = m_0        最大親行
α = f(p)       m_0-親の位置のラベル
β = f(c)       最後の列のラベル
X              コピー区間より前にある列のラベル全体
Y              コピー区間のラベル y_0 < … < y_{s-1}
```

$`p \prec^A_{m_0} c`$ と安定ラベルの条件から $`\alpha \lhd_{m_0} \beta`$ が出るので、
定理 17.1 を適用できる。得られた $`Y'`$ で旧コピーのラベルを置き換えると、
新しいコピーに元の $`y_i`$ を割り当て直せる。

## 4. 原文での使われ方

| 場所 | 使い方 |
|---|---|
| 定義 11.1、補題 11.2 | $`\mathrm{Adm}`$ とその正しさ |
| 定義 15.2、補題 15.3 | $`\mathrm{St}_k`$ とその正しさ |
| 定義 15.4、補題 15.5 | $`\mathrm{Rel}_k`$ とその正しさ |
| 補題 16.1 | $`\gamma \lt \omega_1^V`$ なら $`L_\gamma`$ は可算 |
| 補題 16.2、(16.2) | 初期対 $`\Lambda \lhd_k \Theta`$ |
| 定理 17.1 | 有限行反映 |
| 補題 20.1 | (16.2) を使って $`E_r`$ の安定ラベルを作る |
| 命題 19.1 | 定理 17.1 を $`n = m_0`$ で使い、高さを下げる |

## 5. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 定義 11.1 の $`\mathrm{KPTrue}`$ | `KPTrue` | `Bm4/SetTheory/AdmKP.lean` |
| 定義 11.1 の $`\mathrm{Adm}`$ | `AdmKP` | 同上 |
| $`\mathrm{KPAx}`$ | `KPAxCode` | `Bm4/SetTheory/KPAx.lean` |
| $`\mathrm{Adm} \in \hat\Sigma_1`$ | `sigmaDef_admKP` | `Bm4/SetTheory/AdmKP.lean` |
| 補題 11.2 | `admKP_iff` | 同上 |
| 定義 15.2 の $`\mathrm{St}_k`$ | `StKP` | `Bm4/SetTheory/StKP.lean` |
| $`\mathrm{St}_k \in \hat\Pi_{k+2}`$ | `piDef_StKP` | 同上 |
| 補題 15.3 | `stKP_iff` | 同上 |
| 定義 15.4 の $`\mathrm{Rel}_k`$ | `RelKP` | 同上 |
| $`\mathrm{Rel}_k \in \hat\Sigma_1`$ | `sigmaDef_RelKP` | 同上 |
| 補題 15.5(2) | `relKP_iff` | 同上 |
| 補題 15.5(1) | `relKP_iff_ext` | 同上 |
| 補題 16.1 | `L_countable` | `Bm4/SetTheory/Omega1.lean` |
| $`\omega_1`$ が許容順序数 | `isAdmissible_omega1` | 同上 |
| Skolem 包 | `Bm4/SetTheory/Skolem.lean` | 同上 |
| 補題 16.2 | `exists_admissible_elemFull_pair` | `Bm4/SetTheory/AdmTrans.lean` |
| (16.2) | `exists_relAdm_all` | `Bm4/SetTheory/Stable.lean` |
| 定理 17.1 | `reflect_pattern` | `Bm4/SetTheory/Reflect.lean` |
| (17.5) の複雑度計算 | `sigmaDef_blk`、`sigmaDef_bigAnd`、`PiDef.toSigma` | 同上 |
