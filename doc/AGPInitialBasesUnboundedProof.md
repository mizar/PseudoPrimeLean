# AGP の定理：任意の初期底を通過するカーマイケル数

Alford–Granville–Pomerance（AGP）の構成に基づく、次の存在定理を説明する。

> **調べる底を $1,2,\ldots,B$ のどこまで増やしても、そのすべての強い Miller–Rabin テストを
> 通過するカーマイケル数が、いくらでも大きく存在する。**

カーマイケル数は合成数なので、これは「有限個の底での通過」だけでは、
大きさを制限しないすべての整数について素数性を保証できないことを意味する。
証明では、条件を満たす素数を多数集め、その中から適切な素数を選んで掛け合わせる。

**数学的な流れを知りたい場合**は、[定理と用語](#statement)、[具体例](#example)、
[証明の5段階](#proof)を読むとよい。
**Lean の前提と結論を確認したい場合**は、[宣言の入口](#lean-entry)から入り、
各段階の「Lean で確認する」欄へ進める。
解析的な素数供給と有限群の議論は、後半の[専門向け補足](#analytic)に分けた。

以下のファイル名はリポジトリのルートを基準とし、宣言へのリンクには対象版の行番号を付けた。
ソースの更新で行が移動した場合は、併記した宣言名で検索できる。

<a id="statement"></a>
## 1. 何を証明するのか

### 1.1 二つの数を先に指定する

まず、自然数 $B,C$ を任意に指定する。
$B$ は**調べる底の値の上限**、$C$ は**見つけたい数の大きさの下限**である。

そのとき、次の条件を同時に満たす自然数 $a$ が存在する。

$$
\boxed{
\begin{gathered}
a > C,\\
a\text{ はカーマイケル数},\\
\text{底 }1,2,\ldots,B\text{ のすべてで強いテストを通過する。}
\end{gathered}
}
$$

$B$ は「最初の $B$ 個の素数」という意味ではない。
例えば $B=10$ なら、$2,3,5,7$ だけでなく、$1,4,6,8,9,10$ も対象になる。
また、**一つの $a$ がすべての指定底を通過する**のであり、底ごとに別の数を選ぶわけではない。

$B$ を固定しても $C$ はいくらでも大きくできる。
したがって、その初期底をすべて通過するカーマイケル数は無限に存在する。
ただし、$B$ を増やしたときには別の $a$ を選んでよく、
「一つの合成数が、すべての正整数底を通過する」という主張ではない。

底ごとの通過条件を $\operatorname{MRPass}(a,b)$ と書けば、定理は

$$
\begin{aligned}
\forall B,C\in\mathbb{N},\quad\exists a\in\mathbb{N}:\quad
&a > C\ \land\ \operatorname{Carmichael}(a)\\
&\land\ \forall b\in\{1,\ldots,B\},\ \operatorname{MRPass}(a,b).
\end{aligned}
$$

と表せる。$B,C$ の間に大小関係は要求しない。
$B=0$ では調べる底が空になるが、$C$ を超えるカーマイケル数の存在は依然として要求される。

<details>
<summary>Lean で確認する：命題の定義と量化の順序</summary>

**定義の場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBases.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBases.lean#L44)

名前空間は `PseudoPrime.PrimeTest.MillerRabin.AGP` である。

```lean
def AGPInitialBasesUnbounded : Prop :=
  ∀ B C : ℕ,
    ∃ a : ℕ,
      C < a ∧
        Nat.IsCarmichael a ∧
          ∀ b : ℕ,
            0 < b →
              b ≤ B →
                let (s, d) := Nat.maxPowDvdDiv 2 (a - 1)
                (b : ZMod a) ^ d = 1 ∨ ∃ j < s, (b : ZMod a) ^ (2 ^ j * d) = -1
```

`∀ B C` の後に `∃ a` があり、その後に `∀ b` がある。
つまり、$a$ は $B,C$ に応じて選べるが、対象の底 $b$ ごとに選び直すことはできない。

`def ... : Prop` は**証明する命題に名前を付ける定義**であり、証明そのものではない。
その証明を与えるのが、[第5節](#lean-entry)の `agp_initial_bases_unbounded` である。

</details>

### 1.2 強い Miller–Rabin テストの通過条件

「底」は、検査に使うべき乗の底 $b$ を指す。素数かどうかを調べる数 $a$ とは別の数である。
奇数 $a > 1$ に対して、$a-1$ から因子 $2$ を取り除き、

$$
a-1=2^s d,\qquad d\text{ は奇数}
$$

と書く。底 $b$ で通過する条件は、次のいずれかである。

$$
b^d\equiv1\pmod a,
$$

または、**$0\le j < s$ を満たすある整数 $j$ について**

$$
b^{2^j d}\equiv-1\pmod a
$$

が成り立つことである。$j=0$ も許されるため、最初の $b^d$ が $-1$ に合同でも通過する。
ここで $x\equiv y\pmod a$ は、$x,y$ を $a$ で割った余りが等しいことを表す。

合成数でありながらこの条件を満たす数を、その底に対する**強擬素数**という。
通過したことだけで、素数と確定するわけではない。

<details>
<summary>Lean で確認する：通過述語、指数の分解、実行可能な判定との対応</summary>

**定義の場所：** [`PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean`](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean#L37)

名前空間は `PseudoPrime.PrimeTest` である。

```lean
def StrongMillerRabinPass (n : ℕ) (x : ZMod n) : Prop :=
  x ^ Nat.divMaxPow (n - 1) 2 = 1 ∨
    ∃ j : ℕ, j < padicValNat 2 (n - 1) ∧ x ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1
```

`padicValNat 2 (a - 1)` が $s$、`Nat.divMaxPow (a - 1) 2` が $d$ に対応する。
`Nat.maxPowDvdDiv 2 (a - 1)` は同じ二つを組として扱う表記である。
`ZMod a` の等式は、法 $a$ の合同式を表す。

`StrongMillerRabinPass` 自体は奇数性や合成数性を含まない。
本稿では、それらを別途確認した数に適用している。
実行可能な単一底テストとの対応は、同ファイルの
`strongMillerRabinWithBase_eq_true_iff_pass` で確認できる。

明示的な分解を含む主命題と、`StrongMillerRabinPass` を使う表記の対応は、
[`PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBasesIff.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBasesIff.lean#L50) の
`agpInitialBasesUnbounded_iff` である。証明は `rfl` であり、定義を展開すると一致する。
これは、初期整数底の命題と有限素数底の命題との同値を述べるものではない。

</details>

### 1.3 カーマイケル数と Korselt の判定条件

**カーマイケル数**とは、合成数 $a$ であり、$a$ と互いに素なすべての整数 $b$ に対して

$$
\gcd(a,b)=1\quad\Longrightarrow\quad b^{a-1}\equiv1\pmod a
$$

を満たす数である。「互いに素」とは、共通の正の約数が $1$ だけという意味である。
素数に対するフェルマーの小定理と同じ合同式を、合成数なのに満たす点が特徴となる。

証明では、これと同値な **Korselt の判定条件**を使う。自然数 $a$ がカーマイケル数であることは、
次の三条件と同値である。

1. $a$ は合成数である。
2. $a$ は平方自由である。すなわち、素因数分解に同じ素数が2回以上現れない。
3. $a$ の任意の素因数 $p$ について $p-1\mid a-1$、すなわち **$p-1$ は $a-1$ の約数である**。

この形なら、「相異なる素数を掛け合わせ、各素因数で3番目の条件を確認する」という方法で
カーマイケル数を構成できる。

ただし、カーマイケル数であることだけでは強い Miller–Rabin テストの通過は保証されない。
本証明では、各素因数における累乗の値も揃える。
そのために使うのが、[第4.2節](#signatures)のルジャンドル記号である。

<details>
<summary>Lean で確認する：Korselt 条件への接続</summary>

**構成をまとめる場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/CarmichaelConstruction.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/CarmichaelConstruction.lean#L43)

`isCarmichael_finset_prime_product` の型は次のとおりである。以下は証明本体を省いた抜粋である。

```lean
theorem isCarmichael_finset_prime_product {S : Finset ℕ} {K : ℕ} (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcard : 2 ≤ S.card) (horder : ∀ p ∈ S, p - 1 ∣ K) (hproductMod : K ∣ (∏ p ∈ S, p) - 1) :
    Nat.IsCarmichael (∏ p ∈ S, p)
```

**前提：** `S` は相異なる素数の有限集合で2要素以上を持ち、
各 $p-1$ は共通の整数 $K$ の約数で、$K$ は積から $1$ を引いた数の約数である。

**結論：** `S` の要素の積はカーマイケル数である。

証明内部で `Nat.isCarmichael_iff_korselt` を使う。
mathlib 側で要求される $2 < a$ などの条件も、積の性質からここで確認している。

</details>

<a id="example"></a>
## 2. 一つの数で確かめる

定理の意味と通過の仕組みは、次の例で見ることができる。

$$
a=3215031751=151\cdot751\cdot28351.
$$

三つは相異なる素数であり、

$$
a-1=3215031750=2\cdot1607515875
$$

は $150,750,28350$ のそれぞれで割り切れる。
したがって Korselt の判定条件を満たし、$a$ はカーマイケル数である。

$d=1607515875$ とすると、剰余累乗は次のようになる。

| 底 $b$ | $b^d\bmod a$ | 通過条件 |
|---|---:|---|
| $1,2,4,5,8,9,10$ | $1$ | 第一の条件 |
| $3,6,7$ | $3215031750=a-1$ | 第二の条件、$j=0$ |
| $11$ | $2129160099$ | どちらも満たさない |

この数は、例えば $B=10$、$C=10^9$ に対する証人になる。
一方、底 $11$ では通過しない。ここでは $s=1$ なので、第二の条件に使える $j$ は $0$ だけである。

この具体例は、任意の $B,C$ に対する存在証明の代わりではない。
また、この三素数だけで後述する解析的な個数条件を満たす、と主張するものでもない。

<details>
<summary>具体例の計算の内訳</summary>

| 素因数 $p$ | $p\bmod4$ | $(a-1)/(p-1)$ |
|---|---:|---:|
| $151$ | $3$ | $21433545$ |
| $751$ | $3$ | $4286709$ |
| $28351$ | $3$ | $113405$ |

各底 $1,\ldots,10$ について、三つの素因数におけるルジャンドル記号は一致する。
底 $1,2,4,5,8,9,10$ ではすべて $1$、底 $3,6,7$ ではすべて $-1$ である。
底 $11$ では $(1,-1,-1)$ となり、一致しない。

これが、[第4.5節](#mr-proof)で説明する「素因数ごとの同じ符号を、積全体へまとめる」仕組みの具体例である。
表は合同式の数値例であり、各項の最小性を証明する計算ではない。

</details>

<a id="proof"></a>
## 3. 証明の見取り図

固定した $B,C$ に対し、調べる底の集合を $W=\{1,\ldots,B\}$ とする。
証明では、素数集合を

$$
P\supseteq Q\supseteq U
$$

と順に絞り込み、最後に $a=\prod_{p\in U}p$ を作る。
各段階の目的は異なる。

| 段階 | 何をするか | 次の段階に渡すもの |
|---|---|---|
| 1. 素数の供給 | 共通の算術条件を持つ素数を十分多数集める | 素数集合 $P$ と補助整数 $L,k$ |
| 2. 符号を揃える | 各底に対するルジャンドル記号が一致する素数を集める | 大きな部分集合 $Q$ |
| 3. 積を選ぶ | 法 $L$ で積が $1$ になる、2個以上の素数を選ぶ | 部分集合 $U$ |
| 4. カーマイケル性を確認 | 相異なる素数の積と Korselt 条件を使う | カーマイケル数 $a=\prod_{p\in U}p$ |
| 5. 強いテストの通過を確認 | 素因数ごとの共通符号を法 $a$ にまとめる | 全底で $b^d\equiv1$ または $-1\pmod a$ |

**解析的整数論が担うのは、主に第1段階の「十分多数集める」部分である。**
第2段階以降では、鳩の巣原理、有限アーベル群、合同式、二次剰余の性質を組み合わせる。
最後の数が $C$ を超えることは、最初から各素数を $C$ より大きく取ることで保証する。

以下では各段階の理由を説明し、その直後に対応する Lean 宣言を置く。

## 4. 証明の5段階

<a id="prime-supply"></a>
### 4.1 条件の揃った素数を十分多数用意する

補助整数 $L,k$ と有限素数集合 $P$ を用意する。
各素数 $p\in P$ は、$L$ のある約数 $e_p$ を使って

$$
p=e_p k+1,\qquad e_p\mid L
$$

と書ける。ここで $e_p\mid L$ は、$e_p$ が $L$ の約数であることを表す。
**$k$ は素数ごとに変えず、すべての候補に共通に取る。**

さらに $k,L$ は互いに素で、各 $p$ は $L$ と互いに素、$p\equiv3\pmod4$、$p > C$ とする。
どの $p$ も対象の底 $b\in W$ の約数にならないようにする。

これらはそれぞれ、後の別々の仕事に使う条件である。
$p=e_pk+1$ は積の合同式を揃え、$p\equiv3\pmod4$ は強いテストで使う指数を揃える。
$p > C$ は積の下限を保証する。

難しいのは、この条件を満たす素数が単に存在するだけでなく、
**後で分類して一部を捨てても足りるほど多数存在する**ことを示す点である。
その個数を確保する解析的な議論は、[第6節](#analytic)で説明する。

<details>
<summary>Lean で確認する：素数供給の正確な仕様と個数条件</summary>

**仕様：** [`PseudoPrime/AnalyticNumberTheory/AGP/PrimeSupply.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/PrimeSupply.lean#L43)

```lean
def AGPProgressionPrimeSupply : Prop :=
  ∀ (W : Finset ℕ) (C : ℕ),
    (∀ b ∈ W, 0 < b) →
      ∃ (L k : ℕ) (P : Finset ℕ),
        2 < L ∧
          3 ≤ ArithmeticFunction.carmichael L ∧
          Nat.Coprime k L ∧
          (∀ p ∈ P,
            Nat.Prime p ∧
              Nat.Coprime p L ∧
              (∃ d, d ∣ L ∧ p = d * k + 1) ∧ p % 4 = 3 ∧ C < p ∧ ∀ b ∈ W, ¬p ∣ b) ∧
          2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) < P.card
```

**入力：** 正整数だけからなる有限底集合 `W` と、任意の下限 `C`。

**出力：** $L > 2$、$\lambda(L)\ge3$、$\gcd(k,L)=1$ を満たす $L,k$ と素数集合 $P$。
ここで $\lambda(L)$ は、法 $L$ の可逆な剰余類すべてについて
$g^{\lambda(L)}=1$ となる最小の正整数、すなわちカーマイケル関数である。
「$a$ がカーマイケル数である」という性質とは区別する。

個数条件は

$$
|P| > 2^{|W|}\left\lfloor\lambda(L)\log L\right\rfloor
$$

である。$|P|$ は集合の要素数、$\lfloor x\rfloor$ は $x$ 以下の最大の整数を表す。
$2^{|W|}$ は次段階の符号分類、残りの因子は有限群の部分積のために必要になる。

この仕様への変換は、同ファイルの
`agp_prime_supply_of_progression_count_data` が担う。
その入力 `AGPProgressionCountDataExists` と実際の存在証明は、[第6.1節](#count-data)にまとめた。

</details>

<a id="signatures"></a>
### 4.2 ルジャンドル記号の符号を揃える

奇素数 $p$ と、$p$ で割り切れない底 $b$ に対し、ルジャンドル記号
$\left(\frac bp\right)$ は次を表す。

$$
\left(\frac bp\right)=
\begin{cases}
1 & \text{法 }p\text{ で、ある数の二乗が }b\text{ に合同になるとき},\\
-1 & \text{そうならないとき}.
\end{cases}
$$

各 $p\in P$ に、底 $1,\ldots,B$ それぞれに対する符号を並べた「符号の列」を対応させる。
各欄は $1$ または $-1$ なので、列は高々 $2^{|W|}$ 通りしかない。

素数が十分多数あれば、鳩の巣原理により、同じ符号の列を持つ大きな部分集合 $Q\subseteq P$ が取れる。
つまり、各底 $b$ に対して符号 $\sigma_b\in\{1,-1\}$ が定まり、

$$
\left(\frac bp\right)=\sigma_b\qquad\text{すべての }p\in Q
$$

となる。

**揃えるのは、同じ底に対する、異なる素数での符号である。**
底 $2$ ではすべて $1$、底 $3$ ではすべて $-1$、という組合せでもよい。
すべての底の符号を同じにする必要はなく、あらかじめ符号の列を指定する必要もない。

<details>
<summary>Lean で確認する：鳩の巣原理の入力と出力</summary>

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean#L40)

`exists_large_common_legendre_signature_class` は、素数集合 $P$、有限底集合 $W$、自然数 $N$ に対し、
各素数が各底の約数でないことと $2^{|W|}N < |P|$ を仮定する。
結論は、$Q\subseteq P$、$N < |Q|$、および各底についてルジャンドル記号が素数間で一致することである。

適用時は

$$
N=\left\lfloor\lambda(L)\log L\right\rfloor
$$

と取る。$|Q|$ が整数なので、$N < |Q|$ から
$\lambda(L)\log L < |Q|$ が得られる。

実装は、底を添字とする `Bool` の列で分類する。
各記号が零でないという前提により、この分類から符号の等しさを回復できる。
ペアごとの等しさを一つの $\sigma_b$ にまとめる補題は、同ファイルの
`common_legendre_sign_of_pairwise_signatures` である。

</details>

<a id="subset-product"></a>
### 4.3 積が法 $L$ で $1$ になる素数を選ぶ

$Q$ の各素数は $L$ と互いに素なので、法 $L$ で逆数を持つ剰余類を定める。
法 $L$ で逆数を持つ剰余類全体は、乗法について有限アーベル群

$$
G=(\mathbb{Z}/L\mathbb{Z})^\times
$$

をなす。「アーベル」は、掛ける順序を入れ替えても結果が変わらないことを表す。
ここに、十分長い列から「積が $1$ になる部分」を選ぶ有限群の定理を適用する。
加法で表したときの名前は、**零和部分集合定理**である。

必要な結論は、

$$
U\subseteq Q,\qquad |U|\ge2,\qquad
\prod_{p\in U}p\equiv1\pmod L
$$

となる部分集合 $U$ の存在である。

ここで「非空」だけでは不十分である。一つの素数だけを選ぶと、積が合成数にならない。
本証明では、一要素だけで積が $1$ になる唯一の候補 $kL+1$ を先に除き、
残りに有限群の定理を適用する。第1段階の個数条件には、その一要素を除く余裕も含まれている。

<details>
<summary>Lean で確認する：2個以上を確保する理由と、有限群の個数条件</summary>

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/UnitSubsetProduct.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/UnitSubsetProduct.lean#L282)

中心となる宣言は `exists_two_or_more_unit_product_eq_one_of_progression` である。

**主な前提：** $L > 2$、$\lambda(L)\ge3$、$\gcd(k,L)=1$、
各候補が $L$ と互いに素で $p=e_pk+1$、$e_p\mid L$ と表せること、
および $|Q| > \lambda(L)\log L$。

**結論：** $U\subseteq Q\setminus\{kL+1\}$、$|U|\ge2$、法 $L$ での積が $1$。

一要素の例外を特定するのが `eq_exception_of_unit_eq_one_of_progression` である。
もし $p=e_pk+1\equiv1\pmod L$ なら $L\mid e_pk$。
$\gcd(k,L)=1$ より $L\mid e_p$ となり、$e_p\mid L$ と合わせて $e_p=L$、すなわち $p=kL+1$ である。

個数評価の中身も確認できる。$m=\lambda(L)$ とすると、有限群の定理に必要な長さは

$$
r=\left\lfloor m\log\frac Lm\right\rfloor+m
\le\left\lfloor m\log L\right\rfloor
$$

である。最後の不等式には $m\ge3$ を使う。
$|Q| > m\log L$ なら、一要素を除いても少なくともこの長さが残る。
この処理は `exists_nonempty_unit_product_eq_one_of_card_gt_carmichael_log_erase` にある。

異なる素数が法 $L$ で同じ剰余類になる場合も、元の素数のラベルは保持される。
像の集合を取って重複を消すのではない。
元の有限集合から各素数を一度ずつ選ぶため、次段階の平方自由性が保たれる。

零和定理そのものは、[`PseudoPrime/Combinatorics/Additive/FiniteAbelianZeroSum.lean`](../PseudoPrime/Combinatorics/Additive/FiniteAbelianZeroSum.lean#L1238) の
`exists_nonempty_zero_sum_label_subset_of_segmented_length`。
証明の仕組みは[第7節](#zero-sum)で補足する。

</details>

<a id="carmichael-proof"></a>
### 4.4 積がカーマイケル数になることを示す

$$
a=\prod_{p\in U}p
$$

と置く。$U$ は相異なる素数を2個以上含むため、$a$ は**平方自由な合成数**である。
あとは Korselt の整除条件を示せばよい。

各素数が $p=e_pk+1$ という形なので、その積は

$$
a\equiv1\pmod k
$$

を満たす。第3段階から $a\equiv1\pmod L$ も満たす。
したがって

$$
k\mid a-1,\qquad L\mid a-1
$$

であり、$k,L$ はともに $a-1$ の約数である。
さらに $\gcd(k,L)=1$ なので、

$$
kL\mid a-1,
$$

すなわち **$kL$ は $a-1$ の約数である**。

一方、$e_p\mid L$ と $p-1=e_pk$ から

$$
p-1\mid kL\mid a-1.
$$

よって、各素因数について **$p-1$ は $a-1$ の約数である**。
Korselt の三条件が揃い、$a$ はカーマイケル数となる。

> この接続には、法 $L$ の合同式だけでなく、**法 $k$ の合同式と $\gcd(k,L)=1$** も必要である。
> $p-1\mid kL$ と $L\mid a-1$ だけから結論を出しているのではない。

また、各素因数は $C$ より大きいので、積 $a$ も $C$ より大きい。
平方自由性は「相異なる素数を一度ずつ掛ける」ことから従い、
$p\equiv3\pmod4$ から従うわけではない。

<details>
<summary>Lean で確認する：合同条件から Korselt 条件への正確な橋渡し</summary>

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/CarmichaelConstruction.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/CarmichaelConstruction.lean#L136)

定理の型は次のとおりである。

```lean
theorem isCarmichael_finset_prime_product_of_progression_unit_product {S : Finset ℕ} (L k : ℕ)
    (hkL : Nat.Coprime k L) (hprime : ∀ p ∈ S, Nat.Prime p) (hcard : 2 ≤ S.card)
    (hprogression : ∀ p ∈ S, ∃ d, d ∣ L ∧ p = d * k + 1) (hproductL : (∏ p ∈ S, (p : ZMod L)) = 1) :
    Nat.IsCarmichael (∏ p ∈ S, p) ∧ (∀ p ∈ S, p - 1 ∣ k * L) ∧ k * L ∣ (∏ p ∈ S, p) - 1
```

注目する前提は `hkL`、`hprogression`、`hproductL` の三つである。
結論にはカーマイケル性だけでなく、
$\forall p\in U,\ p-1\mid kL$ と $kL\mid a-1$ も保持される。
これらは次の強いテストの証明でも使われる。

部分集合の選択からこの構成までをまとめるのが、
[`PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean#L140) の
`exists_carmichael_subset_of_progression_primes` である。

$a > C$ の確認は、[`PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean#L42) の
`agp_initial_bases_unbounded_of_prime_supply` 内にある。
$U$ の要素 $p$ を一つ取り、他の素数の積が正であることから
$C < p\le\prod_{q\in U}q$ と評価する。

</details>

<a id="mr-proof"></a>
### 4.5 すべての指定底で強いテストを通過させる

最後に、固定した一つの底 $b\in W$ を考える。
第2段階により、すべての $p\in U$ で

$$
\left(\frac bp\right)=\sigma_b\in\{1,-1\}
$$

となっている。

各 $p$ は $p\equiv3\pmod4$ なので、

$$
p-1=2u_p,\qquad u_p=\frac{p-1}{2}\text{ は奇数}
$$

と書ける。一方、$a-1=2^s d$ の $d$ も奇数である。
Korselt 条件 $p-1\mid a-1$ から $u_p\mid d$、すなわち $u_p$ は $d$ の約数となる。
したがって、ある奇数 $t_p$ を使って $d=u_pt_p$ と書ける。

Euler の規準により、

$$
b^{u_p}\equiv\left(\frac bp\right)=\sigma_b\pmod p.
$$

$1$ と $-1$ は奇数乗しても変わらないため、

$$
b^d=(b^{u_p})^{t_p}\equiv\sigma_b\pmod p
$$

となる。これが $a$ の**すべての素因数で、同じ符号について**成立する。
$a$ は相異なる素数の積なので、これらをまとめて

$$
\boxed{b^d\equiv\sigma_b\pmod a}
$$

を得る。

$\sigma_b=1$ なら第一の通過条件、$\sigma_b=-1$ なら第二の条件を **$j=0$** で満たす。
$a > 1$ は奇数なので $s\ge1$ であり、$j=0$ は許される範囲に入っている。
$b$ は任意だったから、すべての底 $1,\ldots,B$ で通過する。

こうして、$a > C$、カーマイケル性、すべての初期底での通過性が、一つの $a$ について揃う。

<details>
<summary>Lean で確認する：局所的な累乗、平方自由性、通過条件への接続</summary>

**中心となる場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/LocalLegendreCriterion.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/LocalLegendreCriterion.lean#L185)

局所条件をまとめた `strongMillerRabinPass_of_common_legendre_sign` の型は次のとおりである。

```lean
theorem strongMillerRabinPass_of_common_legendre_sign {n b : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnSquarefree : Squarefree n) (hn0 : n ≠ 0) (hb : 0 < b)
    (hpMod : ∀ p : ℕ, Nat.Prime p → p ∣ n → p % 4 = 3)
    (hpK : ∀ p : ℕ, Nat.Prime p → p ∣ n → p - 1 ∣ n - 1)
    (hbp : ∀ p : ℕ, Nat.Prime p → p ∣ n → ¬p ∣ b) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hleg : ∀ p : ℕ, (hp : Nat.Prime p) → p ∣ n → @legendreSym p ⟨hp⟩ b = σ) :
    PrimeTest.StrongMillerRabinPass n (b : ZMod n)
```

**前提：** 奇数 $a > 1$ の平方自由性、正の底 $b$、各素因数での $3\bmod4$ 条件と Korselt 条件、
底が各素因数で割り切れないこと、ルジャンドル記号が共通の $\sigma\in\{1,-1\}$ に等しいこと。

**結論：** 底 $b$ で `StrongMillerRabinPass` が成立する。

同ファイル内の分担は次のとおりである。

| 宣言 | 確認できる内容 |
|---|---|
| `residual_power_eq_legendre_at_prime` | 素因数 $p$ ごとに、$b^d$ がルジャンドル記号に等しい |
| `residual_power_eq_sign_of_squarefree` | 同じ符号を、各素因数の法から積全体の法へまとめる |
| `strongMillerRabinPass_of_residual_power_eq_sign` | $b^d=1$ または $-1$ から通過条件へ進む。負符号では実際に $j=0$ を選ぶ |

素因数ごとの合同式をまとめる部分は、中国剰余定理と同じ内容を使うが、
実装では環の同型を組み立てず、平方自由な数の整除性を用いている。

指数の奇数部分の関係は、[`PseudoPrime/PrimeTest/MillerRabin/KorseltCanonicalSign.lean`](../PseudoPrime/PrimeTest/MillerRabin/KorseltCanonicalSign.lean#L25) の `odd_part_korselt`。
Euler の規準を奇数乗へ拡張する部分は、
[`PseudoPrime/PrimeTest/MillerRabin/LocalLegendrePowers.lean`](../PseudoPrime/PrimeTest/MillerRabin/LocalLegendrePowers.lean#L27) の `pow_half_mul_odd_eq_legendre` である。

必要なのは各素因数の $v_2(p-1)=1$ であり、積全体の $v_2(a-1)=1$ ではない。
$a\equiv1\pmod4$ でも、$j=0$ による同じ議論を使える。

</details>

<a id="lean-entry"></a>
## 5. Lean の証明を確認する入口

### 5.1 まず公開定理を見る

**対象ファイル：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean#L117)

完全修飾名は
`PseudoPrime.PrimeTest.MillerRabin.AGP.agp_initial_bases_unbounded` である。
公開定理の本体は短い。

```lean
theorem agp_initial_bases_unbounded :
    AGPInitialBasesUnbounded :=
  agp_initial_bases_unbounded_of_progression_count_data
    AnalyticNumberTheory.AGP.agp_progression_count_data_exists_unconditional
```

これは、計数データの存在証明を、そのデータから主命題を導く定理へ渡している。
短い証明項の中にすべての数学が書かれているのではなく、次の接続をたどる構造である。

```text
計数データの存在
  agp_progression_count_data_exists_unconditional
    ↓
素数供給への変換
  agp_prime_supply_of_progression_count_data
    ↓
初期底と下限への適用
  agp_initial_bases_unbounded_of_prime_supply
    └─ 有限構成を呼び出す
       exists_carmichael_strongMillerRabin_pass_all_of_large_progression_primes
    ↓
主命題 AGPInitialBasesUnbounded
```

### 5.2 どの宣言の前提を読めばよいか

| 確認したいこと | 最初に読む宣言 | 本文の対応箇所 |
|---|---|---|
| 最終的に何を述べているか | `AGPInitialBasesUnbounded` | [1.1](#statement) |
| 解析部分から何を受け取るか | `AGPProgressionPrimeSupply` | [4.1](#prime-supply) |
| 有限構成全体に何が必要か | `exists_carmichael_strongMillerRabin_pass_all_of_large_progression_primes` | この節の次の折り畳み欄 |
| 合成数であることをどう保証するか | `exists_two_or_more_unit_product_eq_one_of_progression` | [4.3](#subset-product) |
| Korselt 条件の整除性をどう作るか | `isCarmichael_finset_prime_product_of_progression_unit_product` | [4.4](#carmichael-proof) |
| 共通符号から強い通過条件がどう従うか | `strongMillerRabinPass_of_common_legendre_sign` | [4.5](#mr-proof) |
| 計数データの存在を何から導くか | `agp_progression_count_data_exists_unconditional` | [6.1](#count-data) |

<details>
<summary>有限構成全体の定理型：供給された素数から何を取り出すか</summary>

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/LegendreSignature.lean#L256)

```lean
theorem exists_carmichael_strongMillerRabin_pass_all_of_large_progression_primes (L : ℕ) [NeZero L]
    (hL : 2 < L) (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    [NeZero (ArithmeticFunction.carmichael L)] (W P : Finset ℕ) (k : ℕ) (hkL : Nat.Coprime k L)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hcoprime : ∀ p ∈ P, Nat.Coprime p L)
    (hprogression : ∀ p ∈ P, ∃ d, d ∣ L ∧ p = d * k + 1) (hpMod : ∀ p ∈ P, p % 4 = 3)
    (hbase : ∀ b ∈ W, 0 < b) (hnotdiv : ∀ p ∈ P, ∀ b ∈ W, ¬p ∣ b)
    (hsize : 2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P ∧
        2 ≤ U.card ∧
        Nat.IsCarmichael (∏ p ∈ U, p) ∧
        ∀ b ∈ W, PrimeTest.StrongMillerRabinPass (∏ p ∈ U, p) (b : ZMod (∏ p ∈ U, p))
```

この定理が、第4.2〜4.5節をまとめている。
`W` に含まれる底について素数性は要求せず、正であることだけを要求する。
したがって、合成数底も初めから同じ議論で扱っている。

結論の `U ⊆ P` と `2 ≤ U.card` は、外側で $a > C$ を示すときにも使う。
この有限構成の定理そのものには、下限 `C` は登場しない。

`[NeZero L]` と `[NeZero (ArithmeticFunction.carmichael L)]` は、法や群の指数が零でないことを
型クラスとして受け取る記述である。
呼出し側では `2 < L`、`3 ≤ ArithmeticFunction.carmichael L` から用意している。

</details>

<details>
<summary>外側の接続：初期底集合と大きさの下限をどう処理するか</summary>

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/InitialBasesUnbounded.lean#L42)

`agp_initial_bases_unbounded_of_prime_supply` の入力は
`hsupply : AGPProgressionPrimeSupply` であり、結論は `AGPInitialBasesUnbounded` である。
証明内部では、次の局所名を追うと要点が分かる。

| ソース中の位置・局所名 | 数学的な役割 |
|---|---|
| `let W := Finset.Icc 1 B`、`hWpos` | 初期底 $1,\ldots,B$ を有限集合にし、すべて正であると確認 |
| `hsupply W C hWpos` | $L,k,P$ とその全条件を取得 |
| `hNeZeroL`、`hNeZeroLambda` | 有限構成が要求する非零性の型クラスを用意 |
| `⟨U, hUP, hUcard, hUcar, hpass⟩` | 部分集合、要素数、カーマイケル性、全底での通過性を取得 |
| `refine ⟨∏ p ∈ U, p, ...⟩` | 積を存在命題の証人に選ぶ |
| `hpC` と続く `calc` | $C < p\le a$ により積の下限を確認 |
| `hbW` と `hpass b hbW` | $0 < b\le B$ を集合への所属に戻し、通過性を返す |

同ファイルの `agp_initial_bases_unbounded_of_progression_count_data` は、
計数データから素数供給へ変換して、この定理を適用する中継である。

途中の定理の前提を読むときは、それを**呼出し側のどの定理が満たしているか**も確認するとよい。
一部の説明コメントには構築途中の記述が残っているため、ここでは定理の型と実際の証明項を基準にしている。

</details>

<a id="analytic"></a>
## 6. 専門向け補足：素数を「十分多数」供給する部分

第4節の構成は、条件を満たす素数が十分あれば進む。
解析部分の仕事は、底の個数や要求された下限がどれほど大きくても、その入力を実際に用意することである。

単に「ある算術級数に素数が無限にある」だけでは、今回の有限構成には足りない。
共通の $L,k$ に対して、符号分類と部分積選択に必要な個数を同時に確保しなければならない。
対象版では、**算術級数の素数下界、補助法の構成、不要な候補の除去、有限平均**を組み合わせている。

<a id="count-data"></a>
### 6.1 有限構成に渡す計数データ

**データの定義：** [`PseudoPrime/AnalyticNumberTheory/AGP/ProgressionCountData.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ProgressionCountData.lean#L36)

`AGPProgressionCountData W C c₀ x₀` は、$L,k$、候補の上限 $x$、約数の上限 $y$、
小さい素数を除く閾値 $q$ と、それらの必要条件をまとめた構造体である。

**存在証明の入口：** [`PseudoPrime/AnalyticNumberTheory/AGP/UnconditionalProgressionCountData.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/UnconditionalProgressionCountData.lean#L21)

```lean
theorem agp_progression_count_data_exists_unconditional : AGPProgressionCountDataExists := by
  obtain ⟨J, D, Xtheta, hJ, hSupply⟩ := exists_unconditional_narrow_theta_supply
  exact agp_progression_count_data_exists_of_primorial_p2_and_theta_supply J D Xtheta hJ hSupply
```

最初の定理が算術級数の素数下界を与え、次の定理がそれを使って必要な計数データを組み立てる。
構造体を定義しただけでは存在証明にならず、この証明項がその値の存在を供給している。

<details>
<summary>計数データの正確な目標と、小さい素数を除いても個数が残る理由</summary>

$$
\mathcal{D}(L,y)=\{e\in\mathbb{N}:e\mid L,\ e\le y\},\qquad
H_W(L)=2^{|W|}\left\lfloor\lambda(L)\log L\right\rfloor
$$

と置く。$\mathcal{D}(L,y)$ は、$L$ の約数のうち $y$ 以下のものを集めた集合である。
計数データの `hlower` と `hProp15` は、

$$
\begin{aligned}
H_W(L)+q
&<\frac{c_0}{2\log x}|\mathcal{D}(L,y)|\\
&\le
\#\{e\in\mathcal{D}(L,y):
 ek+1\text{ は素数},\ ek+1\le x,\ ek+1\equiv3\pmod4\}
\end{aligned}
$$

を与える。係数の定義は、[`PseudoPrime/AnalyticNumberTheory/AGP/ReliableProp15.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ReliableProp15.lean#L35) の
`reliableProp15Coefficient` で、一般には $c_0/(\varphi(m)\log x)$、ここでは $m=4$ である。
$\varphi(m)$ は $m$ 以下で $m$ と互いに素な正整数の個数を表す。

主要な構造体フィールドは次のとおりである。

| フィールド | 確認する条件 |
|---|---|
| `hL`、`hSquarefree`、`hlambda` | $L > 2$、$L$ の平方自由性、$\lambda(L)\ge3$ |
| `hk`、`hcoprime` | $k > 0$、$\gcd(k,L)=1$ |
| `hCq` | $q\ge\max(C,\sup W)$ |
| `hfactor` | $L$ のすべての素因数は $q$ 以下 |
| `hProp15Input` | 約数範囲など、計数に必要な算術条件 |
| `hlower`、`hProp15` | 上の二段の個数評価 |

存在命題 `AGPProgressionCountDataExists` では、最初に共通定数 $c_0 > 0$、$x_0\ge2$ を選び、
**その後で任意の $W,C$** に対応するデータを取る。
さらに $X\ge2^{56}$、$x=X^5$、$q\le X$ となるスケールも要求する。

`agp_prime_supply_of_progression_count_data` は、この候補から $p\le q$ を除く。
$k > 0$ なので $e\mapsto ek+1$ は単射であり、除く候補は高々 $q$ 個。
元の下界に $q$ 個分の余裕があるため、残った $P$ は $|P| > H_W(L)$ を満たす。

残った $p > q$ は、$p > C$、$\gcd(p,L)=1$、そしてどの正の底 $b\in W$ の約数でもないことを、
同時に満たす。これが `AGPProgressionPrimeSupply` への接続である。

</details>

### 6.2 算術級数の素数下界を得る

**入口：** [`PseudoPrime/AnalyticNumberTheory/AGP/UnconditionalNarrowThetaSupply.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/UnconditionalNarrowThetaSupply.lean#L23)

`exists_unconditional_narrow_theta_supply` は、多数の法を同時に扱える素数下界を与える。
問題になる法を有限個の例外で管理し、それを避けた算術級数では、必要な大きさまでに十分な素数があると示す。

解析的な核心は、ディリクレ $L$ 関数の零点を族全体で数える評価にある。
この評価から例外の個数を制御し、明示公式を通じて素数の個数の下界に戻す。

<details>
<summary>素数下界の前提・量化順序と、零点密度からの接続</summary>

対数の重みを付けた素数計数を

$$
\theta(x;M,r)=
\sum_{\substack{p\le x\\p\text{ は素数}\\p\equiv r\pmod M}}\log p
$$

と書く。対応する定義は、[`PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean#L136) の `thetaInProgressionReal` である。

供給定理の量化順序は

$$
\exists J,D,X_\theta,\quad
\forall Z\ge X_\theta,\quad
\exists E_Z,\quad
\forall m,e,r\ \cdots
$$

であり、$J\ge2$、$|E_Z|\le D$ となる。
例外 $h\in E_Z$ は $h > 1$ かつ $4$ の約数でない。
次の条件を満たすとき、

$$
\begin{gathered}
m\in\{1,4\},\qquad e > 0,\qquad \gcd(e,m)=1,\\
M=em > 1,\qquad M^J\le Z,\qquad\gcd(r,M)=1,\\
\text{どの }h\in E_Z\text{ も }M\text{ の約数ではない},
\end{gathered}
$$

$$
\theta(eZ^3;M,r)\ge\frac{eZ^3}{2\varphi(M)}
$$

を得る。例外集合を法や剰余類より先に選ぶ点が、多数の約数を一度に扱うために重要である。

零点密度の入口は、
[`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyDensity.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyDensity.lean#L210) の
`exists_primitiveCharacterFamily_log_free_density` である。
ここでは、ある定数 $A_*,C_* > 0$ が存在し、整数 $R\ge2$、$1/2\le\sigma\le1$ に対して

$$
N_{\mathrm{fam}}(R,\sigma)\le C_*R^{A_*(1-\sigma)}
$$

を満たす。$N_{\mathrm{fam}}$ は、導手が $R$ 以下の原始非主指標について、
$\sigma\le\operatorname{Re}\rho\le1$、$|\operatorname{Im}\rho|\le R$ の範囲にある零点を、
解析的重複度を含めて数えたものである。

$\log R\ge2$ となる十分大きい $R$ で $\sigma=1-1/\log R$ とすると、
右辺は $C_*e^{A_*}$ になる。
これにより、実部が $1$ に近い零点を持つ導手を、スケールに依存しない個数の例外にまとめられる。
対応する個数評価は、
[`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyExceptionalConductors.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyExceptionalConductors.lean#L64) の
`exists_uniform_exceptionalFamilyConductors_card_bound` で確認できる。

例外を避けた零点和の評価は [`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyExceptionalWeightedGap.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyExceptionalWeightedGap.lean)、
素数下界への接続は [`PseudoPrime/AnalyticNumberTheory/AGP/UniformPolynomialThetaSupply.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/UniformPolynomialThetaSupply.lean#L50) の
`exists_uniform_polynomial_theta_supply` にある。
必要な法 $4$ を排除してしまわないため、導手 $4$ の寄与は別途扱う。
その評価は [`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyFullHalfScaleBudget.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyFullHalfScaleBudget.lean) にある。

最後の整数スケールへの変換は `exists_unconditional_narrow_theta_supply` が担い、
天井関数を使う高さ選択の評価は [`PseudoPrime/AnalyticNumberTheory/AGP/RoundedPolynomialHeight.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/RoundedPolynomialHeight.lean#L29) の
`rounded_polynomial_height_bounds` が担う。

</details>

### 6.3 補助法と共通係数を、二段階で構成する

**組立ての入口：** [`PseudoPrime/AnalyticNumberTheory/AGP/PrimorialProgressionCountData.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/PrimorialProgressionCountData.lean#L32)

対象版は、素数下界を二段階で利用する。

**一段目では、補助法 $L$ を作る。**
小さい素数の積から多数の約数を用意し、その約数を使った算術級数で素数を集める。
得られた素数のうち十分大きいものを掛け合わせて、約数が多く、
有限群で必要な量 $\lambda(L)\log L$ を制御しやすい $L$ を作る。

**二段目では、最終的な素因数の候補を作る。**
$L$ の約数 $e$ を使い、$p=ek+1\equiv3\pmod4$ となる素数を数える。
ただし $k$ が $L$ と共通因子を持つ候補は除く必要がある。
その候補数を篩法で上から抑え、除いた後も必要な個数が残ると示す。
最後に有限平均を使い、一つの共通係数 $k$ を選ぶ。

この二段構成が、[第4.1節](#prime-supply)で要求した算術条件と個数条件を同時に実現する。

<details>
<summary>専門向け：二段階のスケールと個数の余裕</summary>

一段目の入口は、[`PseudoPrime/AnalyticNumberTheory/AGP/PrimorialSeedCount.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/PrimorialSeedCount.lean#L901) の
`exists_primorial_seed_tail_modulus_of_count_margin` である。
全体のスケール選択は、
[`PseudoPrime/AnalyticNumberTheory/AGP/P2SeedScale.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/P2SeedScale.lean#L1056) の
`exists_p2_full_divisor_concentration_bound_above_with_seed_margin` にある。

十分大きい $u$ に対して

$$
z=2^u,\qquad N_0=\prod_{p\le z,\ p\text{ は素数}}p,\qquad X=N_0^J,\qquad q=X^5
$$

と取る。$N_0$ は小さい素数を重複なく掛けた数、すなわち primorial である。
法 $m=1$ の素数下界から、共通係数 $k_1$ に対し
$r=e k_1+1$、$e\mid N_0$ という形の相異なる素数を $t$ 個選ぶ。
この $k_1$ は、二段目の係数 $k$ とは異なる。

そのうち $r > 1024t$ のものの積を $L$ とする。
小さい素数を除いても十分な個数が残るように $t$ を選ぶことで、

$$
\omega(L)\ge t/2,\qquad
\sum_{r\text{ は }L\text{ の素因数}}\frac1r\le\frac1{1024},\qquad
\lambda(L)\le q^2,\qquad L\le q^t
$$

を確保する。$\omega(L)$ は相異なる素因数の個数である。

二段目では

$$
Y=(4qL)^J,\qquad x=Y^5,\qquad y=Y^2
$$

と取る。すべての $e\mid L$ で $(4e)^J\le Y$ となり、素数下界の適用範囲に入る。
また、$L$ の全約数が $y$ 以下になるので、

$$
|\mathcal{D}(L,y)|=2^{\omega(L)}\ge2^{\lfloor t/2\rfloor}.
$$

スケール選択は、これを使って

$$
2^{|W|}\left\lfloor\lambda(L)\log L\right\rfloor+q
<\frac{c_0}{2\log x}|\mathcal{D}(L,y)|
$$

を実現する。対応する評価は、同じ
`PseudoPrime/AnalyticNumberTheory/AGP/P2SeedScale.lean` の
`p2_full_divisor_hlower_of_boxed` である。
補助データの接続は [`PseudoPrime/AnalyticNumberTheory/AGP/PrimorialP2SeedBridge.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/PrimorialP2SeedBridge.lean) にある。

例外となる法を避けるときは、[`PseudoPrime/AnalyticNumberTheory/AGP/ExceptionalModuli.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ExceptionalModuli.lean#L393) の
`exceptionalFreePartForModulus` を使う。
高々 $D$ 個の素因数を除くことによる約数個数の損失を、高々 $2^D$ 倍として管理する。

さらに、$L$ の素因数 $r$ が $k$ の約数になると、候補 $p=ek+1$ は
法 $4er$ のより狭い算術級数に入る。
この不要な候補数を抑えるのが、
[`PseudoPrime/AnalyticNumberTheory/AGP/BrunTitchmarshSpecialization.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/BrunTitchmarshSpecialization.lean#L302) の `agp_coarse_sieve_bound` である。
対象版では、その係数 $640/3$ と上の逆数和 $1/1024$ を用い、残る個数の係数を

$$
\left(\frac12-10^{-6}\right)-\frac{640}{3}\cdot\frac1{1024}
=\frac7{24}-10^{-6} > \frac14
$$

と評価する。
係数計算は、[`PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean#L1465) の
`agp_fifth_power_average_coefficient_640_1024_value` と
`agp_fifth_power_average_coefficient_640_1024_gt_quarter` にある。

共通係数を $c_0=1/(128\cdot2^D)$ と選ぶため、
$16\cdot2^D c_0=1/8 < 1/4$ となり、例外による損失などを吸収する余裕が残る。
この余裕を使って有限平均を取り、$\gcd(k,L)=1$ を満たす一つの $k$ で必要な素数個数を得る。
最後にデータを組み立てる定義は、
[`PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ProgressionTheta.lean#L3624) の
`agpProgressionCountData_of_fifth_power_theta_and_brun_titchmarsh` である。

この二段構成では、狭い範囲への約数の集中を別途仮定するのではなく、
二段目で全約数を含む範囲を選んで、その個数を利用している。

</details>

<details>
<summary>さらに零点密度の証明を追う場合の入口</summary>

主定理の理解にはこの段階まで下る必要はないが、解析的な前提の由来を確認する場合は、
まず `exists_primitiveCharacterFamily_log_free_density` から依存先へ進む。

**零点数から平均二乗の下界へ：**
[`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/GeneralScaleIncidence.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/GeneralScaleIncidence.lean#L276) の
`exists_uniform_general_scale_occurrence_meanSquare_bound`。
零点の出現と重複度を保って、共通の族・高さ格子の計数へつなぐ部分である。

**同じ平均二乗の上界：**
[`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/HighPrimeIncidence.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/HighPrimeIncidence.lean#L822) の
`highPrimeFamilyGridMeanSquareSum_hybrid_bound`。
族全体の hybrid 大篩評価により上から抑える部分である。

**密度評価への合成：**
[`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/GeneralScaleDensity.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/GeneralScaleDensity.lean)、続いて [`PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyDensity.lean`](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/LogFreeDensity/FamilyDensity.lean)。
上の上下評価の比較と、適用範囲外での粗い評価を合わせる。

**明示公式の残りの誤差：**
[`PseudoPrime/AnalyticNumberTheory/AGP/ScalarThetaBudget.lean`](../PseudoPrime/AnalyticNumberTheory/AGP/ScalarThetaBudget.lean)。
主項以外の実数誤差項を吸収する評価を確認できる。

「ある指標の零点を抑える」ことと、「必要な指標族の総数を重複度込みで抑える」ことを
区別して読むと、有限群側へ渡す一様な個数評価の由来が分かる。

</details>

<a id="zero-sum"></a>
## 7. 専門向け補足：有限群の零和定理は何をしているか

第4.3節で使った定理は、「群が有限だから、どこかで同じ積が現れる」というだけの粗い議論ではない。
群の要素数全体ではなく、群の指数を使って必要な列の長さを抑えている。
この違いにより、素数供給に要求する個数を $\lambda(L)\log L$ という形にできる。

**入口：** [`PseudoPrime/Combinatorics/Additive/FiniteAbelianZeroSum.lean`](../PseudoPrime/Combinatorics/Additive/FiniteAbelianZeroSum.lean#L1238)

<details>
<summary>指標を使う零和証明の概要と対応宣言</summary>

有限アーベル群 $G$ を加法表記で考える。
$|G|\le L$、$3\le m\le L$、すべての $g\in G$ について $mg=0$ とする。
今回の適用では $G$ は法 $L$ の単元群を加法表記に直したもの、$m=\lambda(L)$ である。

群の複素指標 $\chi:G\to\mathbb{C}^\times$ は、各 $g$ に $m$ 乗根を対応させる。
固定した $g$ での指標値は高々 $m$ 通りなので、まだ処理していない指標の少なくとも $1/m$ は同じ値を取る。

各座標でその値を選び、対応する指標を処理済みにする。

$$
\ell=\left\lfloor m\log\frac Lm\right\rfloor+1
$$

個の座標を使うと、未処理の指標は $m$ 個未満になる。
残りを $m-1$ 座標で一つずつ処理でき、全長は

$$
\ell+(m-1)=\left\lfloor m\log\frac Lm\right\rfloor+m
$$

となる。

この処理で、各指標 $\chi$ について少なくとも一つの座標 $i$ で
$c_i=\chi(g_i)$ となる非零複素数 $c_i$ を選べる。
群環で

$$
F=\prod_i(c_i[0]-[g_i])
$$

と置くと、どの指標で評価しても一つの因子が零になり、フーリエ反転により $F=0$ となる。
一方、非空の零和部分集合がないなら、$[0]$ の係数は $\prod_i c_i\ne0$ になる。
これは矛盾なので、非空の零和部分集合が存在する。

同ファイルで、順に次の宣言を読むとよい。

| 宣言 | 役割 |
|---|---|
| `exists_greedy_character_prefix_residual_lt` | 前半の座標で未処理の指標を減らす |
| `exists_nonempty_zero_sum_of_log_prefix_and_tail` | 残りの指標も処理して零和部分集合を得る |
| `exists_nonempty_zero_sum_of_character_matches` | 指標と群環の議論による矛盾 |
| `log_length_with_tail_le_floor_log` | 必要な長さを評価する |
| `exists_nonempty_zero_sum_label_subset_of_segmented_length` | 元のラベルを保つ形で部分集合を返す |

</details>

<a id="consequences"></a>
## 8. 系：有限素数底と OEIS A006945

### 8.1 任意の有限素数底への特殊化

有限個の素数底の集合 $S$ を指定する。
その最大値以下の整数底をすべて通過する数を主定理で作れば、当然 $S$ のすべての底も通過する。
これが `AGPFinitePrimeBases` に対応する。

**場所：** [`PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBasesTheorem.lean`](../PseudoPrime/PrimeTest/MillerRabin/AGP/FiniteBasesTheorem.lean#L60)

公開定理は次の形である。

```lean
theorem agp_finite_prime_bases :
    AGPFinitePrimeBases :=
  agp_finite_prime_bases_of_initial agp_initial_bases_unbounded
```

同ファイルの `private theorem agp_finite_prime_bases_of_initial` が、
最大値を使う帰着を行う。実装では `B := S.sup id` として、主定理を $B,C=B$ に適用している。
空集合の場合にも `S.sup id = 0` で扱える。

この系は、初期整数底の主定理から**検査対象を素数底へ制限する**ものである。
「素数底で通過するから、その積を底にしても通過する」という議論は使っていない。

### 8.2 A006945 の候補と最小元

OEIS A006945 は、素数底 $2,3,5,7,\ldots$ を順に使うとき、
**最初の $m-1$ 個のテストをすべて通過する最小の奇合成数**を第 $m$ 項とする数列である。
初項は、通過条件をまだ課していない最小の奇合成数 $9$ となる。

Lean 側では $p_0=2,p_1=3,p_2=5,\ldots$ と0から添字を付け、
`A006945Candidate n a` を

$$
a > 1,\quad a\text{ は奇数かつ合成数},\quad
\forall k < n,\ \operatorname{MRPass}(a,p_k)
$$

という条件にしている。
さらに `IsA006945Term n a` は、$a$ がその候補集合の最小元であることを表す。

$$
\boxed{\texttt{IsA006945Term n a}\text{ は、OEIS の第 }n+1\text{ 項に対応する。}}
$$

**定義：** [`PseudoPrime/PrimeTest/MillerRabin/OEISA006945.lean`](../PseudoPrime/PrimeTest/MillerRabin/OEISA006945.lean#L19)

```lean
noncomputable def IsA006945Term (n a : ℕ) : Prop :=
  IsLeast {b : ℕ | A006945Candidate n b} a
```

`IsLeast` は、集合に属し、かつ集合のどの要素以下でもあるという意味である。
候補条件を共通の通過述語で表す同値は、
[`PseudoPrime/PrimeTest/MillerRabin/OEISA006945Iff.lean`](../PseudoPrime/PrimeTest/MillerRabin/OEISA006945Iff.lean#L18) の `a006945Candidate_iff` にある。

### 8.3 どの添字でも候補があり、最小元がある

最初の $n$ 個の素数からなる有限集合

$$
S_n=\{p_0,\ldots,p_{n-1}\}
$$

に `agp_finite_prime_bases` を適用する。
得られるカーマイケル数は奇合成数であり、$S_n$ の全底を通過するので、A006945 の候補になる。
したがって、候補集合はどの $n$ でも空でない。

自然数の空でない集合には最小元がある。
この整列性により、**A006945 の任意の項の存在**が従う。

**存在定理の場所：** [`PseudoPrime/PrimeTest/MillerRabin/OEISA006945Existence.lean`](../PseudoPrime/PrimeTest/MillerRabin/OEISA006945Existence.lean#L24)

```lean
theorem exists_a006945_candidate (n : ℕ) : ∃ a : ℕ, A006945Candidate n a :=
  exists_a006945_candidate_of_agp MillerRabin.AGP.agp_finite_prime_bases n
```

続く最小元の存在証明は、次のとおりである。

```lean
theorem exists_a006945_term (n : ℕ) : ∃ a : ℕ, IsA006945Term n a := by
  classical
  obtain ⟨a, ha⟩ := exists_a006945_candidate n
  let h : ∃ b : ℕ, A006945Candidate n b := ⟨a, ha⟩
  exact ⟨Nat.find h, Nat.isLeast_find h⟩
```

`Nat.find h` が候補集合の最小元を選び、`Nat.isLeast_find h` がその最小性を与える。
最小元の一意性も、二つの最小元を互いに比較すれば従う。
ただし、このファイルの `exists_a006945_term` が直接述べる型は `∃ a` であり、
`∃! a` という別の定理がここに宣言されているわけではない。

<details>
<summary>候補の存在証明で、どの前提がどの性質を与えるか</summary>

`exists_a006945_candidate_of_agp` の入力は
`hAGP : MillerRabin.AGP.AGPFinitePrimeBases` と添字 `n`。
結論は `∃ a, A006945Candidate n a` である。

| ソース中の項 | 役割 |
|---|---|
| `(Finset.range n).image (Nat.nth Nat.Prime)` | 最初の $n$ 個の素数の集合を作る |
| `Nat.prime_nth_prime` | 集合の各要素が素数であると確認 |
| `agpFinitePrimeBases_iff` | AGP 命題を共通の通過述語で使える表記に揃える |
| `haCarmichael.two_lt`、`.odd`、`.not_prime` | 得られた数が $1$ より大きい奇合成数であると確認 |
| `a006945Candidate_iff` | これらの条件を候補述語へまとめる |

存在証明で選んだ数はカーマイケル数だが、**最小候補がカーマイケル数であるとは限らない**。
最小化の対象には、条件を満たすすべての奇合成数が含まれるからである。
例えば `n = 0` の最小候補は $9$ であり、平方自由ではないためカーマイケル数ではない。

また、`IsA006945Term` の定義は最小元の性質を指定するだけで、その存在を保証するものではない。
候補の存在と自然数の整列性を接続する部分が、上の二つの存在定理である。

</details>

## 9. この定理が保証する範囲

固定した有限個の底だけを使う判定では、入力の大きさを制限しないすべての合成数を検出できない。
任意の有限正整数底集合についても、最大の底を $B$ とすれば同じ結論が得られる。

一方で、入力 $a$ の大きさに応じて検査する底を増やす方法や、
あらかじめ限定した入力範囲について十分な固定底集合を選ぶ方法は否定していない。
定理は $B$ を先に固定して、その $B$ に応じて $a$ を選ぶ命題だからである。

また、存在することと、実用的に見つけられることは別である。
主定理は最小の証人を返す計算手順や小さな探索上限を述べていない。
A006945 の各項の存在を証明することも、個々の項の数値を計算して最小性まで確定することとは区別される。

## 10. 参考文献とソースについて

この文書の証明構成と宣言名は、対象版の Lean ソースに沿っている。
一般向けの本文で省略した条件は、各段階の折り畳み欄から、実際の宣言型へたどれるようにした。

元文書にあった解析的な議論は、第6節の入口と詳細に整理している。
対象版の二段階の構成や篩の係数を、原論文の全補題と同じ順序・同じ定数の翻訳であるとは位置付けていない。

参考文献：W. R. Alford, Andrew Granville, Carl Pomerance,
*On the difficulty of finding reliable witnesses*,
Algorithmic Number Theory, ANTS-I, Lecture Notes in Computer Science 877 (1994), pp. 1–16。
[著者公開版](https://math.dartmouth.edu/~carlp/PDF/reliable.pdf)。
数列の定義・添字については [OEIS A006945](https://oeis.org/A006945) を参照。
