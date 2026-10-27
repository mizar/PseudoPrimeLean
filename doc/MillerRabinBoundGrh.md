# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

公開入口は [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean)。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` からも利用できる。


区間別の公開包絡線は [ImprovedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedIntervalSelection.lean) の `improvedSelectedEnvelope` である。GRHの下で、すべての奇合成数 $n > 1$ について、 `exists_prime_improvedSelected` と `exists_least_improvedSelected` が実際の素数証人と最小素数証人の上界を与える。平方自由性、素因数の個数、Fermat部分群指数に関する追加条件はない。

[ImprovedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedWitnessEnvelope.lean) の `improvedWitnessEnvelope` は、各候補を証明済みの適用条件でのみ使う最小値である。 `improved_eq_selected` が区間選択との一致を証明する。既存の `selectedWitnessEnvelope` とその公開定理も利用できる。

MRの最小素数証人の累積最大値について、既知の更新点を [3種類の最小素数証人の数表](WitnessRecords.md) に参考情報として掲載した。

## 共通の記号

$$
\mathbb N=\lbrace0,1,2,\ldots\rbrace,\qquad
\mathbb P=\lbrace p\in\mathbb N\mid p\text{ は素数}\rbrace.
$$

$\ln$ は自然対数を表す。整数入力 $n$ と底 $p$ は自然数とする。
GRHは、すべての原始複素Dirichlet指標のL関数について、非自明零点の実部が $1/2$ であるという仮定である。
Leanの定義は [Definition.lean](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) の
`PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis` に対応する。

## 証明した主張

前提と主張は次のとおりである。

$$
\mathrm{GRH},\qquad n\in\mathbb N,\qquad n > 1,\qquad n\equiv1\pmod2.
$$

$$
n \text{ が素数}
\iff
\text{すべての素数底 }p \le (\ln\mathrel{} n)^2\text{ が強 Miller–Rabin 条件を満たす}
$$

具体的には、一意な分解を

$$
n - 1 = 2^s d,\qquad s, d \in ℕ,\qquad d \text{ は奇数}
$$

と書く。底 $p$ に対する強 Miller–Rabin の合格条件は、次の冪合同条件である。

$$
p^d \equiv 1 \pmod n
\lor
\exists j \in ℕ,\quad j < s \land p^{2^j d} \equiv -1 \pmod n
$$

任意の自然数底 $a$ について、この条件を次のように略記する。

$$
\mathrm{StrongMRPass}(n,a)
\quad\Longleftrightarrow\quad
\left(a^d\equiv1\pmod n\right)
\lor\left(\exists j\in\mathbb N,\quad j < s\land a^{2^jd}\equiv-1\pmod n\right).
$$

以降、素数底証人とは、 $p\in\mathbb P$ かつ $\neg\mathrm{StrongMRPass}(n,p)$ を満たす底を指す。
この合格条件は、実行用判定 `strongMillerRabinWithBase n p` が `true` を返すことと同値である。対応する定理は [Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) の `strongMillerRabinWithBase_eq_true_iff_pass` である。

前提が $n > 1$ なので、合成数性についても次の同値が成り立つ。

$$
n \text{ が合成数}
\iff
\exists p \text{ 素数},\quad
p \le (\ln\mathrel{} n)^2
\land p^d \not\equiv 1 \pmod n
\land \forall j \in ℕ,\quad
j < s \Longrightarrow p^{2^j d} \not\equiv -1 \pmod n
$$

素数なら上界内のすべての素数底で合格することは、GRHなしに証明できる。逆に、これらの底での合格から素数性を導く向きに GRH を用いる。素数入力では、上界内の素数底は $p < n$ を満たし、 $n$ と互いに素になる。

Lean では、 $n - 1$ の 2 進付値 $s$ と奇数部分 $d$ をそれぞれ `padicValNat 2 (n - 1)` と `Nat.divMaxPow (n - 1) 2` として定義し、合同式を `ZMod n` の等式・不等式として表す。 GRHは前述の命題を仮定するものであり、GRH自体を証明したという主張ではない。

`prime_iff_millerRabin_for_all_primes_le_log_sq` の宣言部は次のとおりである。証明本体は省略している。

```lean
namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    (∀ p : ℕ, Nat.Prime p →
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 →
      ((p : ZMod n) ^ d = 1 ∨
        ∃ j : ℕ, j < s ∧
          (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 公開定理

以下の名前は `PseudoPrime.PrimeTestBounds.MillerRabin` 名前空間に属する。

| 宣言 | 内容 | ソース |
|---|---|---|
| `exists_prime_millerRabin_witness_le_log_sq` | 奇合成数に対する素数底の証人定理 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `prime_iff_millerRabin_for_all_primes_le_log_sq` | GRH の下で、上界内の全素数底の明示的な冪条件と素数性の同値 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq` | `exists_prime_millerRabin_witness_le_log_sq` と同じ冪不等式を述べる別名。定理名に `eq_false` を含むが、型は Boolean の `= false` を直接結論にはしない | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq_of_lt_3000` | GRH を仮定しない $1 < n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

### 1. 合格条件、単元性、素因数底

この節では $x\in\mathbb Z/n\mathbb Z$ を剰余環の元とする。Leanの `ZMod n` はこの剰余環を表す。
`PseudoPrime.PrimeTest.StrongMillerRabinPass n x` は、標準分解の奇数部分 $d$ と指数 $s$ を用いて $x^d = 1$ または、ある $j < s$ に対して $x^{2^j d} = -1$ という条件を定義する。合格すれば $x^{n - 1} = 1$ となり、 $n > 1$ のもとでは $x$ は単元となる。したがって素因数 $p \mid n$ を底にすると不合格になる。

[Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) の `strongMillerRabinPass_isUnit`、 `strongMillerRabinPass_not_of_prime_dvd` がこの性質を示す。同ファイルの `strongMillerRabinWithBase_eq_false_iff_not_pass` は、この合格条件の否定をBoolean 判定へ接続する。素数入力側では、対数上界から底の互いに素性を示し、素数法の受理定理と指定分解の接続を組み合わせて不合格条件と矛盾させる。この節の宣言は `PseudoPrime.PrimeTest` 名前空間に属する。

### 2. 合格底を含む真部分群

自然な埋め込みを $\iota_n:(\mathbb Z/n\mathbb Z)^\times\hookrightarrow\mathbb Z/n\mathbb Z$ とする。
単元とは乗法逆元を持つ剰余環の元であり、その全体が単元群をなす。
$H$ の像とは $\iota_n(H)$ を指す。

奇合成数 $n > 1$ に対して、単元群 $(ℤ/nℤ)^\times$ の真部分群 $H$ が存在し、合格するすべての剰余が $H$ の像に入ることを無条件に証明する。合格集合そのものを部分群と仮定する必要はない。

- 素数 $q$ について $q^2 \mid n$ となる場合は、 単元 $u\in(\mathbb Z/n\mathbb Z)^\times$ で $u^{n - 1} = 1$ を満たすもの全体からなる部分群を使う。法 $q^2$ の $1 + q$ を利用して、この部分群に属さない単元を構成する。
- 異なる素因数 $q,r$ がある場合は、 $q - 1 = 2^t c$、 $t,c\in\mathbb N$、 $c$ は奇数と分解し、 $E = 2^{t - 1} d\in\mathbb N$ と置く。ここで $d$ は $n-1$ の奇数部分である。 $u^E \in \lbrace 1, -1 \rbrace$ を満たす単元 $u$ の部分群を使う。法 $q$ と法 $r$ で異なる符号をとる冪を中国剰余定理（CRT）で構成し、真部分群であることを示す。

各部分群の構成は [WitnessSubgroup.lean](../PseudoPrime/PrimeTest/MillerRabin/WitnessSubgroup.lean)、合成数の分岐と結合は [Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) にある。公開定理 `PseudoPrime.PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass` が、S2 へ渡す真部分群と合格剰余の包含をまとめる。

### 3. 大きい範囲に S2 を適用

$n \ge 3000$ に対し、 $p < (\ln\mathrel{} n)^2$ を満たす素因数があれば、第 1 節の性質によりその $p$ を証人にする。そのような素因数がなければ、[LLS の S2](LLS.md) を第 2 節で構成した真部分群へ適用する。 S2 は $p \le (\ln\mathrel{} n)^2$ で剰余が $H$ の像に入らない素数を与えるため、その底は合格できない。

S2 の適用には $p < (\ln\mathrel{} n)^2$ を満たす素数 $p$ が $n$ を割らないことを用い、結論の証人には $p \le (\ln\mathrel{} n)^2$ を要求する。等号端点で証人が単元になるという追加仮定は用いない。これが `exists_prime_millerRabin_witness_le_log_sq_of_s2` の証明である。最終段階で `PseudoPrime.LLS.llsTheorem11S2_of_grh` により GRH から S2 を供給する。

### 4. 小さい範囲の有限証明

[Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) は、 $1 < n < 3000$ の奇合成数について、底 2 または底 3 で不合格になることを示す。底 2 での不合格を示す有限分類では 2047 を例外候補とし、2047 の底 3 での不合格を別途証明する。公開定理は `PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000`。

証明は自然数 $k$ による奇数の表示 $n = 2k + 1$、 $0 \le k < 1500$ を 256 要素の 5 ブロックと 220 要素の最終ブロックで被覆する。素数性と、明示分解・高速冪の不一致を Lean カーネルで検証し、検証器の健全性を通じて強 Miller–Rabin 判定へ移す。外部の整数探索結果を証明根拠には使わない。

奇合成数 $n > 1$ なら $n \ge 9$ なので $3 \le (\ln\mathrel{} n)^2$ が成立する。 [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) は対数評価を有限分類へ接続し、小範囲の素数証人定理を与える。有限分類だけを使う場合は `PseudoPrime.PrimeTest.MillerRabin.Computation.Small`、対数上界も使う場合は `PseudoPrime.PrimeTestBounds.MillerRabin.SmallLogBound` を import する。

## 証明依存

主定理、証人系、有限分類、小範囲の上界、真部分群の中心定理、利用した S2 定理の推移的公理依存は `propext`、 `Classical.choice`、 `Quot.sound` のみである。有限証明を含め、これらの定理に `sorry` や `native_decide` 由来の公理依存はない。確認例は次のとおり。

```lean
import PseudoPrime

namespace PseudoPrime.PrimeTestBounds.MillerRabin

#print axioms exists_prime_millerRabin_witness_le_log_sq
#print axioms PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 個別の上界と証明

以下では $L=\ln n$、 $q_{\mathrm{MR}}(n)$ を奇合成数 $n$ を棄却する最小の素数基数とする。有限区間の節を除きGRHを仮定する。各節は後の区間表に現れる順に並べている。

### 有限区間 $9\le n < 3000$ の上界

この範囲の奇合成数は $n < 2047$ では基数2で、 $2047\le n < 3000$ では基数2または基数3で不合格になる。後者の区間全体には上界3を使う。

$$
U_{\mathrm{small}}(n)=
\begin{cases}
2 & 9\le n < 2047,\\
3 & 2047\le n < 3000
\end{cases}
$$

GRHは不要である。 [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) の `smallIntervalBound`、 `exists_prime_smallInterval`、 `exists_least_smallInterval` がこの主張を表す。証明はLeanカーネルで検証した既存の有限分類を使う。2047は基数2で合格し基数3で不合格になるため、後者の区間の上界3にはこの例も含まれる。

### $L\le2877/250$ での固定上界61

リーマンゼータ側の逆数誤差に、点ごとの評価

$$
\ell(y)=\frac{78861}{50000}+\frac{231}{5000y}-\frac{16033}{9000y^2}
$$

を用いる。偶指標側の誤差項を保持し、半径 $y=1637/200$ の比較gapが $L\le2877/250=11.508$ で正になることを有理数評価で示す。 $y^2 < 67$ なので、得られた素数証人は67未満である。62から66の合成数性により、証人は61以下となる。入力 $n$ の列挙は行わない。

解析評価と原始導手から法 $n$ への移送は [EndpointPointwise.lean](../PseudoPrime/LLS/EndpointPointwise.lean)、実際のMR証人と最小証人の定理は [EndpointPointwise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwise.lean) の `exists_prime_endpointPointwise61`、 `exists_least_endpointPointwise61` にある。

### $L\le47/4$ での固定上界67

半径 $y=337/40$ の偶指標endpoint gapは、 $L\le47/4=11.75$ で正となる。 $y^2 < 71$ なので証人は71未満の素数であり、68から70の合成数性により67以下となる。 [EndpointFixed67.lean](../PseudoPrime/LLS/EndpointFixed67.lean) が正のgapを、 [EndpointFixed67.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFixed67.lean) の `exists_prime_endpoint67`、 `exists_least_endpoint67` が実際のMR証人と最小証人を与える。

### 偶endpoint gapの四段補正

補正関数を

$$
H(y)=\frac{N_H(y)}{18310000(y-1)((y+1)^2+2y\ln y)},
$$

$$
\begin{aligned}
N_H(y)={}&36620000y^3\ln y-56749471y^3+109860000y^2(\ln y)^2\\
&+73100099y^2\ln y+10777809y^2-73240000y(\ln y)^2\\
&-1528140y\ln y+2824690y-36620000(\ln y)^2\\
&-177204180\ln y-94877470
\end{aligned}
$$

とする。次の4つの半径を用いる。

$$
a(L)=\max\lbrace8,L-H(L)\rbrace,\qquad b(L)=L-H(a(L)),
$$

$$
c(L)=\max\lbrace8,L-H(b(L))\rbrace,\qquad d(L)=L-H(c(L)),\qquad C_4(L)=d(L)^2.
$$

$L\ge45/4$ では $a\le c < d\le b$ となり、半径 $d$ の比較gapが正になる。したがって、対数の上限なしに $q_{\mathrm{MR}}(n)\le C_4(L)$ が成り立つ。解析的な順序とgapは [EndpointFourStep.lean](../PseudoPrime/LLS/EndpointFourStep.lean)、証人定理 `exists_prime_fourStep` と最小証人定理 `exists_least_fourStep` は [EndpointFourStep.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFourStep.lean) にある。

$2877/250\le L\le47/4$ では $67 < C_4(L)$、 $112\le L\le240$ では後述の $G_1(L)\le C_4(L)$ である。これらの連続区間比較は [ImprovedEnvelopeOrder.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedEnvelopeOrder.lean) と [ImprovedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedIntervalSelection.lean) にある。

### Gamma prefix上界と切替点

1000までのGamma prefixには、10節点の証明書から得る下界 $423/100$ を用いる。証明は [GammaCheckpoint1000Sharp.lean](../PseudoPrime/LLS/GammaCheckpoint1000Sharp.lean) にある。平滑化幅 $h=(2/25)r^2$ の評価を合わせ、係数を

$$
K_1=\frac{86733}{98800},\qquad \mu=\frac{11783423}{25000000},\qquad
D_1=\frac{38128717}{11856000},\qquad T_1=\frac{20475759}{494000}
$$

と置く。正規化したgapと、その正の零点を

$$
g_1(L,r)=K_1r-\mu L-D_1-\frac{7L/6+T_1}{r},
$$

$$
\rho_1(L)=\frac{\mu L+D_1+
\sqrt{(\mu L+D_1)^2+4K_1(7L/6+T_1)}}{2K_1},\qquad
G_1(L)=\frac{99}{40}\rho_1(L)^2
$$

と定める。 $L\ge100$ ではまず代数的に $\rho_1(L) > 60$ を示し、その半径で解析評価を適用する。これにより全奇合成数について $q_{\mathrm{MR}}(n)\le G_1(L)$ が成り立つ。 [GammaSharpComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GammaSharpComparison.lean) の `exists_prime_gammaSharp`、 `exists_least_gammaSharp` が証人定理である。

固定35000との切替点は

$$
R=\sqrt{\frac{1400000}{99}},\qquad
S_1=\frac{K_1R-D_1-T_1/R}{\mu+7/(6R)}
$$

である。 $209 < S_1 < 210$ であり、 $100\le L\le S_1$ では $G_1(L)\le35000$、 $S_1\le L$ では $35000\le G_1(L)$、端点では $G_1(S_1)=35000$ となる。厳密式を表す定義 `gammaSharpFixedSwitch` と大小関係の証明は [GammaSharpEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GammaSharpEnvelope.lean) にある。小数での交点を分岐条件には使わない。

### 床付きGaussian上界

共通の定数を

$$
J=10^9,\quad M=\frac{64167}{100000},\quad E=\frac{2129}{2000},\quad
\kappa=\frac25,\quad c_G=\frac{20115621}{50000000},
$$

$$
d_G=\frac{JM-E}{J-1},\qquad
\beta_G=\frac{J}{J-1}\left(\kappa M+\frac{1}{10\kappa}\right)
$$

とする。2つの候補には次のprefixと残差定数を使う。

| 候補 | $N$ | prefix下界 | $D$ | 平方根半径の下限 |
|---|---|---|---|---|
| $U_{35}$ | $35000$ | $189499/40000$ | $29/5$ | $13$ |
| $U_{50}$ | $50000$ | $484381/100000$ | $111/20$ | $14$ |

$$
t_D(L)=\frac{\beta_G+\sqrt{\beta_G^2+4d_G(c_GL+D)}}{2d_G},
$$

$$
s_N(L)=\max\left\lbrace\sqrt{\sqrt{5N/6}},t_D(L)\right\rbrace,\qquad
r_N(L)=s_N(L)^2,\qquad
U_N(L)=\frac65r_N(L)^2=\max\left\lbrace N,\frac65t_D(L)^4\right\rbrace.
$$

$U_{35}$ では $(N,D)=(35000,29/5)$、 $U_{50}$ では $(N,D)=(50000,111/20)$ を用いる。両候補とも $L\ge63$ の全奇合成数に適用でき、対数の上限はない。床を入れた半径では等式でなく

$$
d_Gr_N\ge c_GL+\beta_Gs_N+D
$$

を使う。大指数枝では、係数が負の逆数二次項を一次項と対にしたまま残差を抑える。三素数枝では誤差を11未満、主項を11超とし、有限指数の分類と局所枝を合わせて全入力へ接続する。数値評価は [GaussianMRClippedNumerics.lean](../PseudoPrime/Analysis/GaussianMRClippedNumerics.lean)、実際の証人・最小証人は [GaussianMRClippedWitnessBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianMRClippedWitnessBounds.lean) の `exists_prime_gaussianClipped`、 `exists_least_gaussianClipped` にある。

Gaussian候補の切替点を、厳密式

$$
\sigma_N(D)=\frac{d_G\sqrt{5N/6}-\beta_G\sqrt{\sqrt{5N/6}}-D}{c_G},
$$

$$
\sigma_1=\sigma_{35000}(29/5),\qquad
\sigma_2=\sigma_{50000}(29/5),\qquad
\sigma_3=\sigma_{50000}(111/20)
$$

で定める。 $240 < \sigma_1 < 242$、 $293 < \sigma_2 < \sigma_3 < 294$ である。 $\sigma_1$ では $35000=(6/5)t_{29/5}(\sigma_1)^4$、 $\sigma_2$ では $(6/5)t_{29/5}(\sigma_2)^4=50000$、 $\sigma_3$ では $50000=(6/5)t_{111/20}(\sigma_3)^4$ となる。これらの端点等式と、次の4区間選択が $\min\lbrace U_{35},U_{50}\rbrace$ に等しいことは [GaussianMRClippedComparison.lean](../PseudoPrime/Analysis/GaussianMRClippedComparison.lean) で証明した。

$$
U_G(L)=
\begin{cases}
35000 & L\le\sigma_1,\\
\frac65t_{29/5}(L)^4 & \sigma_1 < L < \sigma_2,\\
50000 & \sigma_2\le L\le\sigma_3,\\
\frac65t_{111/20}(L)^4 & \sigma_3 < L.
\end{cases}
$$

Leanの選択関数は `PseudoPrime.Analysis.gaussianFloorSelected`、候補最小値との等式は `gaussianFloor_min_eq_selected` である。 $L\ge240$ での $U_G < G_1$、 $U_G < C_4$ は [ImprovedEnvelopeGlobalOrder.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedEnvelopeGlobalOrder.lean) にある。

### 全奇合成数に対する係数 $282924/1000000$ の上界

GRHの下で、 $L\ge2\cdot10^{12}$ のすべての奇合成数について

$$
q_{\mathrm{MR}}(n)\le\frac{282924}{1000000}L^2
$$

が成り立つ。大指数枝の閾値を $10^{12}$ とし、 $x=(282924/1000000)L^2$ に対して $x^{1/16}\ge31$、 $\sqrt{x}\ge(5319/10000)L$、符号を保持した誤差コスト $\le(123/1000)L$ を用いる。局所枝と三素数Korselt枝も同じ上界へ接続する。平方自由性や部分群指数の条件は結論に残らない。

数値gapは [TriangularSignedThresholdNumerics.lean](../PseudoPrime/Analysis/TriangularSignedThresholdNumerics.lean)、全入力への接続は [TriangularThresholdBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularThresholdBounds.lean) の `exists_prime_triangularThreshold`、 `exists_least_triangularThreshold` にある。十進の十分条件 $n\ge10^{869565217392}$ からも適用できる。巨大な冪を展開せず、 $\ln10 > 23/10$ から対数閾値を導く。

## 上界式の適用区間と比較

対象は正の奇合成数 $n\ge9$ に対する最小素数基数 $q_{\mathrm{MR}}(n)$ とする。上界式 $2,3$ の行を除きGRHを仮定する。

### 上界式と証明済みの適用条件

| 適用条件 | 上界式 | 対応するLean定理 |
|---|---|---|
| $9\le n < 2047$ | $2$ | [`exists_least_smallInterval`](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) |
| $2047\le n < 3000$ | $3$ | [`exists_least_smallInterval`](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) |
| $L\le2877/250$ | $61$ | [`exists_least_endpointPointwise61`](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwise.lean) |
| $L\le47/4$ | $67$ | [`exists_least_endpoint67`](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFixed67.lean) |
| $L\ge45/4$ | $C_4(L)$ | [`exists_least_fourStep`](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFourStep.lean) |
| $L\ge100$ | $G_1(L)$ | [`exists_least_gammaSharp`](../PseudoPrime/PrimeTestBounds/MillerRabin/GammaSharpComparison.lean) |
| $L\ge63$ | $U_{35}(L),U_{50}(L),U_G(L)$ | [`exists_least_gaussianClippedEnvelope`](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianMRClippedWitnessBounds.lean) |
| $L\ge2\cdot10^{12}$ | $(282924/1000000)L^2$ | [`exists_least_triangularThreshold`](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularThresholdBounds.lean) |

### 区間ごとの包絡線

$T_{\mathrm{tri}}=2\cdot10^{12}$ とする。 $S_1$ と $\sigma_1,\sigma_2,\sigma_3$ は前節の厳密式で定めた切替点である。

| 条件 | $U_{\mathrm{MR}}(n)$ |
|---|---|
| $9\le n < 2047$ | $2$ |
| $2047\le n < 3000$ | $3$ |
| $n\ge3000$、 $L\le2877/250$ | $61$ |
| $2877/250 < L\le47/4$ | $67$ |
| $47/4 < L < 100$ | $C_4(L)$ |
| $100\le L < 112$ | $\min\lbrace C_4(L),G_1(L)\rbrace$ |
| $112\le L\le S_1$ | $G_1(L)$ |
| $S_1 < L\le\sigma_1$ | $35000$ |
| $\sigma_1 < L < \sigma_2$ | $(6/5)t_{29/5}(L)^4$ |
| $\sigma_2\le L\le\sigma_3$ | $50000$ |
| $\sigma_3 < L < 2\cdot10^{12}$ | $(6/5)t_{111/20}(L)^4$ |
| $2\cdot10^{12}\le L$ | $(282924/1000000)L^2$ |

変数で示した境界の値は次のとおりである。小数は参考値であり、区間の条件には前節の厳密式を使う。

- $S_1\approx209.5595004$
- $\sigma_1\approx241.5155012$
- $\sigma_2\approx293.1589138$
- $\sigma_3\approx293.7803214$

この表の定義は `improvedSelectedEnvelope` である。 `improved_eq_selected` は、証明済みの適用条件でのみ候補を使う `improvedWitnessEnvelope` との一致を、すべての $n > 1$ について示す。 $100\le L < 112$ では $C_4$ と $G_1$ の交差位置を厳密に特定していないため、両候補の最小値を残す。その他の区間は連続区間の大小関係と端点等式によって単一式へ選択した。証明と、全奇合成数に対する `exists_prime_improvedSelected`、 `exists_least_improvedSelected` は [ImprovedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedIntervalSelection.lean) にある。

### 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は区間表の $U_{\mathrm{MR}}(n)$、黒の点線は $(\ln n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項に対応する。基数を素数 $2,3,5,7,\ldots$ の順に選んでMiller–Rabinテストを行うと、第 $k$ 項は、最初の $k-1$ 個の素数基数によるテストをすべて通過する最小の奇合成数である。この合成数を棄却するには、少なくとも第 $k$ 番目の素数 $p_k$ を基数とするテストまで進む必要がある。縦座標はその奇合成数 $n$ を棄却する最小の素数基数 $q_{\mathrm{MR}}(n)$ である。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるので、点の縦座標は3となる。

橙線は各入力の証明済み上界であり、入力全体に対する累積最大値ではない。 $L=T_{\mathrm{tri}}$ では採用する式の切替によって上界が下がる。この切替点は図の描画範囲外にある。この下降はその入力から小さい上界を使えることを示す。実際の最小素数証人の累積最大値が減少することや、切替後の上界が切替前の入力にも成り立つことは意味しない。ある $N$ 以下の全入力を一律に覆うには、 $U_{\mathrm{MR}}(N)$ だけでなく、対象となる各区間内の上界の最大値を含めて評価する。

描画範囲は $9\le n\le10^{1024}$ で、挿入図は $n\ge3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。 $L\ge T_{\mathrm{tri}}$ の係数枝は描画範囲外である。図の数値照合はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
