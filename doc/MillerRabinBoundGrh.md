# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

対数平方上界の入口は [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean)。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` からも利用できる。


区間別の公開包絡線は [RefinedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedIntervalSelection.lean) の `refinedSelectedEnvelope` である。GRHの下で、すべての奇合成数 $n > 1$ について、 `exists_prime_refinedSelected` と `exists_least_refinedSelected` が実際の素数証人と最小素数証人の上界を与える。平方自由性、素因数の個数、Fermat部分群指数に関する追加条件はない。

[RefinedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedWitnessEnvelope.lean) の `refinedWitnessEnvelope` は、各候補を証明済みの適用条件でのみ使う最小値である。 `refined_eq_selected` が区間選択との一致を証明する。素数へ丸めた `refinedPrimeEnvelope` についても `exists_prime_refinedPrimeEnvelope` と `exists_least_refinedPrimeEnvelope` が同じ仮定で証人を与える。

MRの最小素数証人の累積最大値について、既知の更新点を [3種類の最小素数証人の数表](WitnessRecords.md) に参考情報として掲載した。

## 共通の記号

$$
\mathbb N=\lbrace0,1,2,\ldots\rbrace,\qquad
\mathbb P=\lbrace p\in\mathbb N\mid p\text{ は素数}\rbrace.
$$

$\ln$ は自然対数を表す。整数入力 $n$ と底 $p$ は自然数とする。
GRHはすべての原始複素Dirichlet指標のL関数について、非自明零点の実部が $1/2$ であるという仮定である。
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

以降、素数底証人とは $p\in\mathbb P$ かつ $\neg\mathrm{StrongMRPass}(n,p)$ を満たす底を指す。
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

Lean では $n - 1$ の 2 進付値 $s$ と奇数部分 $d$ をそれぞれ `padicValNat 2 (n - 1)` と `Nat.divMaxPow (n - 1) 2` として定義し、合同式を `ZMod n` の等式・不等式として表す。 GRHは前述の命題を仮定するものであり、GRH自体を証明したという主張ではない。

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

[Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) の `strongMillerRabinPass_isUnit`、 `strongMillerRabinPass_not_of_prime_dvd` がこの性質を示す。同ファイルの `strongMillerRabinWithBase_eq_false_iff_not_pass` はこの合格条件の否定をBoolean 判定へ接続する。素数入力側では対数上界から底の互いに素性を示し、素数法の受理定理と指定分解の接続を組み合わせて不合格条件と矛盾させる。この節の宣言は `PseudoPrime.PrimeTest` 名前空間に属する。

### 2. 合格底を含む真部分群

自然な埋め込みを $\iota_n:(\mathbb Z/n\mathbb Z)^\times\hookrightarrow\mathbb Z/n\mathbb Z$ とする。
単元とは乗法逆元を持つ剰余環の元であり、その全体が単元群をなす。
$H$ の像とは $\iota_n(H)$ を指す。

奇合成数 $n > 1$ に対して、単元群 $(ℤ/nℤ)^\times$ の真部分群 $H$ が存在し、合格するすべての剰余が $H$ の像に入ることを無条件に証明する。合格集合そのものを部分群と仮定する必要はない。

- 素数 $q$ について $q^2 \mid n$ となる場合は、 単元 $u\in(\mathbb Z/n\mathbb Z)^\times$ で $u^{n - 1} = 1$ を満たすもの全体からなる部分群を使う。法 $q^2$ の $1 + q$ を利用して、この部分群に属さない単元を構成する。
- 異なる素因数 $q,r$ がある場合は、 $q - 1 = 2^t c$、 $t,c\in\mathbb N$、 $c$ は奇数と分解し、 $E = 2^{t - 1} d\in\mathbb N$ と置く。ここで $d$ は $n-1$ の奇数部分である。 $u^E \in \lbrace 1, -1 \rbrace$ を満たす単元 $u$ の部分群を使う。法 $q$ と法 $r$ で異なる符号をとる冪を中国剰余定理（CRT）で構成し、真部分群であることを示す。

各部分群の構成は [WitnessSubgroup.lean](../PseudoPrime/PrimeTest/MillerRabin/WitnessSubgroup.lean)、合成数の分岐と結合は [Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) にある。公開定理 `PseudoPrime.PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass` がS2 へ渡す真部分群と合格剰余の包含をまとめる。

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

対象を正の奇合成数とし、 $9\le n$、 $L=\ln n$ とする。最小素数証人を

$$
q_{\mathrm{MR}}(n)=\min\lbrace p\in\mathbb P\mid\neg\mathrm{StrongMRPass}(n,p)\rbrace
$$

と書く。以下の各候補は記した適用条件の下で $q_{\mathrm{MR}}(n)$ の上界となる。

### 有限区間 $9\le n < 3000$ の上界

$9\le n < 2047$ では2、 $2047\le n < 3000$ では3を返す。有限分類による底2または底3の拒否を、素数証人と最小素数証人へ接続する。GRHは不要である。定義 `smallIntervalBound` と公開定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

### 固定素数上界23〜73

固定半径 $y$ でpointwise gapが正であることを、対数の有理区間と二次式の有理数評価で証明する。GRHの下で $y^2$ 以下に実際のMR拒否素数が存在する。 $y^2$ と次の素数の間にある小さい合成数を除き、表の素数上界へ丸める。

| 対数の適用上端 $L_0$ | 固定半径 $y$ | 素数証人上界 |
|---|---|---:|
| $8032/1000=8.032$ | $53851/10000$ | 23 |
| $8271/1000=8.271$ | $55677/10000$ | 29 |
| $8934/1000=8.934$ | $60827/10000$ | 31 |
| $9339/1000=9.339$ | $64031/10000$ | 37 |
| $9532/1000=9.532$ | $65574/10000$ | 41 |
| $9902/1000=9.902$ | $68556/10000$ | 43 |
| $10422/1000=10.422$ | $72801/10000$ | 47 |
| $10907/1000=10.907$ | $76811/10000$ | 53 |
| $11062/1000=11.062$ | $78102/10000$ | 59 |
| $11509/1000=11.509$ | $1637/200$ | 61 |
| $1179/100=11.79$ | $337/40$ | 67 |
| $1193/100=11.93$ | $1068/125$ | 71 |
| $12337/1000=12.337$ | $1111/125$ | 73 |

各行の定理は $L\le L_0$ 全体に適用できる。前の行の上端より大きい条件や、 $n\ge3000$ は個別定理の前提ではない。23〜59の共通数値証明書は [EndpointLowPrimeTight.lean](../PseudoPrime/LLS/PaperStatements/EndpointLowPrimeTight.lean)、素数証人・最小素数証人の18定理は [MillerRabin/EndpointLowPrimeTight.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointLowPrimeTight.lean) にある。61〜73は [EndpointPointwiseSteps.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwiseSteps.lean) にある。

### pointwise補正の逆関数上界

$y\ge8$、 $z=\ln y$ として、次の関数を用いる。

$$
D_e(y)=(y-1)((y+1)^2+2y\ln y),\qquad
H(y)=\frac{N_H(y)}{18310000D_e(y)},
$$

$$
\begin{aligned}
N_H(y)={}&36620000y^3z-56749471y^3+109860000y^2z^2\\
&+73100099y^2z+10777809y^2-73240000yz^2\\
&-1528140yz+2824690y-36620000z^2-177204180z-94877470.
\end{aligned}
$$

$$
\ell(y)=\frac{78861}{50000}+\frac{231}{5000y}-\frac{16033}{9000y^2},\qquad
\delta(y)=\frac{2y^2(y+1+\ln y)(31551/20000-\ell(y))}{D_e(y)},
$$

$$
H_{\mathrm{pt}}(y)=H(y)+\delta(y),\qquad F_{\mathrm{pt}}(y)=y+H_{\mathrm{pt}}(y).
$$

$H_{\mathrm{pt}}$ と $F_{\mathrm{pt}}$ は $[8,\infty)$ で狭義単調である。 $L\le F_{\mathrm{pt}}(8)$ なら $R_{\mathrm{pt}}(L)=8$ とし、 $L > F_{\mathrm{pt}}(8)$ なら $F_{\mathrm{pt}}(y)=L$ を満たす $y\ge8$ の一意解を $R_{\mathrm{pt}}(L)$ とする。上界は

$$
U_{\mathrm{pt}}(L)=R_{\mathrm{pt}}(L)^2
$$

である。 $F_{\mathrm{pt}}(8)\approx11.2893992652$ で、下限の8はすべての実数 $L$ で保持する。

既存のpointwise gapは正確に $D_e(y)(F_{\mathrm{pt}}(y)-L)$ となる。逆関数半径でgapが0になる場合も、最小素数証人とその平方根の中点を用いる離散的な議論により証人上界が成り立つ。定義・単調性・逆関数は [LLS/EndpointPointwiseRoot.lean](../PseudoPrime/LLS/EndpointPointwiseRoot.lean)、全奇合成数の素数証人・最小素数証人は [MillerRabin/EndpointPointwiseRoot.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwiseRoot.lean) にある。

補正関数全体を使う評価 $H(y)\le y/9$ が $y\ge64$ で成り立つ。この評価と逆関数の仕様から、 $L\ge100$ では $(81/100)L^2\le U_{\mathrm{pt}}(L)$ を得る。実数区間の比較に使う定理は [EndpointPointwiseNinth.lean](../PseudoPrime/LLS/PaperStatements/EndpointPointwiseNinth.lean) の `pointwiseCorrection_ninth` と `pointwiseCutoff_lower81` である。

### 基本Gamma候補と固定stencil上界

$$
K=\frac{86733}{98800},\quad \mu=\frac{11783423}{25000000},\quad
D=\frac{38128717}{11856000},\quad T=\frac{58129633}{2223000}.
$$

$$
r_{\Gamma}(L)=\frac{\mu L+D+\sqrt{(\mu L+D)^2+4K(7L/6+T)}}{2K},\qquad
G_{\Gamma}(L)=\frac{99}{40}r_{\Gamma}(L)^2.
$$

$L\ge100$ で適用できる。幅 $2/25$、1000-prefix下界 $423/100$ と、反射剰余 $\frac{35}{2}x^{-9/16}+\frac1{x\sqrt x}$ を実際の指標和・有限平均へ接続する。局所枝・指数4枝・大指数枝を合わせた公開定理 `exists_prime_gammaReflected` と `exists_least_gammaReflected` は [GammaReflectedComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GammaReflectedComparison.lean) にある。

固定stencil上界では次の定数と正根を使う。

$$
D_{\mathrm R}=\frac{36174637}{11856000},\qquad
r_{\mathrm R}(L)=\frac{\mu L+D_{\mathrm R}+\sqrt{(\mu L+D_{\mathrm R})^2+4K(7L/6+T)}}{2K},
$$

$$
G_{\mathrm R}(L)=\frac{99}{40}r_{\mathrm R}(L)^2.
$$

$L\ge101$ で適用できる。1000-prefix下界は $106/25$。既存の35行・10節点を使い、幅を保ったstencil評価をvariationとprincipalの両方へ接続する。尾部を使う前に $r_{\mathrm R}(L) > 60$ を証明する。素数証人・最小素数証人は [GammaRecoveredBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GammaRecoveredBounds.lean) の `exists_prime_gammaRecovered` と `exists_least_gammaRecovered` である。

### 二つの半径を用いる1000-prefix Gaussian上界

次の定数は床付きGaussian上界でも共通に使う。

$$
J=10^9,\quad M=\frac{64167}{100000},\quad E=\frac{2129}{2000},\quad
k=\frac25,\quad c_G=\frac{20115621}{50000000},
$$

$$
d=\frac{JM-E}{J-1},\quad
\beta=\frac{J}{J-1}\left(Mk+\frac1{10k}\right),\quad
d_4=\frac{4M-E}{3},\quad
\beta_4=\frac43\left(Mk+\frac1{10k}\right).
$$

大指数枝と指数4枝の半径を別々に定義する。

$$
s_{\mathrm{large}}(L)=\frac{\beta+\sqrt{\beta^2+4d(c_GL+163/20)}}{2d},
$$

$$
s_4(L)=\frac{\beta_4+\sqrt{\beta_4^2+4d_4(2c_GL/3+127/10)}}{2d_4},
$$

$$
s(L)=\max\lbrace10,s_{\mathrm{large}}(L),s_4(L)\rbrace,\qquad
U_{1000}(L)=\frac65s(L)^4.
$$

Gaussianの1000-prefix下界は $7191/2000$ である。 $s\ge10$ がprefixと尾部評価の範囲を保証し、二つの二次方程式がそれぞれの枝の残差を抑える。 $L\ge63$ で全奇合成数に適用できる。定義は [GaussianMR1000Numerics.lean](../PseudoPrime/Analysis/GaussianMR1000Numerics.lean)、公開定理 `exists_prime_gaussian1000` と `exists_least_gaussian1000` は [GaussianMR1000WitnessBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianMR1000WitnessBounds.lean) にある。

### 一根のGaussian上界

$$
t_{\mathrm R}(L)=\frac{\beta+\sqrt{\beta^2+4d(c_GL+407/50)}}{2d},\qquad
A_{\mathrm R}(L)=\frac65\left(\max\lbrace10,t_{\mathrm R}(L)\rbrace\right)^4.
$$

$L\ge63$ で適用できる。1000-prefix下界は $901/250$。 $s=\max\lbrace10,t_{\mathrm R}(L)\rbrace$、 $r=s^2$ とする。大指数枝は半径 $r$、指数4枝は半径 $3r/4$ と幅 $k/s$ を使う。指数4枝の探索cutoffは $(21/10)(3r/4)^2\le(6/5)r^2$ を満たすため、公開cutoff以下の合格仮定から実際の相対比較を構成できる。local枝を含めた全奇合成数のprime/least定理は [GaussianRecoveredBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianRecoveredBounds.lean) の `exists_prime_gaussianRecovered` と `exists_least_gaussianRecovered` である。

### 床付きGaussian上界

$$
t_D(L)=\frac{\beta+\sqrt{\beta^2+4d(c_GL+D)}}{2d},\qquad
V_D(L)=\frac65t_D(L)^4,
$$

$$
U_{35}(L)=\max\lbrace35000,V_{567/100}(L)\rbrace,\qquad
U_{50}(L)=\max\lbrace50000,V_{109/20}(L)\rbrace.
$$

$L\ge63$ では両者の小さい方を上界に使える。35000-prefixのGaussian下界は $191471/40000$、50000-prefixは $489311/100000$ である。共通のGamma seedからprefixを運び、局所枝・指数4枝・大指数枝へ接続する。素数証人・最小素数証人の定理は [GaussianMRSeededWitnessBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianMRSeededWitnessBounds.lean) にある。

切替点を次の厳密式で定義する。

$$
\sigma_N(D)=\frac{d\sqrt{5N/6}-\beta\sqrt{\sqrt{5N/6}}-D}{c_G},
$$

$$
\sigma_1=\sigma_{35000}(567/100),\quad
\sigma_2=\sigma_{50000}(567/100),\quad
\sigma_3=\sigma_{50000}(109/20).
$$

$\sigma_1 < \sigma_2 < \sigma_3$ で、隣り合う式は各切替点で同じ値になる。最小値は順に35000、 $V_{567/100}$、50000、 $V_{109/20}$ を選ぶ。厳密な区間等式は [GaussianMRSeededComparison.lean](../PseudoPrime/Analysis/GaussianMRSeededComparison.lean) にある。

prefix下界を $958409/200000$ と $244919/50000$ として供給する床付き候補は、次のとおりである。

$$
U_{35,\mathrm R}(L)=\max\lbrace35000,V_{283/50}(L)\rbrace,\qquad
U_{50,\mathrm R}(L)=\max\lbrace50000,V_{136/25}(L)\rbrace,
$$

$$
S_{\mathrm R}(L)=\min\lbrace U_{35,\mathrm R}(L),U_{50,\mathrm R}(L)\rbrace.
$$

$L\ge63$ で適用できる。切替点は $\tau_1=\sigma_{35000}(283/50)$、 $\tau_2=\sigma_{50000}(283/50)$、 $\tau_3=\sigma_{50000}(136/25)$。値は順に35000、 $V_{283/50}$、50000、 $V_{136/25}$ を取る。区間等式は [GaussianRecoveredSeededComparison.lean](../PseudoPrime/Analysis/GaussianRecoveredSeededComparison.lean)、選択式のprime/least定理は [GaussianRecoveredSeededOrder.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianRecoveredSeededOrder.lean) にある。

### 高域のtriangular上界

$$
T_{\mathrm{early}}=1500000000000,\qquad T_{\mathrm{lower}}=2000000000000.
$$

$L\ge T_{\mathrm{early}}$ では $\frac{282924}{1000000}L^2$、 $L\ge T_{\mathrm{lower}}$ では $\frac{2827}{10000}L^2$ を使える。指数分割は $10^{12}$、kernelのパラメータは18である。係数 $2827/10000$ の三素数Korselt枝は、対応するGaussian scaleと分母下界 $10971611/5000000$ で証明する。公開定理は [TriangularEarlyBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularEarlyBounds.lean) と [TriangularNextBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularNextBounds.lean) にある。

加えて、 $T_{\mathrm R}=1100000000000$ から $(71/250)L^2$、 $T_{\mathrm S}=2000000000000$ から $(28237/100000)L^2$ を使える。大指数枝は同じalpha-18の比較に2組の有理予算を渡す。係数 $28237/100000$ の三素数枝は、実際の相対Gaussian比較でconductor係数 $c_G$ と50000-prefixを保持して証明する。各分岐を解消した公開定理は [TriangularRefinedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularRefinedBounds.lean) の `exists_prime_triangularEarlier`、 `exists_least_triangularEarlier`、 `exists_prime_triangularRefined`、 `exists_least_triangularRefined` である。

## 上界式の適用区間と比較

### 上界式と証明済みの適用条件

次の表は正の奇合成数 $n\ge9$ を対象とする。有限区間の2・3を除きGRHを仮定する。

| 適用条件 | 上界式 |
|---|---|
| $9\le n < 2047$ | $2$ |
| $2047\le n < 3000$ | $3$ |
| $L\le L_0$ | 固定23〜73の表にある各素数 |
| すべての $L$ | $U_{\mathrm{pt}}(L)$ |
| $100\le L$ | $G_{\Gamma}(L)$ |
| $63\le L$ | $U_{1000}(L)$ |
| $63\le L$ | $\min\lbrace U_{35}(L),U_{50}(L)\rbrace$ |
| $T_{\mathrm{early}}\le L$ | $\frac{282924}{1000000}L^2$ |
| $T_{\mathrm{lower}}\le L$ | $\frac{2827}{10000}L^2$ |
| $63\le L$ | $A_{\mathrm R}(L)$ |
| $101\le L$ | $G_{\mathrm R}(L)$ |
| $63\le L$ | $S_{\mathrm R}(L)$ |
| $T_{\mathrm R}\le L$ | $\frac{71}{250}L^2$ |
| $T_{\mathrm S}\le L$ | $\frac{28237}{100000}L^2$ |

### 区間ごとの包絡線

基本選択関数を $B(n)=\mathrm{lowPrimeTightSelected}(n)$ とする。次の表はこの関数を上から順に評価する。固定23〜59の9段階と基本候補の選択を明記し、公開包絡線の有効条件付き最小値へ渡す。定義と区間等式は [LowPrimeTightEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/LowPrimeTightEnvelope.lean) にある。

| 条件 | $B(n)$ |
|---|---|
| $9\le n < 2047$ | $2$ |
| $2047\le n < 3000$ | $3$ |
| $\ln 3000\le L\le8032/1000$ | $23$ |
| $8032/1000 < L\le8271/1000$ | $29$ |
| $8271/1000 < L\le8934/1000$ | $31$ |
| $8934/1000 < L\le9339/1000$ | $37$ |
| $9339/1000 < L\le9532/1000$ | $41$ |
| $9532/1000 < L\le9902/1000$ | $43$ |
| $9902/1000 < L\le10422/1000$ | $47$ |
| $10422/1000 < L\le10907/1000$ | $53$ |
| $10907/1000 < L\le11062/1000$ | $59$ |
| $11062/1000 < L\le11509/1000$ | $61$ |
| $11509/1000 < L\le1179/100$ | $\min\lbrace67,U_{\mathrm{pt}}(L)\rbrace$ |
| $1179/100 < L\le1193/100$ | $\min\lbrace71,U_{\mathrm{pt}}(L)\rbrace$ |
| $1193/100 < L\le12337/1000$ | $\min\lbrace73,U_{\mathrm{pt}}(L)\rbrace$ |
| $12337/1000 < L < 100$ | $U_{\mathrm{pt}}(L)$ |
| $100\le L < 132$ | $\min\lbrace U_{\mathrm{pt}}(L),G_{\Gamma}(L),U_{1000}(L)\rbrace$ |
| $132\le L\le235$ | $\min\lbrace U_{\mathrm{pt}}(L),U_{1000}(L)\rbrace$ |
| $235 < L < 240$ | $\min\lbrace35000,U_{1000}(L)\rbrace$ |
| $240\le L\le\sigma_1$ | $35000$ |
| $\sigma_1 < L < \sigma_2$ | $V_{567/100}(L)$ |
| $\sigma_2\le L\le\sigma_3$ | $50000$ |
| $\sigma_3 < L < T_{\mathrm{early}}$ | $V_{109/20}(L)$ |
| $T_{\mathrm{early}}\le L < T_{\mathrm{lower}}$ | $\frac{282924}{1000000}L^2$ |
| $T_{\mathrm{lower}}\le L$ | $\frac{2827}{10000}L^2$ |

変数で示した境界の近似値は次のとおり。区間の判定には上の厳密式を使う。

- $\sigma_1\approx241.8386331811$。
- $\sigma_2\approx293.4820457177$。
- $\sigma_3\approx294.0288844159$。
- $T_{\mathrm{early}}=1.5\cdot10^{12}$。
- $T_{\mathrm{lower}}=2\cdot10^{12}$。

公開包絡線 $U_{\mathrm{MR}}(n)=\mathrm{refinedSelectedEnvelope}(n)$ は、次の表で定義する。表の $B(n)$ は上の基本選択関数である。

| 条件 | $U_{\mathrm{MR}}(n)$ |
|---|---|
| $9\le n < 2047$ | $2$ |
| $2047\le n < 3000$ | $3$ |
| $n\ge3000$、 $L < 63$ | $B(n)$ |
| $63\le L < 101$ | $\min\lbrace B(n),A_{\mathrm R}(L),S_{\mathrm R}(L)\rbrace$ |
| $101\le L < T_{\mathrm R}$ | $\min\lbrace B(n),A_{\mathrm R}(L),G_{\mathrm R}(L),S_{\mathrm R}(L)\rbrace$ |
| $T_{\mathrm R}\le L < T_{\mathrm S}$ | $\min\lbrace B(n),A_{\mathrm R}(L),G_{\mathrm R}(L),S_{\mathrm R}(L),(71/250)L^2\rbrace$ |
| $T_{\mathrm S}\le L$ | $\min\lbrace B(n),A_{\mathrm R}(L),G_{\mathrm R}(L),S_{\mathrm R}(L),(71/250)L^2,(28237/100000)L^2\rbrace$ |

この表に現れる境界の値は次のとおり。判定には定義の厳密式を使う。

- $\tau_1\approx241.8634894856$。
- $\tau_2\approx293.5069020222$。
- $\tau_3\approx294.0537407203$。
- $T_{\mathrm R}=1.1\cdot10^{12}$。
- $T_{\mathrm S}=2\cdot10^{12}$。

`refined_eq_selected` はすべての $n > 1$ に対する数値関数の等式で、GRH・奇数・合成数を仮定しない。 `exists_prime_refinedSelected` と `exists_least_refinedSelected` がGRHの下で全奇合成数の証人上界を与える。小入力の区間値は $2047 < n < 3000$ でも3である。

### 素数への丸め

実数上界 $R$ が2以上なら、その値以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R)\le R$ が成り立ち、 $p\le R$ を満たす素数 $p$ は丸め後も範囲内にある。定義と保存定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

公開定義 `refinedPrimeEnvelope n` は `refinedWitnessEnvelope n` を丸める。素数上界2・3・固定23〜73は丸めても同じ値である。整数化は底として調べる素数の集合を変えないため、解析上界の式と区別して示す。 $29/2\le L\le15$ では公開丸め値 `refinedPrimeEnvelope n` が113である。定理 `refinedPrime_eq113` は [RefinedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedIntervalSelection.lean) にある。

### 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は区間表の $U_{\mathrm{MR}}(n)$、黒の点線は $(\ln n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項に対応する。基数を素数 $2,3,5,7,\ldots$ の順に選んでMiller–Rabinテストを行うと、第 $k$ 項は、最初の $k-1$ 個の素数基数によるテストをすべて通過する最小の奇合成数である。この合成数を棄却するには、少なくとも第 $k$ 番目の素数 $p_k$ を基数とするテストまで進む必要がある。縦座標はその奇合成数 $n$ を棄却する最小の素数基数 $q_{\mathrm{MR}}(n)$ もしくは $N$ 以下の全入力に対する上界 $Q_{\mathrm{MR}}(N)$ である。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるので、点の縦座標は3となる。

橙線は各入力の証明済み上界であり、入力全体に対する累積最大値ではない。 $L=1.1\cdot10^{12}$ と $L=2\cdot10^{12}$ では、有効になる候補の追加によって上界が下がることがある。この切替点は図の描画範囲外にある。この下降はその入力から小さい上界を使えることを示す。実際の最小素数証人の累積最大値が減少することや、切替後の上界が切替前の入力にも成り立つことは意味しない。ある $N$ 以下の全入力を一律に覆うには、 $U_{\mathrm{MR}}(N)$ だけでなく、対象となる各区間内の上界の最大値を含めて評価する。

描画範囲は $9\le n\le10^{1024}$ で、挿入図は $n\ge3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。 $L\ge1.1\cdot10^{12}$ の係数枝は描画範囲外である。図の数値照合はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
