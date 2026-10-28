# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

対数平方上界の入口は [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean)。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` からも利用できる。


区間別の公開包絡線は [TunedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedWitnessEnvelope.lean) の `tunedSelectedEnvelope` である。GRHの下で、すべての奇合成数 $n > 1$ について、 `exists_prime_tunedSelected` と `exists_least_tunedSelected` が実際の素数証人と最小素数証人の上界を与える。平方自由性、素因数の個数、Fermat部分群指数に関する追加条件はない。

[TunedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedWitnessEnvelope.lean) の `tunedWitnessEnvelope` は、各候補を証明済みの適用条件でのみ使う最小値である。 `tuned_eq_selected` が区間選択との一致を証明する。素数へ丸めた `tunedPrimeEnvelope` についても `exists_prime_tunedPrimeEnvelope` と `exists_least_tunedPrimeEnvelope` が同じ仮定で証人を与える。

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

対象を正の奇合成数とし、 $9 \le n$、 $L=\ln n$ とする。最小素数証人を

$$
q_{\mathrm{MR}}(n)=\min\lbrace p\in\mathbb P\mid\neg\mathrm{StrongMRPass}(n,p)\rbrace
$$

と書く。公開する実数上界を $U_{\mathrm{MR}}(n)=\mathrm{tunedSelectedEnvelope}(n)$ とする。GRHの下で $q_{\mathrm{MR}}(n) \le U_{\mathrm{MR}}(n)$ が成り立つ。

### 有限区間 $9 \le n < 3000$ の上界

$9 \le n < 2047$ では2、 $2047 \le n < 3000$ では3を返す。底2または底3での拒否を有限分類で証明し、素数証人と最小素数証人へ接続する。この範囲ではGRHは不要である。定義と証人定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

公開数値関数の仕様としても、すべての自然数 $2047 \le n < 3000$ で `tunedSelectedEnvelope n` と `tunedPrimeEnvelope n` はともに3である。この等式には奇数性や合成数性を仮定しない。 $n < 2047$ では両関数が2を返す。対応する定理は [TunedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedIntervalSelection.lean) の `tunedSelected_small_two`、 `tunedSelected_small_three`、 `tunedPrime_small_two`、 `tunedPrime_small_three` である。

### 固定素数上界23〜79と有限principal和

固定半径 $y$ に対して、次の実際のvon Mangoldt和を使う。

$$
R(x)=\sum_{1 \le m \le x}\Lambda(m)\left(\frac1m-\frac1x\right),\qquad
S(x)=\sum_{1 \le m \le x}\Lambda(m)\ln\frac xm.
$$

$\ell(y)$ は次節の有理関数とする。各半径で、次の2本の下界を有限和から証明する。

$$
2\ln y-\ell(y)+\delta_R \le R(y^2),
$$

$$
y^2-\frac y{20}-\frac{1839}{500}\ln y-\frac{21}{20}+\delta_S \le S(y^2).
$$

各半径で既存の有理部分和が与える余裕を使い、補強量を分母 $10^6$ の有理数に固定する。73以下の21素数について対数の有理区間をTaylor級数8項で検証し、相異なる最大30個の素数冪の寄与を加える。残りの項は非負なので、これらの部分和は元の和の下界となる。

次節で定義する $D_e(y)$ と $F_{\mathrm{pt}}(y)$ を使うと、強化した比較gapは

$$
G_+(L,y)=D_e(y)(F_{\mathrm{pt}}(y)-L)
 +(y-1)^2\delta_S+2y^2(y+1+\ln y)\delta_R
$$

となる。実際の $R(y^2)$ と $S(y^2)$ に対する下界を指標の比較定理へ渡し、 $G_+(L,y) > 0$ から $y^2$ 以下のMR拒否素数を得る。表の各行で $y^2$ は次の素数より小さいため、素数間の有限検証により表の上界へ丸められる。

| 適用条件 | 固定半径 $y$ | $10^6\delta_R$ | $10^6\delta_S$ | 素数証人上界 |
|---|---|---:|---:|---:|
| $L \le 8.0901$ | $53851/10000$ | 7385 | 597822 | 23 |
| $L \le 8.3320$ | $55677/10000$ | 7794 | 630000 | 29 |
| $L \le 9.0031$ | $60827/10000$ | 9395 | 729227 | 31 |
| $L \le 9.3961$ | $64031/10000$ | 6554 | 651721 | 37 |
| $L \le 9.5875$ | $65574/10000$ | 6072 | 648651 | 41 |
| $L \le 9.9619$ | $68556/10000$ | 6816 | 712934 | 43 |
| $L \le 10.4895$ | $72801/10000$ | 8072 | 819332 | 47 |
| $L \le 10.9671$ | $76811/10000$ | 6484 | 769482 | 53 |
| $L \le 11.1199$ | $78102/10000$ | 6009 | 755180 | 59 |
| $L \le 11.5654$ | $1637/200$ | 5520 | 761820 | 61 |
| $L \le 11.8463$ | $337/40$ | 4829 | 739461 | 67 |
| $L \le 11.9879$ | $1068/125$ | 4972 | 762726 | 71 |
| $L \le 12.3975$ | $1111/125$ | 5757 | 856932 | 73 |
| $L \le 12.6409$ | $5694/625$ | 3135 | 667896 | 79 |

各行は記した上端以下の全域で使え、個別の証人定理には $n \ge 3000$ や前行の上端を仮定しない。13行のデータは [EndpointFiniteCredits.lean](../PseudoPrime/Analysis/EndpointFiniteCredits.lean)、素数証人・最小素数証人は [EndpointFiniteTuned.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFiniteTuned.lean) にある。固定79には既存の30項をそのまま使い、新半径の実際の和へ埋め込む。対数証明書を半径 $5694/625$ に1本追加し、素数79の寄与は追加しない。実際の和・gap・証人の接続は [Analysis/EndpointPrime79.lean](../PseudoPrime/Analysis/EndpointPrime79.lean)、[LLS/PaperStatements/EndpointPrime79.lean](../PseudoPrime/LLS/PaperStatements/EndpointPrime79.lean)、[MillerRabin/EndpointPrime79.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPrime79.lean) に分けてある。

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

pointwise gapは正確に $D_e(y)(F_{\mathrm{pt}}(y)-L)$ となる。逆関数半径でgapが0になる場合も、最小素数証人とその平方根の中点を用いる離散的な議論により証人上界が成り立つ。定義・単調性・逆関数は [LLS/EndpointPointwiseRoot.lean](../PseudoPrime/LLS/EndpointPointwiseRoot.lean)、全奇合成数の素数証人・最小素数証人は [MillerRabin/EndpointPointwiseRoot.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwiseRoot.lean) にある。

### 低床Gaussianの4profile

Gaussian候補に共通の定数を次のように置く。

$$
J=10^9,\quad M=\frac{64167}{100000},\quad E=\frac{2129}{2000},\quad k=\frac25,
$$

$$
d=\frac{JM-E}{J-1},\qquad
\beta=\frac{J}{J-1}\left(kM+\frac1{10k}\right),\qquad
c=\frac{20115621}{50000000}.
$$

残差予算 $D$ に対する二次式の正根と上界を

$$
t_D(L)=\frac{\beta+\sqrt{\beta^2+4d(cL+D)}}{2d},\qquad
V_D(L)=\frac65t_D(L)^4
$$

とする。根の下限 $u$ を持つprofileは

$$
A_{u,D}(L)=\max\left\lbrace\frac65u^4,V_D(L)\right\rbrace
$$

である。 $L \ge 63$ で次の4profileがそれぞれ素数証人上界を与える。

| 根の下限 $u$ | 残差予算 $D$ | 使用するprefix下界 |
|---|---|---|
| $91/10=9.1$ | $929/100=9.29$ | $901/250=3.604$ |
| $93/10=9.3$ | $87/10=8.7$ | $901/250=3.604$ |
| $237/25=9.48$ | $1629/200=8.145$ | $722517/200000=3.612585$ |
| $979/100=9.79$ | $65/8=8.125$ | $722517/200000=3.612585$ |

実際の有限prefix和は表の値以上になる。大指数側の半径を $r=s^2$ とし、指数4側は $r_4=(7559/10000)r$、幅は両側とも $k/s$ とする。lowとbridgeはcoarse評価、middleとupperは符号を保った2項の評価を使う。指数4側の残差閾値は全profileで $204/5=40.8$ を保つ。大指数・指数4・局所部分群の分類を通じ、すべての奇合成数に対して実際の拒否素数を得る。

4profileの最小を $A_+(L)$ と書く。切替境界を

$$
\phi(u,D)=\frac{du^2-\beta u-D}{c},
$$

$$
\begin{aligned}
a_1&=\phi(9.1,9.29),& a_2&=\phi(9.3,9.29),& a_3&=\phi(9.3,8.7),\\
a_4&=\phi(9.48,8.7),& a_5&=\phi(9.48,8.145),& a_6&=\phi(9.79,8.145),\\
a_7&=\phi(9.79,8.125)
\end{aligned}
$$

とする。境界は正確な有理数であり、数値的な根探索をguardに使わない。

| 適用条件 | $A_+(L)$ |
|---|---|
| $63 \le L \le a_1$ | $(6/5)(9.1)^4$ |
| $a_1 < L \le a_2$ | $V_{9.29}(L)$ |
| $a_2 < L \le a_3$ | $(6/5)(9.3)^4$ |
| $a_3 < L \le a_4$ | $V_{8.7}(L)$ |
| $a_4 < L \le a_5$ | $(6/5)(9.48)^4$ |
| $a_5 < L \le a_6$ | $V_{8.145}(L)$ |
| $a_6 < L \le a_7$ | $(6/5)(9.79)^4$ |
| $a_7 < L$ | $V_{8.125}(L)$ |

数値証明書は [GaussianTunedProfiles.lean](../PseudoPrime/Analysis/GaussianTunedProfiles.lean)、素数証人・最小素数証人は [GaussianTunedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianTunedBounds.lean) にある。

### prefix付きGaussian上界

既存35行の対数moment下界と実際のsmoothed sum $S(100)$ の上界から、境界項の下界を強める。これを実際のGamma prefixへ輸送し、係数 $17/20$ でGaussian prefixに移す。新しい素数行やquadrature節点は使わない。対応する定理は [GammaSeedLogMoment.lean](../PseudoPrime/LLS/GammaSeedLogMoment.lean) にある。

$N=35000$ と $N=50000$ の有限prefixを用い、次の2候補を定める。

$$
S_{35}(L)=\max\lbrace35000,V_{5.619}(L)\rbrace,\qquad
S_{50}(L)=\max\lbrace50000,V_{5.372}(L)\rbrace.
$$

実際のprefix和の下界はそれぞれ $481117/100000=4.81117$ と $983059/200000=4.915295$ である。cutoffの下限を保持することで、証明に必要なprefixの範囲を確保する。両候補は $L \ge 63$ で有効であり、その最小を $S_+(L)$ とする。

$$
\psi(N,D)=\phi\left(\left(\frac{5N}{6}\right)^{1/4},D\right),\qquad
\sigma_1=\psi(35000,5.619),\quad
\sigma_2=\psi(50000,5.619),\quad
\sigma_3=\psi(50000,5.372).
$$

| 適用条件 | $S_+(L)$ |
|---|---|
| $63 \le L \le \sigma_1$ | $35000$ |
| $\sigma_1 < L < \sigma_2$ | $V_{5.619}(L)$ |
| $\sigma_2 \le L \le \sigma_3$ | $50000$ |
| $\sigma_3 < L$ | $V_{5.372}(L)$ |

定義と厳密な切替等式は [GaussianSeededTuned.lean](../PseudoPrime/Analysis/GaussianSeededTuned.lean)、素数証人・最小素数証人は [GaussianSeededTunedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianSeededTunedBounds.lean) にある。

### 高域のtriangular上界

triangular kernelの明示公式から、各行の適用条件で $C_iL^2$ 以下の素数証人を得る。主指標の下界、指標平均、conductor比較、signed零点質量の評価を、共通のprofile定理へ渡す。

| $i$ | 適用条件 $T_i \le L$ | 係数 $C_i$ |
|---:|---|---|
| 1 | $3\cdot10^{10} \le L$ | $4603/10000=0.4603$ |
| 2 | $4\cdot10^{10} \le L$ | $829/2000=0.4145$ |
| 3 | $10^{11} \le L$ | $663/2000=0.3315$ |
| 4 | $2.5\cdot10^{11} \le L$ | $374/1250=0.2992$ |
| 5 | $5\cdot10^{11} \le L$ | $2891/10000=0.2891$ |
| 6 | $1.08\cdot10^{12} \le L$ | $28399/100000=0.28399$ |
| 7 | $1.48\cdot10^{12} \le L$ | $28289/100000=0.28289$ |
| 8 | $1.82\cdot10^{12} \le L$ | $1411811/5000000=0.2823622$ |

各profileは自分の入口 $T_i$ 以上でのみ有効になる。定数の証明書は [TriangularTunedProfiles.lean](../PseudoPrime/Analysis/TriangularTunedProfiles.lean)、素数証人・最小素数証人は [TriangularTunedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedBounds.lean) にある。

最後の8行目は比較基準のsharpと共通で、定数と証人定理は [TriangularProfiles.lean](../PseudoPrime/Analysis/TriangularProfiles.lean) と [TriangularProfileBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularProfileBounds.lean) にある。新しい7profileの入口は変更しない。

## 上界式の適用区間と比較

### 上界式と証明済みの適用条件

以下の解析候補と固定23〜79にはGRHを仮定する。有限区間の2と3は無条件である。

| 適用条件 | 上界式 |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| 固定素数の表にある $L \le L_0$ | 表の各素数23〜79 |
| すべての実数 $L$ | $U_{\mathrm{pt}}(L)$ |
| $63 \le L$ | $A_{9.1,9.29}(L)$、 $A_{9.3,8.7}(L)$、 $A_{9.48,8.145}(L)$、 $A_{9.79,8.125}(L)$ |
| $63 \le L$ | $S_{35}(L)$、 $S_{50}(L)$ |
| 各 $T_i \le L$ | $C_iL^2$、 $i=1,\ldots,8$ |

### 区間ごとの包絡線

055559版の `sharpSelectedEnvelope` を $U_{\mathrm{sharp}}(n)$ と書く。新公開関数はこの比較基準を候補として保持し、14個の固定素数候補、4個のGaussian候補、2個のprefix付き候補、新しい7個の高域候補との最小値をとる。候補はそれぞれの証明済みguardでのみ有効になる。

| 適用条件 | $U_{\mathrm{MR}}(n)$ |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| $\ln3000 \le L \le 8.0901$ | $23$ |
| $8.0901 < L \le 8.3320$ | $29$ |
| $8.3320 < L \le 9.0031$ | $31$ |
| $9.0031 < L \le 9.3961$ | $37$ |
| $9.3961 < L \le 9.5875$ | $41$ |
| $9.5875 < L \le 9.9619$ | $43$ |
| $9.9619 < L \le 10.4895$ | $47$ |
| $10.4895 < L \le 10.9671$ | $53$ |
| $10.9671 < L \le 11.1199$ | $59$ |
| $11.1199 < L \le 11.5654$ | $61$ |
| $11.5654 < L \le 11.8463$ | $67$ |
| $11.8463 < L \le 11.9879$ | $71$ |
| $11.9879 < L \le 12.3975$ | $73$ |
| $12.3975 < L \le 12.6409$ | $79$ |
| $12.6409 < L < 63$ | $U_{\mathrm{pt}}(L)$ |
| $63 \le L < T_1$ | $\min\lbrace U_{\mathrm{sharp}}(n),A_+(L),S_+(L)\rbrace$ |
| $T_i \le L < T_{i+1}$、 $1 \le i \le 6$ | $\min\lbrace U_{\mathrm{sharp}}(n),A_+(L),S_+(L),C_iL^2\rbrace$ |
| $T_7 \le L$ | $\min\lbrace U_{\mathrm{sharp}}(n),A_+(L),S_+(L),C_7L^2\rbrace$ |

高域の入口は前節の正確な値を使う。新しい7profileでは入口が増加し係数が減少するため、有効なもののうち最後の候補だけを残せる。 $T_8$ 以降の既存の第8候補は $U_{\mathrm{sharp}}$ に含まれる。比較基準の候補も残すため、新しい上界は全入力で悪化しない。

数値関数と実証人の接続は [TunedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedWitnessEnvelope.lean)、小入力の等式は [TunedIntervalSelection.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedIntervalSelection.lean) にある。有限区間の選択は [EndpointTunedEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointTunedEnvelope.lean) が与える。

### 055559版からの厳密な改善

13個の既存固定素数について、旧capを $L_{\mathrm{old}}$、上の表の新capを $L_{\mathrm{new}}$ とする。 $n \ge 3000$ かつ $L_{\mathrm{old}} < L \le L_{\mathrm{new}}$ では選択値・丸め値ともに旧sharpより小さい。旧capは順に8.087、8.325、8.987、9.390、9.583、9.952、10.471、10.955、11.109、11.546、11.830、11.970、12.373である。固定79も閉区間 $12.61 \le L \le 12.6409$ で両値を厳密に改善する。証明は [EndpointTunedComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointTunedComparison.lean) と [EndpointPrime79.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPrime79.lean) にある。

Gaussianの4候補の最小は旧Gaussianの3候補の最小より $L \ge 100$ で小さい。旧sharp全体に対する選択値の厳密改善は閉区間 $100 \le L \le 235.73$ で成り立つ。

旧seededの切替点を $\tau_1=\mathrm{Switch}(\mathrm{false},35000)$、 $\tau_2=\mathrm{Switch}(\mathrm{false},50000)$、 $\tau_3=\mathrm{Switch}(\mathrm{true},50000)$ とし、profileごとの移動量を

$$
\delta_{35}=\frac{550000}{20115621},\qquad
\delta_{50}=\frac{1900000}{20115621}
$$

とする。各profileの新数値関数は旧数値関数の $L-\delta_N$ での値と一致する。証人定理は元の入力 $L=\ln n$ に適用し、数値式の比較に限ってprofileごとに異なる移動量を使う。新しい切替は順に $\tau_1+\delta_{35}$、 $\tau_2+\delta_{35}$、 $\tau_3+\delta_{50}$ となる。旧sharpに対する選択値の厳密改善区間は

$$
\tau_1 < L < \tau_2+\delta_{35},\qquad
\tau_3 < L < 3\cdot10^{10}
$$

である。近似すると $(241.9380584,293.6088129)$ と $(294.1283096,3\cdot10^{10})$ になる。いずれも指定した端点は開く。

高域の新7候補は $3\cdot10^{10} \le L < 1.82\cdot10^{12}$ で旧sharpの選択値を厳密に改善する。証明は [TriangularTunedOrder.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedOrder.lean) にある。Gaussian・seeded・高域について、選択値の厳密改善だけから丸め値の厳密改善は結論しない。丸め値には全域での非悪化が成り立つ。

### 素数への丸め

実数上界 $R \ge 2$ に対して、 $R$ 以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R) \le R$ が成り立ち、 $p \le R$ を満たす素数 $p$ は丸め後も範囲内にある。また、 `primeRound_mono` はこの丸めの単調性を示す。定義と定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

`tunedPrimeEnvelope n` は `tunedWitnessEnvelope n` を丸める。2・3・固定23〜79は丸めても同じ値である。素数への丸めは調べる素数基数の集合を変えずに、実数上界をその集合の最大要素へ置き換える。

### 累積最大値と単調性

自然数 $N \ge 9$ に対して、最小素数証人の累積最大値を

$$
Q_{\mathrm{MR}}(N)=\max\lbrace q_{\mathrm{MR}}(n)\mid
 9 \le n \le N, n\text{ は奇合成数}\rbrace
$$

と定める。 `tunedSelected_mono_normal` と `tunedPrime_mono_normal` は、 $9 \le m \le n$ かつ $\ln n < 3\cdot10^{10}$ の範囲で公開数値関数が単調非減少であることを示す。これらは [TunedEnvelopeOrder.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TunedEnvelopeOrder.lean) にある。GRHの下で、通常域 $N \ge 9$、 $\ln N < 3\cdot10^{10}$ では

$$
Q_{\mathrm{MR}}(N) \le U_{\mathrm{MR}}(N),\qquad
Q_{\mathrm{MR}}(N) \le \mathrm{tunedPrimeEnvelope}(N)
$$

が従う。各奇合成数に対する証人上界と、 $n \le N$ での単調性を組み合わせるためである。高域で新しいguardが有効になると、入力ごとの上界が下がることがある。その範囲全体を一律に覆う場合は、各区間内の上界の最大値を含めて評価する。累積最大値 $Q_{\mathrm{MR}}$ 自体は、すべての範囲で単調非減少である。

### 比較グラフ

055559版のsharpと新しいtunedを重ねた [比較図](figures/mr_tuned_vs_sharp.svg) を用意した。低域の固定素数、Gaussianとseeded、高域のtriangularを3パネルで示す。 [PNG版](figures/mr_tuned_vs_sharp.png) も参照できる。

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は表の $U_{\mathrm{MR}}(n)$、黒の点線は $(\ln n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

基数を素数 $p_1=2,p_2=3,p_3=5,\ldots$ の順に選んでMiller–Rabinテストを行う。青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項、すなわち最初の $k-1$ 個の素数基数 $p_1,\ldots,p_{k-1}$ によるテストをすべて通過する最小の奇合成数である。縦座標はその入力を棄却する最小素数基数 $q_{\mathrm{MR}}(n)$ であり、記録更新点では $Q_{\mathrm{MR}}(n)$ と一致する。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるため、点の縦座標は3となる。青緑の階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。

描画範囲は $9 \le n \le 10^{1024}$ である。この範囲は単調性の証明範囲に入り、橙線は単調非減少となる。挿入図は $n \ge 3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。この比の下降は分子である上界 $U_{\mathrm{MR}}(n)$ の下降を意味しない。triangular候補が有効になる高域の入口は描画範囲外であり、そこで入力ごとの上界に下降が生じても、累積最大値の下降を表すものではない。

図の数値計算はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
