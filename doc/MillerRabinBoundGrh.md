# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

GRHの下で、奇合成数 $n \ge 9$ の最小Miller–Rabin拒否素数は $\max\lbrace 2,(517/1250)(\ln n)^2\rbrace$ 以下であり、 $2(\log_9 n)^2$ 以下でもある。定理は [LeastPrime4136.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/LeastPrime4136.lean) にある。 $(4/9)(\ln n)^2$ による素数判定条件の同値は [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) にある。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` から利用できる。

[JointSurplusEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusEnvelope.lean) の `jointSelected` は有限区間と解析的な上界を組み合わせ、 `jointSelected_least` は最小拒否素数がその値以下であることを示す。 `jointPrime` は選択値を素数へ丸める。本稿と図では、この選択値と上記のmax形の小さい方を $U_{\mathrm{MR}}(n)$ とする。Leanにはこの最小値の専用定義を設けず、証明済みの2つの上界から導く。

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
\text{すべての素数底 }p \le \frac{4}{9}(\ln\mathrel{} n)^2\text{ が強 Miller–Rabin 条件を満たす}
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

この前提の下で合成数なら $n \ge 9$ であり、合成数性について次の同値が成り立つ。

$$
n \text{ が合成数}
\iff
\exists p \text{ 素数},\quad
p \le \frac{4}{9}(\ln\mathrel{} n)^2
\land p^d \not\equiv 1 \pmod n
\land \forall j \in ℕ,\quad
j < s \Longrightarrow p^{2^j d} \not\equiv -1 \pmod n
$$

素数なら上界内のすべての素数底で合格することは、GRHなしに証明できる。逆に、これらの底での合格から素数性を導く向きに GRH を用いる。素数入力では、上界内の素数底は $p < n$ を満たし、 $n$ と互いに素になる。

Lean では $n - 1$ の 2 進付値 $s$ と奇数部分 $d$ をそれぞれ `padicValNat 2 (n - 1)` と `Nat.divMaxPow (n - 1) 2` として定義し、合同式を `ZMod n` の等式・不等式として表す。 GRHは前述の命題を仮定するものであり、GRH自体を証明したという主張ではない。

`prime_iff_mr_le_four_ninths_log_sq` の宣言部を示す。証明本体は省略している。

```lean
namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem prime_iff_mr_le_four_ninths_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 公開定理

以下の名前は `PseudoPrime.PrimeTestBounds.MillerRabin` 名前空間に属する。

| 宣言 | 内容 | ソース |
|---|---|---|
| `exists_prime_reject_max_4136` | GRH下の奇合成数に対する係数 $517/1250$ のmax形の証人上界 | [GlobalMax4136.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GlobalMax4136.lean) |
| `compositeLeastPrime_le_max_4136`・`compositeLeastPrime_le_log9_sq` | 最小拒否素数のmax形と底9の上界 | [LeastPrime4136.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/LeastPrime4136.lean) |
| `exists_prime_witness_four_ninths`・`exists_least_witness_four_ninths` | GRH下の奇合成数 $n \ge 9$ に対する $4/9$ の証人と最小証人 | [FourNinthsBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsBounds.lean) |
| `prime_iff_mr_le_four_ninths_log_sq` | $4/9$ の上界による素数判定条件 | [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) |
| `cumulativeLeastPrime_le_four_ninths_log_sq` | 全自然数の上端に対する累積最大値の $4/9$ 上界 | [FourNinthsCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCumulative.lean) |
| `jointSurplus_least` | 全域上界 $F(\ln n)$ による最小証人の評価 | [JointSurplusEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusEnvelope.lean) |
| `jointSelected_least`・`jointPrime_least` | 選択上界と素数丸めによる最小証人の評価 | [JointSurplusEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusEnvelope.lean) |
| `cumulativeLeastPrime_le_joint` | 全自然数の上端に対する累積最大値の評価 | [JointSurplusCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusCumulative.lean) |
| `jointSurplusGlobal_ratio_anti` | 全域上界を $L^2$ で割った係数の単調非増加性 | [GaussianSurplusShape.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianSurplusShape.lean) |
| `jointSurplus_lt_042` など | 指定した入口以降での係数評価 | [JointSurplusThresholds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusThresholds.lean) |
| `exists_primeWitness_lt_3000` | GRHを仮定しない奇合成数 $9 \le n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

係数 $517/1250$ のmax形では、 $\ln n < 8$ を底2・3の有限分類で扱う。 $8 \le \ln n \le 350$ で素因数が重複込みで2個の場合は、平方数について係数 $0.371$、相異なる2素数の積について係数 $0.409$ の上界を使う。有限証明では90組の素数供給と956個の計数候補を認証し、平方数の78行と半素数の122区間を接続する。素因数が3個以上の場合は、 $8 \le \ln n \le 25/2$ で小さい素因数を使い、 $25/2 \le \ln n \le 3461/10$ で偶指標の補正を使う。 $\ln n \ge 3461/10$ は全域Gaussian上界で覆う。

係数 $4/9$ の定理では重複込みの素因数個数により奇合成数を分類する。素因数が3個以上なら既存の因数個数による上界を使う。2個の場合は平方と異なる2素数の積に分け、局所核の大きさと素数積の個数を比較する。低域では重複を許す素数積と有限個の有理数証明書を使い、中域では素数個数の解析的下界と61行の証明書を使う。 $\ln n \ge 1024$ は一様な評価で扱う。小さい入力と固定素数23・29の既存定理を接続し、全域を覆う。実装は [FourNinthsFiniteWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsFiniteWitness.lean) と [FourNinthsHighWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsHighWitness.lean) を経て全域定理に至る。

全域上界 $F$ では尺度1の算術和の寄与と符号付きGamma評価を組み合わせる。共同の重みに対するAbel評価と素数供給の下界を使って、大きな部分群指数の場合に証人を得る。一様な3素因子の場合はGaussian比較を使う。各因数構造の証人を同じ切断点へ接続し、最小証人と累積上界を導く。

合格底の構造と小さい入力の有限分類は [Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) と [Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) にある。有限分類は $9 \le n < 3000$ の奇合成数に対して底2または3の不合格を示す。素数入力の合格方向にはGRHを使わない。

## 証明依存

主定理、証人系、有限分類、小範囲の上界、真部分群の中心定理、利用した S2 定理の推移的公理依存は `propext`、 `Classical.choice`、 `Quot.sound` のみである。有限証明を含め、これらの定理に `sorry` や `native_decide` 由来の公理依存はない。確認例は次のとおり。

```lean
import PseudoPrime

namespace PseudoPrime.PrimeTestBounds.MillerRabin

#print axioms prime_iff_mr_le_four_ninths_log_sq
#print axioms exists_prime_reject_max_4136
#print axioms compositeLeastPrime_le_max_4136
#print axioms compositeLeastPrime_le_log9_sq
#print axioms exists_prime_witness_four_ninths
#print axioms cumulativeLeastPrime_le_four_ninths_log_sq
#print axioms jointPrime_least
#print axioms cumulativeLeastPrime_le_joint
#print axioms PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 個別の上界と証明

対象を正の奇合成数とし、 $9 \le n$、 $L=\ln n$ とする。最小素数証人を

$$
q_{\mathrm{MR}}(n)=\min\lbrace p\in\mathbb P\mid\neg\mathrm{StrongMRPass}(n,p)\rbrace
$$

と書く。実数上界を次のように定める。

$$
C(L)=\max\left\lbrace 2,\frac{517}{1250}L^2\right\rbrace,\qquad
U_{\mathrm{MR}}(n)=\min\lbrace\mathrm{jointSelected}(n),C(\ln n)\rbrace.
$$

GRHの下で $q_{\mathrm{MR}}(n) \le U_{\mathrm{MR}}(n)$ が成り立つ。さらに $n \ge 9$ では $C(\ln n) \le 2(\log_9 n)^2$ である。両方の上界は [LeastPrime4136.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/LeastPrime4136.lean) にあり、その数値比較は [LogNineComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/LogNineComparison.lean) にある。

### 有限区間 $9 \le n < 3000$ の上界

$9 \le n < 2047$ では2、 $2047 \le n < 3000$ では3を返す。底2または底3での拒否を有限分類で証明し、素数証人と最小素数証人へ接続する。この範囲ではGRHは不要である。定義と証人定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

公開数値関数の仕様としても、すべての自然数 $2047 \le n < 3000$ で `jointSelected n` と `jointPrime n` はともに3である。この等式には奇数性や合成数性を仮定しない。 $n < 2047$ では両関数が2を返す。

### 固定素数上界23・31と有限principal和

固定半径 $y$ に対して、次の実際のvon Mangoldt和を使う。

$$
R(x)=\sum_{1 \le m \le x}\Lambda(m)\left(\frac1m-\frac1x\right),\qquad
S(x)=\sum_{1 \le m \le x}\Lambda(m)\ln\frac xm.
$$

各半径で、次の2本の下界を有限和から証明する。

$$
\ell(y)=\frac{78861}{50000}+\frac{231}{5000y}-\frac{16033}{9000y^2}.
$$

$$
2\ln y-\ell(y)+\delta_R \le R(y^2),
$$

$$
y^2-\frac y{20}-\frac{1839}{500}\ln y-\frac{21}{20}+\delta_S \le S(y^2).
$$

各半径で既存の有理部分和が与える余裕を使い、補強量を分母 $10^6$ の有理数に固定する。必要な素数の対数について有理区間をTaylor級数8項で検証し、相異なる素数冪の寄与を加える。残りの項は非負なので、これらの部分和は元の和の下界となる。

実際の $R(y^2)$ と $S(y^2)$ に対する下界を指標の比較定理へ渡し、強化した比較gapが正であることから $y^2$ 以下のMR拒否素数を得る。表の各行で $y^2$ は次の素数より小さいため、素数間の有限検証により表の上界へ丸められる。

| 適用条件 | 固定半径 $y$ | $10^6\delta_R$ | $10^6\delta_S$ | 素数証人上界 |
|---|---|---:|---:|---:|
| $L \le 8.0901$ | $53851/10000$ | 7385 | 597822 | 23 |
| $L \le 9.0031$ | $60827/10000$ | 9395 | 729227 | 31 |

各行は記した上端以下の全域で使え、個別の証人定理には $n \ge 3000$ や前行の上端を仮定しない。証明書は [EndpointFiniteCredits.lean](../PseudoPrime/Analysis/EndpointFiniteCredits.lean)、素数証人・最小素数証人は [EndpointFiniteTuned.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFiniteTuned.lean) にある。

### 全域の解析的上界

$L > 0$ に対して、次の定数と関数を定める。

$$
A=\frac{20115621}{25000000},\quad V=\frac{28794111}{12500000},\quad
D=\frac{10971611}{5000000},\quad
s_R(L)=\frac{V+\sqrt{V^2+4D(AL+R)}}{2D}.
$$

$$
\Phi_{35}(L)=\frac{21}{10}\max\lbrace130,s_{30}(L)^2\rbrace^2,\quad
\Phi_{50}(L)=\frac{21}{10}\max\lbrace155,s_{29}(L)^2\rbrace^2,
$$

$$
F(L)=\min\left\lbrace\frac49L^2,\Phi_{35}(L),\Phi_{50}(L)\right\rbrace.
$$

GRHの下で、すべての奇合成数 $n \ge 9$ に対して $q_{\mathrm{MR}}(n) \le F(\ln n)$ である。 $F$ は非負の範囲で単調非減少であり、 $F(L)/L^2$ は $L > 0$ で単調非増加である。証明は [GaussianSurplusGlobal.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianSurplusGlobal.lean) と [GaussianSurplusShape.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianSurplusShape.lean) にある。

| 入口 $L$ | その入口以降で成り立つ評価 |
|---:|---:|
| $3461/10$ | $F(L) < (517/1250)L^2$ |
| $400$ | $F(L) < 0.397L^2$ |
| $1000$ | $F(L) < 0.338L^2$ |
| $4000$ | $F(L) < 0.304L^2$ |
| $6500$ | $F(L) < 0.3L^2$ |
| $25000$ | $F(L) < 0.29L^2$ |

最初の行は [GaussianHigh4136.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianHigh4136.lean)、残りの行は [JointSurplusThresholds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusThresholds.lean) で証明した。 $F(L)/L^2$ は $L \to \infty$ で次の値に収束する。

$$
\frac{21}{10}\left(\frac{20115621/25000000}{10971611/5000000}\right)^2.
$$

この極限は [JointSurplusAsymptotic.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusAsymptotic.lean) で証明している。

### 素数への丸め

実数上界 $R \ge 2$ に対して、 $R$ 以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R) \le R$ が成り立ち、 $p \le R$ を満たす素数 $p$ は丸め後も範囲内にある。また、 `primeRound_mono` はこの丸めの単調性を示す。定義と定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

`jointPrime n` は `jointSelected n` を丸める。2・3と表の固定素数は丸めても同じ値である。素数への丸めは調べる素数基数の集合を変えずに、実数上界をその集合の最大要素へ置き換える。

### 全域の累積上界

$Q_{\mathrm{MR}}(N)$ を $9 \le n \le N$ の奇合成数 $n$ に対する最小拒否素数の最大値とし、対象がないときは0とする。以下では $N \ge 9$、 $L=\ln N$ とする。 $N < 9$ では $Q_{\mathrm{MR}}(N)=0$ である。

全域で有効な $F$ は非減少なので、 GRHの下で $Q_{\mathrm{MR}}(N) \le F(\ln N)$ である。 `jointCumulative` は、この上界と `smoothCumulative` の最小値に等しい。この同値は [JointSurplusComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/JointSurplusComparison.lean) の `jointCumulative_eq_scaleOne_min` で証明している。 $C(L)$ も $L \ge 0$ で非減少なので、各入力へのmax形から $Q_{\mathrm{MR}}(N) \le C(\ln N)$ が従う。図ではこの2つの累積上界の小さい方を描く。

### 包絡線の構成

$n < 3000$ では小域の値2または3を使う。 $n \ge 3000$ では固定素数候補、 $F(\ln n)$、 $C(\ln n)$ を比較する。上界の選択は入力ごとに行うため、その値自体を累積上界として扱わない。

## 上界式の適用区間

次の表は描画範囲で数値比較により確認した $U_{\mathrm{MR}}$ の候補を示す。 $C(L)$ と31の交点を $L_{31}=\sqrt{31\cdot1250/517}$ とする。図の上界の定義は全域で $\mathrm{jointSelected}(n)$ と $C(\ln n)$ の最小値である。

| 適用条件 | 現行の上界を構成する候補 |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| $\ln3000 \le L \le 8.0901$ | $23$ |
| $8.0901 < L < L_{31}$ | $C(L)$ |
| $L_{31} \le L \le 9.0031$ | $31$ |
| $9.0031 < L$ | $\min\lbrace C(L),F(L)\rbrace$ |

### 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は $\mathrm{jointSelected}(n)$ と $C(\ln n)$ の最小値、黒の点線は $2(\log_9 n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

基数を素数 $p_1=2,p_2=3,p_3=5,\ldots$ の順に選んでMiller–Rabinテストを行う。青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項、すなわち最初の $k-1$ 個の素数基数 $p_1,\ldots,p_{k-1}$ によるテストをすべて通過する最小の奇合成数である。縦座標はその入力を棄却する最小素数基数 $q_{\mathrm{MR}}(n)$ であり、記録更新点では $Q_{\mathrm{MR}}(n)$ と一致する。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるため、点の縦座標は3となる。青緑の階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。

主図の描画範囲は $9 \le n \le 10^{64}$、縦軸は $10^0$ から $10^4$ である。点ごとの上界を描いており、累積上界としての単調性は仮定していない。挿入図は $3000 \le n \le e^{10^{14}}$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。この比の下降は分子である上界 $U_{\mathrm{MR}}(n)$ の下降を意味しない。全域上界 $F$ が $4/9$ の上界を改善する範囲は主図の範囲外にある。そこで入力ごとの上界に下降が生じても、累積最大値の下降を表すものではない。

図の数値計算はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

### 累積上界と点ごとの上界の比較

![MR累積上界と点ごとの候補](figures/mr_cumulative_high_comparison.svg)

橙線は `jointCumulative` と $C(L)$ の小さい方を $L^2$ で割った累積上界、青い破線は点ごとの上界 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。黒点線の高さは $2/(\ln 9)^2$ である。実数軸の描画と、Leanによる自然数上端の証明は区別する。[PNG版](figures/mr_cumulative_high_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
