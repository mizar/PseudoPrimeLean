# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

GRHの下で、奇合成数 $n \ge 9$ には $(4/9)(\ln n)^2$ 以下のMiller–Rabin拒否素数が存在する。証人と最小証人の定理は [FourNinthsBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsBounds.lean)、素数判定条件の同値は [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) にある。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` から利用できる。

さらに $\ln n \ge 70000$ では、上界を $(7/16)(\ln n)^2$ に改善できる。証人と最小証人の定理は [HighCoefficientBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientBounds.lean) にある。

公開選択上界 $U_{\mathrm{MR}}(n)$ は [ImprovedFixedEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedFixedEnvelope.lean) の `fixedImprovedSelected` である。対による計数、階乗評価、係数 $427/1000$、尺度に応じて選ぶtriangular・Gaussian上界と、3つの固定係数候補を組み合わせる。 `exists_least_fixedImproved` は最小拒否素数が選択値以下であることを示す。 `fixedImprovedPrime` は選択値を素数へ丸め、同じ最小証人を保持する。

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
| `exists_prime_witness_four_ninths`・`exists_least_witness_four_ninths` | GRH下の奇合成数 $n \ge 9$ に対する $4/9$ の証人と最小証人 | [FourNinthsBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsBounds.lean) |
| `prime_iff_mr_le_four_ninths_log_sq` | $4/9$ の上界による素数判定条件 | [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) |
| `exists_least_fourNinthsSelected`・`exists_least_fourNinthsPrime` | 選択値と素数丸め値による最小証人の上界 | [FourNinthsEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsEnvelope.lean) |
| `cumulativeLeastPrime_le_four_ninths_log_sq` | 全自然数の上端に対する累積最大値の $4/9$ 上界 | [FourNinthsCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCumulative.lean) |
| `highCoeff_prime_witness`・`highCoeff_least_witness` | $\ln n \ge 70000$ における $7/16$ の証人と最小証人 | [HighCoefficientBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientBounds.lean) |
| `prime_iff_mr_highCoeff` | $\ln n \ge 70000$ における $7/16$ の素数判定条件 | [HighCoefficientCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientCriterion.lean) |
| `exists_least_highCoeffSelected`・`exists_least_highCoeffPrime` | 高域候補を加える前の選択値と素数丸め値による最小証人の上界 | [HighCoefficientEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientEnvelope.lean) |
| `exists_least_highWindowSelected`・`exists_least_highWindowPrime` | 高域候補を加えた選択値と素数丸め値による最小証人の上界 | [HighWindowEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowEnvelope.lean) |
| `exists_least_highWindowExtended`・`exists_least_highWindowExtendedPrime` | 追加の高域候補を含む選択値と素数丸め値による最小証人の上界 | [HighWindowExtended.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtended.lean) |
| `paired_prime_witness`・`factorial_prime_witness` | 可変係数による全奇合成数の証人上界 | [HighVariableBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighVariableBounds.lean)、[HighFactorialBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighFactorialBounds.lean) |
| `prime_witness_427` | $\ln n \ge 80000$ における係数 $427/1000$ の証人上界 | [MeanAllFactors.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/MeanAllFactors.lean) |
| `exists_least_meanSelected`・`exists_least_meanSelectedPrime` | 現行の選択値と素数丸め値による最小証人の上界 | [MeanEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/MeanEnvelope.lean) |
| `meanSelected_lt_factorial` | $10^7 \le \ln n \le 2\cdot10^7$ における従来の包絡線からの厳密な改善 | [MeanComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/MeanComparison.lean) |
| `pairedSelected_lt_previous`・`factorialSelected_lt_paired` | 各候補の入口付近における従来の包絡線からの厳密な改善 | [HighVariableComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighVariableComparison.lean)、[HighFactorialComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighFactorialComparison.lean) |
| `cumulativeLeastPrime_le_mean` | 可変係数、固定係数と入口以前の履歴を含む累積最大値の上界 | [MeanEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/MeanEnvelope.lean) |
| `triangularAdaptive_prime_witness` | $\ln n \ge 3\cdot 10^{10}$ における可変triangular上界の素数証人 | [TriangularAdaptiveWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularAdaptiveWitness.lean) |
| `exists_least_triangularAdaptive`・`exists_least_triangularAdaptivePrime` | 現行の選択値と素数丸め値による最小証人の上界 | [TriangularAdaptiveEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularAdaptiveEnvelope.lean) |
| `triangularAdaptive_lt_mean` | $5\cdot 10^{10} \le \ln n < 6\cdot 10^{10}$ での厳密な改善 | [TriangularAdaptiveComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularAdaptiveComparison.lean) |
| `cumulativeLeastPrime_le_triangular` | 可変triangular候補と切替前の履歴を含む累積上界 | [TriangularAdaptiveCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularAdaptiveCumulative.lean) |
| `gaussianAdaptive_prime_witness` | $\ln n \ge 2\cdot 10^{12}$ の全奇合成数に対する可変Gaussian上界 | [GaussianAdaptiveWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianAdaptiveWitness.lean) |
| `exists_least_gaussianAdaptive`・`exists_least_gaussianAdaptivePrime` | 現行の選択値と素数丸め値による最小証人の上界 | [GaussianAdaptiveEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianAdaptiveEnvelope.lean) |
| `gaussianAdaptive_lt_triangular` | $\ln n \ge 2\cdot 10^{12}$ での従来の包絡線からの厳密な改善 | [GaussianAdaptiveComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianAdaptiveComparison.lean) |
| `cumulativeLeastPrime_le_gaussianAdaptive` | Gaussian候補と入口以前の履歴を含む累積上界 | [GaussianAdaptiveCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianAdaptiveCumulative.lean) |
| `exists_least_fixedImproved`・`exists_least_fixedImprovedPrime` | 現行の選択値と素数丸め値による最小証人の上界 | [ImprovedFixedEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedFixedEnvelope.lean) |
| `fixedImproved_lt_03869`・`fixedImproved_lt_03552`・`fixedImproved_lt_03134` | 3つの固定係数候補による厳密な改善 | [ImprovedFixedComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedFixedComparison.lean) |
| `cumulativeLeastPrime_le_fixedImproved` | 固定係数候補と入口以前の履歴を含む累積上界 | [ImprovedFixedCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ImprovedFixedCumulative.lean) |
| `highWindow_lt_previous` | $4.5\cdot10^{10} \le \ln n < 10^{11}$ における従来の選択上界からの厳密な改善 | [HighWindowComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowComparison.lean) |
| `highWindow_lt_previous_early` | $3.8\cdot10^{10} \le \ln n < 4\cdot10^{10}$ における従来の選択上界からの厳密な改善 | [HighWindowComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowComparison.lean) |
| `highWindowExtended_lt_0323`・`highWindowExtended_lt_0296`・`highWindowExtended_lt_0288` | 追加3候補の各入口から次の既存入口までにおける厳密な改善 | [HighWindowExtendedComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtendedComparison.lean) |
| `cumulativeLeastPrime_le_highCoeff_quad` | $\ln N \ge 71000$ における累積最大値の $7/16$ 上界 | [HighCoefficientCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientCumulative.lean) |
| `cumulativeLeastPrime_le_highWindow` | 追加した高域候補を含む累積最大値の上界 | [HighWindowCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowCumulative.lean) |
| `exists_primeWitness_lt_3000` | GRHを仮定しない奇合成数 $9 \le n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

係数 $4/9$ の定理では重複込みの素因数個数により奇合成数を分類する。素因数が3個以上なら既存の因数個数による上界を使う。2個の場合は平方と異なる2素数の積に分け、局所核の大きさと素数積の個数を比較する。低域では重複を許す素数積と有限個の有理数証明書を使い、中域では素数個数の解析的下界と61行の証明書を使う。 $\ln n \ge 1024$ は一様な評価で扱う。小さい入力と固定素数23・29の既存定理を接続し、全域を覆う。実装は [FourNinthsFiniteWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsFiniteWitness.lean) と [FourNinthsHighWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsHighWitness.lean) を経て全域定理に至る。

高域の $7/16$ の定理でも、重複込みの素因数個数で分類する。4個以上は因数個数の上界で扱う。2個の場合と、3個で重複因子がある場合は局所核と素数積を比較する。相異なる3素数の場合は、非Korselt因子または異なる2進付値があれば因子の選択を使い、残る場合は導手の対数和を用いたGaussian評価を適用する。素数積の計数は連続した対数区間で評価し、遠い高域では既存の係数0.4145の定理につなぐ。詳細は [HighCoefficientBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientBounds.lean) とそのimport先にある。

可変係数の定理でも同じ因数構造を扱う。RHから正方半径での素数供給を $99/100$ に強め、局所核と素数積の個数を比較する。階乗型では対数階乗の上界から二項係数を評価し、床・天井と $\ln(k+1)$ の損失を残す。平方自由3素因子の特殊な場合は、それぞれの半径でGaussian比較の余裕を確認する。

係数 $427/1000$ の定理では素数積の平均対数で選別した積を局所核へ注入する。第一Chebyshev関数の評価とAbel公式の積分項から素数供給を得て、有限誤差付きStirling評価で個数を下から抑える。重複因子と平方自由3素因子も扱い、 $\ln n \ge 4\cdot10^{10}$ は既存のtriangular上界で覆う。

合格底の構造と小さい入力の有限分類は [Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) と [Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) にある。有限分類は $9 \le n < 3000$ の奇合成数に対して底2または3の不合格を示す。素数入力の合格方向にはGRHを使わない。

## 証明依存

主定理、証人系、有限分類、小範囲の上界、真部分群の中心定理、利用した S2 定理の推移的公理依存は `propext`、 `Classical.choice`、 `Quot.sound` のみである。有限証明を含め、これらの定理に `sorry` や `native_decide` 由来の公理依存はない。確認例は次のとおり。

```lean
import PseudoPrime

namespace PseudoPrime.PrimeTestBounds.MillerRabin

#print axioms prime_iff_mr_le_four_ninths_log_sq
#print axioms exists_prime_witness_four_ninths
#print axioms cumulativeLeastPrime_le_four_ninths_log_sq
#print axioms PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 個別の上界と証明

対象を正の奇合成数とし、 $9 \le n$、 $L=\ln n$ とする。最小素数証人を

$$
q_{\mathrm{MR}}(n)=\min\lbrace p\in\mathbb P\mid\neg\mathrm{StrongMRPass}(n,p)\rbrace
$$

と書く。現在の実数上界を $U_{\mathrm{MR}}(n)=\mathrm{fixedImprovedSelected}(n)$ とする。GRHの下で $q_{\mathrm{MR}}(n) \le U_{\mathrm{MR}}(n)$ が成り立つ。

### 有限区間 $9 \le n < 3000$ の上界

$9 \le n < 2047$ では2、 $2047 \le n < 3000$ では3を返す。底2または底3での拒否を有限分類で証明し、素数証人と最小素数証人へ接続する。この範囲ではGRHは不要である。定義と証人定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

公開数値関数の仕様としても、すべての自然数 $2047 \le n < 3000$ で `fixedImprovedSelected n` と `fixedImprovedPrime n` はともに3である。この等式には奇数性や合成数性を仮定しない。 $n < 2047$ では両関数が2を返す。

### 可変係数による高域上界

$L=\ln n$ とし、次の係数を定める。

$$
C_{\mathrm{pair}}(L)=\left(\frac{2\ln L+1/100}{3\ln L+339/500}\right)^2,
\qquad
C_{\mathrm{fac}}(L)=\left(\frac{2\ln L+3/200}{3\ln L+49/50}\right)^2.
$$

GRHの下で、すべての奇合成数について $L \ge 70000$ なら $q_{\mathrm{MR}}(n) \le C_{\mathrm{pair}}(L)L^2$、 $L \ge 80000$ なら $q_{\mathrm{MR}}(n) \le C_{\mathrm{fac}}(L)L^2$ が成り立つ。 $70000 \le L \le 100000$ では対による候補が以前の包絡線を、 $80000 \le L \le 100000$ では階乗型が対による候補を、それぞれ厳密に下回る。

さらに $L \ge 80000$ では $q_{\mathrm{MR}}(n) \le (427/1000)L^2$ が成り立つ。この候補は $10^7 \le L \le 2\cdot10^7$ で、それまでの包絡線を厳密に下回る。

### 固定素数上界23〜53と有限principal和

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
| $L \le 8.3320$ | $55677/10000$ | 7794 | 630000 | 29 |
| $L \le 9.0031$ | $60827/10000$ | 9395 | 729227 | 31 |
| $L \le 9.3961$ | $64031/10000$ | 6554 | 651721 | 37 |
| $L \le 9.9619$ | $68556/10000$ | 6816 | 712934 | 43 |
| $L \le 10.4895$ | $72801/10000$ | 8072 | 819332 | 47 |
| $L \le 10.9671$ | $76811/10000$ | 6484 | 769482 | 53 |

各行は記した上端以下の全域で使え、個別の証人定理には $n \ge 3000$ や前行の上端を仮定しない。小域の値2・3と $(4/9)L^2$ も含めた公開包絡線では、表の7候補がそれぞれ選択される区間を持つ。証明書は [EndpointFiniteCredits.lean](../PseudoPrime/Analysis/EndpointFiniteCredits.lean)、素数証人・最小素数証人は [EndpointFiniteTuned.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFiniteTuned.lean) にある。

固定上界41、59、61、67、71、73、79は、それぞれの適用上端 $L_0$ で $(4/9)L_0^2$ が固定上界より小さい。したがって $n \ge 3000$ の適用範囲全体でも $(4/9)L^2$ の方が小さい。 $n < 3000$ では値2または3を使うため、これらの固定上界は公開包絡線を更新しない。

### 高域のtriangular上界

triangular kernelの明示公式から、認証した入口以上で固定係数による素数証人を得る。現行の選択上界はこれらの候補と以下の可変候補を組み合わせる。固定profileの定義と証人定理は [TriangularTunedProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedProfiles.lean) と [HighWindowBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowBounds.lean) などにある。

さらに $L \ge 3\cdot 10^{10}$ で、次の尺度依存の上界を最小値に加える。

$$
\begin{aligned}
m(L)&=\left((5313/10000)L\right)^{1/8},\\
A(L)&=36+\frac{1456+13/10000000}{\sqrt L}+\frac{165102}{L},\\
D(L)&=\frac{4\cdot 10^{12}(1001/1000)}{m(L)L},\qquad K=68-3/10000,\\
r(L)&=\frac{A(L)+\sqrt{A(L)^2+4KD(L)}}{2K},\\
g(L)&=\begin{cases}28237/100000&L < 1.82\cdot 10^{12},\\
1411811/5000000&L \ge 1.82\cdot 10^{12},\end{cases}\\
a(L)&=\max\lbrace\sqrt{g(L)},r(L)\rbrace.
\end{aligned}
$$

GRHの下で $q_{\mathrm{MR}}(n) \le a(L)^2L^2$ が成り立つ。 $5\cdot 10^{10} \le L < 6\cdot 10^{10}$ では、この候補を加えた包絡線がそれまでの包絡線を厳密に下回る。

可変候補の入口付近をさらに改善するため、次の固定係数も加える。各行の右端は、その候補を加えた選択上界が、加える前のGaussian選択上界を厳密に下回ると証明した区間である。適用範囲は記載した入口以上の全域であり、右端に制限されない。

| 入口 $T$ | 係数 $C$ | 厳密な改善を証明した範囲 |
|---:|---:|---|
| $5\cdot 10^{10}$ | $3869/10000$ | $5\cdot 10^{10} \le L \le 5.04\cdot 10^{10}$ |
| $7\cdot 10^{10}$ | $222/625$ | $7\cdot 10^{10} \le L \le 7.04\cdot 10^{10}$ |
| $1.5\cdot 10^{11}$ | $1567/5000$ | $1.5\cdot 10^{11} \le L \le 1.501\cdot 10^{11}$ |

### 可変Gaussian係数

$L \ge 2\cdot 10^{12}$ では、次の係数も選択上界に加える。

$$
a_G(L)=\frac{2(20115621/50000000)
+(61/100)(28794111/12500000)/\sqrt L+39/L}{10971611/5000000},
\qquad C_G(L)=\frac{21}{10}a_G(L)^2.
$$

GRHの下で、すべての奇合成数について $q_{\mathrm{MR}}(n) \le C_G(L)L^2$ が成り立つ。この係数は対象範囲全体で $1411811/5000000$ を厳密に下回り、選択上界も従来の包絡線を厳密に下回る。三素因子にはGaussian比較を使い、それ以外の分類には同じ半径でtriangular比較の条件を満たすことを示す。

### 素数への丸め

実数上界 $R \ge 2$ に対して、 $R$ 以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R) \le R$ が成り立ち、 $p \le R$ を満たす素数 $p$ は丸め後も範囲内にある。また、 `primeRound_mono` はこの丸めの単調性を示す。定義と定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

`fixedImprovedPrime n` は `fixedImprovedSelected n` を丸める。2・3と表の固定素数は丸めても同じ値である。素数への丸めは調べる素数基数の集合を変えずに、実数上界をその集合の最大要素へ置き換える。

### 全域の累積上界

$Q_{\mathrm{MR}}(N)$ を $9 \le n \le N$ の奇合成数 $n$ に対する最小拒否素数の最大値とし、対象がないときは0とする。累積上界は次の共通尺度の基底と8個のtriangular候補から構成する。 $L \ge 0$ に対して

$$
B(L)=\min\left\lbrace G(L),\frac49 L^2,
\max\left\lbrace\frac49 70000^2,\frac7{16}L^2\right\rbrace\right\rbrace.
$$

ここで $G(L)$ は既存のGaussian共通尺度上界 `gaussianTightHistoryBase` である。従来の累積上界を定める8候補は [HistoryCumulativeBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HistoryCumulativeBounds.lean) の `historyProfiles` にある。これらの入口と係数を昇順に $(E_i,F_i)$ とし、 $H_0(L)=B(L)$ とする。

$$
H_i(L)=\min\left\lbrace H_{i-1}(L),
\max\left\lbrace H_{i-1}(E_i),F_iL^2\right\rbrace\right\rbrace.
$$

GRHの下ですべての自然数 $N$ について $Q_{\mathrm{MR}}(N) \le H_8(\ln N) \le (4/9)(\ln N)^2$ が成り立つ。さらに $\ln N \ge 71000$ では $Q_{\mathrm{MR}}(N) \le (7/16)(\ln N)^2$ となる。入口より前の入力は $(4/9)70000^2$ が覆う。triangular候補の入口より前は $H_{i-1}(E_i)$ が覆う。証明は [HighCoefficientCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientCumulative.lean) にある。

累積上界の計算では [HighWindowCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowCumulative.lean) の `highWindowHistoryProfiles` にある15候補を使う。入口と係数を昇順に $(S_j,D_j)$ とし、 $K_0(L)=B(L)$ とする。

$$
K_j(L)=\min\left\lbrace K_{j-1}(L),
\max\left\lbrace K_{j-1}(S_j),D_jL^2\right\rbrace\right\rbrace
\qquad (j=1,\ldots,15)
$$

と定める。各入口より前の入力には $K_{j-1}(S_j)$ を使う。GRHの下で $Q_{\mathrm{MR}}(N) \le \min\lbrace H_8(\ln N),K_{15}(\ln N)\rbrace$ が成り立つ。証明と定義は [HighWindowCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowCumulative.lean) にある。点ごとの包絡線に全域単調性は要求しない。

可変係数を含む累積上界は、さらに次の3つの入口履歴付き上界との最小値をとる。

$$
V(L)=\min\left\lbrace H_8(L),K_{15}(L),
\max\left\lbrace\frac49 70000^2,C_{\mathrm{pair}}(L)L^2\right\rbrace,
\max\left\lbrace H_{\mathrm{pair}},C_{\mathrm{fac}}(L)L^2\right\rbrace,
\max\left\lbrace H_{\mathrm{pair}},\frac{427}{1000}L^2\right\rbrace
\right\rbrace.
$$

ここで $H_{\mathrm{pair}}=\max\lbrace(4/9)70000^2,C_{\mathrm{pair}}(80000)80000^2\rbrace$ である。最初の定数は $L < 70000$、 $H_{\mathrm{pair}}$ は $L < 80000$ の入力を覆う。各可変係数は適用範囲内で増加するため、現在の $L$ による式をその範囲の過去の入力にも使える。Leanでは自然数上端 $N$ について `meanCumulative N` を定義し、GRHの下で $Q_{\mathrm{MR}}(N) \le \mathrm{meanCumulative}(N)$ を証明している。詳細は [MeanEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/MeanEnvelope.lean) にある。

切替前の値を保持する関数 $J(L)$ と現行の累積上界 $W(L)$ を次のように定める。

$$
J(L)=\begin{cases}0&L < 1.82\cdot 10^{12},\\
\sqrt{28237/100000}(1.82\cdot 10^{12})&L \ge 1.82\cdot 10^{12},\end{cases}
$$

$$
W(L)=\min\left\lbrace V(L),\max\left\lbrace\frac49(3\cdot 10^{10})^2,
\max\lbrace a(L)L,J(L)\rbrace^2\right\rbrace\right\rbrace.
$$

最初の定数は可変triangular候補の入口以前を覆い、 $J(L)$ は係数切替以前の履歴を保持する。GRHの下で $Q_{\mathrm{MR}}(N) \le W(\ln N)$ が成り立つ。Leanでの定義と証明は [TriangularAdaptiveCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularAdaptiveCumulative.lean) にある。

Gaussian候補を含む累積上界は、 $T=2\cdot 10^{12}$ として

$$
W_G(L)=\min\left\lbrace W(L),\max\left\lbrace
\mathrm{triangularAdaptiveCap}(T),C_G(L)L^2\right\rbrace\right\rbrace
$$

である。入口以前にはtriangular側の共通尺度上界を用いる。 $a_G(L)L$ の単調性により、入口以後の過去の入力を上端のGaussian候補で覆う。GRHの下で $Q_{\mathrm{MR}}(N) \le W_G(\ln N)$ が成り立つ。証明は [GaussianAdaptiveCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianAdaptiveCumulative.lean) にある。

固定係数の3候補を含む現行の累積上界は、上表の入口と係数を $(T_i,C_i)$ として

$$
W_F(L)=\min\left\lbrace W_G(L),
\min_{i=1,2,3}\max\left\lbrace\mathrm{triangularAdaptiveCap}(T_i),C_iL^2\right\rbrace
\right\rbrace.
$$

各入口以前にはtriangular側の共通尺度上界を保持する。GRHの下で $Q_{\mathrm{MR}}(N) \le W_F(\ln N)$ が成り立つ。

### 包絡線の構成

$n \ge 3000$ では固定素数候補、適用条件を満たすtriangular上界、および $(4/9)L^2$ の最小値をとる。さらに $L \ge 70000$ では $(7/16)L^2$ と $C_{\mathrm{pair}}(L)L^2$、 $L \ge 80000$ では $C_{\mathrm{fac}}(L)L^2$ と $(427/1000)L^2$ を加える。 $n < 3000$ では小域の値2または3を使う。

### 上界式と証明済みの適用条件

以下の解析候補と表の固定素数上界にはGRHを仮定する。有限区間の2と3は無条件である。

| 適用条件 | 上界式 |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| 固定素数表にある $L \le L_0$ | 表の各素数23〜53 |
| 各 $T_i \le L$ | $C_iL^2$、 $i=1,\ldots,14$ |
| 奇合成数 $n \ge 9$ | $(4/9)L^2$ |
| 奇合成数 $n \ge 9$、 $70000 \le L$ | $(7/16)L^2$ |
| 奇合成数 $n \ge 9$、 $70000 \le L$ | $C_{\mathrm{pair}}(L)L^2$ |
| 奇合成数 $n \ge 9$、 $80000 \le L$ | $C_{\mathrm{fac}}(L)L^2$ |
| 奇合成数 $n \ge 9$、 $80000 \le L$ | $(427/1000)L^2$ |

## 上界式の適用区間

次の表では $n \ge 3000$ の各行にある候補と $(4/9)L^2$ の最小値をとり、 $L \ge 70000$ では $(7/16)L^2$ と $C_{\mathrm{pair}}(L)L^2$、 $L \ge 80000$ では $C_{\mathrm{fac}}(L)L^2$ と $(427/1000)L^2$ も加える。小域の2行は記載した値をそのまま使う。

| 適用条件 | 現行の上界を構成する候補 |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| $\ln3000 \le L \le 8.0901$ | $23$ |
| $8.0901 < L \le 8.3320$ | $29$ |
| $8.3320 < L \le 9.0031$ | $31$ |
| $9.0031 < L \le 9.3961$ | $37$ |
| $9.3961 < L \le 9.9619$ | $43$ |
| $9.9619 < L \le 10.4895$ | $47$ |
| $10.4895 < L \le 10.9671$ | $53$ |
| $10.9671 < L < T_1$ | $(4/9)L^2$、 $L \ge 70000$ では $(7/16)L^2$ |
| $T_i \le L < T_{i+1}$、 $1 \le i \le 13$ | $C_iL^2$ |
| $T_{14} \le L$ | $C_{14}L^2$ |

### 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は表の候補と $4/9$ の上界から定めた $U_{\mathrm{MR}}(n)$、黒の点線は $(4/9)(\ln n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

基数を素数 $p_1=2,p_2=3,p_3=5,\ldots$ の順に選んでMiller–Rabinテストを行う。青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項、すなわち最初の $k-1$ 個の素数基数 $p_1,\ldots,p_{k-1}$ によるテストをすべて通過する最小の奇合成数である。縦座標はその入力を棄却する最小素数基数 $q_{\mathrm{MR}}(n)$ であり、記録更新点では $Q_{\mathrm{MR}}(n)$ と一致する。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるため、点の縦座標は3となる。青緑の階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。

描画範囲は $9 \le n \le 10^{64}$、縦軸は $10^0$ から $10^4$ である。点ごとの上界を描いており、累積上界としての単調性は仮定していない。挿入図は $n \ge 3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。この比の下降は分子である上界 $U_{\mathrm{MR}}(n)$ の下降を意味しない。可変係数とtriangular候補が有効になる高域の入口は描画範囲外であり、そこで入力ごとの上界に下降が生じても、累積最大値の下降を表すものではない。

図の数値計算はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

### 累積上界と点ごとの上界の比較

![MR累積上界と点ごとの候補](figures/mr_cumulative_high_comparison.svg)

橙線は累積最大値の上界 $W_F(L)/L^2$、青い破線は点ごとの上界 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。黒点線の高さは $4/9$ である。実数軸の描画と、Leanによる自然数上端の証明は区別する。[PNG版](figures/mr_cumulative_high_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
