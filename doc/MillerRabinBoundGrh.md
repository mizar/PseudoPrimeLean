# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

GRHの下で、奇合成数 $n \ge 9$ には $(4/9)(\ln n)^2$ 以下のMiller–Rabin拒否素数が存在する。証人と最小証人の定理は [FourNinthsBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsBounds.lean)、素数判定条件の同値は [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) にある。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` から利用できる。

さらに $\ln n \ge 70000$ では、上界を $(7/16)(\ln n)^2$ に改善できる。証人と最小証人の定理は [HighCoefficientBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientBounds.lean) にある。

公開選択上界 $U_{\mathrm{MR}}(n)$ は [HighWindowExtended.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtended.lean) の `highWindowExtended` である。各入口から下表の係数を持つ候補を加える。 `exists_least_highWindowExtended` は最小拒否素数が選択値以下であることを示す。 `highWindowExtendedPrime` は選択値を素数へ丸め、同じ最小証人を保持する。

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
| `highWindow_lt_previous` | $4.5\cdot10^{10} \le \ln n < 10^{11}$ における従来の選択上界からの厳密な改善 | [HighWindowComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowComparison.lean) |
| `highWindow_lt_previous_early` | $3.8\cdot10^{10} \le \ln n < 4\cdot10^{10}$ における従来の選択上界からの厳密な改善 | [HighWindowComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowComparison.lean) |
| `highWindowExtended_lt_0323`・`highWindowExtended_lt_0296`・`highWindowExtended_lt_0288` | 追加3候補の各入口から次の既存入口までにおける厳密な改善 | [HighWindowExtendedComparison.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtendedComparison.lean) |
| `cumulativeLeastPrime_le_highCoeff_quad` | $\ln N \ge 71000$ における累積最大値の $7/16$ 上界 | [HighCoefficientCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientCumulative.lean) |
| `cumulativeLeastPrime_le_highWindow` | 追加した高域候補を含む累積最大値の上界 | [HighWindowCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowCumulative.lean) |
| `exists_primeWitness_lt_3000` | GRHを仮定しない奇合成数 $9 \le n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

係数 $4/9$ の定理では重複込みの素因数個数により奇合成数を分類する。素因数が3個以上なら既存の因数個数による上界を使う。2個の場合は平方と異なる2素数の積に分け、局所核の大きさと素数積の個数を比較する。低域では重複を許す素数積と有限個の有理数証明書を使い、中域では素数個数の解析的下界と61行の証明書を使う。 $\ln n \ge 1024$ は一様な評価で扱う。小さい入力と固定素数23・29の既存定理を接続し、全域を覆う。実装は [FourNinthsFiniteWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsFiniteWitness.lean) と [FourNinthsHighWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsHighWitness.lean) を経て全域定理に至る。

高域の $7/16$ の定理でも、重複込みの素因数個数で分類する。4個以上は因数個数の上界で扱う。2個の場合と、3個で重複因子がある場合は局所核と素数積を比較する。相異なる3素数の場合は、非Korselt因子または異なる2進付値があれば因子の選択を使い、残る場合は導手の対数和を用いたGaussian評価を適用する。素数積の計数は連続した対数区間で評価し、遠い高域では既存の係数0.4145の定理につなぐ。詳細は [HighCoefficientBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientBounds.lean) とそのimport先にある。

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

と書く。現在の実数上界を $U_{\mathrm{MR}}(n)=\mathrm{highWindowExtended}(n)$ とする。GRHの下で $q_{\mathrm{MR}}(n) \le U_{\mathrm{MR}}(n)$ が成り立つ。

### 有限区間 $9 \le n < 3000$ の上界

$9 \le n < 2047$ では2、 $2047 \le n < 3000$ では3を返す。底2または底3での拒否を有限分類で証明し、素数証人と最小素数証人へ接続する。この範囲ではGRHは不要である。定義と証人定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

公開数値関数の仕様としても、すべての自然数 $2047 \le n < 3000$ で `highWindowExtended n` と `highWindowExtendedPrime n` はともに3である。この等式には奇数性や合成数性を仮定しない。 $n < 2047$ では両関数が2を返す。値3の等式は [HighWindowExtended.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtended.lean) で示す。

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

triangular kernelの明示公式から、各入口 $T_i$ 以上で $C_iL^2$ 以下の素数証人を得る。次の表には公開上界の包絡線を更新する候補を入口順に示す。各候補は次の入口以降も有効だが、より小さい係数の候補に引き継がれる。

| $i$ | 適用条件 $T_i \le L$ | 係数 $C_i$ |
|---:|---|---|
| 1 | $3.8\cdot10^{10} \le L$ | $423/1000=0.423$ |
| 2 | $4\cdot10^{10} \le L$ | $829/2000=0.4145$ |
| 3 | $4.5\cdot10^{10} \le L$ | $2/5=0.4$ |
| 4 | $6\cdot10^{10} \le L$ | $369/1000=0.369$ |
| 5 | $8\cdot10^{10} \le L$ | $173/500=0.346$ |
| 6 | $10^{11} \le L$ | $663/2000=0.3315$ |
| 7 | $1.2\cdot10^{11} \le L$ | $323/1000=0.323$ |
| 8 | $2.5\cdot10^{11} \le L$ | $374/1250=0.2992$ |
| 9 | $3\cdot10^{11} \le L$ | $37/125=0.296$ |
| 10 | $5\cdot10^{11} \le L$ | $2891/10000=0.2891$ |
| 11 | $6\cdot10^{11} \le L$ | $36/125=0.288$ |
| 12 | $1.08\cdot10^{12} \le L$ | $28399/100000=0.28399$ |
| 13 | $1.48\cdot10^{12} \le L$ | $28289/100000=0.28289$ |
| 14 | $1.82\cdot10^{12} \le L$ | $1411811/5000000=0.2823622$ |

各profileの証明書と証人定理は [HighWindowProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowProfiles.lean)、[HighWindowBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowBounds.lean)、[TriangularTunedProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedProfiles.lean)、[TriangularTunedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedBounds.lean)、[TriangularProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularProfiles.lean)、[TriangularProfileBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularProfileBounds.lean) にある。

### 素数への丸め

実数上界 $R \ge 2$ に対して、 $R$ 以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R) \le R$ が成り立ち、 $p \le R$ を満たす素数 $p$ は丸め後も範囲内にある。また、 `primeRound_mono` はこの丸めの単調性を示す。定義と定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

`highWindowExtendedPrime n` は `highWindowExtended n` を丸める。2・3と表の固定素数は丸めても同じ値である。素数への丸めは調べる素数基数の集合を変えずに、実数上界をその集合の最大要素へ置き換える。

### 全域の累積上界

$Q_{\mathrm{MR}}(N)$ を $9 \le n \le N$ の奇合成数 $n$ に対する最小拒否素数の最大値とし、対象がないときは0とする。累積上界は次の共通尺度の基底と8個のtriangular候補から構成する。 $L \ge 0$ に対して

$$
B(L)=\min\left\lbrace \frac49 L^2,
\max\left\lbrace\frac49 70000^2,\frac7{16}L^2\right\rbrace\right\rbrace.
$$

従来の累積上界を定める8候補は [HistoryCumulativeBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HistoryCumulativeBounds.lean) の `historyProfiles` にある。これらの入口と係数を昇順に $(E_i,F_i)$ とし、 $H_0(L)=B(L)$ とする。

$$
H_i(L)=\min\left\lbrace H_{i-1}(L),
\max\left\lbrace H_{i-1}(E_i),F_iL^2\right\rbrace\right\rbrace.
$$

GRHの下ですべての自然数 $N$ について $Q_{\mathrm{MR}}(N) \le H_8(\ln N) \le (4/9)(\ln N)^2$ が成り立つ。さらに $\ln N \ge 71000$ では $Q_{\mathrm{MR}}(N) \le (7/16)(\ln N)^2$ となる。入口より前の入力は $(4/9)70000^2$ が覆う。triangular候補の入口より前は $H_{i-1}(E_i)$ が覆う。証明は [HighCoefficientCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighCoefficientCumulative.lean) にある。

累積上界の計算では上表の14候補に加え、従来の履歴に含まれる1候補を保持する。この15候補を入口の昇順に $(S_j,D_j)$ とし、 $K_0(L)=B(L)$ とする。

$$
K_j(L)=\min\left\lbrace K_{j-1}(L),
\max\left\lbrace K_{j-1}(S_j),D_jL^2\right\rbrace\right\rbrace
\qquad (j=1,\ldots,15)
$$

と定める。各入口より前の入力には $K_{j-1}(S_j)$ を使う。GRHの下で $Q_{\mathrm{MR}}(N) \le \min\lbrace H_8(\ln N),K_{15}(\ln N)\rbrace$ が成り立つ。証明と定義は [HighWindowCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowCumulative.lean) にある。点ごとの包絡線に全域単調性は要求しない。

![MR累積上界と点ごとの候補](figures/mr_cumulative_high_comparison.png)

図の橙線は累積最大値の上界 $\min\lbrace H_8(L),K_{15}(L)\rbrace/L^2$、青い破線は点ごとの上界 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。黒点線の高さは $4/9$ である。実数軸の描画と、Leanによる自然数上端の証明は区別する。

### 包絡線の構成

$n \ge 3000$ では固定素数候補、適用条件を満たすtriangular上界、および $(4/9)L^2$ の最小値をとる。さらに $L \ge 70000$ では $(7/16)L^2$ を加える。 $n < 3000$ では小域の値2または3を使う。高域候補のガードは [HighWindowExtended.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/HighWindowExtended.lean) とそのimport先にある。

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

## 上界式の適用区間

次の表では $n \ge 3000$ の各行にある候補と $(4/9)L^2$ の最小値をとり、 $L \ge 70000$ では $(7/16)L^2$ も加える。小域の2行は記載した値をそのまま使う。

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

描画範囲は $9 \le n \le 10^{1024}$ である。点ごとの上界を描いており、累積上界としての単調性は仮定していない。挿入図は $n \ge 3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。この比の下降は分子である上界 $U_{\mathrm{MR}}(n)$ の下降を意味しない。triangular候補が有効になる高域の入口は描画範囲外であり、そこで入力ごとの上界に下降が生じても、累積最大値の下降を表すものではない。

図の数値計算はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
