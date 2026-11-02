# PrimeTestBounds.MillerRabin　GRH下の素数判定同値と証人上界

GRHの下で、奇合成数 $n \ge 9$ には $(4/9)(\ln n)^2$ 以下のMiller–Rabin拒否素数が存在する。証人と最小証人の定理は [FourNinthsBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsBounds.lean)、素数判定条件の同値は [FourNinthsCriterion.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean) にある。名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、 `import PseudoPrime` から利用できる。

公開選択上界 $U_{\mathrm{MR}}(n)$ は [FourNinthsEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsEnvelope.lean) の `fourNinthsSelectedEnvelope` である。 $n < 3000$ の既存値を保ち、 $n \ge 3000$ では `nextTunedSelectedEnvelope` と $(4/9)(\ln n)^2$ の最小値をとる。 `exists_least_fourNinthsSelected` はGRHの下で最小拒否素数がこの値以下であることを示す。 `fourNinthsPrimeEnvelope` は選択値を素数へ丸め、 `exists_least_fourNinthsPrime` が同じ最小証人を保持する。

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
| `exists_primeWitness_lt_3000` | GRHを仮定しない奇合成数 $9 \le n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

係数 $4/9$ の定理では重複込みの素因数個数により奇合成数を分類する。素因数が3個以上なら既存の因数個数による上界を使う。2個の場合は平方と異なる2素数の積に分け、局所核の大きさと素数積の個数を比較する。低域では重複を許す素数積と有限個の有理数証明書を使い、中域では素数個数の解析的下界と61行の証明書を使う。 $\ln n \ge 1024$ は一様な評価で扱う。小さい入力と固定素数23・29の既存定理を接続し、全域を覆う。実装は [FourNinthsFiniteWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsFiniteWitness.lean) と [FourNinthsHighWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsHighWitness.lean) を経て全域定理に至る。

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

と書く。現在の実数上界を $U_{\mathrm{MR}}(n)=\mathrm{fourNinthsSelectedEnvelope}(n)$ とする。GRHの下で $q_{\mathrm{MR}}(n) \le U_{\mathrm{MR}}(n)$ が成り立つ。

### 有限区間 $9 \le n < 3000$ の上界

$9 \le n < 2047$ では2、 $2047 \le n < 3000$ では3を返す。底2または底3での拒否を有限分類で証明し、素数証人と最小素数証人へ接続する。この範囲ではGRHは不要である。定義と証人定理は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。

公開数値関数の仕様としても、すべての自然数 $2047 \le n < 3000$ で `fourNinthsSelectedEnvelope n` と `fourNinthsPrimeEnvelope n` はともに3である。この等式には奇数性や合成数性を仮定しない。 $n < 2047$ では両関数が2を返す。値3と局所単調性は [FourNinthsEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsEnvelope.lean) で示し、2の分岐は同ファイルの定義と小域定理から従う。

### 固定素数上界23〜79と有限principal和

固定半径 $y$ に対して、次の実際のvon Mangoldt和を使う。

$$
R(x)=\sum_{1 \le m \le x}\Lambda(m)\left(\frac1m-\frac1x\right),\qquad
S(x)=\sum_{1 \le m \le x}\Lambda(m)\ln\frac xm.
$$

$\ell(y)$ は後述する有理関数とする。各半径で、次の2本の下界を有限和から証明する。

$$
2\ln y-\ell(y)+\delta_R \le R(y^2),
$$

$$
y^2-\frac y{20}-\frac{1839}{500}\ln y-\frac{21}{20}+\delta_S \le S(y^2).
$$

各半径で既存の有理部分和が与える余裕を使い、補強量を分母 $10^6$ の有理数に固定する。73以下の21素数について対数の有理区間をTaylor級数8項で検証し、相異なる最大30個の素数冪の寄与を加える。残りの項は非負なので、これらの部分和は元の和の下界となる。

後述する $D_e(y)$ と $F_{\mathrm{pt}}(y)$ を使うと、強化した比較gapは

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

各行は記した上端以下の全域で使え、個別の証人定理には $n \ge 3000$ や前行の上端を仮定しない。23〜73の13行のデータは [EndpointFiniteCredits.lean](../PseudoPrime/Analysis/EndpointFiniteCredits.lean)、素数証人・最小素数証人は [EndpointFiniteTuned.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointFiniteTuned.lean) にある。固定79には30項の素数冪の寄与と、半径 $5694/625$ の対数証明書を使う。素数79の寄与はこの部分和に含まれない。実際の和・gap・証人の接続は [Analysis/EndpointPrime79.lean](../PseudoPrime/Analysis/EndpointPrime79.lean)、[LLS/PaperStatements/EndpointPrime79.lean](../PseudoPrime/LLS/PaperStatements/EndpointPrime79.lean)、[MillerRabin/EndpointPrime79.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPrime79.lean) に分けてある。

### 固定79の適用範囲

入力が3000以上で $L\le12659/1000$ のとき、固定素数上界79を使える。証明書は有限principal和の32個の相異なる項を使う。2047未満の値2と、2047以上3000未満の値3を優先し、他の有効な上界との最小値をとる。

証人への接続は [Endpoint79TunedEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Endpoint79TunedEnvelope.lean)、選択式への接続は [NextTunedWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/NextTunedWitnessEnvelope.lean) にある。

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

pointwise gapは正確に $D_e(y)(F_{\mathrm{pt}}(y)-L)$ となる。逆関数半径でgapが0になる場合も、最小素数証人とその平方根の中点を用いる離散的な議論により証人上界が成り立つ。定義・単調性・逆関数は [LLS/PaperStatements/EndpointPointwiseRoot.lean](../PseudoPrime/LLS/PaperStatements/EndpointPointwiseRoot.lean)、全奇合成数の素数証人・最小素数証人は [MillerRabin/EndpointPointwiseRoot.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/EndpointPointwiseRoot.lean) にある。

### Gaussian上界

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

とする。現行の包絡線に使う3候補は次のとおりである。

$$
G_{35}(L)=\max\lbrace35000,V_{837/200}(L)\rbrace,\qquad
G_{50}(L)=\max\lbrace50000,V_{1967/500}(L)\rbrace
$$

である。

$$
G_A(L)=\max\lbrace(6/5)(91/10)^4,V_{36/5}(L)\rbrace
$$

とする。

以降、 $G_+(L)=\min\lbrace G_{35}(L),G_{50}(L)\rbrace$ とする。これらは $L \ge 63$ で適用できる。数値評価と証人定理は [GaussianTightBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianTightBounds.lean) と [GaussianSeededSurplusBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/GaussianSeededSurplusBounds.lean) にある。

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

各profileは自分の入口 $T_i$ 以上でのみ有効になる。定数の証明書は [TriangularTunedProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedProfiles.lean)、素数証人・最小素数証人は [TriangularTunedBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularTunedBounds.lean) にある。

第8行の定数と証人定理は [TriangularProfiles.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularProfiles.lean) と [TriangularProfileBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/TriangularProfileBounds.lean) にある。

### 素数への丸め

実数上界 $R \ge 2$ に対して、 $R$ 以下の最大素数を $\mathrm{primeRound}(R)$ とする。 $R < 2$ では値を変えない。すべての実数で $\mathrm{primeRound}(R) \le R$ が成り立ち、 $p \le R$ を満たす素数 $p$ は丸め後も範囲内にある。また、 `primeRound_mono` はこの丸めの単調性を示す。定義と定理は [PrimeCutoff.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/PrimeCutoff.lean) にある。

`fourNinthsPrimeEnvelope n` は `fourNinthsSelectedEnvelope n` を丸める。2・3・固定23〜79は丸めても同じ値である。素数への丸めは調べる素数基数の集合を変えずに、実数上界をその集合の最大要素へ置き換える。

### 全域の累積上界

$Q_{\mathrm{MR}}(N)$ を $9 \le n \le N$ の奇合成数 $n$ に対する最小拒否素数の最大値とし、対象がないときは0とする。累積上界は次の共通尺度の基底と8個のtriangular候補から構成する。

$$
B(L)=\min\left\lbrace \frac49 L^2, G_A(\max\lbrace63,L\rbrace)\right\rbrace.
$$

入口の昇順に $H_0(L)=B(L)$ とし、表の $C_i,T_i$ に対して

$$
H_i(L)=\min\left\lbrace H_{i-1}(L),
\max\left\lbrace H_{i-1}(T_i),C_iL^2\right\rbrace\right\rbrace.
$$

GRHの下ですべての自然数 $N$ について $Q_{\mathrm{MR}}(N) \le H_8(\ln N) \le (4/9)(\ln N)^2$ が成り立つ。入口より前の入力は $H_{i-1}(T_i)$ が覆う。証明は [FourNinthsCumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsCumulative.lean) の `cumulativeLeastPrime_le_fourNinths` と `cumulativeLeastPrime_le_four_ninths_log_sq` にある。点ごとの包絡線に全域単調性は要求しない。

![MR累積上界と点ごとの候補](figures/mr_cumulative_high_comparison.png)

図は高域の累積上界と点ごとの候補を $L^2$ で割って示す。黒点線の高さは $4/9$ である。実数軸の描画と、Leanによる自然数上端の証明は区別する。

### 包絡線の構成

$n \ge 3000$ では固定素数候補、pointwise上界、Gaussian上界、適用条件を満たすtriangular上界、および $(4/9)L^2$ の最小値をとる。 $n < 3000$ では小域の値2または3を使う。表の $U_{\mathrm{sharp}}(n)$ は `sharpSelectedEnvelope n` であり、適用条件を満たす候補を含む。その定義は [SharpWitnessEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SharpWitnessEnvelope.lean) にある。候補のガードと数値関数の定義は [FourNinthsEnvelope.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FourNinthsEnvelope.lean) にある。

### 上界式と証明済みの適用条件

以下の解析候補と固定23〜79にはGRHを仮定する。有限区間の2と3は無条件である。

| 適用条件 | 上界式 |
|---|---|
| $9 \le n < 2047$ | $2$ |
| $2047 \le n < 3000$ | $3$ |
| 固定素数表にある $L \le L_0$ | 表の各素数23〜79 |
| $n\ge3000$、 $L\le12659/1000$ | 固定上界79 |
| すべての実数 $L$ | $U_{\mathrm{pt}}(L)$ |
| $63 \le L$ | $G_A(L)$ |
| $63 \le L$ | $G_{35}(L)$、 $G_{50}(L)$ |
| 各 $T_i \le L$ | $C_iL^2$、 $i=1,\ldots,8$ |
| 奇合成数 $n \ge 9$ | $(4/9)L^2$ |

## 上界式の適用区間

次の表では $n \ge 3000$ の各行にある候補と $(4/9)L^2$ の最小値をとる。小域の2行は記載した値をそのまま使う。

| 適用条件 | 現行の上界を構成する候補 |
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
| $12.6409 < L \le 12659/1000$ | $\min\lbrace U_{\mathrm{pt}}(L),79\rbrace$ |
| $12659/1000 < L < 63$ | $U_{\mathrm{pt}}(L)$ |
| $63 \le L < T_1$ | $\min\lbrace U_{\mathrm{sharp}}(n),G_A(L),G_+(L)\rbrace$ |
| $T_i \le L < T_{i+1}$、 $1 \le i \le 6$ | $\min\lbrace U_{\mathrm{sharp}}(n),G_A(L),G_+(L),C_iL^2\rbrace$ |
| $T_7 \le L$ | $\min\lbrace U_{\mathrm{sharp}}(n),G_A(L),G_+(L),C_7L^2\rbrace$ |

### 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

横軸は $\ln(\ln n)$ に線形なスケールとし、目盛りには $n$ を10の累乗で示す。縦軸は対数軸である。 $2^{64}$、 $2^{80}$、 $2^{128}$ の縦グリッドを重ねた。橙の実線は表の候補と $4/9$ の上界から定めた $U_{\mathrm{MR}}(n)$、黒の点線は $(4/9)(\ln n)^2$、青緑の点と階段線は最小素数証人の記録を表す。

基数を素数 $p_1=2,p_2=3,p_3=5,\ldots$ の順に選んでMiller–Rabinテストを行う。青緑の点の横座標は [OEIS A006945](https://oeis.org/A006945) の第 $k$ 項、すなわち最初の $k-1$ 個の素数基数 $p_1,\ldots,p_{k-1}$ によるテストをすべて通過する最小の奇合成数である。縦座標はその入力を棄却する最小素数基数 $q_{\mathrm{MR}}(n)$ であり、記録更新点では $Q_{\mathrm{MR}}(n)$ と一致する。例えば、 $n=2047$ は基数2で通過し、基数3で棄却されるため、点の縦座標は3となる。青緑の階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。

描画範囲は $9 \le n \le 10^{1024}$ である。点ごとの上界を描いており、累積上界としての単調性は仮定していない。挿入図は $n \ge 3000$ での比 $U_{\mathrm{MR}}(n)/(\ln n)^2$ を示す。この比の下降は分子である上界 $U_{\mathrm{MR}}(n)$ の下降を意味しない。triangular候補が有効になる高域の入口は描画範囲外であり、そこで入力ごとの上界に下降が生じても、累積最大値の下降を表すものではない。

図の数値計算はLeanの証明を代替しない。 [PNG版](figures/mr_upper_bound_comparison.png)

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
