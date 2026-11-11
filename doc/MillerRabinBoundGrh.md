# Miller–Rabinの拒否素数上界

GRHの下で、奇合成数を棄却する最小の素数底には、下記の点ごとの上界と累積上界がある。図は有限区間の底2・3、係数 $1/4$ と $3/11$、および区分上界を描く。図の選択式と累積履歴は、それぞれのLean定理から構成した値である。

## 対象と記号

$n > 1$ を奇合成数、 $L = \ln n$ とし、 $q_{\mathrm{MR}}(n)$ を $n$ がMiller–Rabinテストに不合格となる最小の素数底とする。 $Q_{\mathrm{MR}}(N)$ は $9 \le n \le N$ の奇合成数に対する $q_{\mathrm{MR}}(n)$ の最大値である。対象がない場合は0とする。

本ページの解析的な上界は一般化Riemann予想（GRH）を仮定する。GRH自体を証明するものではない。底2・3の有限分類はGRHを仮定しない。最小拒否素数の存在とMiller–Rabin合格条件の定義は [Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) と関連する上界定理にある。

## 点ごとの包絡線

GRHの下、全ての奇合成数 $n > 1$ について、最小拒否素数には次の上界がある。

$$
q_{\mathrm{MR}}(n) \le \max\lbrace2,(3/11)L^2\rbrace.
$$

[ThreeEleventhsGRH.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/ThreeEleventhsGRH.lean) の `three_eleven_least_of_grh` は、この範囲の拒否素数とその最小性を示す。`composite_least_prime_three_eleven_grh` は最小拒否素数について上式を直接示す。さらに [QuarterBridge465.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/QuarterBridge465.lean) の `quarter_least_through465` は、 $L \le 465$ で係数 $1/4$ のmax形を示す。

高域の上界を表すため、 $D = 24439/50000$、 $A = 3/(8(27/25)^5)$、 $V = 53/500$ として、

$$
B_0(L)=\left(\frac{V+\sqrt{V^2+4DAL}}{2D}\right)^4
$$

とおく。[RefinedPiecewiseWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedPiecewiseWitness.lean) の区分上界は $L \ge 10000$ で $B_0(L)$ に一致する。図の点ごとの上界は、 $c(L)=1/4$（ $L \le 465$ ）、それ以外では $c(L)=3/11$ として、次の枝で表せる。

$$
U_{\mathrm{new}}(n)=
\begin{cases}
2 & 9 \le n < 2047,\\
3 & 2047 \le n < 3000,\\
c(L)L^2 & 3000 \le n,\quad L < 10000,\\
\min\lbrace(3/11)L^2,B_0(L)\rbrace & 10000 \le L.
\end{cases}
$$

小入力の有限分類は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。 $3000 \le n$ なら $8 \le L$ であり、後の枝には $1/4$ または $3/11$ の上界を使い、 $L \ge 10000$ では $B_0(L)$ との小さい方を使う。この簡略形と描画スクリプトの選択式の一致は、 $\ln 3000 \le L \le 10^{15}$ の標本点で数値確認した。全域での一致はLeanでは証明していない。

## 上界を与える定理と証明方法

| 範囲・役割 | 主な定理 | 証明方法 |
|---|---|---|
| $9 \le n < 3000$ | `exists_primeWitness_lt_3000` | 小入力を有限分類し、底2または3の不合格を検証する。 |
| 全域の係数 $3/11$ | `three_eleven_least_of_grh` | 対数の範囲と因数構造で場合分けし、一様型の中域と高域、非一様型を統合する。 |
| $L \le 465$ の係数 $1/4$ | `quarter_least_through465` | 一様型と非一様型の区間定理を統合する。 |
| $L \ge 1000$、小さいFermat部分群指数 | `refined_index16_witness` | 局所部分群に対する証人と、一様Korselt三素数積の場合を分ける。後者は六次有理極核のEuler項・Gamma項・零点和と有限主和を評価し、端点の有理数計算で残差を抑える。 |
| $L \ge 1000$、大きいFermat部分群指数 | `refined_24_inner_witness`、`refined_24_outer_witness` | 幅24の三角核について二尺度の明示公式と指標族平均を使う。内側ではAbel和とChebyshev関数の下界、外側では幅18の二つの支持和を使い、有限主和と数値ギャップから拒否素数を得る。 |
| 高域の区分上界 | `refined_piecewise_witness` | $L \ge 10000$ では $B_0(L)$ 以下の拒否素数を与える。 |

## 係数 $3/11$ の全域接続

`three_eleven_least_of_grh` は $L \le 10300$ を先に扱い、それより大きい入力を一様Korselt型と非一様型に分ける。一様型は $L \le 4000000$ の累積区間定理と、それ以降の高域定理を使う。非一様型は $L \ge 8$ の係数 $1/4$ 定理を使う。これらを小入力の結果と統合し、最小拒否素数を選ぶ。

## RefinedSixPolePiecewise.lean：区分係数と証人の接続

[RefinedSixPolePiecewise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPolePiecewise.lean) は区分係数を定め、 $L \ge 10000$ の式を与える。[RefinedPiecewiseWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedPiecewiseWitness.lean) の `refined_piecewise_witness` は、GRHの下、 $L \ge 8$ の奇合成数に対して対応する拒否素数を与える。高域の証明では、Fermat部分群の指数に応じて六次有理極核または幅24の三角核による評価を使う。

係数 $3/11$ の素数判定同値 `prime_millerRabin_027_criterion` は [PrimeMillerRabinWitnessSolution.lean](../ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessSolution.lean) にある。奇数 $n > 1$ について、指定範囲内のすべての素数底で合格することと $n$ の素数性が同値である。合成数を排除する向きにGRHを使い、素数が対象の底で合格する向きには使わない。

## 累積上界

GRHの下、係数 $3/11$ のmax形は対数の単調性によって累積最大値の上界にもなる。図の範囲では、 $H_0(L)=\max\lbrace2,c(L)L^2\rbrace$ とし、 $T=10000$ として累積上界を次の形で表せる。

$$
H(L)=
\begin{cases}
H_0(L) & L < T,\\
\min\lbrace H_0(L),\max\lbrace H_0(T),B_0(L)\rbrace\rbrace & T \le L.
\end{cases}
$$

入口以前の履歴と入口以降の $B_0$ 上界の大きい方で全入力を覆う。図の選択式との一致は同じ範囲の標本点で数値確認した。この簡略化の全域での一致はLeanでは証明していない。

## 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

橙線は $U_{\mathrm{new}}(n)$、黒点線は $\max\lbrace2,(3/11)(\ln n)^2\rbrace$、紫の一点鎖線は $L \le 465$ の係数 $1/4$ の上界を示す。横軸は $\ln(\ln n)$ に線形な尺度、縦軸は対数軸である。主図は $9 \le n \le 10^{256}$、挿入図は $3000 \le n \le e^{10^{14}}$ を対象とし、挿入図では上界を $(\ln n)^2$ で割る。

青緑の点は [OEIS A006945](https://oeis.org/A006945) の記録となる奇合成数と、その最小拒否素数を示す。階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。[PNG版](figures/mr_upper_bound_comparison.png)

### 累積上界と点ごとの上界

![MR累積上界と点ごとの上界](figures/mr_cumulative_high_comparison.svg)

橙線は $H(L)/L^2$、青い破線は点ごとの上界 $U_{\mathrm{new}}(n)/(\ln n)^2$、黒点線は係数 $3/11$ のmax形を $L^2$ で割った値を示す。切替点では以前の履歴を保持するため、累積上界は点ごとの上界と異なる場合がある。[PNG版](figures/mr_cumulative_high_comparison.png)

図は数値描画であり、Leanによる自然数入力の証明と区別する。生成方法は [図の一覧](figures/README.md) にある。

## 公理依存の確認

次の宣言について、`#print axioms` で推移的な依存を確認できる。

```lean
import PseudoPrime
import ComparatorChallenges.PrimeMillerRabinWitness.PrimeMillerRabinWitnessSolution

#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_witness
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_branches
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.composite_least_prime_three_eleven_grh
#print axioms ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_027_criterion
#print axioms ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_log_nine_criterion
```

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
