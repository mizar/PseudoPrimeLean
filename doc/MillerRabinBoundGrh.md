# Miller–Rabinの拒否素数上界

GRHの下で、奇合成数を棄却する最小の素数底には、下記の点ごとの上界と累積上界がある。図は有限区間の底2・3、係数 $7/25$、および区分上界を描く。図の選択式と累積履歴は、それぞれのLean定理から構成した値である。

## 対象と記号

$n > 1$ を奇合成数、 $L = \ln n$ とし、 $q_{\mathrm{MR}}(n)$ を $n$ がMiller–Rabinテストに不合格となる最小の素数底とする。 $Q_{\mathrm{MR}}(N)$ は $9 \le n \le N$ の奇合成数に対する $q_{\mathrm{MR}}(n)$ の最大値である。対象がない場合は0とする。

本ページの解析的な上界は一般化Riemann予想（GRH）を仮定する。GRH自体を証明するものではない。底2・3の有限分類はGRHを仮定しない。最小拒否素数の存在とMiller–Rabin合格条件の定義は [Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) と関連する上界定理にある。

## 点ごとの包絡線

GRHの下、全ての奇合成数 $n > 1$ について、最小拒否素数には次の上界がある。

$$
q_{\mathrm{MR}}(n) \le \max\lbrace2,(7/25)L^2\rbrace.
$$

証人の存在は [Target028GlobalBridge.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target028GlobalBridge.lean) の `exists_prime_reject_028_global` が示す。

新しい区分上界を定めるため、 $D = 24439/50000$、 $A = 3/(8(27/25)^5)$、 $V = 53/500$、 $K \ge 0$ として、

$$
s_K(L)=\frac{V+\sqrt{V^2+4D(AL+K)}}{2D},
\qquad B_K(L)=s_K(L)^4
$$

とおく。Leanではそれぞれ `refinedPaperRoot` と `refinedPaperBound` に対応する。 $L \ge 8$ における区分係数は次のとおりである。

$$
C_{\mathrm{new}}(L)=
\begin{cases}
3/10 & 8 \le L < 1000,\\
B_3(L)/L^2 & 1000 \le L < 3000,\\
B_1(L)/L^2 & 3000 \le L < 10000,\\
B_0(L)/L^2 & 10000 \le L.
\end{cases}
$$

[RefinedSixPolePiecewise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPolePiecewise.lean) の `refined_piecewise_branches` はこの分岐を表し、[RefinedPiecewiseWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedPiecewiseWitness.lean) の `refined_piecewise_witness` はGRHの下、 $L \ge 8$ の奇合成数に対して $p \le C_{\mathrm{new}}(L)L^2$ を満たす拒否素数を与える。

図の点ごとの上界は次の3つの証明済みの枝から定める。

$$
U_{\mathrm{new}}(n)=
\begin{cases}
2 & 9 \le n < 2047,\\
3 & 2047 \le n < 3000,\\
\min\lbrace(7/25)L^2,C_{\mathrm{new}}(L)L^2\rbrace & 3000 \le n.
\end{cases}
$$

小入力の有限分類は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。 $3000 \le n$ なら $8 \le L$ なので、最後の枝には係数0.28の全域定理と区分上界の両方を適用できる。図の選択式自体はLeanの単一の定義ではなく、これらの定理を組み合わせたものである。 $B_3(L)$ は $L$ が約1846.306を超えると $(7/25)L^2$ を下回る。この交点は描画上の数値である。

## 上界を与える定理と証明方法

| 範囲・役割 | 主な定理 | 証明方法 |
|---|---|---|
| $9 \le n < 3000$ | `exists_primeWitness_lt_3000` | 小入力を有限分類し、底2または3の不合格を検証する。 |
| 全域の係数0.28 | `exists_prime_reject_028_global` | 小入力の有限分類と、 $\ln n \ge 8$ に対する証人定理を結合する。因数構造ごとに局所部分群、有限計数、有理極核と三角核を用いる。 |
| 区分上界の定義と低域 | `refined_piecewise_low_witness` | 既存の区分候補は低域で係数0.3を使う。図では係数0.28との最小値を採用する。 |
| $L \ge 1000$、小さいFermat部分群指数 | `refined_index16_witness` | 局所部分群に対する証人と、一様Korselt三素数積の場合を分ける。後者は六次有理極核のEuler項・Gamma項・零点和と有限主和を評価し、端点の有理数計算で残差を抑える。 |
| $L \ge 1000$、大きいFermat部分群指数 | `refined_24_inner_witness`、`refined_24_outer_witness` | 幅24の三角核について二尺度の明示公式と指標族平均を使う。内側ではAbel和とChebyshev関数の下界、外側では幅18の二つの支持和を使い、有限主和と数値ギャップから拒否素数を得る。 |
| 区分上界の全域接続 | `refined_piecewise_witness` | 対数の大きさ、部分群指数、三角核の内外で場合分けし、上記の証人を統合する。 |

## 小入力の有限分類と全域への接続

[Target028GlobalBridge.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target028GlobalBridge.lean) は、[Target028Log8.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target028Log8.lean) の $L \ge 8$ に対する係数0.28の証人定理を、小入力の有限分類と接続する。 $n < 2047$ では底2、 $2047 \le n < 3000$ では底3以下の拒否素数を使う。対数の有理区間評価から後者では $L \ge 7$ を示し、底3を係数0.28の上限に収める。 $n \ge 3000$ では同様に $L \ge 8$ を得る。

## Target028Log8.lean：対数尺度8以上の係数0.28

`exists_prime_reject_028_log8` はGRHの下、奇合成数の $L \ge 8$ に対し $p \le (7/25)L^2$ を満たす拒否素数を与える。小域と $L \ge 106$ を先に処理し、残る範囲は素因数の数と平方因子の有無で分ける。

- 重複込みの素因数が4個以上なら、素因数の個数による係数 $1/4$ の上界を使う。
- 異なる3素数の積で一様Korselt型以外なら、Korselt条件または2進付値の差から局所部分群の証人を得る。
- 一様Korselt型の3素数積について、有理極核の指標和と有限主和を比較する。 $L \le 30$ の有限区間、40個の中域セル、 $L \ge 100$ の残差評価を接続する。反射Euler項は6個の対数モーメントに分け、Gamma項は片側評価を用いる。各セルの端点と有限素数冪表はLeanで検査する。
- 平方因子を持つ場合は、局所Fermat核の大きさと重み付き素数積の個数を比較する。既存の平方被覆と複数の有限計数表を接続し、残る境界区間では1801以下の素数供給を使う。
- 平方自由な2素数積は、片方の素因数についてKorselt条件が成立しないことを利用する。小域では細かい対数重みを用いた素数積の有限計数、中域では偶指標の局所補正を使う。高域では素数群を二つの重みに分け、選ぶ個数ごとの寄与を合算して局所核より多い素数積を得る。

$L \ge 106$ の非一様型では、Fermat部分群の指数に応じて局所証人と幅24の三角核による指標族平均を使う。 [Target028From106.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target028From106.lean) が高域を統合する。

## 対数尺度1000以下の区分上界

[Target028Analytic1000.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target028Analytic1000.lean) は、 $8 \le L \le 1000$ の奇合成数について係数0.28の証人を与える。この定理は上の全域定理から導く。区分係数はこの範囲で0.3なので、係数の比較によって区分上界にも同じ証人を使える。素因数の数とKorselt型による証明の分類は前節に示した。

## RefinedSixPolePiecewise.lean：区分係数と証人の接続

[RefinedSixPolePiecewise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPolePiecewise.lean) は、上記の $C_{\mathrm{new}}(L)$ と、高域で使う余裕項 $K \in \lbrace 3,1,0\rbrace$ を定義する。`refined_piecewise_branches` は各切替点での式を確定し、`refined_piecewise_high` は $L \ge 1000$ のとき $C_{\mathrm{new}}(L)L^2=B_K(L)$ となることを示す。

[RefinedPiecewiseWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedPiecewiseWitness.lean) の `refined_piecewise_low_witness` は、 $8 \le L < 1000$ で係数0.28の証人を区分係数の証人として使う。一方、`refined_pair_piecewise_witness` は、一様なKorselt型の三素数積に対し、所定の残差評価を仮定して高域の区分上界を与える。このファイルだけでは高域の全奇合成数に対する証人の存在は結論していない。小さいFermat部分群指数の場合は [RefinedSixPoleIndex.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPoleIndex.lean) で扱い、残る大きい指数の場合と統合は次のファイルで扱う。

高域の式の根幹は、上で定義した正の根 $s=s_K(L)$ が二次方程式

$$
D s^2-V s=AL+K
$$

を満たし、証人の探索範囲を $B_K(L)=s^4$ とする点にある。先行する `refined_pair_root_witness` は、探索範囲内のすべての素数が合格すると仮定して得られる必要条件と、この根の等式および残差の上界を比較し、矛盾を導く。残差評価は同定理の仮定であり、区分係数を定義しただけでは自動的に得られない。

`refined_pair_piecewise_witness` は、選択した $K$ が $0 \le K \le 3$ を満たすことと、 $L > 0$ によって $C_{\mathrm{new}}(L)L^2=B_K(L)$ と約分できることを使い、この条件付き証人を区分係数の形式に移す。小さい指数の全域証明では、局所的な場合と一様Korselt型三素数積の場合を分類し、後者に必要な残差評価も確保する。

## RefinedTriangularWidth24.lean：大きい指数と区分上界の統合

[RefinedTriangularWidth24.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedTriangularWidth24.lean) は、Fermat部分群の指数が少なくとも $10^{16}$ の場合を幅24の三角核で扱う。指標族の二尺度の明示公式から、対象の素数が存在しない場合の評価を導き、有限主和の下界との矛盾によって、法を割るか部分群の外にある素数を得る。その素数がMiller–Rabinテストの拒否素数になることを使う。

具体的には、幅24の核について、尺度 $x$ と逆尺度 $x^{-1}$ の指標和を、導手の対数、Gamma項、零点和に結びつける。尺度1ではGRHの下で零点項の絶対値の和を取り出せる。Gamma項の実部を指標とその逆指標のそれぞれについて $-27$ 以下に抑えることで、零点和の評価に $-54$ の項と尺度1の算術和を残す。これを部分群を消す指標族について合計し、主指標を分離する。

探索範囲内に法を割る素数も部分群の外にある素数もないと仮定すると、尺度 $x$ と尺度1の有限主和に対する上界が得られる。一方、主和を下から評価する。指数が大きい場合には、その下界と導手・Gamma項などから得た上界の間に厳密な数値ギャップができ、仮定に矛盾する。得られた素数が法を割る場合、Miller–Rabin合格に必要な互いに素という条件に反する。部分群の外にある場合も、合格する底がFermat部分群に属することに反する。

高域では $x=B_K(L)$ とおき、 $\ln x \le 48$ と $48 \le \ln x$ に分ける。前者の `refined_24_inner_witness` では、Abel和とChebyshev関数の評価による有限主和の下界を使う。後者の `refined_24_outer_witness` では、幅18の二つの支持和に分けて評価する。`refined_24_outer_lower` は、その有限主和が $(9199/100)\sqrt{x}-2000x^{1/4}$ 以上であることを示し、数値ギャップの証明へ渡す。

内側で下から抑えるのは、尺度 $x$ の有限主和と尺度1の有限主和の2倍との和である。外側では尺度1の主和の非負性を使い、尺度 $x$ の有限主和だけで矛盾を得る。外側の係数 $9199/100$ は、より精密な係数 $92-20e^{-18}$ の指数関数項を有理数で抑えたものだ。これらの下界と数値ギャップは、それぞれの範囲の仮定を明示してLeanで証明している。

[RefinedPiecewiseWitness.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedPiecewiseWitness.lean) の `refined_piecewise_witness` は、 $8 \le L < 1000$、 $L \ge 1000$ かつ指数が $10^{16}$ 以下の場合、大きい指数の内側・外側の場合を結合する。結果としてGRHの下、 $L \ge 8$ のすべての奇合成数に対して $p \le C_{\mathrm{new}}(L)L^2$ を満たす拒否素数を与える。切替点における具体的な式は、前節の `refined_piecewise_branches` と組み合わせて得られる。

係数0.28の素数判定同値 `prime_millerRabin_028_criterion` は [PrimeMillerRabinWitnessSolution.lean](../ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessSolution.lean) にある。奇数 $n > 1$ について、指定範囲内のすべての素数底で合格することと $n$ の素数性が同値である。合成数を排除する向きにGRHを使い、素数が対象の底で合格する向きには使わない。

## 累積上界

GRHの下、係数0.28のmax形は対数の単調性によって累積最大値の上界にもなる。この累積上界は `Target028Cumulative.lean` で証明し、`Target028Selection.lean` から直接利用する。図では $H_0(L)=\max\lbrace2,(7/25)L^2\rbrace$ とし、 $(T_i,K_i)=(1000,3),(3000,1),(10000,0)$ に対して次を順に適用する。

$$
H_i(L)=
\begin{cases}
H_{i-1}(L) & L < T_i,\\
\min\lbrace H_{i-1}(L),\max\lbrace H_{i-1}(T_i),B_{K_i}(L)\rbrace\rbrace & T_i \le L.
\end{cases}
$$

各 $B_K$ は $K \ge 0$、 $L \ge 0$ で非減少であり、 $B_0 \le B_1 \le B_3$ が成り立つ。したがって、入口以前の履歴と入口以降の区分上界の大きい方で全入力を覆える。図の累積上界は $H_3$ である。この組合せを独立したLean定義として証明したわけではない。

## 比較グラフ

![Miller–Rabinの最小素数証人と上界式の比較](figures/mr_upper_bound_comparison.svg)

橙線は $U_{\mathrm{new}}(n)$、黒点線は $\max\lbrace2,(7/25)(\ln n)^2\rbrace$ を示す。横軸は $\ln(\ln n)$ に線形な尺度、縦軸は対数軸である。主図は $9 \le n \le 10^{64}$、挿入図は $3000 \le n \le e^{10^{14}}$ を対象とし、挿入図では上界を $(\ln n)^2$ で割る。

青緑の点は [OEIS A006945](https://oeis.org/A006945) の記録となる奇合成数と、その最小拒否素数を示す。階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。[PNG版](figures/mr_upper_bound_comparison.png)

### 累積上界と点ごとの上界

![MR累積上界と点ごとの上界](figures/mr_cumulative_high_comparison.svg)

橙線は $H_3(L)/L^2$、青い破線は点ごとの上界 $U_{\mathrm{new}}(n)/(\ln n)^2$、黒点線は係数0.28のmax形を $L^2$ で割った値を示す。切替点では以前の履歴を保持するため、累積上界は点ごとの上界と異なる場合がある。[PNG版](figures/mr_cumulative_high_comparison.png)

図は数値描画であり、Leanによる自然数入力の証明と区別する。生成方法は [図の一覧](figures/README.md) にある。

## 公理依存の確認

次の宣言について、`#print axioms` で推移的な依存を確認できる。

```lean
import PseudoPrime
import ComparatorChallenges.PrimeMillerRabinWitness.PrimeMillerRabinWitnessSolution

#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_witness
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_branches
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.exists_prime_reject_028_log8
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.exists_prime_reject_028_global
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.cumulativeLeastPrime_le_028
#print axioms ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_028_criterion
```

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
