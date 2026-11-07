# Miller–Rabinの拒否素数上界

GRHの下で、奇合成数を棄却する最小の素数底には、下記の点ごとの上界と累積上界がある。図は有限区間の底2・3、係数 $3/10$、および新しい区分上界を描く。図の選択式と累積履歴は、それぞれのLean定理から構成した値である。

## 対象と記号

$n > 1$ を奇合成数、 $L = \ln n$ とし、 $q_{\mathrm{MR}}(n)$ を $n$ がMiller–Rabinテストに不合格となる最小の素数底とする。 $Q_{\mathrm{MR}}(N)$ は $9 \le n \le N$ の奇合成数に対する $q_{\mathrm{MR}}(n)$ の最大値である。対象がない場合は0とする。

本ページの解析的な上界は一般化Riemann予想（GRH）を仮定する。GRH自体を証明するものではない。底2・3の有限分類はGRHを仮定しない。最小拒否素数の存在とMiller–Rabin合格条件の定義は [Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) と関連する上界定理にある。

## 点ごとの包絡線

GRHの下、全ての奇合成数 $n > 1$ について、最小拒否素数には次の上界がある。

$$
q_{\mathrm{MR}}(n) \le \max\lbrace2,(3/10)L^2\rbrace.
$$

証人の存在は [Target030Global.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030Global.lean) の `exists_prime_reject_03_global` が示す。

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

[RefinedSixPolePiecewise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPolePiecewise.lean) の `refined_piecewise_branches` はこの分岐を表し、[RefinedTriangularWidth24.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedTriangularWidth24.lean) の `refined_piecewise_witness` はGRHの下、 $L \ge 8$ の奇合成数に対して $p \le C_{\mathrm{new}}(L)L^2$ を満たす拒否素数を与える。

図の点ごとの上界は次の3つの証明済みの枝から定める。

$$
U_{\mathrm{new}}(n)=
\begin{cases}
2 & 9 \le n < 2047,\\
3 & 2047 \le n < 3000,\\
C_{\mathrm{new}}(L)L^2 & 3000 \le n.
\end{cases}
$$

小入力の有限分類は [SmallPointwiseBounds.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallPointwiseBounds.lean) にある。 $3000 \le n$ なら $8 \le L$ なので、最後の枝には区分上界を適用できる。図の選択式自体はLeanの単一の定義ではなく、これらの定理を組み合わせたものである。以前の選択式と区分上界の最小値とは、切替点の前後を含む10万点で数値が一致した。全入力で同じ値になることは、この数値検証からは結論できない。

## 上界を与える定理と証明方法

| 範囲・役割 | 主な定理 | 証明方法 |
|---|---|---|
| $9 \le n < 3000$ | `exists_primeWitness_lt_3000` | 小入力を有限分類し、底2または3の不合格を検証する。 |
| 全域の係数0.3 | `exists_prime_reject_03_global` | 小入力の有限分類と、 $\ln n \ge 8$ に対する証人定理を結合する。低域では因数構造に応じた有限証明と局所指標の評価を使い、高域ではGaussian比較を使う。 |
| $8 \le L < 1000$ の区分上界 | `refined_piecewise_low_witness` | 係数0.3の証人定理を、区分係数の最初の枝へ書き換える。 |
| $L \ge 1000$、小さいFermat部分群指数 | `refined_index16_witness` | 局所部分群に対する証人と、一様Korselt三素数積の場合を分ける。後者は六次有理極核のEuler項・Gamma項・零点和と有限主和を評価し、端点の有理数計算で残差を抑える。 |
| $L \ge 1000$、大きいFermat部分群指数 | `refined_24_inner_witness`、`refined_24_outer_witness` | 幅24の三角核について二尺度の明示公式と指標族平均を使う。内側ではAbel和とChebyshev関数の下界、外側では幅18の二つの支持和を使い、有限主和と数値ギャップから拒否素数を得る。 |
| 区分上界の全域接続 | `refined_piecewise_witness` | 対数の大きさ、部分群指数、三角核の内外で場合分けし、上記の証人を統合する。 |

## 小入力の有限分類と全域への接続

[Target030Global.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030Global.lean) は、 [Target030Log8.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030Log8.lean) の $L \ge 8$ における係数0.3の証人定理を、小入力の有限分類と接続する。 $n < 2047$ では底2、 $2047 \le n < 3000$ では底3以下の証人を使う。後者では $\ln n \ge 7$ から $3 \le (3/10)L^2$ を示す。 $n \ge 3000$ では $L \ge 8$ を示して係数0.3の定理を適用する。

こうして `exists_prime_reject_03_global` は、GRHの下ですべての奇合成数 $n > 1$ に対して $p \le \max\lbrace2,(3/10)L^2\rbrace$ を満たす拒否素数 $p$ を与える。さらに `compositeLeastPrime_le_03_global` は、その証人との比較から最小拒否素数にも同じ上界が成り立つことを示す。

証明の接続点は、有限計算で得た整数の上界を対数の式へ移すことである。 $2047 \le n < 3000$ では底3以下という事実だけでは係数0.3の評価にならないため、対数の単調性と検証済みの有理数による下界から $L \ge 7$ を得る。 $n \ge 3000$ でも同様に $L \ge 8$ を得る。これらの対数評価は有理数区間の判定をLeanで検証したものである。

## Target030Global.lean：対数尺度8以上の係数0.3

係数0.3の解析的な根拠は、`Target030Global.lean` が呼び出す [Target030Log8.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030Log8.lean) の `exists_prime_reject_03_log8` である。この定理はGRHの下、奇合成数の $L = \ln n$ が $8 \le L$ を満たせば、 $p \le (3/10)L^2$ となる拒否素数 $p$ が存在すると示す。証明は対数尺度と因数構造に応じて次の枝を結合する。

- $8 \le L \le 1000$： [QuadraticGammaAnalyticBridgeCombined.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/QuadraticGammaAnalyticBridgeCombined.lean) の `exists_reject_03_analytic1000` を使う。 $L \le 550$ の既存の証明に91個の解析セルを継ぎ足し、隣接セルの端点を接続する。各セルの評価を検証することで、有限区間全体に係数0.3を適用する。
- $L > 1000$ で一様Korselt型三素数積の場合：平方因子を持たず、異なる3つの素因数を持ち、各素因数 $p$ について $p-1$ が $n-1$ を割り、各 $p-1$ の2進付値が等しい場合である。Gaussian核を使った評価から証人が存在するための数値比較を導き、`gaussian030_scalar_gap` でその不等式を検証する。選んだGaussianの尺度から得られる探索上限も $(3/10)L^2$ 以下である。
- $L > 1000$ で上記以外の場合： [Target030NonuniformLog8.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030NonuniformLog8.lean) の `exists_prime_reject_03_nonuniform_log8` を使う。素因数の個数や局所部分群による分類を用い、指数が小さい場合の局所証人と、指数が大きい場合の解析的な証人を組み合わせる。

一様Korselt型では、探索範囲内に拒否素数がないと仮定したときの指標和の評価と、Gaussian核による下界を比較する。`gaussian030_scalar_gap` が両者の間に必要な厳密な差を与えるため、この仮定を排除できる。係数0.3は単に数値実験から選んだ値ではなく、証人の探索上限が $(3/10)L^2$ 以下になることと、この差が正になることの両方をLeanで検証している。

### 素因数の数とKorselt型による分類

証明で扱う素因数の個数には、重複を込めて数える個数と、異なる素因数の個数がある。例えば $p^2q$ は前者では3個、後者では2個である。合成数には重複を込めて少なくとも2個の素因数がある。係数0.3の証明では、この個数と平方因子の有無を使い、局所的な条件から証人を得られる場合と、複数の指標をまとめて評価する必要がある場合に分ける。

重複を込めた素因数が4個以上の場合、`exists_prime_reject_03_four_factors` は、素因数の総数を $k$ とする既存の上界 $4L^2/k^2$ を使う。 $k \ge 4$ なら係数は高々 $1/4$ なので、係数0.3の範囲に収まる。平方因子がある場合には、平方因子に対する上界も利用できる。例えば $8 \le L \le 100$ の非一様の場合、`exists_prime_reject_03_nonuniform_100` は平方因子がある場合を先に分離する。

平方因子がなく異なる2素数の積となる場合は、2素数積向けの証人定理を使う。 $8 \le L \le 100$ では `exists_prime_reject_03_semiprime_100` がこの場合を扱う。より大きい尺度では、非一様の場合に対する局所部分群の分類と解析的上界を使い、指数に応じた場合分けを通じて証人を得る。

異なる3素数の積では、特にKorselt条件 $p-1 \mid n-1$ がすべての素因数 $p$ について成り立つ場合に注意が必要である。Korselt条件に加えて各 $p-1$ の2進付値がすべて等しいものを、ここでは一様Korselt型と呼ぶ。この型は、単一の素因数に着目した局所条件による証人の構成から残る例外であり、上述のGaussian核を使う高域の証明で重点的に扱う。区分上界の小指数側でも、この型に対して六次有理極核を使う別の証明を用いる。

3素数の場合でも、一様Korselt型以外は局所的な差を利用できる。ある素因数でKorselt条件が成立しないか、2つの素因数の前身 $p-1$ の2進付値が異なるためである。`exists_prime_reject_03_nonuniform_three` は、この違いから `exists_prime_reject_03_local_factor` を適用し、係数高々 $1/4$ の証人を得る。Korselt条件を満たしていても、2進付値が異なればこちらに含まれる。

この因数分類による証明は、解析セルによる有限範囲の一括証明と重なる部分を持つ。最終定理 `exists_prime_reject_03_log8` が直接使うのは、 $L \le 1000$ では解析セルによる定理であり、 $L > 1000$ では一様Korselt型とそれ以外の定理である。

`Target030Global.lean` 自体はこれらの解析評価を再証明せず、上記の $8 \le L$ の定理を前節の有限分類と接続してmax形の全域定理を得る。

## RefinedSixPolePiecewise.lean：区分係数と証人の接続

[RefinedSixPolePiecewise.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPolePiecewise.lean) は、上記の $C_{\mathrm{new}}(L)$ と、高域で使う余裕項 $K \in \lbrace 3,1,0\rbrace$ を定義する。`refined_piecewise_branches` は各切替点での式を確定し、`refined_piecewise_high` は $L \ge 1000$ のとき $C_{\mathrm{new}}(L)L^2=B_K(L)$ となることを示す。

同ファイルの `refined_piecewise_low_witness` は、 $8 \le L < 1000$ で係数0.3の証人を区分係数の証人として使う。また `refined_pair_piecewise_witness` は、一様なKorselt型の三素数積に対し、所定の残差評価を仮定して高域の区分上界を与える。このファイルだけでは高域の全奇合成数に対する証人の存在は結論していない。小さいFermat部分群指数の場合は [RefinedSixPoleIndex.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/RefinedSixPoleIndex.lean) で扱い、残る大きい指数の場合と統合は次のファイルで扱う。

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

最後の `refined_piecewise_witness` は、 $8 \le L < 1000$、 $L \ge 1000$ かつ指数が $10^{16}$ 以下の場合、大きい指数の内側・外側の場合を結合する。結果としてGRHの下、 $L \ge 8$ のすべての奇合成数に対して $p \le C_{\mathrm{new}}(L)L^2$ を満たす拒否素数を与える。切替点における具体的な式は、前節の `refined_piecewise_branches` と組み合わせて得られる。

係数0.3の素数判定同値 `prime_millerRabin_03_criterion` は [PrimeMillerRabinWitnessSolution.lean](../ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessSolution.lean) にある。奇数 $n > 1$ について、指定範囲内のすべての素数底で合格することと $n$ の素数性が同値である。合成数を排除する向きにGRHを使い、素数が対象の底で合格する向きには使わない。

## 累積上界

GRHの下、係数0.3のmax形は累積最大値の上界にもなる。これは [Target030Cumulative.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/Target030Cumulative.lean) の `cumulativeLeastPrime_le_03` が示す。図では $H_0(L)=\max\lbrace2,(3/10)L^2\rbrace$ とし、 $(T_i,K_i)=(1000,3),(3000,1),(10000,0)$ に対して次を順に適用する。

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

橙線は $U_{\mathrm{new}}(n)$、黒点線は $\max\lbrace2,(3/10)(\ln n)^2\rbrace$ を示す。横軸は $\ln(\ln n)$ に線形な尺度、縦軸は対数軸である。主図は $9 \le n \le 10^{64}$、挿入図は $3000 \le n \le e^{10^{14}}$ を対象とし、挿入図では上界を $(\ln n)^2$ で割る。

青緑の点は [OEIS A006945](https://oeis.org/A006945) の記録となる奇合成数と、その最小拒否素数を示す。階段線は掲載した記録を結んだもので、未探索範囲への外挿ではない。[PNG版](figures/mr_upper_bound_comparison.png)

### 累積上界と点ごとの上界

![MR累積上界と点ごとの上界](figures/mr_cumulative_high_comparison.svg)

橙線は $H_3(L)/L^2$、青い破線は点ごとの上界 $U_{\mathrm{new}}(n)/(\ln n)^2$、黒点線は係数0.3のmax形を $L^2$ で割った値を示す。切替点では以前の履歴を保持するため、累積上界は点ごとの上界と異なる場合がある。[PNG版](figures/mr_cumulative_high_comparison.png)

図は数値描画であり、Leanによる自然数入力の証明と区別する。生成方法は [図の一覧](figures/README.md) にある。

## 公理依存の確認

次の宣言について、`#print axioms` で推移的な依存を確認できる。

```lean
import PseudoPrime
import ComparatorChallenges.PrimeMillerRabinWitness.PrimeMillerRabinWitnessSolution

#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_witness
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.refined_piecewise_branches
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.exists_prime_reject_03_global
#print axioms PseudoPrime.PrimeTestBounds.MillerRabin.cumulativeLeastPrime_le_03
#print axioms ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_03_criterion
```

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
