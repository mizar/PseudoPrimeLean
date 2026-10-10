# 定理1.3の指数4〜6と共通核による比較の限界

## 対象となる主張と論文との関係

[LLS論文 arXiv:1309.3595v3](https://arxiv.org/abs/1309.3595v3) の定理1.3、およびそのLean命題 `lls_theorem13` に現れる係数を

$$
C_h(\varepsilon)=
\left(\frac14+\varepsilon\right)
\left(1-\frac1h\right)^2
\left(\frac{\log(2h)}{\log(2h)-4}\right)^2
$$

とする。ここで $h=[(\mathbb Z/q\mathbb Z)^\times:H]$ は部分群の指数、 $\log$ は自然対数である。Lean命題は、GRHの下で、固定した $h \ge 4$ と任意の $\varepsilon > 0$ に対して閾値 $Q$ が存在し、 $q \ge Q$ と指数 $h$ の任意の部分群 $H$ について、 $p \nmid q$ かつ $p \bmod q \notin H$ を満たす最小素数が $C_h(\varepsilon)(\log q)^2$ 未満となることを述べる。閾値は $h,\varepsilon$ に依存してよいが、 $q,H$ には依存しない。

論文の第6.1節は、命題6.1による共通核の比較では先頭係数 $1/4$ より小さい上界を得られないことを述べる。本プロジェクトでは、この比較の限界を指数4〜6で $60/121$ に強めて形式化している。以下の係数障害自体はGRHを仮定しない解析的な命題であり、GRHから導かれる素数上界に適用する際に命題6.1と接続する。

### 原文 §6.2 の導出に関する疑義

論文の第6.2節は三角形型核と $\lambda=1$、 $\alpha=\log(2h)/2$ を選び、 $h \ge 4$ で定理1.3の係数が得られると述べる。この核を用いた比較不等式の左辺の係数を $D_h=h(4\alpha-4+4e^{-\alpha})-4(e^{\alpha/2}-e^{-\alpha/2})^2$ とすると、そこで用いる簡略下界は

$$
D_h \ge 2h\bigl(\log(2h)-4\bigr)
$$

である。この下界で比較不等式を除して上界を得るには、右辺が正である必要がある。整数の指数では $h \ge 28$ がこの条件に対応する。これは実際の $D_h$ の符号とは別の条件であり、簡略下界が負の場合にそれを二乗しても、上界の導出は正当化されない。

とくに $C_4(0)=0.1648545\ldots < 1/4$ は論文自身の §6.1 の方法の限界より小さい。したがって、少なくとも指数4の係数は、同じ命題6.1の比較からそのまま導けるものではない。指数5・6も、以下の $60/121$ の障害により同じ比較では達成できない。この指摘は、原文の導出への疑義であり、定理1.3の数論的な結論の反例ではない。

本プロジェクトでは $h \ge 28$ を三角形型核で、 $7 \le h \le 27$ を第6.3節のガンマ核と係数比較で証明する。対応する証明は `triangular_kernel_bound_of_large_index`、 `triangularCoefficient_gt_gamma_of_small_index`（[`PseudoPrime/LLS/TheoreticalKernelProfiles.lean`](../PseudoPrime/LLS/TheoreticalKernelProfiles.lean)）と、それらから最小素数の上界を導く [`PseudoPrime/LLS/TheoreticalPrimeBounds.lean`](../PseudoPrime/LLS/TheoreticalPrimeBounds.lean) にある。指数4〜6の一般の場合は、原文のこの計算から証明済みとは扱わない。

## 共通核による比較と正規化

ここでいう許容核は、[`PseudoPrime/LLS/PaperDefinitions.lean`](../PseudoPrime/LLS/PaperDefinitions.lean) の `MellinKernel` を指す。解析性・減衰・Mellin積分の可積分性と積分路の独立性に加え、正の引数で逆Mellin変換が実数値・非負であり、少なくとも一つの正の引数で非零であることを要求する。

$\widetilde K(u)$ はコードの `K.transform u`、 $K(s)$ は `K.function s` とする。正の切断点 $\lambda$ に対して、

$$
M_K=\frac{1}{2\pi}\int_{-\infty}^{\infty}|K(it)|dt,
$$

$$
\begin{aligned}
A_K(\lambda)&=\int_0^\lambda\frac{\Re\widetilde K(u)}{\sqrt u}du,\\
B_K&=\Re K(1/2),\\
D_h&=hA_K(\lambda)-B_K
\end{aligned}
$$

と置く。質量 $M_K$ はコードの `K.mass` と同じ正規化であり、許容核では $M_K > 0$ である。

命題6.1で、非主の消去指標 $h-1$ 個に共通核を使い、各指標の零点項の費用を $M_K\log q$ で一律に評価すると、

$$
D_h\sqrt X
\le (1+o(1))\sqrt\lambda(h-1)M_K\log q
$$

という比較を得る。ここで $X$ 以下の素数のうち $q$ と互いに素なものはすべて $H$ に属すると仮定している。 $D_h > 0$ の場合にこの比較を解いて得られる、漸近誤差を加える前の先頭係数は

$$
c_h(K,\lambda)=\lambda
\left(\frac{(h-1)M_K}{D_h}\right)^2
$$

である。障害定理が対象とするのは、この係数式である。

## 指数6のFourier双対評価

指数6では、Mellin核に対応する関数を含む、より広いFourier試験関数のクラスに対して下限を証明する。 $F:\mathbb R\to\mathbb C$ のFourier変換は $(\mathcal F F)(t)=\int_{-\infty}^{\infty}F(x)e^{-2\pi ixt}dx$ の規約を用い、

$$
\begin{aligned}
R(t)&=\Re(\mathcal F F)(t),\\
R_+(t)&=\max(R(t),0),\\
R_-(t)&=\max(-R(t),0),
\end{aligned}
$$

$$
J(F)=\int_{-\infty}^{0}R(t)e^{\pi t}dt
-\int_0^\infty\left(R_-(t)+\frac15R_+(t)\right)e^{\pi t}dt
$$

と置く。これは `ep1Numerator F` である。試験関数には $F$ と `ep1Integrand F` の可積分性、および $J(F) > 0$ を要求する。 $R(t)$ の符号は制限しない。

双対重みは、 $a=\log(5/2)/\pi$ として

$$
w(t)=
\begin{cases}
e^{\pi t} & t \le 0,\\
-\dfrac15e^{\pi t} & 0 < t \le a,\\
0 & a < t
\end{cases}
$$

である。重み全体の台は $(-\infty,a]$ であり、コンパクトではない。 有限区間に切り詰めているのは正の半直線側の項であり、非正の半直線上の項も双対評価に必要である。 $w$ は実直線上で可積分で、点ごとの比較から

$$
J(F)\le\int_{-\infty}^{\infty}w(t)R(t)dt
$$

を得る。

$b=\log(5/2)$ と置くと、正規化した双対関数 `dualValue` は

$$
\begin{aligned}
V(u)&=\frac{2\left(6/5-(1/2)e^{-ibu}\right)}{1-iu},\\
(\mathcal Fw)(x)&=\frac{V(2x)}{2\pi}
\end{aligned}
$$

である。そのノルム平方は

$$
|V(u)|^2=
\frac{49/25+(24/5)(1-\cos(bu))}{1+u^2}
\le\frac{121}{60}
$$

と全実数 $u$ で評価できる。証明では $1-\cos v \le v^2/2$ と $0 < b < 11/12$ を使う。後者は指数関数の級数の最初の7項による有理数評価から証明しており、有限点での数値サンプリングには依存しない。

積分の交換とこのノルム評価により、

$$
\begin{aligned}
2\pi J(F)&\le\sqrt{121/60}\int_{-\infty}^{\infty}|F(x)|dx,\\
\left(\frac{\lVert F\rVert_1}{2\pi J(F)}\right)^2&\ge\frac{60}{121}
\end{aligned}
$$

となる。後者が `IndexSixBarrier.ep1_coefficient_ge` である。 $60/121$ は証明済みの下限であり、最適値であるとは主張していない。

Mellin核には

$$
F_{K,\lambda}(x)=\frac{1}{2\pi}K(ix)\lambda^{-ix}
$$

を対応させる。Mellin変換の順変換公式と変数変換をLeanで証明し、

$$
\begin{aligned}
(\mathcal F F_{K,\lambda})(t)&=\widetilde K(\lambda e^{2\pi t}),\\
\lVert F_{K,\lambda}\rVert_1&=M_K,\\
J(F_{K,\lambda})&=\frac{D_6}{10\pi\sqrt\lambda}
\end{aligned}
$$

を得ている。必要な可積分性も許容核の条件から証明する。これにより、 $\lambda > 0$ と $D_6 > 0$ の下で

$$
c_6(K,\lambda)\ge\frac{60}{121}
$$

が従う。符号を変える $R(t)$ に対しても、上記の罰則項を含むFourier汎関数についてこの下限が成立する。非負性を取り除いたMellin核に同じ係数式をそのまま適用するという意味ではない。

## 指数4〜6への拡張と目標係数との差

Mellin変換の順変換公式と逆変換の非負性から、

$$
A_K(\lambda)\le B_K
=\int_0^\infty\frac{\Re\widetilde K(u)}{\sqrt u}du
$$

が成り立つ。したがって $h \le 6$ なら

$$
(h-1)D_6-5D_h=(6-h)\bigl(B_K-A_K(\lambda)\bigr)\ge 0.
$$

$4 \le h \le 6$ と $D_h > 0$ の下では $D_6 > 0$ も従い、質量の正値性と合わせて

$$
c_h(K,\lambda)\ge c_6(K,\lambda)\ge\frac{60}{121}
$$

を得る。一方、同じ範囲では $0 < \log(2h) < 5/2$ と $0 < 1-1/h \le 5/6$ より、

$$
C_h(1/200)
<\left(\frac14+\frac1{200}\right)
\left(\frac56\right)^2\left(\frac53\right)^2
=\frac{425}{864}
<\frac{60}{121}.
$$

指数6の中間比較は `paperCoefficient_one_div_two_hundred_lt`、最後の有理数比較は `rational_gap`、指数4〜6の結論は `smallIndexTargetWithSlack_lt_barrier` で証明されている。 $\varepsilon=1/200$ は $1/4$ に加わる量であり、積全体への加算ではない。

`MellinKernel.no_small_index_mellin_certificate` は、各 $4 \le h \le 6$ に対して

$$
\neg\exists K,\lambda:
\lambda > 0 \land D_h > 0 \land
c_h(K,\lambda)\le C_h(1/200)
$$

を述べる。定理1.3は任意の正の誤差での上界を要求するため、この特定の正の誤差でも目標係数に達する必要がある。したがって、同じ係数式を使う限り、許容核の探索、尺度の変更、Taylor項数の増加、有理近似の分母の変更だけでは目標係数に達しない。指数6では、分母に制限のない有理数証明書についても `no_rational_ep1_certificate_at_paper_target` と `no_rational_mellin_certificate_at_paper_target` が明示されている。

### 障害定理の実装対応

| ファイル | 主な証明内容 |
| --- | --- |
| [`PseudoPrime/LLS/MethodBarrier/IndexSixNumerics.lean`](../PseudoPrime/LLS/MethodBarrier/IndexSixNumerics.lean) | `dualValue_norm_sq_le`：双対関数の全域ノルム評価。対数評価と有理数の係数差。 |
| [`PseudoPrime/LLS/MethodBarrier/IndexSixDualIntegral.lean`](../PseudoPrime/LLS/MethodBarrier/IndexSixDualIntegral.lean) | `fourier_dualWeight`、`integral_dualWeight_fourier`、`dual_pairing_le`：重みのFourier変換、積分交換、双対評価。 |
| [`PseudoPrime/LLS/MethodBarrier/IndexSixFourier.lean`](../PseudoPrime/LLS/MethodBarrier/IndexSixFourier.lean) | `ep1_coefficient_ge`：許容Fourier試験関数全体で $60/121$ の下限。 |
| [`PseudoPrime/LLS/MethodBarrier/MellinKernel.lean`](../PseudoPrime/LLS/MethodBarrier/MellinKernel.lean) | `indexSixMethodCoefficient_ge`：正規化と可積分性を証明し、Mellin核の係数へ移す。 |
| [`PseudoPrime/LLS/MethodBarrier/SmallIndex.lean`](../PseudoPrime/LLS/MethodBarrier/SmallIndex.lean) | `ambientMethodCoefficient_ge`、`no_small_index_mellin_certificate`：指数4〜6への拡張と目標係数の不達成。 |

## 証明済みの部分定理と残る範囲

定理1.3の指数7以上は、[`PseudoPrime/LLS/PaperProofs.lean`](../PseudoPrime/LLS/PaperProofs.lean) の `lls_theorem13_of_index_ge_seven_proof` で証明されている。指数4〜6についても、GRHの下で、十分大きな法に対する次の部分定理がある。名前空間はいずれも `PseudoPrime.LLS.PaperStatements` である。

| 定理 | 追加条件 |
| --- | --- |
| `theorem13_small_index_of_odd_proper_prime_power` — [`PseudoPrime/LLS/PrimePowerSubgroupBounds.lean`](../PseudoPrime/LLS/PrimePowerSubgroupBounds.lean) | 法が $q=r^k$、 $r$ が奇素数、 $k \ge 2$。底の素数に例外は残していない。 |
| `theorem13_small_index_of_conductor_sum_le_half` — [`PseudoPrime/LLS/SmallIndexConductorBounds.lean`](../PseudoPrime/LLS/SmallIndexConductorBounds.lean) | `subgroupConductorLogSum H` が $(h-1)\log q/2$ 以下。法は一般の正整数でよい。 |

`subgroupConductorLogSum H` は、 $H$ 上で1となる指標のうち非主のものについて、その原始導手 $f_\chi$ の対数を足した

$$
\sum_{\substack{\chi\in H^\perp\\\chi\ne\chi_0}}\log f_\chi
$$

である。各導手を法で抑える一般評価は $(h-1)\log q$ であり、その半分以下という条件は追加仮定である。

両定理では $4 \le h \le 6$ を満たす指数を固定し、閾値 $Q$ を与える。追加条件を満たす $q \ge Q$ と指数 $h$ の部分群について、最小の部分群外素数を $C_h(0)(\log q)^2$ 未満に抑える。したがって、任意の正の誤差での定理1.3の上界も得られる。この閾値は、該当範囲の法と部分群について一様である。

どちらの追加条件も満たさない指数4〜6の場合については、一般の結論は未証明である。公開証明の対象は指数7以上の制限版であり、上記の部分定理を合わせても `lls_theorem13` 全体の証明にはなっていない。

上の障害は、各指標の導手を法で一律に抑え、共通核と指標ごとの独立した絶対値評価を使う係数式についての結果である。導手の節約や法の縮約を用いる部分定理は、その一律評価を改善するため障害と矛盾しない。残る範囲を扱うには、導手や局所群の性質、零点の同時制約、または別の数論的比較を使い、この係数式を改善する必要がある。

この結果は定理1.3自体の反例を示すものではなく、任意の解析手法や多核方式を排除するものでもない。
