# 定理1.3の指数4〜6と共通核による比較の限界

## 証明済みの障害

定理1.3のLean命題に現れる係数を
$$
C_h(\varepsilon)=
\left(\frac14+\varepsilon\right)
\left(1-\frac1h\right)^2
\left(\frac{\log(2h)}{\log(2h)-4}\right)^2
$$
とする。

許容Mellin核 $K$ と正の切断点 $\lambda$ に対して、
$$
A_K(\lambda)=\int_0^\lambda
\frac{\Re\widehat K(u)}{\sqrt u} du,
\qquad B_K=\Re K(1/2),
\qquad D_h=hA_K(\lambda)-B_K
$$
と置く。ここでは $\widehat K$ はコードの `K.transform` を表し、Fourier変換とは区別する。核の質量を $M_K$ とすると、非主指標の零点費用を法の対数で一律に評価する比較から得られる先頭係数は
$$
c_h(K,\lambda)=\lambda
\left(\frac{(h-1)M_K}{D_h}\right)^2
$$
である。比較から上界を得るには $D_h > 0$ が必要になる。

明示的な双対重みにより、指数6では $c_6(K,\lambda)\ge60/121$ が成り立つ。この下限は、Fourier変換の実部が正負の値を取る試験関数にも成り立つ。双対重みの台は $[0,\log(5/2)/\pi]$ で、余弦の全域評価から双対関数のノルム平方を $121/60$ 以下に抑える。積分の交換とMellin変換の順変換により、Mellin核にもこのFourier評価を適用できる。

さらに、核の非負性から $A_K(\lambda)\le B_K$ が成り立つ。 $h\le6$ なら
$$
5D_h\le(h-1)D_6
$$
となる。 $4\le h\le6$ と $D_h > 0$ の下で、質量の正値性とこの不等式から
$$
c_h(K,\lambda)\ge c_6(K,\lambda)\ge\frac{60}{121}
$$
を得る。一方、同じ範囲では
$$
C_h(1/200)<\frac{425}{864}<\frac{60}{121}
$$
である。この比較は、 $\log(2h)<5/2$ と $1-1/h\le5/6$ を用いてLeanで証明されている。

`MellinKernel.no_small_index_mellin_certificate` は、指数4〜6について、この方式で $C_h(1/200)$ 以下の係数を得る核と切断点が存在しないことを述べる。任意の正の誤差で目標係数に達するには、誤差 $1/200$ でも達する必要がある。このため、核の探索、尺度の変更、Taylor項数の増加、有理数の分母の変更だけでは、この方式で目標係数に達しない。

## 残る証明に必要な情報

定理1.3の指数7以上は証明済みである。指数4〜6についても、GRHの下で、十分大きな法に対する次の条件付き定理がある。名前空間はいずれも `PseudoPrime.LLS.PaperStatements` である。

- [`theorem13_small_index_of_odd_proper_prime_power`](../PseudoPrime/LLS/PrimePowerSubgroupBounds.lean)：法が $q=p^k$、 $p$ が奇素数、 $k \ge 2$ の場合。
- [`theorem13_small_index_of_conductor_sum_le_half`](../PseudoPrime/LLS/SmallIndexConductorBounds.lean)：`subgroupConductorLogSum H` が $(h-1)\log q/2$ 以下の場合。この和は、非主の消去指標の原始導手の対数和である。

両定理は固定した $4\le h\le6$ に対して閾値 $Q$ を与え、 $q\ge Q$ と指数 $h$ の部分群について、最小の部分群外素数を $C_h(0)(\log q)^2$ 未満に抑える。したがって、任意の正の誤差での定理1.3の上界も得られる。

どちらの条件も満たさない場合については、結論をまだ証明できていない。公開証明は指数7以上の制限版を対象とする。

上の障害は、導手を法で一律に抑え、共通核と指標ごとの独立した絶対値評価を使う係数式についての結果である。導手の節約や法の縮約を用いる証明では、この一律評価を改善できる。未証明の範囲を扱うには、導手や局所群の性質、零点の同時制約、または別の数論的比較を使い、この係数式を改善する必要がある。

定理1.3自体の反例は示していない。任意の解析手法や多核方式を排除する結果でもない。
