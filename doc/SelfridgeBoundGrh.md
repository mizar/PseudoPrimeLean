# Selfridge停止値へのGRH上界の接続（PrimeTestBounds.Selfridge）

対象: [`PseudoPrime/PrimeTestBounds/Selfridge`](../PseudoPrime/PrimeTestBounds/Selfridge)。公開入口は [`PseudoPrime/PrimeTestBounds.lean`](../PseudoPrime/PrimeTestBounds.lean)、上界の名前空間は `PseudoPrime.PrimeTestBounds.Selfridge`。離散的な候補列・試行回数・証人比較は `PseudoPrime.PrimeTest` に属する。

この領域では、[PrimeTest](PrimeTest.md) の数学的な Selfridge 停止値を [PseudoSquare](PseudoSquare.md) の Jacobi 証人上界に接続する。ルートの `import PseudoPrime` からも、この入口を利用できる。

## 構成

| モジュール | 内容 |
|---|---|
| [WitnessBridge.lean](../PseudoPrime/PrimeTest/Selfridge/WitnessBridge.lean) | 共通数論の素数証人と Selfridge 停止値の比較 |
| [MaximumBridge.lean](../PseudoPrime/PrimeTestBounds/Selfridge/MaximumBridge.lean) | 古典候補・Wheel30 の停止値最大と `QNeOne`／ `QNegOne` の接続 |
| [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) | 因子検出停止、純粋 $-1$ 停止、明示的半径の点ごとの比較 |
| [CubicConductorBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/CubicConductorBounds.lean) | 平方自由部分別の根上界と対数一次上界、古典候補・Wheel30への接続 |
| [WitnessTransfer.lean](../PseudoPrime/PrimeTestBounds/Selfridge/WitnessTransfer.lean) | 任意の素数証人上界を古典候補・Wheel30の停止値へ移す汎用補題 |
| [AnalyticWitnessBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/AnalyticWitnessBounds.lean) | 負値停止の3係数上界と因子検出停止の対数補正式 |
| [LogSqMaximum.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogSqMaximum.lean) | 停止値の有限最大に対する対数二乗上界 |
| [LogGRH.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogGRH.lean) | GRH を仮定する点ごとの上界 |
| [TrialCount.lean](../PseudoPrime/PrimeTestBounds/Selfridge/TrialCount.lean) | 無条件の最大試行回数と実数への比較 |
| [Selfridge/TrialCount.lean](../PseudoPrime/PrimeTest/Selfridge/TrialCount.lean) | 離散的な候補列と試行回数（PrimeTest） |
| [LogBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogBounds.lean) | 無条件の数値対数評価・小区間評価 |
| [Comparison.lean](../PseudoPrime/PrimeTestBounds/Selfridge/Comparison.lean) | 無条件の実数への停止値比較 |
| [TrialCountGRH.lean](../PseudoPrime/PrimeTestBounds/Selfridge/TrialCountGRH.lean) | GRH 付き試行回数上界 |

## 停止値の意味

古典候補は大きさ $5, 7, 9, 11, \ldots$ の順に並ぶ。`selfridgeD` はこれらを符号付き判別式 $5, -7, 9, -11, \ldots$ に変換する。

`firstStopNegOne` は Jacobi 値が $-1$ になる最初の候補の大きさを表す。`firstStopNeOne` は $n \nmid i$ かつ Jacobi 値が $1$ でない最初の候補の大きさを表し、非自明因子の検出も含む。どちらも、集合の非空性の証明を受け取る数学的な最小元である。

対応する符号付き停止値を $g_{-1}(n)$ と $g_{\ne 1}(n)$ と書くと、絶対値は候補の大きさに等しい。この領域の上界はこれらの数学的停止値について述べる。現行 BPSW の実行用探索に Jacobi 値 $0$ による早期停止を追加するものではない。

Wheel30候補による対応する符号付き停止値を $g^{(30)}_{-1}(n)$、 $g^{(30)}_{\ne1}(n)$ と書く。
奇数かつ非平方数の入力では、各停止値は対応する古典候補の停止値と等しい。
以下の解析的な上界は、両候補についてLeanで接続している。

## 主要な公開結果

自然対数を用いて

$$
R(n) = \Bigl(\ln(4n) + \frac{24}{5}\ln(\ln(4n)) + 3\Bigr)^2
$$

と置く。GRH と各定理の奇数・非平方条件のもとで、以下を得る。

| 公開定理 | 入力範囲と結論 |
|---|---|
| `classicalSelfridgeD_elementary_bound_explicit` | $n \ge 3$ で $\lvert g_{\ne 1}(n) \rvert \le \lvert g_{-1}(n) \rvert \le R(n)$ |
| `classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le` | $n \ge 13$ で $\lvert g_{\ne 1}(n) \rvert \le (\ln\mathrel{} n)^2$ |
| `classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq` | 奇数かつ非平方数の入力で $\lvert g_{\ne 1}(n) \rvert \le \max\left\lbrace 13, (\ln\mathrel{} n)^2 \right\rbrace$ |
| `classicalNeOneMaximum_cast_le_log_sq_of_751_le` | $B \ge 751$ で因子検出停止値の最大が $(\ln\mathrel{} B)^2$ 以下 |

名前に `log_sq` を含む既存定理でも、純粋 $-1$ 側には右辺が $R(n)$ のものがある。利用時は名前だけでなく定理の型を確認する。

## 素数証人の解析的上界による拡張

次の二つの表では、以下を共通の前提とする。

$$
\begin{gathered}
n\in\mathbb N,\quad n > 1,\quad n\text{ は奇数},\quad
\forall s\in\mathbb N,\ n\ne s^2,
\\
\mathrm{GRH},\qquad L=\ln n.
\end{gathered}
$$

### 純粋負値停止の係数上界

各行の条件から、古典候補とWheel30の両方に共通の上界が得られる。

| 条件 | $\lvert g_{-1}(n)\rvert$ と $\lvert g^{(30)}_{-1}(n)\rvert$ の上界 | Lean定理 |
|---|---|---|
| $L\ge255$ | $(9999/10000)L^2$ | `selfridgeNegOneMagnitudes_le_joint_entrance` |
| $L\ge290$ | $(99/100)L^2$ | `selfridgeNegOneMagnitudes_le_mixed_log_290` |
| $L\ge46000$ | $(4/5)L^2$ | `selfridgeNegOneMagnitudes_le_four_fifths` |

いずれも非平方の正奇数全体を対象とし、入力の因数分解に追加条件を課さない。
表は新たに接続した3つの係数上界の適用条件を示す。

### 因子検出停止の専用上界

| 条件 | $\lvert g_{\ne1}(n)\rvert$ と $\lvert g^{(30)}_{\ne1}(n)\rvert$ の上界 | Lean定理 |
|---|---|---|
| $L\ge50$ | $(L-2\ln L+37/5)^2$ | `selfridgeNeOneMagnitudes_le_shifted_double_log_from_fifty` |
| $L\ge22221$ | $(4/5)L^2$ | `selfridgeNeOneMagnitudes_le_four_fifths` |

各定理は独立した上界を述べる。非1証人では値0も利用できるため、
係数 $4/5$ の開始尺度は純粋負値停止の46000から22221へ下がる。
前者の対数補正式は $L\ge50$ で $L^2$ 未満となる。

### 中間尺度の因子検出停止と最大値への拡張

$$
r(L)=\frac{3200}{3241}\left(L-\frac{18}{25}\right).
$$

前節と同じ奇数・非平方条件のもとで、次が成立する。

$$
\mathrm{GRH},\quad \frac{3259}{25}\le L=\ln n\le\frac{16277}{100}
\quad\Longrightarrow\quad
\lvert g_{\ne1}(n)\rvert\le r(L)^2,\quad
\lvert g^{(30)}_{\ne1}(n)\rvert\le r(L)^2.
$$

`selfridgeNeOneMagnitudes_le_oddMidscale` が対応する。
同じ区間全体で $r(L)^2 < (L-2\ln L+149/20)^2$ となることは
[奇素数非1証人の比較定理](../PseudoPrime/LLS/OddMidscaleEndpointRadius.lean) で証明した。

有限範囲の停止値最大も、同じ上界で抑えられる。 $B\in\mathbb N$ に対して

$$
\mathcal A_B=\left\lbrace n\in\mathbb N:
0 < n\le B,\quad n\text{ は奇数かつ非平方}\right\rbrace,
$$

$$
M_{\mathrm{cl}}(B)=\max\left(\lbrace0\rbrace\cup
\left\lbrace\lvert g_{\ne1}(n)\rvert:n\in\mathcal A_B\right\rbrace\right),
\quad
M_{30}(B)=\max\left(\lbrace0\rbrace\cup
\left\lbrace\lvert g^{(30)}_{\ne1}(n)\rvert:n\in\mathcal A_B\right\rbrace\right)
$$

と定める。

$$
\mathrm{GRH},\quad \frac{3259}{25}\le\ln B\le\frac{16277}{100}
\quad\Longrightarrow\quad
M_{\mathrm{cl}}(B)\le r(\ln B)^2,\quad M_{30}(B)\le r(\ln B)^2.
$$

`selfridgeNeOneMaxima_le_oddMidscale` が対応する。
$\ln n$ が適用区間に入らない小さい入力も、 $n\in\mathcal A_B$ なら最大値の対象に含む。
[OddMidscaleBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/OddMidscaleBounds.lean)
の汎用補題 `selfridgeNeOneMaxima_le_of_QNeOne_bound` は、
$X\ge15$ と $Q_{\ne1}(B)\le X$ だけから両方の最大値を $X$ 以下に移す。

古典候補列の試行回数最大は、既存の全域定義に従い

$$
T_{\mathrm{cl}}(B)=
\left\lfloor\frac{\max\lbrace M_{\mathrm{cl}}(B)-5,0\rbrace}{2}\right\rfloor+1
$$

とする。

$$
\mathrm{GRH},\quad \frac{3259}{25}\le\ln B\le\frac{16277}{100}
\quad\Longrightarrow\quad
T_{\mathrm{cl}}(B)\le\frac{r(\ln B)^2-3}{2}.
$$

`classicalNeOneTrialMaximum_le_oddMidscale` が対応する。
任意の停止値上界 $X\ge5$ から試行回数を $(X-3)/2$ 以下へ移す汎用補題も証明した。
従来の $X/2+1$ より上界を $5/2$ 小さくできる。
これらは値0による因子検出を含む停止値とJacobi試行回数の結果であり、純粋負値停止の開始条件を変えるものではない。

### 補正定数37/5による最大値と試行回数

$$
u(L)=L-2\ln L+\frac{37}{5}\qquad(L > 0).
$$

上で定義した $M_{\mathrm{cl}}(B),M_{30}(B),T_{\mathrm{cl}}(B)$ に対し、次が成立する。

$$
\begin{gathered}
\mathrm{GRH},\quad B\in\mathbb N,\quad\ln B\ge50
\\
\Longrightarrow\quad
M_{\mathrm{cl}}(B)\le u(\ln B)^2,\quad
M_{30}(B)\le u(\ln B)^2,\quad
T_{\mathrm{cl}}(B)\le\frac{u(\ln B)^2-3}{2}.
\end{gathered}
$$

`selfridgeNeOneMaxima_le_shifted_double_log_from_fifty` と
`classicalNeOneTrialMaximum_le_shifted_double_log_from_fifty` が対応する。
共通尺度 $B$ での $Q_{\ne1}(B)$ 上界を使うため、 $\ln n < 50$ の対象入力も最大値に含む。
試行回数はJacobi記号の評価回数であり、ビット演算の計算量ではない。
[FiniteScaleShiftedDoubleLogBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/FiniteScaleShiftedDoubleLogBounds.lean) で証明した。

### 任意の上界を受け取る汎用の接続

最小奇素数証人を

$$
q_{-1}(n)=\min\left\lbrace p\in\mathbb P:p\text{ は奇数},\quad
\left(\frac np\right)=-1\right\rbrace,
$$

$$
q_{\ne1}(n)=\min\left\lbrace p\in\mathbb P:p\text{ は奇数},\quad
\left(\frac np\right)\ne1\right\rbrace
$$

とする。 $\mathbb P$ は正の素数全体、 $(n/p)$ は奇素数 $p$ を分母とするLegendre記号である。
この記号と証人の詳細は [PseudoSquare](PseudoSquare.md) を参照する。
停止値への移送自体はGRHを必要としない。上の奇数・非平方条件のもとで

$$
\begin{gathered}
X\in\mathbb R,\quad X\ge27,\quad q_{-1}(n)\le X
\\
\Longrightarrow\quad
\lvert g_{-1}(n)\rvert\le X,\quad\lvert g^{(30)}_{-1}(n)\rvert\le X,
\end{gathered}
$$

$$
\begin{gathered}
X\in\mathbb R,\quad X\ge15,\quad q_{\ne1}(n)\le X
\\
\Longrightarrow\quad
\lvert g_{\ne1}(n)\rvert\le X,\quad\lvert g^{(30)}_{\ne1}(n)\rvert\le X.
\end{gathered}
$$

`selfridgeNegOneMagnitudes_le_of_prime_witness_bound` と
`selfridgeNeOneMagnitudes_le_of_prime_witness_bound` が対応する。
これらの汎用移送は `WitnessTransfer.lean` にあり、三次核と係数上界の両方から利用する。
任意の解析評価を同じ入口へ渡せる。

## 平方自由部分別の上界の拡張

$$
\begin{gathered}
n=ds^2,\quad d > 1,\quad d,s\in\mathbb N,\quad
d,s\text{ は奇数},\quad d\text{ は平方自由},
\\
L=\ln n,\quad G=\ln(4d),\quad B_d=\frac{10}{13}G+35,\quad\widetilde B_d=\frac{10}{13}G+\frac{2434}{75},
\\
E_-(s)=\sum_{\substack{p\mid s\\p\text{ は奇素数}\\(d/p)=-1}}\ln p,
\quad F_d(L)=\frac43L+4B_d^2+2B_d\sqrt{\frac43L}.
\end{gathered}
$$

ここで $(d/p)$ はLegendre記号である。この分解のもとで次が成立する。

$$
\mathrm{GRH}\quad\Longrightarrow\quad
\lvert g_{\ne1}(n)\rvert\le\lvert g_{-1}(n)\rvert
\le\left(\widetilde B_d+\sqrt{\widetilde B_d^2+\frac83E_-(s)}\right)^2.
$$

$$
\mathrm{GRH}\quad\Longrightarrow\quad
\lvert g_{\ne1}(n)\rvert\le\lvert g_{-1}(n)\rvert\le F_d(L).
$$

`classicalSelfridgeD_cubic2434_negative_support_bound` と
`classicalSelfridgeD_cubic_linear_bound` が対応する。
負値奇素数証人から停止値へ移す際の例外定数27は、根上界と $F_d(L)$ が
いずれも27以上であることから吸収する。入力の有限検証は用いない。
Wheel30候補による対応する停止値にも同じ二つの式が成立し、
`wheel30SelfridgeD_cubic2434_negative_support_bound` と
`wheel30SelfridgeD_cubic_linear_bound` が対応する。

さらに、同じ分解のもとで

$$
\begin{gathered}
\mathrm{GRH},\quad\delta > 0,\quad
8B_d^2\le\delta L,\quad64B_d^2\le\delta^2L
\\
\Longrightarrow\quad
\lvert g_{\ne1}(n)\rvert\le\lvert g_{-1}(n)\rvert
\le\left(\frac43+\delta\right)L.
\end{gathered}
$$

`classicalSelfridgeD_cubic_linear_coefficient` が対応する。
固定した $d$ では、二つの開始条件を満たす全ての $L$ で対数一次の評価となる。
これらは平方自由部分に依存する結果であり、全入力一様の係数改善とは区別する。

### 切断点以下の除外費用による停止上界の改良

[PseudoSquareの切断費用](PseudoSquare.md#切断点以下の素因数費用による負値証人上界の改良)
で定義した $\theta_n,G,U_n(G;X)$ を用いる。

$$
\begin{gathered}
\mathrm{GRH},\quad n > 0,\quad n\text{ は奇数かつ非平方},\quad
\ln\mathrm{cond}(\theta_n)\le G,\\
X\ge27,\quad U_n(G;X)\le X
\\
\Longrightarrow\quad
\lvert g_{-1}(n)\rvert\le X,\quad
\lvert g^{(30)}_{-1}(n)\rvert\le X.
\end{gathered}
$$

[TruncatedCubicBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/TruncatedCubicBounds.lean)
の `selfridgeNegOneMagnitudes_le_of_truncated_cubic_radius` が対応する。
最小負値奇素数証人の上界を、両候補列の純粋負値停止へ移す。
除外費用は $X$ 以下の素因数だけを数え、値 $0$ の証人は用いない。

### 大きい平方因子を持つ入力族への一定停止上界の拡張

$G_d,X_d$ は [固定平方自由部分の証人上界](PseudoSquare.md#大きい平方因子を持つ入力族への一定上界の拡張) で定義した値とする。
奇素数の集合を $\mathbb P_{\mathrm{odd}}$ とする。

$$
\begin{gathered}
\mathrm{GRH},\quad n\in\mathbb N,\quad n > 0,\quad n\text{ は奇数かつ非平方},\\
n=ds^2,\quad d,s\in\mathbb N,\quad d > 1,\quad d\text{ は平方自由},\\
\forall\ell\in\mathbb P_{\mathrm{odd}},\quad
\bigl(\ell\mid s\land\left(\frac d\ell\right)=-1
\Longrightarrow X_d < \ell\bigr)
\\
\Longrightarrow\quad
\lvert g_{-1}(n)\rvert\le X_d,\quad
\lvert g^{(30)}_{-1}(n)\rvert\le X_d,\\
\lvert g_{\ne1}(n)\rvert\le X_d,\quad
\lvert g^{(30)}_{\ne1}(n)\rvert\le X_d.
\end{gathered}
$$

[FixedSquarefreeCubicBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/FixedSquarefreeCubicBounds.lean)
の `selfridgeNegOneMagnitudes_le_fixed_squarefree_family` が純粋負値停止、
`selfridgeNeOneMagnitudes_le_fixed_squarefree_family` が因子検出停止に対応する。
$X_d\ge27$ もLeanで証明しており、素数3に由来する停止値の例外を含めて同じ上界で抑える。
固定した $d$ では、条件を満たす平方因子 $s$ を大きくしても四つの上界は変わらない。

## 証人評価との接続

因子検出停止の大きさは、Jacobi 記号が $1$ でない最小の素数証人との比較を経て、PseudoSquare の対数二乗評価へ接続する。純粋 $-1$ 停止の大きさは、定数 $27$ と Jacobi 記号が $-1$ となる最小素数証人の最大値以下という比較を経て、一般 S1 由来の $R(n)$ へ接続する。この接続が [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) の点ごとの明示的上界を供給する。

有限最大では、 $B \ge 399$ で古典的な純粋 $-1$ 停止最大と $\mathrm{QNegOne}(B)$ が等しく、 $B \ge 751$ で因子検出停止最大と $\mathrm{QNeOne}(B)$ が等しい。対応する定理は `classicalNegOneMaximum_eq_QNegOne_of_399_le` と `classicalNeOneMaximum_eq_QNeOne_of_751_le`。Wheel30 版の等式もある。これらの比較・等式自体には GRH を必要とせず、GRH は解析的な上界を代入する段階で使う。

## 試行回数と計算量

`PseudoPrime.PrimeTest.classicalCandidateAt` は候補列、 `PseudoPrime.PrimeTest.classicalTrialCountThrough` は指定候補までの試行回数を定義する。奇数 $i \ge 5$ を古典候補とすると、その候補までの回数は $(i - 3) / 2$。 `classicalTrialMaximum_elementary_bound_explicit` は停止値最大の上界を、試行回数最大の明示上界に変換する。

具体的には GRH と $B \ge 751$ のもとで、因子検出の試行回数最大は純粋 $-1$ の試行回数最大以下、後者は $R(B) / 2 + 1$ 以下となる。

ここで数えるのは Jacobi 記号の試行回数である。1回の Jacobi 計算にかかる費用や、平方数チェック、Miller–Rabin、Lucas 評価を含むビット計算量・実測時間は評価しない。また、GRH を仮定する上界と、PrimeTest の素数完全性に使う無条件の有限探索成功は別の結果である。

## 利用方法

```lean
import PseudoPrime.PrimeTestBounds

#check PseudoPrime.PrimeTestBounds.Selfridge.classicalSelfridgeD_elementary_bound_explicit
#check PseudoPrime.PrimeTestBounds.Selfridge.classicalNeOneMaximum_cast_le_log_sq_of_751_le
#check PseudoPrime.PrimeTestBounds.Selfridge.classicalTrialMaximum_elementary_bound_explicit
#check PseudoPrime.PrimeTestBounds.Selfridge.selfridgeNegOneMagnitudes_le_four_fifths
#check PseudoPrime.PrimeTestBounds.Selfridge.selfridgeNeOneMagnitudes_le_sharp_double_log
```

全体を検証する場合は、 `lakefile.toml` のある `PseudoPrime` ディレクトリで `lake build` を実行する。

[構成全体へ](README.md)
