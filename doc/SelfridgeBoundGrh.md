# Selfridge停止値へのGRH上界の接続（PrimeTestBounds.Selfridge）

対象: [`PseudoPrime/PrimeTestBounds/Selfridge`](../PseudoPrime/PrimeTestBounds/Selfridge)。公開入口は [`PseudoPrime/PrimeTestBounds.lean`](../PseudoPrime/PrimeTestBounds.lean)、上界の名前空間は `PseudoPrime.PrimeTestBounds.Selfridge`。離散的な候補列・試行回数・証人比較は `PseudoPrime.PrimeTest` に属する。

この領域では、[PrimeTest](PrimeTest.md) の数学的な Selfridge 停止値を [PseudoSquare](PseudoSquare.md) の Jacobi 証人上界に接続する。ルートの `import PseudoPrime` からも、この入口を利用できる。

## 構成

| モジュール | 内容 |
|---|---|
| [WitnessBridge.lean](../PseudoPrime/PrimeTest/Selfridge/WitnessBridge.lean) | 共通数論の素数証人と Selfridge 停止値の比較 |
| [MaximumBridge.lean](../PseudoPrime/PrimeTestBounds/Selfridge/MaximumBridge.lean) | 古典候補・Wheel30 の停止値最大と `QNeOne`／ `QNegOne` の接続 |
| [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) | 因子検出停止、純粋 $-1$ 停止、明示的半径の点ごとの比較 |
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

## 累積最大値の一致条件

PseudoSquareと同じ、 $0 < n\le B$ の奇数・非平方入力で累積最大値を取る。上端 $B$ 自身は任意の自然数である。上端0を含む式は、Leanの $\mathrm{Real.log}(0)=0$ と空の最大値0の規約で読む。古典停止最大を $M_{\ne1}(B),M_{-1}(B)$、Wheel30版を $M^{(30)}_{\ne1}(B),M^{(30)}_{-1}(B)$ と書く。

| 系列 | 一致を証明した範囲 | GRHなしで成り立つ等式 |
|---|---|---|
| 非1値・因子検出 | $B\ge751$ | $M^{(30)}_{\ne1}(B)=M_{\ne1}(B)=Q_{\ne1}(B)$ |
| 純粋負値 | $B\ge399$ | $M^{(30)}_{-1}(B)=M_{-1}(B)=Q_{-1}(B)$ |

[MaximumBridge.lean](../PseudoPrime/PrimeTestBounds/Selfridge/MaximumBridge.lean) の `classicalNeOneMaximum_eq_QNeOne_of_751_le`、`wheel30NeOneMaximum_eq_QNeOne_of_751_le`、`classicalNegOneMaximum_eq_QNegOne_of_399_le`、`wheel30NegOneMaximum_eq_QNegOne_of_399_le` が対応する。

小さい上端も含む全域では $Q_{\ne1}\le M_{\ne1}=M^{(30)}_{\ne1}\le\max\lbrace15,Q_{\ne1}\rbrace$、 $Q_{-1}\le M_{-1}=M^{(30)}_{-1}\le\max\lbrace27,Q_{-1}\rbrace$ を使う。 $B < 3$ の空の対象範囲では全て0である。[共通前提と小入力の扱い](PseudoSquare.md#selfridgeと共有する前提と累積最大値) を参照する。以下の解析的上界を代入する段階でGRHを加える。

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
| $L\ge10^{18}$ | $(777/1000)L^2$ | `selfridgeNegOne_fourPole_sharp` |

いずれも非平方の正奇数全体を対象とし、入力の因数分解に追加条件を課さない。
表は各係数上界の適用条件を示す。条件が重なる範囲では、その最小値を使う。

### 因子検出停止の専用上界

| 条件 | $\lvert g_{\ne1}(n)\rvert$ と $\lvert g^{(30)}_{\ne1}(n)\rvert$ の上界 | Lean定理 |
|---|---|---|
| $L\ge50$ | $(L-2\ln L+37/5)^2$ | `selfridgeNeOneMagnitudes_le_shifted_double_log_from_fifty` |
| $L\ge22221$ | $(4/5)L^2$ | `selfridgeNeOneMagnitudes_le_four_fifths` |
| $L\ge10^{18}$ | $(777/1000)L^2$ | `selfridgeNeOne_fourPole_sharp` |

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

### 係数777/1000の点ごと・累積上界

[FourPoleSharpFiniteBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/FourPoleSharpFiniteBounds.lean) は、GRH下で、対数が $10^{18}$ 以上の奇数・非平方入力について、古典SelfridgeとWheel30の負値停止・非1値停止の判別式の絶対値を $(777/1000)(\ln n)^2$ 以下に抑える。実際の最小Jacobi証人から既存の移送定理を使い、停止集合に含まれる条件を保持している。

累積最大値には [FourPoleFiniteBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/FourPoleFiniteBounds.lean) の `selfridgeMaxima_le_fourPole` を使う。入口未満を覆う定数項を残した `PseudoSquare.fourPoleCumulativeBound` が、4種類の停止最大値を全ての自然数上端で抑える。`classicalTrials_le_fourPole` は、古典方式の負値停止・非1値停止の両試行回数の累積最大値を、その候補の半分に1を加えた量で抑える。これらは数学的な停止値・回数の評価であり、実行用の探索アルゴリズムや偶数入力の規約を変更するものではない。

## 証人評価との接続

因子検出停止の大きさは、Jacobi 記号が $1$ でない最小の素数証人との比較を経て、PseudoSquare の対数二乗評価へ接続する。純粋 $-1$ 停止の大きさは、定数 $27$ と Jacobi 記号が $-1$ となる最小素数証人の最大値以下という比較を経て、一般 S1 由来の $R(n)$ へ接続する。この接続が [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) の点ごとの明示的上界を供給する。

有限最大では、 $B \ge 399$ で古典的な純粋 $-1$ 停止最大と $\mathrm{QNegOne}(B)$ が等しく、 $B \ge 751$ で因子検出停止最大と $\mathrm{QNeOne}(B)$ が等しい。対応する定理は `classicalNegOneMaximum_eq_QNegOne_of_399_le` と `classicalNeOneMaximum_eq_QNeOne_of_751_le`。Wheel30 版の等式もある。これらの比較・等式自体には GRH を必要とせず、GRH は解析的な上界を代入する段階で使う。

## 累積上界の適用区間と図

この節ではGRHを仮定する。 $U_{\ne1}(B),U_{-1}(B)$ は [PseudoSquareの区間別まとめ](PseudoSquare.md#証人別の上界式の適用区間と比較) にある、証明済み候補の最小値である。共通端点255、適用域内の定数4093、入口の履歴を保持する第四極核候補も含む。

| 対象 | 上端の条件 | 共通の累積上界 |
|---|---|---|
| 古典・Wheel30の非1値停止最大 | $B\ge751$ | $U_{\ne1}(B)$。 $Q_{\ne1}(B)$ と同じ図を使える |
| 古典・Wheel30の純粋負値停止最大 | $B\ge399$ | $U_{-1}(B)$。 $Q_{-1}(B)$ と同じ図を使える |
| 上記4種類の停止最大 | 全ての $B\in\mathbb N$ | $U_4(B)=\max\lbrace(9999/10000)(10^{18})^2,(777/1000)(\ln B)^2\rbrace$ |
| 上記4種類の停止最大 | $\ln B\ge L_{\mathrm{recover}}$ | $U_4(B)=(777/1000)(\ln B)^2$ |
| 古典方式の2種類の試行回数最大 | 全ての $B\in\mathbb N$ | $U_4(B)/2+1$ |

ここで $E=10^{18}$、 $L=\ln B$、 $L_{\mathrm{cross}}=E\sqrt{9999/8000}$、 $L_{\mathrm{recover}}=E\sqrt{9999/7770}$ とする。係数4/5と第四極核候補を選ぶ高域の区間は、PseudoSquareと同じである。

| 対数上端の区間 | 4種類の停止最大に共通の上界 |
|---|---|
| $E\le L\le L_{\mathrm{cross}}$ | $(4/5)L^2$ |
| $L_{\mathrm{cross}} < L < L_{\mathrm{recover}}$ | $(9999/10000)E^2$ |
| $L_{\mathrm{recover}}\le L$ | $(777/1000)L^2$ |

切替は候補の定義式の代数比較であり、[PseudoSquareの高域区間表](PseudoSquare.md#高域の累積上界) と同じものを使う。図の浮動小数の交点を証人定理の適用条件にしない。

小さい上端でPseudoSquareの図を停止最大の上界に使う場合は、非1値側に $\max\lbrace15,U_{\ne1}(B)\rbrace$、負値側に $\max\lbrace27,U_{-1}(B)\rbrace$ を使う。一致範囲で等しいのは実際の累積最大値どうしであり、上界曲線と実際値の等号を意味しない。小さい上端では、PseudoSquareの記録線をSelfridgeの記録と同一視しない。

点ごとの777/1000は $\ln n\ge10^{18}$ から使えるが、累積値にはそれ未満の入力も入る。したがって累積候補は $U_4$ の定数項を残し、既存候補より小さくなった範囲で採用する。

![非1値証人と、751以上で一致するSelfridge停止最大の共通上界](figures/qne1_upper_bound_comparison.svg)

![負値証人と、399以上で一致するSelfridge停止最大の共通上界](figures/qneg1_upper_bound_comparison.svg)

この2図はPseudoSquareと共有する。上端751以上の非1値系列、399以上の負値系列では、記録線は古典・Wheel30の対応する停止最大値の記録としても読め、上界曲線も共通に使える。それ未満の記録線はPseudoSquareの証人最大値として読む。

![入口の履歴を残した第四極核の共通累積上界](figures/q_four_pole_high_comparison.svg)

高域図は $U_4$ と係数4/5の候補の最小値を $(\ln B)^2$ で割ったもの。一致範囲では同じ曲線がSelfridgeの停止最大も抑える。図の補間はLeanの証明を代替しない。[図・適用条件・生成スクリプトの一覧](figures/README.md) を参照する。

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
