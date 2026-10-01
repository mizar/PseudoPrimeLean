# PrimeTestBounds.Selfridge — Selfridge 停止値への GRH 上界の接続

対象: [`PseudoPrime/PrimeTestBounds/Selfridge`](../PseudoPrime/PrimeTestBounds/Selfridge)。公開入口は [`PseudoPrime/PrimeTestBounds.lean`](../PseudoPrime/PrimeTestBounds.lean)、上界の名前空間は `PseudoPrime.PrimeTestBounds.Selfridge`。離散的な候補列・試行回数・証人比較は `PseudoPrime.PrimeTest` に属する。

この領域は [PrimeTest](PrimeTest.md) の数学的な Selfridge 停止値と、[PseudoSquare](PseudoSquare.md) の Jacobi 証人上界を接続する。入口はルートの `import PseudoPrime` からも到達できる。

## 構成

| モジュール | 内容 |
|---|---|
| [WitnessBridge.lean](../PseudoPrime/PrimeTest/Selfridge/WitnessBridge.lean) | 共通数論の素数証人と Selfridge 停止値の比較 |
| [MaximumBridge.lean](../PseudoPrime/PrimeTestBounds/Selfridge/MaximumBridge.lean) | 古典候補・Wheel30 の停止値最大と `QNeOne`／ `QNegOne` の接続 |
| [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) | 因子検出停止、純粋 $-1$ 停止、明示的半径の点ごとの比較 |
| [LogSqMaximum.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogSqMaximum.lean) | 停止値の有限最大に対する対数二乗上界 |
| [LogGRH.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogGRH.lean) | GRH を仮定する点ごとの上界 |
| [TrialCount.lean](../PseudoPrime/PrimeTestBounds/Selfridge/TrialCount.lean) | 無条件の最大試行回数と実数への比較 |
| [Selfridge/TrialCount.lean](../PseudoPrime/PrimeTest/Selfridge/TrialCount.lean) | 離散的な候補列と試行回数（PrimeTest） |
| [LogBounds.lean](../PseudoPrime/PrimeTestBounds/Selfridge/LogBounds.lean) | 無条件の数値対数評価・小区間評価 |
| [Comparison.lean](../PseudoPrime/PrimeTestBounds/Selfridge/Comparison.lean) | 無条件の実数への停止値比較 |
| [TrialCountGRH.lean](../PseudoPrime/PrimeTestBounds/Selfridge/TrialCountGRH.lean) | GRH 付き試行回数上界 |

## 停止値の意味

古典候補は大きさ $5, 7, 9, 11, \ldots$ を昇順に並べ、 `selfridgeD` が符号付き判別式 $5, -7, 9, -11, \ldots$ に変換する。

`firstStopNegOne` は Jacobi 値が $-1$ になる最初の候補の大きさ。 `firstStopNeOne` は $n \nmid i$ を満たし、Jacobi 値が $1$ と異なる最初の候補の大きさで、非自明因子検出も含める。いずれも非空性の証明を受け取る数学的最小元である。

対応する符号付き停止値を $g_{-1}(n)$ と $g_{\ne 1}(n)$ と書くと、絶対値は候補の大きさに等しい。この領域の上界はこれらの数学的停止値について述べる。現行 BPSW の実行用探索に Jacobi 値 $0$ による早期停止を追加するものではない。

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

## 証人評価との接続

因子検出停止の大きさは、Jacobi 記号が $1$ でない最小の素数証人との比較を経て、PseudoSquare の対数二乗評価へ接続する。純粋 $-1$ 停止の大きさは、定数 $27$ と Jacobi 記号が $-1$ となる最小素数証人の最大値以下という比較を経て、一般 S1 由来の $R(n)$ へ接続する。この接続が [ElementaryRadius.lean](../PseudoPrime/PrimeTestBounds/Selfridge/ElementaryRadius.lean) の点ごとの明示的上界を供給する。

有限最大では、 $B \ge 399$ で古典的な純粋 $-1$ 停止最大と $\mathrm{QNegOne}(B)$ が等しく、 $B \ge 751$ で因子検出停止最大と $\mathrm{QNeOne}(B)$ が等しい。対応する定理は `classicalNegOneMaximum_eq_QNegOne_of_399_le` と `classicalNeOneMaximum_eq_QNeOne_of_751_le`。Wheel30 版の等式もある。これらの比較・等式自体には GRH を必要とせず、GRH は解析的な上界を代入する段階で使う。

## 試行回数と計算量

`PseudoPrime.PrimeTest.classicalCandidateAt` は候補列、 `PseudoPrime.PrimeTest.classicalTrialCountThrough` は指定候補までの試行回数を定義する。奇数 $i \ge 5$ を古典候補とすると、その候補までの回数は $(i - 3) / 2$。 `classicalTrialMaximum_elementary_bound_explicit` は停止値最大の上界を、試行回数最大の明示上界に変換する。

具体的には GRH と $B \ge 751$ のもとで、因子検出の試行回数最大は純粋 $-1$ の試行回数最大以下、後者は $R(B) / 2 + 1$ 以下となる。

ここで数えるのは Jacobi 記号の試行回数である。1 回の Jacobi 計算の費用、平方数チェック、Miller–Rabin、Lucas 評価を含むビット計算量や実測時間そのものではない。また、GRH を仮定する上界と、PrimeTest の素数完全性に用いる無条件の有限探索成功は別の結果である。

## 利用方法

```lean
import PseudoPrime.PrimeTestBounds

#check PseudoPrime.PrimeTestBounds.Selfridge.classicalSelfridgeD_elementary_bound_explicit
#check PseudoPrime.PrimeTestBounds.Selfridge.classicalNeOneMaximum_cast_le_log_sq_of_751_le
#check PseudoPrime.PrimeTestBounds.Selfridge.classicalTrialMaximum_elementary_bound_explicit
```

全体を検証する場合は、 `lakefile.toml` のある `PseudoPrime` ディレクトリで `lake build` を実行する。

[構成全体へ](README.md)
