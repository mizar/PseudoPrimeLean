# SelfridgeBoundGrh — Selfridge停止値へのGRH上界の接続

対象: [`PseudoPrime/SelfridgeBoundGrh`](../PseudoPrime/SelfridgeBoundGrh)。公開入口は [`PseudoPrime/SelfridgeBoundGrh.lean`](../PseudoPrime/SelfridgeBoundGrh.lean)、名前空間は `PseudoPrime.SelfridgeBoundGrh`。

この領域は [PrimeTest](PrimeTest.md) の数学的なSelfridge停止値と、[PseudoSquare](PseudoSquare.md) のJacobi目撃者上界を接続する。入口はルートの `import PseudoPrime` からも到達できる。

## 構成

| モジュール | 内容 |
|---|---|
| [WitnessBridge.lean](../PseudoPrime/SelfridgeBoundGrh/WitnessBridge.lean) | 共通数論の素数目撃者とSelfridge停止値の比較 |
| [MaximumBridge.lean](../PseudoPrime/SelfridgeBoundGrh/MaximumBridge.lean) | 古典候補・Wheel30の停止値最大と `QNeOne`／`QNegOne` の接続 |
| [ElementaryRadius.lean](../PseudoPrime/SelfridgeBoundGrh/ElementaryRadius.lean) | 因子検出停止、純粋-1停止、明示的半径の点ごとの比較 |
| [LogSqMaximum.lean](../PseudoPrime/SelfridgeBoundGrh/LogSqMaximum.lean) | 停止値の有限最大に対する対数二乗上界 |
| [LogSq.lean](../PseudoPrime/SelfridgeBoundGrh/LogSq.lean) | 小区間と一般区間を合わせた点ごとの上界 |
| [TrialCount.lean](../PseudoPrime/SelfridgeBoundGrh/TrialCount.lean) | 停止候補をJacobi試行回数へ変換した上界 |

## 停止値の意味

古典候補は大きさ `5, 7, 9, 11, ...` を昇順に並べ、`selfridgeD` が符号付き判別式 `5, -7, 9, -11, ...` に変換する。

`firstStopNegOne` はJacobi値が `-1` になる最初の候補の大きさ。`firstStopNeOne` は `¬ n ∣ i` とJacobi値 `≠ 1` を満たす最初の候補の大きさで、非自明因子検出も含める。いずれも非空性の証明を受け取る数学的最小元である。

対応する符号付き停止値を `g_-1(n)` と `g_≠1(n)` と書くと、絶対値は候補の大きさに等しい。この領域の上界はこれらの数学的停止値について述べる。現行BPSWの実行用探索にJacobi=0の早期停止を追加するものではない。

## 主要な公開結果

自然対数を用いて

$$
R(n)=\left(\log(4n)+\frac{24}{5}\log\log(4n)+3\right)^2
$$

と置く。GRHと各定理の奇数・非平方条件のもとで、以下を得る。

| 公開定理 | 入力範囲と結論 |
|---|---|
| `classicalSelfridgeD_elementary_bound_explicit` | `n ≥ 3` で `|g_≠1(n)| ≤ |g_-1(n)| ≤ R(n)` |
| `classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le` | `n ≥ 13` で `|g_≠1(n)| ≤ (log n)^2` |
| `classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq` | 奇非平方入力で `|g_≠1(n)| ≤ max 13 (log n)^2` |
| `classicalNeOneMaximum_cast_le_log_sq_of_751_le` | `B ≥ 751` で因子検出停止値の最大が `(log B)^2` 以下 |

名前に `log_sq` を含む既存定理でも、純粋-1側には右辺が `R(n)` のものがある。利用時は名前だけでなく定理の型を確認する。

## 目撃者評価との接続

因子検出停止は最小の `≠1` 素数目撃者との比較を経て、PseudoSquareの対数二乗評価へ接続する。
純粋−1停止は `max 27 (最小の−1素数目撃者)` 以下という比較を経て、一般S1由来の `R(n)` へ接続する。
この接続が [ElementaryRadius.lean](../PseudoPrime/SelfridgeBoundGrh/ElementaryRadius.lean) の
点ごとの明示的上界を供給する。

有限最大では、`B ≥ 399` で古典的な純粋−1停止最大と `QNegOne B` が等しく、
`B ≥ 751` で因子検出停止最大と `QNeOne B` が等しい。
対応する定理は `classicalNegOneMaximum_eq_QNegOne_of_399_le` と
`classicalNeOneMaximum_eq_QNeOne_of_751_le`。Wheel30版の等式もある。
これらの比較・等式自体にはGRHを必要とせず、GRHは解析的な上界を代入する段階で使う。

## 試行回数と計算量

`classicalCandidateAt` は候補列、`classicalTrialCountThrough` は指定候補までの試行回数を定義する。古典候補 `i` までの回数は `(i - 3) / 2`。`classicalTrialMaximum_elementary_bound_explicit` は停止値最大の上界を、試行回数最大の明示上界に変換する。

具体的にはGRHと `B ≥ 751` のもとで、因子検出の試行回数最大は純粋−1の試行回数最大以下、
後者は `R(B)/2 + 1` 以下となる。

ここで数えるのはJacobi記号の試行回数である。1回のJacobi計算の費用、平方数チェック、Miller–Rabin、Lucas評価を含むビット計算量や実測時間そのものではない。また、GRHを仮定する上界と、PrimeTestの素数完全性に用いる無条件の有限探索成功は別の結果である。

## 利用方法

```lean
import PseudoPrime.SelfridgeBoundGrh

#check PseudoPrime.SelfridgeBoundGrh.classicalSelfridgeD_elementary_bound_explicit
#check PseudoPrime.SelfridgeBoundGrh.classicalNeOneMaximum_cast_le_log_sq_of_751_le
#check PseudoPrime.SelfridgeBoundGrh.classicalTrialMaximum_elementary_bound_explicit
```

全体を検証する場合は、`lakefile.toml` のある `PseudoPrime` ディレクトリで `lake build` を実行する。

[構成全体へ](README.md)
