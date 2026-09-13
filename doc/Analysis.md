# Analysis — 数値比較を支える実解析

公開入口: [Analysis.lean](../PseudoPrime/Analysis.lean)。名前空間は `PseudoPrime.Analysis`。

この層は対数、Euler–Mascheroni定数、対数比、明示公式に現れる実数の誤差項を扱う。
LLSやJacobi目撃者を前提にせず、後続の数値比較を既存の実解析定理から証明できる形にする。
RH・GRHは仮定しない。

## 主な構成と成果

| ファイル | 主な内容・使い道 |
|---|---|
| [LogTaylorBounds.lean](../PseudoPrime/Analysis/LogTaylorBounds.lean) | Taylor展開と剰余評価から対数の上下界を得る。有限数値証明の基盤 |
| [RealLog.lean](../PseudoPrime/Analysis/RealLog.lean) | `log(y²)` の変形と、正の実数に対する対数の比較 |
| [EulerMascheroniBounds.lean](../PseudoPrime/Analysis/EulerMascheroniBounds.lean)・[ElementaryBounds.lean](../PseudoPrime/Analysis/ElementaryBounds.lean) | Euler–Mascheroni定数の有理数評価、平方根・対数の初等評価 |
| [NumericalLogBounds.lean](../PseudoPrime/Analysis/NumericalLogBounds.lean) | `log 12` 等の具体的な有理数評価、`q ≥ 3000` から `log q > 8` を得る定理 |
| [LogarithmicRatios.lean](../PseudoPrime/Analysis/LogarithmicRatios.lean) | 対数比の微分と単調性 |
| [LogarithmicConstants.lean](../PseudoPrime/Analysis/LogarithmicConstants.lean) | `log π`、`log 4`、`log 48` と分母の正値性の評価 |
| [LogarithmicMainTerms.lean](../PseudoPrime/Analysis/LogarithmicMainTerms.lean) | 偶・奇指標に対応する対数/逆数重みの誤差項の実数式 |
| [QNeOneElementaryBounds.lean](../PseudoPrime/Analysis/QNeOneElementaryBounds.lean) | QNeOneの比較で使う実変数の多項式・対数不等式 |
| [IntegralLimits.lean](../PseudoPrime/Analysis/IntegralLimits.lean) | 積分経路の極限に使う実変数の補助極限 |

## 代表的な主張

Euler–Mascheroni定数を `γ` とすると、次を証明している。

\[
\frac{27}{50}<\gamma<\frac{29}{50}.
\]

対応する定理は `twenty_seven_fiftieths_lt_eulerMascheroniConstant` と
`eulerMascheroniConstant_lt_twentyNine_fiftieths`。

`logLinearRatio y = (2 log y + 1)/y` と `logSquareRatio y = (log y)²/y` は、
ともに `y ≥ 8` で狭義単調減少する。
`strictAntiOn_logLinearRatio` と `strictAntiOn_logSquareRatio` により、
無限区間の比較を端点での評価へ帰着できる。

偶指標の対数誤差項は

\[
E_{\mathrm{even}}(x)=\frac{\pi^2}{24}-\frac\gamma2\log x-\frac12(\log x)^2
\]

として `primitiveLogEvenMainError` に定義されている。
この層で定義するのは実数式であり、L関数の重み付き和に対する上界であることは
[AnalyticNumberTheory](AnalyticNumberTheory.md)・[LLS](LLS.md)側で証明する。
式を粗い定数へ丸める一般評価と、式を保持する偶指標の精密評価の双方に再利用される。

## 利用例

```lean
import PseudoPrime.Analysis

#check PseudoPrime.Analysis.log_bounds_of_taylor
#check PseudoPrime.Analysis.eight_lt_log_level
#check PseudoPrime.Analysis.strictAntiOn_logLinearRatio
#check PseudoPrime.Analysis.strictAntiOn_logSquareRatio
```

[構成全体へ](README.md)
