# AnalyticNumberTheory — 重み付き素数和とL関数の解析基盤

公開入口: [AnalyticNumberTheory.lean](../PseudoPrime/AnalyticNumberTheory.lean)。
主な名前空間は `PseudoPrime.AnalyticNumberTheory` とその下位名前空間。

この層は算術的な有限和、導手による法変更、ζ・ξ・Dirichlet L関数、矩形輪郭積分、
零点和の極限を接続する。[LLS](LLS.md)固有の最終半径と数値分離はLLS側に置く。
この入口からLLSやPseudoSquareへの逆向きのimportはない。

## 構成

| 領域 | 主な成果 |
|---|---|
| [Arithmetic](../PseudoPrime/AnalyticNumberTheory/Arithmetic) | 重み付きvon Mangoldt和、素因数和、導手・法変更の補正、初等的な素因数個数評価 |
| [GRH](../PseudoPrime/AnalyticNumberTheory/GRH) | 原始指標に対するGRHの定義、自明零点の除外、GRHからRHへの取り出し |
| [General](../PseudoPrime/AnalyticNumberTheory/General) | Mellin重み、極・留数、減衰評価、関数の分解と近傍の補助定理 |
| [RectangleGeometry](../PseudoPrime/AnalyticNumberTheory/RectangleGeometry)・[Rectangle](../PseudoPrime/AnalyticNumberTheory/Rectangle) | 矩形境界、格子分割、特異点分離、有限留数和との対応 |
| [Gamma](../PseudoPrime/AnalyticNumberTheory/Gamma) | Gamma関数の成長とtrigamma特殊値 |
| [RiemannZeta](../PseudoPrime/AnalyticNumberTheory/RiemannZeta) | 零点計数・可算和、良い高さ列、平滑化核、水平辺・左辺の評価と極限 |
| [RiemannXi](../PseudoPrime/AnalyticNumberTheory/RiemannXi) | 整関数ξの成長、零点の有限性、Hadamard型極限、零点質量評価 |
| [DirichletLFunction](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction) | 一般原始指標の関数等式・共役・零点・明示公式と、二次/偶指標の精密評価 |

## 重み付き和と導手補正

`Λ` をvon Mangoldt関数、`χ` を複素Dirichlet指標とする。
[WeightedMangoldt.lean](../PseudoPrime/AnalyticNumberTheory/Arithmetic/WeightedMangoldt.lean) は

\[
S(x,\chi)=\sum_{1\le m\le\lfloor x\rfloor}\Lambda(m)\log(x/m)\chi(m),\qquad
T(x,\chi)=\sum_{1\le m\le\lfloor x\rfloor}\frac{\Lambda(m)}m(1-m/x)\chi(m)
\]

を `characterLogWeightedSum`、`characterReciprocalWeightedSum` として定義する。
指標を掛けない実数版も定義し、素数冪への分解や共通因子を持つ項の分離を証明する。

[LogLevelChange.lean](../PseudoPrime/AnalyticNumberTheory/Arithmetic/LogLevelChange.lean) と
[ReciprocalLevelChange.lean](../PseudoPrime/AnalyticNumberTheory/Arithmetic/ReciprocalLevelChange.lean)
は、法 `q` の指標とその導手 `f` の原始指標との間の有限和の差を明示する。
`primitiveLogConductorAbsorption` などは、その補正を法 `q` の上界に吸収する。
この一般指標の処理により、LLS S1の解析経路は二次性を仮定せず組み立てられる。

## GRHと輪郭積分の成果

[Definition.lean](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) の
`GeneralizedRiemannHypothesis` は、法1を含む全原始複素Dirichlet指標について、
所定の自明零点以外のL関数の零点の実部が `1/2` であるという命題である。
`GeneralizedRiemannHypothesis.riemann` が法1からRHを導く。
したがって後続のGRH定理に独立したRH仮定を追加する必要はない。

解析証明では、有限矩形の境界積分を留数和に変換し、良い高さ列に沿って水平辺を消し、
さらに左辺を遠方へ移す。一般指標用の
[PrimitiveGenericLogLeftVertical.lean](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/PrimitiveGenericLogLeftVertical.lean)
などがこの極限を供給する。有限輪郭の条件と極限の条件を個別の定理で確認する構成である。
RH・GRHが必要な零点評価は、それぞれの定理の引数として受け取る。

偶原始二次指標については
[EvenLogWeightedUpper.lean](../PseudoPrime/AnalyticNumberTheory/DirichletLFunction/EvenLogWeightedUpper.lean)
の `primitiveLogWeightedUpper_of_grh_even_exact` が、`x ≥ 64` で偶指標の誤差項を保持した
`Re S(x,χ)` の上界を与える。一般の偶指標すべてを対象とする型ではなく、現状は二次性も要求する。

## 無条件の定量的成果

[ElementaryOmegaFiniteCertificates.lean](../PseudoPrime/AnalyticNumberTheory/Arithmetic/ElementaryOmegaFiniteCertificates.lean)
の `elementaryOmegaStatement` は、奇数 `n ≥ 750` に対して

\[
\omega(4n)\le\frac75\frac{\log(4n)}{\log\log(4n)}
\]

を与える。ここで `ω` は異なる素因数の個数。
有限証明書と解析的な尾部評価を組み合わせた無条件の結果であり、Robin評価を仮定しない。
LLSの補正項をPseudoSquareの明示的な初等半径に直す際に使う。

## 利用例

```lean
import PseudoPrime.AnalyticNumberTheory

#check PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis.riemann
#check PseudoPrime.AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
#check PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveLogConductorAbsorption
#check PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement
```

[構成全体へ](README.md)
