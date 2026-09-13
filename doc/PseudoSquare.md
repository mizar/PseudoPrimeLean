# PseudoSquare — Jacobi目撃者の最大値とGRHに基づく解析的上界

対象: [`PseudoPrime/PseudoSquare`](../PseudoPrime/PseudoSquare)。公開入口は [`PseudoPrime/PseudoSquare.lean`](../PseudoPrime/PseudoSquare.lean)、名前空間は `PseudoPrime.PseudoSquare`。

この領域は、奇非平方数に対する最小Jacobi目撃者の最大値を定義し、有限計算とDirichlet指標・L関数の解析を組み合わせて上界を証明する。実行用のBPSW本体は [PrimeTest](PrimeTest.md)、Selfridge固有の上界への接続は [SelfridgeBoundGrh](SelfridgeBoundGrh.md) が担当する。

## 構成

| ディレクトリ | 内容 |
|---|---|
| [Bounds](../PseudoPrime/PseudoSquare/Bounds) | 目撃者の有限最大、点ごとの上界、対数・初等半径の評価 |
| [Computation](../PseudoPrime/PseudoSquare/Computation) | 小区間の証明書、閾値、剰余類を用いた有限部分の検証 |
| [CharacterBound.lean](../PseudoPrime/PseudoSquare/CharacterBound.lean) | 一般S1の結論をJacobi値−1の目撃者へ変換 |
| [QNeOneConcrete.lean](../PseudoPrime/PseudoSquare/QNeOneConcrete.lean)・[QNeOneFinal.lean](../PseudoPrime/PseudoSquare/QNeOneFinal.lean) | Q≠1の解析的三分岐と有限範囲を統合 |

二次指標の構成・原始化・導手算術は [NumberTheory](NumberTheory.md)、一般解析は
[Analysis.lean](../PseudoPrime/Analysis.lean)、GRH・L関数・ζ/ξ・輪郭と平滑化明示公式は
[AnalyticNumberTheory.lean](../PseudoPrime/AnalyticNumberTheory.lean) に分離されている。
これらの一般層はPseudoSquareをimportしない。LLSには専用の誤差配分・数値分離と結論への接続を置く。
LLSの公開入口と主張は [LLS](LLS.md) を参照する。

## QNeOneとQNegOne

[Bounds/WitnessMaximum.lean](../PseudoPrime/PseudoSquare/Bounds/WitnessMaximum.lean) は、許容入力 `n ≤ B` における最小奇素数目撃者の最大値を定義する。

- `QNeOne B`：`jacobiSym n p ≠ 1` を満たす最小奇素数の最大値。
- `QNegOne B`：`jacobiSym n p = -1` を満たす最小奇素数の最大値。

目撃者そのものは [NumberTheory](NumberTheory.md) の定義を使用する。許容集合が空の場合の最大値は0で、定義は `noncomputable`。`QNeOne_le_QNegOne` が両者の比較を与える。許容入力は奇非平方数であり、古典的pseudosquareの `n ≡ 1 (mod 8)` という条件だけに限定した定義ではない。

## GRHと主要な結果

[GRH/Definition.lean](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) の `PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis` が解析的前提である。`GeneralizedRiemannHypothesis.riemann` によりRHを取り出せるが、GRH自体を証明するものではない。

`log` を自然対数とし、

\[
R(n)=\left(\log(4n)+\frac{24}{5}\log\log(4n)+3\right)^2
\]

と置く。[Bounds/PointwiseWitness.lean](../PseudoPrime/PseudoSquare/Bounds/PointwiseWitness.lean) は、GRHのもとで正の奇非平方数 `n` に対し次の奇素数目撃者の存在を示す。

| 公開定理 | 保証 |
|---|---|
| `exists_prime_ne_one_witness_of_grh` | `p ≤ max 5 (log n)^2` かつ `jacobiSym n p ≠ 1` |
| `exists_prime_neg_one_witness_of_grh` | `p ≤ R(n)` かつ `jacobiSym n p = -1` |

有限最大についても次を証明している。

| 公開定理 | 前提と結論 |
|---|---|
| `QNeOne_le_log_sq_of_grh` | GRH、`B ≥ 10` なら `QNeOne B ≤ (log B)²` |
| `QNeOne_le_greatestOddPrimeLE_of_grh` | 同じ前提で、`QNeOne B` はその半径以下の最大奇素数以下 |
| `elementary_formula_explicit` | GRH、`B ≥ 3` なら `QNeOne B ≤ QNegOne B` かつ `QNegOne B ≤ R(B)`（実数に変換して比較） |

`primeNeOneWitness_cast_le_log_sq_of_11_le` は、奇非平方数 `n ≥ 11` の最小目撃者について
直接 `(log n)²` 以下を示す。公開の存在定理では小さい入力を `max 5` でまとめる。

## LLSの役割

[LLS/Statement.lean](../PseudoPrime/LLS/Statement.lean) の `llsTheorem11S1Character` は、法 `q ≥ 3000` の非自明Dirichlet指標について、法を割らず指標値が1でない素数を明示的な上界以下に求める仕様である。部分群についての主張を指標の核に特殊化した形を採用する。

[LLS/Theorem11S1GRH.lean](../PseudoPrime/LLS/Theorem11S1GRH.lean) は一般指標の解析結果を組み立てる。Jacobi値−1の評価は、この一般S1を法 `4n` の指標に適用して得る。[JacobiCharacterArithmetic.lean](../PseudoPrime/NumberTheory/JacobiCharacterArithmetic.lean) の算術と中間の重み付き評価を用いるQ≠1経路、有限区間の数値証明は別の役割を持つ。`QNeOne` と `QNegOne` の二分だけを、そのまま原論文のpart (1)とpart (2)の対応と読むことはできない。

`=-1` の大きい入力 `n ≥ 750` は一般S1から、小さい入力は有限証明書から得る。
初等半径への変換には無条件の素因数個数評価を使い、Robin評価は仮定しない。
`≠1` は原始指標の2での値が0・1・−1となる三分岐を扱い、有限範囲と接続する。
両存在定理は公開APIであり、Selfridge側はその手前の最小目撃者・最大値評価も直接利用する。

## 利用方法

```lean
import PseudoPrime.PseudoSquare

#check PseudoPrime.PseudoSquare.QNeOne_le_QNegOne
#check PseudoPrime.PseudoSquare.exists_prime_ne_one_witness_of_grh
#check PseudoPrime.PseudoSquare.exists_prime_neg_one_witness_of_grh
```

個別の結果だけ必要なら、対応するBounds等のモジュールを直接importできる。Selfridgeの候補順序・停止値を含む結果は専用の統合領域へ進む。

[構成全体へ](README.md)
