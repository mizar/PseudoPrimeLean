# PseudoSquare — Jacobi 証人の最大値と GRH に基づく解析的上界

対象: [`PseudoPrime/PseudoSquare`](../PseudoPrime/PseudoSquare)。公開入口は [`PseudoPrime/PseudoSquare.lean`](../PseudoPrime/PseudoSquare.lean)、名前空間は `PseudoPrime.PseudoSquare`。

この領域は、奇数かつ非平方数に対する最小 Jacobi 証人の最大値を定義し、有限計算と Dirichlet 指標・ L 関数の解析を組み合わせて上界を証明する。実行用の BPSW 本体は [PrimeTest](PrimeTest.md)、Selfridge 固有の上界への接続は [SelfridgeBoundGrh](SelfridgeBoundGrh.md) が担当する。

## 構成

| ディレクトリ | 内容 |
|---|---|
| [Bounds](../PseudoPrime/PseudoSquare/Bounds) | 証人の有限最大、点ごとの上界、対数・初等半径の評価 |
| [Computation](../PseudoPrime/PseudoSquare/Computation) | 小区間の証明書、閾値、剰余類を用いた有限部分の検証 |
| [CharacterBound.lean](../PseudoPrime/PseudoSquare/CharacterBound.lean) | 一般 S1 の結論を Jacobi 値が $-1$ の証人へ変換 |
| [QNeOneConcrete.lean](../PseudoPrime/PseudoSquare/QNeOneConcrete.lean)・[QNeOneFinal.lean](../PseudoPrime/PseudoSquare/QNeOneFinal.lean) | `QNeOne` の上界に向けた解析的三分岐と有限範囲を統合 |

二次指標の構成・原始化・導手算術は [NumberTheory](NumberTheory.md)、一般解析は [Analysis.lean](../PseudoPrime/Analysis.lean)、GRH・L 関数・Riemann の $\zeta$ 関数・ $\xi$ 関数・輪郭と平滑化明示公式は [AnalyticNumberTheory.lean](../PseudoPrime/AnalyticNumberTheory.lean) に分離されている。これらの一般層は PseudoSquare を import しない。LLS には専用の誤差配分・数値分離と結論への接続を置く。 LLS の公開入口と主張は [LLS](LLS.md) を参照する。

## `QNeOne` と `QNegOne`

[Bounds/WitnessMaximum.lean](../PseudoPrime/PseudoSquare/Bounds/WitnessMaximum.lean) は、正の奇数かつ非平方数 $n \le B$ における最小奇素数証人の最大値を定義する。以下では `QNeOne B` と `QNegOne B` を、それぞれ $\mathrm{QNeOne}(B)$ と $\mathrm{QNegOne}(B)$ と表す。奇素数 $p$ に対する Legendre 記号 $\bigl(\frac{n}{p}\bigr)$ は、Lean の `jacobiSym n p` に一致する。

- $\mathrm{QNeOne}(B)$： $\bigl(\frac{n}{p}\bigr) \ne 1$ を満たす最小奇素数の最大値。
- $\mathrm{QNegOne}(B)$： $\bigl(\frac{n}{p}\bigr) = -1$ を満たす最小奇素数の最大値。

証人そのものは [NumberTheory](NumberTheory.md) の定義を使用する。許容集合が空の場合の最大値は $0$ で、定義は `noncomputable`。 `QNeOne_le_QNegOne` が両者の比較を与える。許容入力は奇数かつ非平方数であり、古典的 pseudosquare の $n \equiv 1 \pmod 8$ という条件だけに限定した定義ではない。

## GRH と主要な結果

[GRH/Definition.lean](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) の `PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis` が解析的前提である。 `GeneralizedRiemannHypothesis.riemann` により RH を取り出せるが、GRH 自体を証明するものではない。

$\ln$ を自然対数とし、

$$
R(n) = \Bigl(\ln(4n) + \frac{24}{5}\ln(\ln(4n)) + 3\Bigr)^2
$$

と置く。[Bounds/PointwiseWitness.lean](../PseudoPrime/PseudoSquare/Bounds/PointwiseWitness.lean) は、GRH のもとで正の奇数かつ非平方数 $n$ に対し次の奇素数証人の存在を示す。

| 公開定理 | 保証 |
|---|---|
| `exists_prime_ne_one_witness_of_grh` | $p \le \max\left\lbrace 5, (\ln\mathrel{} n)^2 \right\rbrace$ かつ $\bigl(\frac{n}{p}\bigr) \ne 1$ |
| `exists_prime_neg_one_witness_of_grh` | $p \le R(n)$ かつ $\bigl(\frac{n}{p}\bigr) = -1$ |

有限最大についても次を証明している。

| 公開定理 | 前提と結論 |
|---|---|
| `QNeOne_le_log_sq_of_grh` | GRH、 $B \ge 10$ なら $\mathrm{QNeOne}(B) \le (\ln\mathrel{} B)^2$ |
| `QNeOne_le_greatestOddPrimeLE_of_grh` | 同じ前提で、 $\mathrm{QNeOne}(B)$ はその半径以下の最大奇素数以下 |
| `elementary_formula_explicit` | GRH、 $B \ge 3$ なら $\mathrm{QNeOne}(B) \le \mathrm{QNegOne}(B)$ かつ $\mathrm{QNegOne}(B) \le R(B)$（実数に変換して比較） |

`primeNeOneWitness_cast_le_log_sq_of_11_le` は、奇数かつ非平方数 $n \ge 11$ の最小証人について直接 $(\ln\mathrel{} n)^2$ 以下を示す。公開の存在定理では小さい入力を定数 $5$ と対数二乗上界の最大値でまとめる。

## LLS の役割

[LLS/Statement.lean](../PseudoPrime/LLS/Statement.lean) の `llsTheorem11S1Character` は、法 $q \ge 3000$ の非自明な Dirichlet 指標について、法を割らず指標値が $1$ でない素数を明示的な上界以下に求める仕様である。部分群についての主張を指標の核に特殊化した形を採用する。

[LLS/Theorem11S1GRH.lean](../PseudoPrime/LLS/Theorem11S1GRH.lean) は一般指標の解析結果を組み立てる。Jacobi 値が $-1$ の評価は、この一般 S1 を法 $4n$ の指標に適用して得る。[JacobiCharacterArithmetic.lean](../PseudoPrime/NumberTheory/JacobiCharacterArithmetic.lean) の算術と中間の重み付き評価を用いて `QNeOne` の上界を導く経路と、有限区間の数値証明はそれぞれ異なる役割を持つ。 `QNeOne` と `QNegOne` の二分だけを、そのまま原論文の part (1) と part (2) の対応と読むことはできない。

Jacobi 記号が $-1$ となる証人について、大きい入力 $n \ge 750$ での存在は一般 S1 から、小さい入力での存在は有限証明書から得る。明示的半径への変換には無条件の素因数個数評価を使い、Robin 評価は仮定しない。 Jacobi 記号が $1$ でない証人については、原始指標の $2$ での値が $0$・ $1$・ $-1$ となる三分岐を扱い、有限範囲と接続する。両存在定理は公開 API であり、Selfridge 側はその手前の最小証人・最大値評価も直接利用する。

## 利用方法

```lean
import PseudoPrime.PseudoSquare

#check PseudoPrime.PseudoSquare.QNeOne_le_QNegOne
#check PseudoPrime.PseudoSquare.exists_prime_ne_one_witness_of_grh
#check PseudoPrime.PseudoSquare.exists_prime_neg_one_witness_of_grh
```

個別の結果だけ必要なら、対応する Bounds 等のモジュールを直接 import できる。Selfridge の候補順序・停止値を含む結果は専用の統合領域へ進む。

[構成全体へ](README.md)
