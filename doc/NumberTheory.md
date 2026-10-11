# NumberTheoryの共通数論基盤

対象: [`PseudoPrime/NumberTheory`](../PseudoPrime/NumberTheory)。名前空間は `PseudoPrime.NumberTheory`。

この領域では、奇数かつ非平方数、素因数分解、Jacobi 記号、最小の奇素数証人を扱う。実行用の素数判定と GRH に基づく解析的上界に共通する算術を提供する。プロジェクト内の依存関係は NumberTheory 内で完結し、PrimeTest や PseudoSquare は import しない。

## 構成

| モジュール | 内容 |
|---|---|
| [Fibonacci/Greatest.lean](../PseudoPrime/NumberTheory/Fibonacci/Greatest.lean) | 最大Fibonacci添字の二進探索と正当性 |
| [Euclid.lean](../PseudoPrime/NumberTheory/Euclid.lean) | 互除法のFibonacci燃料、gcdの正当性、除数縮小付き遷移 |
| [OddNonsquare.lean](../PseudoPrime/NumberTheory/OddNonsquare.lean) | 奇数かつ非平方数の許容入力と有限集合 |
| [Factorization.lean](../PseudoPrime/NumberTheory/Factorization.lean) | 素因数分解から必要な素因数を取り出す補題 |
| [TwoAdic.lean](../PseudoPrime/NumberTheory/TwoAdic.lean) | 奇数部分の抽出と2進分解に伴うgcdの恒等式 |
| [Jacobi/Normalization.lean](../PseudoPrime/NumberTheory/Jacobi/Normalization.lean) | Jacobi記号の分子の符号・2冪と分母の2冪の分解 |
| [Jacobi/Symbol.lean](../PseudoPrime/NumberTheory/Jacobi/Symbol.lean) | 2進分解と累積符号による記号専用再帰、参照計算との一致 |
| [Jacobi/Gcd.lean](../PseudoPrime/NumberTheory/Jacobi/Gcd.lean) | 記号・gcd共有状態、不変条件、燃料による停止保証 |
| [Jacobi/Fast.lean](../PseudoPrime/NumberTheory/Jacobi/Fast.lean) | 全自然数分母の記号専用入口・gcd共有入口と正当性 |
| [Kronecker/Basic.lean](../PseudoPrime/NumberTheory/Kronecker/Basic.lean) | 全整数入力のKronecker記号の数学的仕様 |
| [Kronecker/Compatibility.lean](../PseudoPrime/NumberTheory/Kronecker/Compatibility.lean)・[Kronecker/Properties.lean](../PseudoPrime/NumberTheory/Kronecker/Properties.lean) | Jacobi記号との対応と記号の零判定 |
| [Kronecker/Computation.lean](../PseudoPrime/NumberTheory/Kronecker/Computation.lean) | 全整数入力の記号・gcd同時計算と正当性 |
| [Kronecker/Fast.lean](../PseudoPrime/NumberTheory/Kronecker/Fast.lean) | 全整数入力の記号専用計算と正当性 |
| [Jacobi/Basic.lean](../PseudoPrime/NumberTheory/Jacobi/Basic.lean) | Jacobi 記号の基本的な算術 |
| [Jacobi/Prime.lean](../PseudoPrime/NumberTheory/Jacobi/Prime.lean) | 素数を法とする Jacobi 記号の性質 |
| [Jacobi/Numerator.lean](../PseudoPrime/NumberTheory/Jacobi/Numerator.lean) | 指定した Jacobi 値を持つ分子の構成 |
| [JacobiWitness/Basic.lean](../PseudoPrime/NumberTheory/JacobiWitness/Basic.lean) | 証人集合、最小元、所属・最小性・比較 |
| [JacobiWitness/Smaller.lean](../PseudoPrime/NumberTheory/JacobiWitness/Smaller.lean) | 入力より小さい Jacobi $-1$ 証人の構成 |
| [JacobiWitness/Existence.lean](../PseudoPrime/NumberTheory/JacobiWitness/Existence.lean) | 奇数かつ非平方数についての証人集合の非空性 |
| [JacobiCharacter.lean](../PseudoPrime/NumberTheory/JacobiCharacter.lean)・[PrimitiveJacobiCharacter.lean](../PseudoPrime/NumberTheory/PrimitiveJacobiCharacter.lean) | 法 $4n$ の Jacobi 指標と原始化 |
| [JacobiCharacterArithmetic.lean](../PseudoPrime/NumberTheory/JacobiCharacterArithmetic.lean) | 平方自由部分・基本判別式・導手を同定する `JacobiCharacterArithmeticData` |
| [JacobiCharacterCutoff.lean](../PseudoPrime/NumberTheory/JacobiCharacterCutoff.lean) | 無証人仮定から素数冪 cutoff 内の指標値 $1$ を導く |
| [JacobiCongruence.lean](../PseudoPrime/NumberTheory/JacobiCongruence.lean)・[DirichletCharacter.lean](../PseudoPrime/NumberTheory/DirichletCharacter.lean) | Jacobi 合同式と一般指標の法変更 |
| [PrimeIndexing.lean](../PseudoPrime/NumberTheory/PrimeIndexing.lean)・[PrimeTable.lean](../PseudoPrime/NumberTheory/PrimeTable.lean)・[PrimorialCertificates.lean](../PseudoPrime/NumberTheory/PrimorialCertificates.lean) | 素数列、最初の 163 素数の表、累積 primorial の有限証明書 |

数学的な記号・証人の宣言は`PseudoPrime.NumberTheory`に置く。参照用のJacobi計算は`PseudoPrime.NumberTheory.Jacobi`、記号とgcdの共有状態・遷移は`PseudoPrime.NumberTheory.Jacobi.Gcd`、記号に依存しない2進分解の補題は`PseudoPrime.NumberTheory.TwoAdic`に属する。`kroneckerSym`の仕様・性質と、`kroneckerGcd`の実行・正当性は別のモジュールに分けている。`jacobiSymFast` と `kroneckerSymFast` はgcdを計算しない記号専用の入口であり、記号とgcdの同時計算には `jacobiGcdFast` と `kroneckerGcd` を使う。

高速計算と停止上界の理論は [Fibonacci最大添字と互除法の燃料](FibonacciEuclid.md) にまとめている。Jacobi計算への接続も同ページで説明する。

## 二種類の証人

入力を $n$ とすると、 `primeNeOneWitnessSet n` は `jacobiSym n p ≠ 1` を満たす奇素数 $p$ の集合、 `primeNegOneWitnessSet n` は値が $-1$ になる奇素数の集合である。分子は $n$、分母は $p$ であり、Selfridge 探索の `jacobiSym D n` とは引数の向きが異なる。

Jacobi 記号が $1$ でないという条件は値 $0$ も許すため、 $p \mid n$ による因子検出も含む。 Jacobi 記号が $-1$ という条件は平方非剰余だけを要求する。最小元 `primeNeOneWitness` と `primeNegOneWitness` は非空性の証明を引数に取り、 `Nat.find` による `noncomputable` な数学的定義である。有限 `fuel` 付きの実行用探索ではない。

主な比較定理は `primeNeOneWitness_le_primeNegOneWitness` である。存在証明には `primeNegOneWitnessSet_nonempty_of_odd_nonsquare`、より小さい証人の構成には `exists_smaller_prime_jacobiSym_eq_neg_one_of_odd_nonsquare` と `exists_smaller_prime_jacobiSym_eq_neg_one_of_prime` を参照する。これらの算術的な存在証明に GRH は必要ない。

## 主要な主張と成果

| 定理 | 前提と結論 |
|---|---|
| `primeNegOneWitnessSet_nonempty_of_odd_nonsquare` | 奇数かつ非平方数 $n$ に Jacobi 値が $-1$ の奇素数証人が存在 |
| `exists_smaller_prime_jacobiSym_eq_neg_one_of_odd_nonsquare` | 奇数かつ非平方数 $n > 3$ なら、その証人を $p < n$ に取れる |
| `exists_smaller_prime_jacobiSym_eq_neg_one_of_prime` | 素数 $n > 3$ なら、別途奇数を仮定せず $p < n$ の証人を得る |
| `primeNeOneWitness_le_primeNegOneWitness` | 非空性のもとでJacobi 記号が $1$ でない最小証人は、記号が $-1$ となる最小証人以下 |

存在証明には合同式、素因数分解、二次相互法則を用いる。$n > 3$ を仮定する小証人定理と、小さい入力も含む非空性定理は別の結果である。

法 $4n$ の `complexQuadraticCharacter` と、その原始指標を構成する。奇数かつ非平方数では原始指標は非自明で、二次性・偶性を持つことを証明している。 [JacobiCharacterPrimeEvaluation.lean](../PseudoPrime/NumberTheory/JacobiCharacterPrimeEvaluation.lean) の `primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one` は、素数 $p \nmid 4n$ で指標値が $1$ でないことから、Jacobi 値が $-1$ の奇素数証人を取り出す。 $p \nmid 4n$ が素数 $2$ と Jacobi 値 $0$ を排除するため、[LLS](LLS.md) の一般 S1 の結論をそのまま利用できる。

## 利用方法と下流

一括入口は [NumberTheory.lean](../PseudoPrime/NumberTheory.lean)。必要な下位モジュールだけを直接 import することもできる。

```lean
import PseudoPrime.NumberTheory.JacobiWitness.Existence

#check PseudoPrime.NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
#check PseudoPrime.NumberTheory.primeNeOneWitness_le_primeNegOneWitness
```

[PrimeTest](PrimeTest.md) は証人を Selfridge 候補へ移送して探索成功を示す。[PseudoSquare](PseudoSquare.md) は最小証人の有限最大と解析的上界を構成し、[SelfridgeBoundGrh](SelfridgeBoundGrh.md) がそれを Selfridge 停止値へ接続する。

[構成全体へ](README.md)

燃料計算を省く同時計算には `kroneckerGcdFast` と `jacobiGcdFuelFreeFast` を使う。分子が各回で真に減少することから停止を証明し、零の記号になった後もgcdを求める計算を続ける。既存の `kroneckerGcd` と `jacobiGcdFast` はFibonacci燃料を使う実装として残している。両方式が全入力で同じ値を返すことも証明済みである。
