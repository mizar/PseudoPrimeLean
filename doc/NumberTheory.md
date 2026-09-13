# NumberTheory — 共通の数論基盤

対象: [`PseudoPrime/NumberTheory`](../PseudoPrime/NumberTheory)。名前空間は `PseudoPrime.NumberTheory`。

この領域は、奇非平方数、素因数分解、Jacobi記号、最小の奇素数目撃者を扱う。実行用の素数判定やGRHによる解析的上界に共通する算術を供給する。領域内のプロジェクト依存は NumberTheory 内に収まり、PrimeTest や PseudoSquare をimportしない。

## 構成

| モジュール | 内容 |
|---|---|
| [OddNonsquare.lean](../PseudoPrime/NumberTheory/OddNonsquare.lean) | 奇非平方数の許容入力と有限集合 |
| [Factorization.lean](../PseudoPrime/NumberTheory/Factorization.lean) | 素因数分解から必要な素因数を取り出す補題 |
| [Jacobi/Basic.lean](../PseudoPrime/NumberTheory/Jacobi/Basic.lean) | Jacobi記号の基本的な算術 |
| [Jacobi/Prime.lean](../PseudoPrime/NumberTheory/Jacobi/Prime.lean) | 素数を法とするJacobi記号の性質 |
| [Jacobi/Numerator.lean](../PseudoPrime/NumberTheory/Jacobi/Numerator.lean) | 指定したJacobi値を持つ分子の構成 |
| [JacobiWitness/Basic.lean](../PseudoPrime/NumberTheory/JacobiWitness/Basic.lean) | 目撃者集合、最小元、所属・最小性・比較 |
| [JacobiWitness/Smaller.lean](../PseudoPrime/NumberTheory/JacobiWitness/Smaller.lean) | 入力より小さいJacobi `-1` 目撃者の構成 |
| [JacobiWitness/Existence.lean](../PseudoPrime/NumberTheory/JacobiWitness/Existence.lean) | 奇非平方数についての目撃者集合の非空性 |
| [JacobiCharacter.lean](../PseudoPrime/NumberTheory/JacobiCharacter.lean)・[PrimitiveJacobiCharacter.lean](../PseudoPrime/NumberTheory/PrimitiveJacobiCharacter.lean) | 法4nのJacobi指標と原始化 |
| [JacobiCharacterArithmetic.lean](../PseudoPrime/NumberTheory/JacobiCharacterArithmetic.lean) | 平方自由部分・基本判別式・導手を同定するJacobiCharacterArithmeticData |
| [JacobiCharacterCutoff.lean](../PseudoPrime/NumberTheory/JacobiCharacterCutoff.lean) | 無目撃者仮定から素数冪cutoff内の指標値1を導く |
| [JacobiCongruence.lean](../PseudoPrime/NumberTheory/JacobiCongruence.lean)・[DirichletCharacter.lean](../PseudoPrime/NumberTheory/DirichletCharacter.lean) | Jacobi合同式と一般指標の法変更 |
| [PrimeIndexing.lean](../PseudoPrime/NumberTheory/PrimeIndexing.lean)・[PrimeTable.lean](../PseudoPrime/NumberTheory/PrimeTable.lean)・[PrimorialCertificates.lean](../PseudoPrime/NumberTheory/PrimorialCertificates.lean) | 素数列、最初の163素数の表、累積primorialの有限証明書 |

## 二種類の目撃者

入力を `n` とすると、`PrimeNeOneWitnessSet n` は `jacobiSym n p ≠ 1` を満たす奇素数 `p` の集合、`PrimeNegOneWitnessSet n` は値が `-1` になる奇素数の集合である。分子は `n`、分母は `p` であり、Selfridge探索の `jacobiSym D n` とは引数の向きが異なる。

`≠ 1` は値 `0` も許すため、`p ∣ n` による因子検出も含む。`-1` は非剰余だけを要求する。最小元 `primeNeOneWitness` と `primeNegOneWitness` は非空性の証明を引数に取り、`Nat.find` による `noncomputable` な数学的定義である。有限fuel付きの実行用探索ではない。

主要な比較は `primeNeOneWitness_le_primeNegOneWitness`。存在証明は `primeNegOneWitnessSet_nonempty_of_odd_nonsquare`、小さい目撃者の構成は `oddNonsquareHasSmallerNegOneWitness` と `primeHasSmallerNegOneWitness` を参照する。これらの算術的存在証明にGRHは必要ない。

## 主要な主張と成果

| 定理 | 前提と結論 |
|---|---|
| `primeNegOneWitnessSet_nonempty_of_odd_nonsquare` | 奇非平方数 `n` にJacobi値−1の奇素数目撃者が存在 |
| `oddNonsquareHasSmallerNegOneWitness` | 奇非平方数 `n > 3` なら、その目撃者を `p < n` に取れる |
| `primeHasSmallerNegOneWitness` | 素数 `n > 3` なら、別途奇数を仮定せず `p < n` の目撃者を得る |
| `primeNeOneWitness_le_primeNegOneWitness` | 非空性のもとで最小の `≠1` 目撃者は最小の `=-1` 目撃者以下 |

存在証明には合同式・素因数分解・二次相互法則を用いる。`n > 3` の制約を持つ小目撃者定理と、
小さい入力も含む非空性定理を区別する。

法 `4n` の `complexQuadraticCharacter` と、その原始指標を構成する。
奇非平方数では原始指標は非自明で、二次性・偶性を持つことを証明している。
[JacobiCharacterPrimeEvaluation.lean](../PseudoPrime/NumberTheory/JacobiCharacterPrimeEvaluation.lean)
の `primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one` は、素数 `p ∤ 4n` で
指標値が1でないことから、Jacobi値−1の奇素数目撃者を取り出す。
`p ∤ 4n` が素数2とJacobi値0を排除するため、[LLS](LLS.md)の一般S1の結論をそのまま利用できる。

## 利用方法と下流

一括入口は [NumberTheory.lean](../PseudoPrime/NumberTheory.lean)。必要な下位モジュールだけを直接importすることもできる。

```lean
import PseudoPrime.NumberTheory.JacobiWitness.Existence

#check PseudoPrime.NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
#check PseudoPrime.NumberTheory.primeNeOneWitness_le_primeNegOneWitness
```

[PrimeTest](PrimeTest.md) は目撃者をSelfridge候補へ移送して探索成功を示す。[PseudoSquare](PseudoSquare.md) は最小目撃者の有限最大と解析的上界を構成し、[SelfridgeBoundGrh](SelfridgeBoundGrh.md) がそれをSelfridge停止値へ接続する。

[構成全体へ](README.md)
