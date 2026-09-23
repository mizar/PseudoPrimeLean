# PrimeTest — 実行可能な素数性テストと仕様

対象: [`PseudoPrime/PrimeTest`](../PseudoPrime/PrimeTest)。公開入口は [`PseudoPrime/PrimeTest.lean`](../PseudoPrime/PrimeTest.lean)、名前空間は `PseudoPrime.PrimeTest`。

この領域はBoolean値を返す素数性テスト、その数学的仕様、素数を受理する証明、Selfridgeパラメータ探索を実装する。

## 構成

| モジュール・ディレクトリ | 内容 |
|---|---|
| [Basic.lean](../PseudoPrime/PrimeTest/Basic.lean) | `PrimalityTest` と `PrimalityTestSpec` |
| [Precheck.lean](../PseudoPrime/PrimeTest/Precheck.lean) | 小さい入力・偶数・平方数の事前判定 |
| [EulerJacobi](../PseudoPrime/PrimeTest/EulerJacobi) | 自然数底・整数底のEuler–Jacobi合同式 |
| [MillerRabin](../PseudoPrime/PrimeTest/MillerRabin) | Strong Miller–Rabin、底2、素数完全性 |
| [Lucas](../PseudoPrime/PrimeTest/Lucas) | パラメータ、整数列、ZMod上の列、高速評価、有限体による証明 |
| [StrongLucas](../PseudoPrime/PrimeTest/StrongLucas) | Strong Lucasの有限選言と実行結果の対応 |
| [LucasV](../PseudoPrime/PrimeTest/LucasV) | Jacobi `-1` 枝の `V_(n+1) = 2Q` 判定 |
| [Selfridge](../PseudoPrime/PrimeTest/Selfridge) | 候補、数学的停止値、昇順探索、Method A/A*、探索上界 |
| [BPSW](../PseudoPrime/PrimeTest/BPSW) | 通常版・強化版の組合せとトップレベル仕様 |
| [Regression.lean](../PseudoPrime/PrimeTest/Regression.lean) | 擬素数、大整数、平方数などの実行回帰 |

## 実行順序

`bailliePSW` と `strengthenedBPSW` は共通の `primalityPrecheck` を呼ぶ。`n < 2` はfalse、2はtrue、その他の偶数と平方数はfalseになる。平方数チェックは `Nat.sqrt n ^ 2 == n` であり、Selfridge探索より前に実行する。

残る入力では `selfridgeClassicalMethodAStarParamsWithinTwoMul` により昇順探索し、成功後に底2 Strong Miller–RabinとStrong Lucasを評価する。強化版はさらにLucas-Vと、整数底 `Q` のEuler–Jacobiを評価する。現行探索は純粋なJacobi `-1` 探索で、Jacobi `0` による因子検出付き早期停止やMR先行の制御フローは実装していない。

探索fuelは `n - 2`。内部の探索は `Option` で成功・失敗を区別し、トップレベルでは探索失敗をfalseにする。Wheel30・素数候補のみを用いる `bailliePSWWheel30Ascending`、`bailliePSWPrimeAscending` は明示的fuelを受け取り、`Option Bool` を返す。

## Selfridgeと証明の範囲

Method Aは `P = 1, Q = (1-D)/4`。Method A*は `D = 5` の場合に `P = Q = 5` を用い、それ以外はMethod Aと一致する。

[MethodAStarEquivalence.lean](../PseudoPrime/PrimeTest/Selfridge/MethodAStarEquivalence.lean) の `strongLucasMethodAStar_eq_methodA` は、同じ `D`、奇数 `n`、`(1-D) % 4 = 0`、`jacobiSym D n = -1` のもとでStrong Lucasの結果一致を示す。合成数にも適用でき、D=5も含む。強化版のLucas-V／Euler–JacobiまでをMethod Aへ置換する同値ではない。

`firstStopNegOne` と `firstStopNeOne` は数学的な最小停止候補で、実行用探索と区別する。後者は `¬ n ∣ i` とJacobi値 `≠ 1` を要求して因子検出も扱う。

## Miller–Rabinの素数底証人

GRHの下で、任意の奇合成数 $n>1$ に対して $p\le(\log n)^2$ を満たす素数底が存在し、
`strongMillerRabinWithBase n p = false` となることも証明されている。
詳しい主張と利用例は [MillerRabinBoundGrh](MillerRabinBoundGrh.md) を参照する。
この上界の入口は `PseudoPrime.MillerRabinBoundGrh.FromLLS` である。

無条件の基盤は [MillerRabin/Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean)
の真部分群存在定理と、
[MillerRabin/Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean)
の $1<n<3000$ における底2または3の不合格定理である。
分解 $n-1=2^s d$（ $s,d\in\mathbb N$、 $d$ は奇数）と実行用判定の接続は
[Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) にある。

## 保証と利用例

`PrimalityTestSpec.prime_true` は「素数ならtrue」という完全性を表す。`bailliePSW_spec_unconditional` と `strengthenedBPSW_spec_unconditional` は探索成功も含めてこの仕様を証明し、GRHを仮定しない。逆の「trueなら素数」はこの仕様に含まれない。

仕様には0・1の棄却、2の受理、2以外の偶数の棄却も含まれる。
`bailliePSW_of_prime_of_search` などの探索成功を仮定した段階と、
`bailliePSW_spec_unconditional` の無条件のトップレベル保証が接続されている。
したがって、GRH上界を実行時の停止保証に組み込む必要はない。

Euler–Jacobiや明示パラメータのStrong Lucasはrawな合同式チェックで、共通precheckを自動適用しない。パラメータ付き素数完全性定理には判別式条件やJacobi条件がある。

```lean
import PseudoPrime.PrimeTest

#eval PseudoPrime.PrimeTest.bailliePSW 7
#eval PseudoPrime.PrimeTest.strengthenedBPSW 2047
#check PseudoPrime.PrimeTest.bailliePSW_spec_unconditional
#check PseudoPrime.PrimeTest.strongLucasMethodAStar_eq_methodA
```

依存は主に [NumberTheory](NumberTheory.md) とmathlibである。ただし `Selfridge/Finite.lean` は `PseudoSquare/Computation/SmallN.lean` の有限証明書をimportするため、PseudoSquareと完全に独立したimport構成ではない。

回帰テストは公開入口とは別に、Leanプロジェクト直下で `lake build PseudoPrime/PrimeTest/Regression.lean` を実行する。回帰の `native_decide` assertionは、公開定理の数学的証明とは区別する。

## C++・Pythonの参考実装

[examples/bpsw](../examples/bpsw) に通常版・強化版BPSWのC++・Python実装を配置している。
[実行方法とLeanとの対応](BPSWImplementations.md)を参照する。
これらはMR先行・Wheel30・因子検出付き探索を用いるため、上記のLeanトップレベルと
制御フローが一致するコードではない。Leanから抽出したプログラムではなく、言語間の
プログラム同値性を証明したものでもない。

[構成全体へ](README.md)
