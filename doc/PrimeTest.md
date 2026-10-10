# PrimeTest — 実行可能な素数性テストと仕様

対象: [`PseudoPrime/PrimeTest`](../PseudoPrime/PrimeTest)。公開入口は [`PseudoPrime/PrimeTest.lean`](../PseudoPrime/PrimeTest.lean)、名前空間は `PseudoPrime.PrimeTest`。

この領域では、Boolean 値を返す素数性テストとその数学的仕様、素数を受理する証明、Selfridge パラメータ探索を実装する。

## 構成

実行用コードでは通常版に `bailliePSWWheel30`、強化版に `strengthenedBPSWWheel30`を使う。証明付き判定には `BPSW.decideWheel30 n false`または `BPSW.decideWheel30 n true`、段階実行には `Execution.runBPSWWheel30`を使う。平方数ではMRを先に実行する分の費用がかかる。Euler省略入口は任意の最適化である。

| モジュール・ディレクトリ | 内容 |
|---|---|
| [Basic.lean](../PseudoPrime/PrimeTest/Basic.lean) | `PrimalityTest` と `PrimalityTestSpec` |
| [Precheck.lean](../PseudoPrime/PrimeTest/Precheck.lean) | 小さい入力・偶数・平方数の事前判定 |
| [JacobiFuel.lean](../PseudoPrime/PrimeTest/JacobiFuel.lean) | 2進付値による一括除去、Fibonacci燃料、正規化した整数入力のJacobi計算 |
| [EulerJacobi](../PseudoPrime/PrimeTest/EulerJacobi) | 自然数底・整数底の Euler–Jacobi 合同式 |
| [MillerRabin](../PseudoPrime/PrimeTest/MillerRabin) | Strong Miller–Rabin、底 2、素数完全性 |
| [Lucas](../PseudoPrime/PrimeTest/Lucas) | パラメータ、整数列、ZMod 上の列、高速評価、有限体による証明 |
| [StrongLucas](../PseudoPrime/PrimeTest/StrongLucas) | Strong Lucas の有限選言と実行結果の対応 |
| [LucasV](../PseudoPrime/PrimeTest/LucasV) | Jacobi $-1$ 枝の $V_{n+1} = 2Q$ 判定 |
| [Selfridge](../PseudoPrime/PrimeTest/Selfridge) | 候補、数学的停止値、昇順探索、Method A / `A*`、探索上界 |
| [Selfridge/MethodALists.lean](../PseudoPrime/PrimeTest/Selfridge/MethodALists.lean) | 因子検出付き古典探索とWheel30のDの一致、Method A/A*の通常Lucas判定とlpsp集合の一致 |
| [BPSW](../PseudoPrime/PrimeTest/BPSW) | 通常版・強化版の組合せとトップレベル仕様 |
| [BPSW/EulerModEight.lean](../PseudoPrime/PrimeTest/BPSW/EulerModEight.lean) | n mod 8 = 5のMR受理段階と符号付き2冪のEuler条件 |
| [BPSW/EulerBaseTwo.lean](../PseudoPrime/PrimeTest/BPSW/EulerBaseTwo.lean) | 奇数のn > 1での底2 Strong MRからEuler条件への帰結と符号付き2冪全体への拡張 |
| [BPSW/ConditionalEuler.lean](../PseudoPrime/PrimeTest/BPSW/ConditionalEuler.lean) | 底2 MR後の条件付きEuler省略と従来版との全入力一致 |
| [Regression.lean](../PseudoPrime/PrimeTest/Regression.lean) | 擬素数、大整数、平方数などの実行回帰 |

Jacobiの一括除去と燃料の数え方、停止と正当性の証明は [FibonacciとJacobiの燃料上界](FibonacciEuclid.md#jacobi記号の燃料上界) を参照する。燃料枯渇は `none` として返し、Jacobi値0と区別する。

### 因子検出付き探索とMethod A/A*の一致

奇数の非平方数では、全候補を調べる因子検出付き探索とWheel30探索の最初の停止値が一致する。`firstStopD_wheel30_eq_classical`で、その停止値から定める符号付きDの一致まで接続した。Jacobi値0による因子停止も含む。

`Selfridge/MethodALists.lean`で、奇数入力と選択したDのJacobi値−1を前提に、Method AとA*の通常Lucas判定が一致することを証明した。D=5では $U_{2m}(5,5)=5^m U_{2m}(1,-1)$ を使い、法nで5が単元であることから零条件が一致する。それ以外のDではパラメータ自体が同じである。非素数条件を保ったlpspの同値と、任意の適格なD選択関数に対するlpsp集合の一致まで証明している。Strong Lucasの一致は既存の `MethodAStarEquivalence.lean`で証明済みである。

原論文第6節の5段階仕様と強化Wheel30の全入力一致は、`BFWSpec.lean`の `strengthenedBPSWWheel30_eq_bfw`で証明済みである。純粋−1探索との互換性は本計画の対象に含めない。

## 証明付き判定・証明書・解析的上界

`Result.lean` の `Decision` は、素数・非素数の証明と `unknown` を区別する。[Execution.lean](../PseudoPrime/PrimeTest/Execution.lean) は方式ごとの判定を接続する。APR-CL の局所数論核が未証明の証明書は `pending` のまま保持する。底2・3による有限範囲の確定は [MillerRabin/Finite.lean](../PseudoPrime/PrimeTest/MillerRabin/Finite.lean) にあり、保証範囲は3000未満である。一般の Miller–Rabin・Lucas・BPSW は、テストを通過しただけでは素数と確定しない。

BLS の入口は責務別に分かれる。

| 入口 | 役割 |
|---|---|
| [Certificate.lean](../PseudoPrime/PrimeTest/BLS/Certificate.lean) | square・cube・BLS5 の外部証明書検証と健全性 |
| [CertificateJson.lean](../PseudoPrime/PrimeTest/BLS/CertificateJson.lean) | JSON 復号・符号化・検証（生成器に非依存） |
| [Search.lean](../PseudoPrime/PrimeTest/BLS/Search.lean) | 予算付き探索、証人生成、素数・合成数の結果 |
| [CertificateGenerate.lean](../PseudoPrime/PrimeTest/BLS/CertificateGenerate.lean) | 検証済み外部証明書の生成 |
| [CertificateGenerateJson.lean](../PseudoPrime/PrimeTest/BLS/CertificateGenerateJson.lean) | JSON 生成 |

因数分解器は `NumberTheory.Factorization`、葉の素数確認方針との接続は `FactorizationPolicy` にある。 `PrimeTest` の import 閉包にはプロジェクト固有の解析・GRH 層を含めない。解析的上界の総合入口は [PrimeTestBounds.lean](../PseudoPrime/PrimeTestBounds.lean)。 Selfridge の無条件の評価と GRH 付き評価は [上界ガイド](SelfridgeBoundGrh.md) を参照する。

JSON の自然数は共通の `CertificateJson.readNat` で十進文字列から復号する。 CLI の `Tools.CertificateIO.readFileBounded` は上限超過を復号前に拒否する。入力バイト制限は、数学的検証の時間・総メモリ上限を保証するものではない。

## 実行順序

推奨するWheel30入口は、小入力と偶数を処理した後、底2 MR、平方判定、因子検出付きSelfridge探索、Lucas判定の順で実行する。強化版はStrong・最終V・Eulerの条件を共有状態から検査する。

共通の事前判定を使う `bailliePSWWheel30WithPrecheck`と `strengthenedBPSWWheel30WithPrecheck`も用意する。`primalityPrecheck`で小入力・偶数・平方数を先に処理し、残った入力にMR、Selfridge探索、Lucas判定を実行する。元のWheel30入口と全入力で結果が一致し、`BPSW.decideWheel30WithPrecheck`と `Execution.runBPSWWheel30WithPrecheck`も同じ証明付き結果を返す。

以下はSelfridge探索の境界処理で使う通常版の純粋−1探索入口の処理順である。

`bailliePSW` と `strengthenedBPSW` は、共通の `primalityPrecheck` を呼ぶ。$n < 2$ は false、2 は true、その他の偶数と平方数は false になる。平方数は `Nat.sqrt n ^ 2 == n` で判定し、Selfridge 探索より前に除外する。

それ以外の入力では `selfridgeClassicalMethodAStarParamsWithinTwoMul` が候補を昇順に調べる。探索に成功すると、底2 Strong Miller–Rabin と Strong Lucas を評価する。強化版ではさらに Lucas-V と整数底 $Q$ の Euler–Jacobi を評価する。現在の探索は Jacobi 値が $-1$ となる候補を探す。Jacobi 値 $0$ による因子検出で早期停止する処理や、Miller–Rabin を先に実行する制御フローは実装していない。

探索 `fuel` は `n - 2`。内部の探索は `Option` で成功・失敗を区別し、トップレベルでは探索失敗を false にする。Wheel30・素数候補のみを用いる `bailliePSWWheel30Ascending`、 `bailliePSWPrimeAscending` は明示的な `fuel` を受け取り、 `Option Bool` を返す。

## Selfridge と証明の範囲

Method A は $P = 1,\quad Q = (1 - D)/4$。 `Method A*` は $D = 5$ の場合に $P = Q = 5$ を用い、それ以外は Method A と一致する。

[MethodAStarEquivalence.lean](../PseudoPrime/PrimeTest/Selfridge/MethodAStarEquivalence.lean) の `strongLucasMethodAStar_eq_methodA` は、同じ $D$、奇数 $n$、 $1 - D \equiv 0 \pmod 4$、 `jacobiSym D n = -1` のもとで Strong Lucas の結果一致を示す。合成数にも適用でき、 $D = 5$ も含む。強化版の Lucas-V／Euler–Jacobi までを Method A へ置換する同値ではない。

`firstStopNegOne` と `firstStopNeOne` は数学的な最小停止候補で、実行用探索と区別する。後者は $n \nmid i$ と Jacobi 値が $1$ と異なることを要求して因子検出も扱う。

## Miller–Rabin の素数判定同値と素数底証人

公開定理 `prime_iff_millerRabin_for_all_primes_le_log_sq` は、奇数 $n > 1$ について、GRH の下で「上界内の全素数底が合格」と素数性が同値であることを示す。

GRH の下で、任意の奇合成数 $n > 1$ に対して $p \le (\ln\mathrel{} n)^2$ を満たし、標準分解に対する強 Miller–Rabin の不合格条件を満たす素数底 $p$ が存在する。この冪不等式は `not_strongMillerRabinPass_iff` により強 Miller–Rabin 合格条件の否定と同値であり、さらに `strongMillerRabinWithBase_eq_false_iff_not_pass` により `strongMillerRabinWithBase n p = false` と同値である。詳しい主張と利用例は [MillerRabinBoundGrh](MillerRabinBoundGrh.md) を参照する。この上界の入口は `PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS` である。

無条件の基盤は [MillerRabin/Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) の真部分群存在定理と、 [MillerRabin/Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) の $1 < n < 3000$ における底 2 または底 3 の不合格定理である。分解 $n - 1 = 2^s d$（ $s, d \in \mathbb{N}$、 $d$ は奇数）と実行用判定の接続は [Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) にある。

## Strong Lucasの定義用と実行用

`strongLucasWithParams`は定義用の有限添字判定として保持する。実行用には [StrongLucas/Fast.lean](../PseudoPrime/PrimeTest/StrongLucas/Fast.lean) の `strongLucasWithPQ`と `strongLucasWithParamsFast`を使う。コンパイラ用の自動書き換えは使わず、呼び出し先を明示する。

`strongLucasWithPQ n P Q`はC++・Pythonの `isprime_lucas_strong_pq`に対応する。奇数の $n \ge 3$ と、判別式 $D=P^2-4Q$ のJacobi値 $(D/n)=-1$ を想定し、これらの条件は呼び出し元が確認する。関数内部では $n+1=2^s d$ と分解し、初期の $U_d,V_d,Q^d$ を一度だけ計算する。初期Uが0なら受理し、それ以外は $r < s$ のVを検査してから次の添字へ倍加する。一致すれば直ちに受理し、最後の検査が失敗した後の倍加は行わない。

通常版ではQのEuler条件を検査しないが、Vの倍加式 $V_{2k}=V_k^2-2Q^k$ にQの冪が必要となる。そのため、初期Uの検査後はVとQの冪だけを更新する。Uの更新や各添字からの漸化式の再計算は行わない。

`strongLucasWithParamsFast`は対応する奇数・Jacobi値 $-1$ の入力でPQ実行コアを使い、他の入力では初期U・Vの計算を共有した汎用の倍加ループを使う。定義用APIとの全入力一致を証明済みである。`StrongLucas.decideWithParams`、通常Wheel30、有限探索の通常Decisionは、この実行用APIを明示的に呼ぶ。パラメータ指定の通常BPSWには [BPSW/Fast.lean](../PseudoPrime/PrimeTest/BPSW/Fast.lean) の `bailliePSWWithParamsFast`を用意し、定義用との全入力一致と素数受理を証明した。

## 保証と利用例

`PrimalityTestSpec.prime_true` は「素数なら true」という完全性を表す。 `bailliePSW_spec_unconditional` と `strengthenedBPSW_spec_unconditional` は探索成功も含めてこの仕様を証明し、GRH を仮定しない。逆の「true なら素数」はこの仕様に含まれない。

仕様には、$0$ と $1$ の棄却、2 の受理、2 以外の偶数の棄却も含まれる。`bailliePSW_of_prime_of_search` などの探索成功を仮定する段階を、`bailliePSW_spec_unconditional` が無条件のトップレベル保証へつなぐ。そのため、GRH による上界を実行時の停止保証に組み込む必要はない。

Euler–Jacobi や明示パラメータを使う Strong Lucas は、前処理を伴わない合同式の検査である。共通の precheck は自動適用しない。パラメータ付き素数完全性定理には判別式や Jacobi 記号の条件がある。

```lean
import PseudoPrime.PrimeTest

#eval PseudoPrime.PrimeTest.bailliePSW 7
#eval PseudoPrime.PrimeTest.strengthenedBPSW 2047
#check PseudoPrime.PrimeTest.bailliePSW_spec_unconditional
#check PseudoPrime.PrimeTest.strongLucasMethodAStar_eq_methodA
```

依存は主に [NumberTheory](NumberTheory.md) と mathlib である。ただし `Selfridge/Finite.lean` は `PseudoSquare/Computation/SmallN.lean` の有限証明書を import するため、PseudoSquare と完全に独立した import 構成ではない。

回帰テストは公開入口とは別に、Lean プロジェクト直下で `lake build PseudoPrime/PrimeTest/Regression.lean` を実行する。回帰テストで `native_decide` が行う検査は、公開定理の数学的証明とは区別する。

## C++・Python の参考実装

[examples/bpsw](../examples/bpsw) に通常版・強化版 BPSW の C++・Python 実装を配置している。 [実行方法と Lean との対応](BPSWImplementations.md) を参照する。これらは MR 先行・Wheel30・因子検出付き探索を用いるため、上記の Lean トップレベルと制御フローが一致するコードではない。Lean から抽出したプログラムではなく、言語間のプログラム同値性を証明したものでもない。

[構成全体へ](README.md)
