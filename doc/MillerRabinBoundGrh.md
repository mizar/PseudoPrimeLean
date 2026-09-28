# PrimeTestBounds.MillerRabin — GRH 下の素数底 Miller–Rabin 証人上界

公開入口は [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean)。
名前空間は `PseudoPrime.PrimeTestBounds.MillerRabin` で、`import PseudoPrime` からも利用できる。

## 証明した主張

奇数 $n>1$ に対して $n-1=2^s d$（ $d$ は奇数）と分解する。 $s$ は $n-1$ の 2 進付値、つまり $n-1$ を割り切る 2 の最大の指数である。 $d$ は $n-1$ から 2 の因子を可能な限り取り除いた奇数である。

$p\not\equiv 0\pmod{n}$ である底 $p$ について、Miller–Rabin テストの通過条件は次の通りである。

* $p^d\equiv 1\pmod n$ または $0\le j<s$ のいずれかで $p^{2^j d}\equiv -1\pmod n$ なら通過する。
* $p^d\not\equiv 1\pmod n$ かつ、すべての $0\le j<s$ で $p^{2^j d}\not\equiv -1\pmod n$ なら通過しない。

$n>1$ において $p\le(\log n)^2$ を満たす素数 $p\in\mathbb P$ は $0 < p < n$ であり、 $p\not\equiv 0\pmod{n}$ を満たす。

GRH の下では、 $p\le(\log n)^2$ を満たすすべての素数底 $p\in\mathbb P$ が Miller–Rabin テストに通過すれば、 $n$ は素数である。一方、 Miller–Rabin テストを通過しない $p\le(\log n)^2$ の素数底 $p\in\mathbb P$ が存在すれば、$n$ は合成数である。

ここで $\mathbb P$ は素数全体の集合、 $\log$ は自然対数である。以上を同値式で表すと次のようになる。

$$
\begin{gathered}
\left(
\begin{aligned}
  &\forall p\in\mathbb P,\quad p\le(\log n)^2\Longrightarrow\\
  &\qquad\Bigl[\bigl(p^d\equiv1\pmod n\bigr)\\
  &\qquad\quad\lor\
    \bigl(\exists j\in\mathbb N,\ j<s\ \land\
      p^{2^j d}\equiv-1\pmod n\bigr)\Bigr]
\end{aligned}
\right)\\
\Longleftrightarrow\quad n\in\mathbb P.
\end{gathered}
$$

Lean では、 $n-1$ の 2 進付値 $s$ と奇数部分 $d$ をそれぞれ `padicValNat 2 (n - 1)` と `Nat.divMaxPow (n - 1) 2` として定義し、合同式を `ZMod n` の等式・不等式として表す。 GRH は [既存の定義](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) `PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis` を仮定する。 GRH 自体を証明したという主張ではない。

`prime_iff_millerRabin_for_all_primes_le_log_sq` の宣言部は次のとおり（証明本体は省略）。

```lean
namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    (∀ p : ℕ, Nat.Prime p →
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 →
      ((p : ZMod n) ^ d = 1 ∨
        ∃ j : ℕ, j < s ∧
          (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by

end PseudoPrime.PrimeTestBounds.MillerRabin
```

## 公開定理

以下の名前は `PseudoPrime.PrimeTestBounds.MillerRabin` 名前空間に属する。

| 宣言 | 内容 | ソース |
|---|---|---|
| `exists_prime_millerRabin_witness_le_log_sq` | 奇合成数に対する素数底の証人定理 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `prime_iff_millerRabin_for_all_primes_le_log_sq` | GRH の下で、上界内の全素数底の明示的な冪条件と素数性の同値 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq` | 標準分解の冪不等式を明示する証人系 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq_of_s2` | S2を仮定した $n\ge3000$ の接続定理 | [FromLLS.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq_of_lt_3000` | GRHを仮定しない $1 < n < 3000$ の定理 | [SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean) |

## 証明の流れ

### 1. 合格条件、単元性、素因数底

`PseudoPrime.PrimeTest.StrongMillerRabinPass n x` は、標準分解の奇数部分 $d$ と指数 $s$ を用いて
$x^d=1$ または、ある $j < s$ に対して $x^{2^j d}=-1$ という条件を定義する。
合格すれば $x^{n-1}=1$ となり、 $n>1$ のもとでは $x$ は単元となる。
したがって素因数 $p\mid n$ を底にすると不合格になる。

[Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) の
`strongMillerRabinPass_isUnit`、`strongMillerRabinPass_not_of_prime_dvd` がこの性質を示す。
同ファイルの `strongMillerRabinWithBase_eq_false_iff_not_pass` は、
この合格条件の否定を既存の Boolean 判定へ接続する。
素数入力側では、対数上界から底の互いに素性を示し、素数法の受理定理と
指定分解の接続を組み合わせて不合格条件と矛盾させる。
この節の宣言は `PseudoPrime.PrimeTest` 名前空間に属する。

### 2. 合格底を含む真部分群

同じ仮定のもとで、単元群 $(\mathbb Z/n\mathbb Z)^\times$ の真部分群 $H$ が存在し、
合格するすべての剰余が $H$ の像に入ることを無条件に証明する。
合格集合そのものを部分群と仮定する必要はない。

- 素数平方 $q^2\mid n$ がある場合は、 $u^{n-1}=1$ を満たす単元の部分群を使う。
  法 $q^2$ の $1+q$ を利用して、この部分群に属さない単元を構成する。
- 異なる素数 $q,r$ があり $qr\mid n$ の場合は、 $q-1=2^t c$（ $c$ は奇数）、
  $E=2^{t-1}d$ とおき、 $u^E\in\{1,-1\}$ を満たす単元の部分群を使う。
  法 $q$ と法 $r$ で異なる符号をとる冪をCRTで構成し、真部分群であることを示す。

各部分群の構成は
[WitnessSubgroup.lean](../PseudoPrime/PrimeTest/MillerRabin/WitnessSubgroup.lean)、
合成数の分岐と結合は [Composite.lean](../PseudoPrime/PrimeTest/MillerRabin/Composite.lean) にある。
公開定理 `PseudoPrime.PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass`
が、S2へ渡す真部分群と合格剰余の包含をまとめる。

### 3. 大きい範囲にS2を適用

$n\ge3000$ に対し、 $p < (\log n)^2$ を満たす素因数があれば、1の性質でその $p$ を証人にする。
そのような素因数がなければ、[LLSのS2](LLS.md)を2の真部分群へ適用する。
S2は $p\le(\log n)^2$ で剰余が $H$ の像に入らない素数を与えるため、
その底は合格できない。

前提の小素因数除外は狭義の $\lt$、証人の上界は $\le$ である。
等号端点で証人が単元になるという追加仮定は用いない。
これが `exists_prime_millerRabin_witness_le_log_sq_of_s2` の証明である。
最終段階で `PseudoPrime.LLS.llsTheorem11S2_of_grh` によりGRHからS2を供給する。

### 4. 小さい範囲の有限証明

[Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) は、
$1 < n < 3000$ の奇合成数について、底2または底3で不合格になることを示す。
底2での不合格を示す有限分類では2047を例外候補とし、2047の底3での不合格を別途証明する。
公開定理は `PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000`。

証明は奇数 $n=2k+1$、 $0\le k < 1500$ を128要素の11ブロックと92要素の最終ブロックで被覆する。
素数性と、明示分解・高速冪の不一致をLeanカーネルで検証し、checkerの健全性を通じて
既存のStrong Miller–Rabin判定へ移す。外部の整数探索結果を証明根拠には使わない。

奇合成数 $n>1$ なら $n\ge9$ なので $3\le(\log n)^2$ が成立する。
[SmallLogBound.lean](../PseudoPrime/PrimeTestBounds/MillerRabin/SmallLogBound.lean)
は対数評価を有限分類へ接続し、小範囲の素数証人定理を与える。
有限分類だけを使う場合は `PseudoPrime.PrimeTest.MillerRabin.Computation.Small`、
対数上界も使う場合は `PseudoPrime.PrimeTestBounds.MillerRabin.SmallLogBound` をimportする。

## 証明依存

主定理、証人系、有限分類、小範囲の上界、真部分群の中心定理、利用したS2定理の
推移的公理依存は `propext`、`Classical.choice`、`Quot.sound` のみである。
有限証明を含め、これらの定理に `sorry` や `native_decide` 由来の公理依存はない。
確認例は次のとおり。

```lean
import PseudoPrime

namespace PseudoPrime.PrimeTestBounds.MillerRabin

#print axioms exists_prime_millerRabin_witness_le_log_sq
#print axioms PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000

end PseudoPrime.PrimeTestBounds.MillerRabin
```

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
