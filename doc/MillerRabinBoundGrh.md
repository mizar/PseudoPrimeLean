# MillerRabinBoundGrh — GRH 下の素数底 Miller–Rabin 証人上界

公開入口は [FromLLS.lean](../PseudoPrime/MillerRabinBoundGrh/FromLLS.lean)。
名前空間は `PseudoPrime.MillerRabinBoundGrh` で、`import PseudoPrime` からも利用できる。

## 証明した主張

GRH の下で、任意の奇合成数 $n>1$ に対し、 $n-1=2^s d$
（ $s,d\in\mathbb N$、 $d$ は奇数）と一意に分解すると、
次の条件をすべて満たす素数 $p$ が存在する。ここで $\log$ は自然対数である。

$$
p\le(\log n)^2,\qquad p^d\not\equiv1\pmod n,
$$

$$
\forall j\in\mathbb N,\quad j<s\Longrightarrow p^{2^j d}\not\equiv-1\pmod n.
$$

これは底 $p$ で Strong Miller–Rabin の合格条件がすべて失敗することを表す。
証人は $p=2$ でも $p\mid n$ でもよく、平方合成数・他の完全冪も含めて全範囲を扱う。
Lean の定理では、この一意な分解を `s,d` と分解式・奇数性の仮定として受け取る。

Lean では合同式を `ZMod n` の等式・不等式として表す。
GRH は [既存の定義](../PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean)
`PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis` を仮定する。
GRH 自体を証明したという主張ではない。

## 公開定理と利用方法

以下の名前は `PseudoPrime.MillerRabinBoundGrh` 名前空間に属する。

| 宣言 | 内容 | ソース |
|---|---|---|
| `PrimeMillerRabinWitnessBound` | GRHからすべての奇合成数とその分解に対する証人存在を述べる `Prop` | [Definition.lean](../PseudoPrime/MillerRabinBoundGrh/Definition.lean) |
| `primeMillerRabinWitnessBound_of_grh` | 上記の `Prop` の証明 | [FromLLS.lean](../PseudoPrime/MillerRabinBoundGrh/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq` | 指定した `n,s,d` に対する主定理 | [FromLLS.lean](../PseudoPrime/MillerRabinBoundGrh/FromLLS.lean) |
| `exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq` | 計算済み分解を使うBoolean判定の不合格という形の系 | [FromLLS.lean](../PseudoPrime/MillerRabinBoundGrh/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq_of_s2` | S2を仮定した $n\ge3000$ の接続定理 | [FromLLS.lean](../PseudoPrime/MillerRabinBoundGrh/FromLLS.lean) |
| `exists_prime_millerRabin_witness_le_log_sq_of_lt_3000` | GRHを仮定しない $1<n<3000$ の定理 | [Small.lean](../PseudoPrime/MillerRabinBoundGrh/Small.lean) |

次の例は主定理の前提と結論をそのまま示す。

```lean
import PseudoPrime.MillerRabinBoundGrh.FromLLS

example
    (hGRH : PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n s d : ℕ} (hn : 1 < n) (hnOdd : Odd n) (hnNotPrime : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d) (hdOdd : Odd d) :
    ∃ p : ℕ,
      Nat.Prime p ∧ (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n) := by
  exact PseudoPrime.MillerRabinBoundGrh.exists_prime_millerRabin_witness_le_log_sq
    hGRH hn hnOdd hnNotPrime hdecomp hdOdd

#check PseudoPrime.MillerRabinBoundGrh.PrimeMillerRabinWitnessBound
#check PseudoPrime.MillerRabinBoundGrh.primeMillerRabinWitnessBound_of_grh
#check PseudoPrime.MillerRabinBoundGrh.exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq
```

Boolean系の結論は、同じ素数性・実数上界と
`PseudoPrime.PrimeTest.strongMillerRabinWithBase n p = false` である。
この系は素数底の存在を証明するものであり、新たな全底走査アルゴリズムを定義するものではない。
また、BPSW全体の「受理なら素数」という主張ではない。

## 証明の流れ

### 1. 合格条件、単元性、素因数底

`PseudoPrime.PrimeTest.StrongMillerRabinPass n s d x` は
$x^d=1$ または、ある $j<s$ に対して $x^{2^j d}=-1$ という条件を定義する。
合格すれば $x^{n-1}=1$ となり、 $n>1$ のもとでは $x$ は単元となる。
したがって素因数 $p\mid n$ を底にすると不合格になる。

[Decomposition.lean](../PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) の
`strongMillerRabinPass_isUnit`、`strongMillerRabinPass_not_of_prime_dvd` がこの性質を示す。
同ファイルの `strongMillerRabinWithBase_eq_false_iff_not_pass_decomp` は、
この分解での合格条件の否定を既存のBoolean判定へ接続する。
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

$n\ge3000$ に対し、 $p<(\log n)^2$ を満たす素因数があれば、1の性質でその $p$ を証人にする。
そのような素因数がなければ、[LLSのS2](LLS.md)を2の真部分群へ適用する。
S2は $p\le(\log n)^2$ で剰余が $H$ の像に入らない素数を与えるため、
その底は合格できない。

前提の小素因数除外は狭義の $<$、証人の上界は $\le$ である。
等号端点で証人が単元になるという追加仮定は用いない。
これが `exists_prime_millerRabin_witness_le_log_sq_of_s2` の証明である。
最終段階で `PseudoPrime.LLS.llsTheorem11S2_of_grh` によりGRHからS2を供給する。

### 4. 小さい範囲の有限証明

[Computation/Small.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/Small.lean) は、
$1<n<3000$ の奇合成数について、底2または底3で不合格になることを示す。
底2での不合格を示す有限分類では2047を例外候補とし、2047の底3での不合格を別途証明する。
公開定理は `PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000`。

証明は奇数 $n=2k+1$、 $0\le k<1500$ を128要素の11ブロックと92要素の最終ブロックで被覆する。
素数性と、明示分解・高速冪の不一致をLeanカーネルで検証し、checkerの健全性を通じて
既存のStrong Miller–Rabin判定へ移す。外部の整数探索結果を証明根拠には使わない。

奇合成数 $n>1$ なら $n\ge9$ なので $3\le(\log n)^2$ が成立する。
[Computation/SmallLogBound.lean](../PseudoPrime/PrimeTest/MillerRabin/Computation/SmallLogBound.lean)
は対数評価を有限分類へ接続し、小範囲の素数証人定理を与える。
有限分類だけを使う場合は `PseudoPrime.PrimeTest.MillerRabin.Computation.Small`、
対数上界も使う場合は `PseudoPrime.PrimeTest.MillerRabin.Computation.SmallLogBound` をimportする。

## 証明依存

主定理、Boolean系、有限分類、小範囲の上界、真部分群の中心定理、利用したS2定理の
推移的公理依存は `propext`、`Classical.choice`、`Quot.sound` のみである。
有限証明を含め、これらの定理に `sorry` や `native_decide` 由来の公理依存はない。
確認例は次のとおり。

```lean
import PseudoPrime

#print axioms PseudoPrime.MillerRabinBoundGrh.primeMillerRabinWitnessBound_of_grh
#print axioms PseudoPrime.PrimeTest.base_two_or_three_rejects_of_lt_3000
```

[構成全体へ](README.md) · [PrimeTest](PrimeTest.md) · [LLS](LLS.md)
