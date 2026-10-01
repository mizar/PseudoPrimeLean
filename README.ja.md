# PseudoPrime

> このプロジェクトは AI の支援を受けて開発されました。

[English](README.md) · [モジュール案内と成果](doc/README.md) · [C++ / Python による BPSW 実装例](doc/BPSWImplementations.md)

## 概要

このプロジェクトは、**一般化リーマン予想（GRH）** の下での素数判定と二次指標の証人に対する明示的上界を Lean で形式化している。

解析的な展開は、Lamzouri、Li、Soundararajan の論文 [*Conditional bounds for the least quadratic non-residue and related problems*](https://arxiv.org/abs/1309.3595) に沿っている。これらの上界に必要な部分を、有限範囲の議論及び代数的議論とともに Lean で形式化している。

主な結果は次の二つである。

1. GRH の下で、奇数 $n > 1$ が素数であることと、すべての素数底 $p \le (\ln\mathrel{} n)^2$ に対する強 Miller–Rabin 条件を満たすことは同値である。
2. GRH の下で、任意の正の奇数かつ非平方数 $n$ に対し、2 種類の奇素数証人 $p$ の存在を示し、それぞれに明示的上界を与える。一つは Legendre 記号 $\bigl(\frac{n}{p}\bigr)$ が $1$ と異なるもの、もう一つは $-1$ となるものである。

以下、 $\ln$ は底が $e$ の自然対数を表す。Lean では `Real.log` に対応する。

## GRH の下での強 Miller–Rabin 素数判定条件

奇数 $n > 1$ をとる。このプロジェクトでは、GRH の下で次を証明する。

$$
\boxed{
n \text{ が素数}
\iff
\text{すべての素数 }p \le (\ln\mathrel{} n)^2 \text{ が } n \text{ に対する強 Miller–Rabin 条件を満たす}
}
$$

具体的には、一意な分解を

$$
n - 1 = 2^s d,\qquad s, d \in \mathbb{N},\quad d \text{ は奇数}
$$

と書くと、

$$
n \text{ が素数}
\iff
\forall p \text{ 素数},\quad p \le (\ln\mathrel{} n)^2
\Longrightarrow \bigl(p^d \equiv 1 \pmod n
\lor
\exists j \in \mathbb{N},\quad j < s \land p^{2^j d} \equiv -1 \pmod n\bigr).
$$

前提が $n > 1$ なので、同じ GRH の仮定の下で、次のように同値に言い換えられる。

$$
n \text{ が合成数}
\iff
\exists p \text{ 素数},\quad
p \le (\ln\mathrel{} n)^2
\land
p^d \not\equiv 1 \pmod n
\land
\forall j \in \mathbb{N},\quad j < s \Longrightarrow p^{2^j d} \not\equiv -1 \pmod n.
$$

つまり、奇数 $n > 1$ の合成数性は、それを棄却する素数底 $p \le (\ln\mathrel{} n)^2$ の存在と同値である。

ここで $\mathbb{N} = \lbrace 0, 1, 2, \ldots \rbrace$ とし、Lean の `ℕ` に合わせる。

同値の二つの向きでは、仮定の役割が異なる。

- $\text{Prime} \to (\text{all pass})$ の向きに GRH は不要である。 $n$ が素数なら、指定の上界以下の各素数底が合格する。
- $(\text{all pass}) \to \text{Prime}$ の向きに GRH を用いる。奇合成数 $n > 1$ には、 $n$ を棄却する素数底 $p \le (\ln\mathrel{} n)^2$ が存在する。

Lean では $n - 1$ の分解を $n$ から標準的に定める。値 $s$、値 $d$、及び分解の等式は、この公開定理における追加仮定ではない。

公開定理は名前空間 `PseudoPrime.PrimeTestBounds.MillerRabin` の [FromLLS.lean](PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean) にある。以下の宣言抜粋では証明本体を省略している。

```lean
theorem prime_iff_millerRabin_for_all_primes_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hnOdd : Odd n) :
    let s := padicValNat 2 (n - 1)
    let d := Nat.divMaxPow (n - 1) 2
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n
```

連鎖する含意 `Nat.Prime p → (p : ℝ) ≤ ... → ...` は、任意の底 `p` が素数であり、かつ上界以下であるときに Miller–Rabin 条件を要求する。この明示的な冪合同条件は、実行用判定 `PrimeTest.strongMillerRabinWithBase n p` が `true` を返すことと同値であり、 [`strongMillerRabinWithBase_eq_true_iff_pass`](PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean) で証明している。

## GRH の下での Legendre 記号の証人

正の奇数かつ非平方数 $n$ をとる。

### Legendre 記号が $1$ でない素数証人

GRH の下で、次を満たす奇素数 $p$ が存在する。

$$
p \le \max\left\lbrace 5, (\ln\mathrel{} n)^2 \right\rbrace,\qquad
\boxed{\Bigl(\frac{n}{p}\Bigr) \ne 1}
$$

公開定理は名前空間 `PseudoPrime.PseudoSquare` の [PointwiseWitness.lean](PseudoPrime/PseudoSquare/Bounds/PointwiseWitness.lean) にある。

```lean
theorem exists_prime_ne_one_witness_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1
```

### 平方非剰余となる素数の証人

GRH の下で、次を満たす奇素数 $p$ も存在する。

$$
p \le \Bigl(\ln(4n) + \frac{24}{5}\ln(\ln(4n)) + 3\Bigr)^2,\qquad
\boxed{\Bigl(\frac{n}{p}\Bigr) = -1}
$$

対応する公開定理も、同じ名前空間・ファイルにある。

```lean
theorem exists_prime_neg_one_witness_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 ∧
        jacobiSym n p = -1
```

Lean の定理では `jacobiSym n p` を用いる。分母 $p$ は奇素数なので、これは Legendre 記号 $\bigl(\frac{n}{p}\bigr)$ と一致する。

最初の結果は $\bigl(\frac{n}{p}\bigr) = 0$ または $\bigl(\frac{n}{p}\bigr) = -1$ を許す。前者は $p \mid n$ と同値であり、後者は $n$ が $p$ を法として平方非剰余であることを意味する。第 2 の定理は後者を保証する。

## GRH の仮定の位置付け

上記の条件付き結果では、GRH を明示的な仮定とする。Lean では、名前空間 `PseudoPrime` 内の [`AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis`](PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) として定義している。

このプロジェクトは **GRH 自体を証明しない**。GRH から、LLS Theorem 1.1 の関連する部分に対応する結果を Lean 内で導出する。これには [`LLS.llsTheorem11S1_of_grh`](PseudoPrime/LLS/Theorem11S1GRH.lean) と [`LLS.llsTheorem11S2_of_grh`](PseudoPrime/LLS/Theorem11S2.lean) が含まれる。これらをプロジェクトの代数的・数論的議論及び有限範囲の議論と組み合わせ、上記の明示的上界を得る。

## 詳細な資料

- [Miller–Rabin の上界](doc/MillerRabinBoundGrh.md)
- [LLS の解析的上界](doc/LLS.md)
- [疑似平方数と素数の証人](doc/PseudoSquare.md)
- [Selfridge 探索の上界](doc/SelfridgeBoundGrh.md)

## 参考文献

### 最小非剰余に対する LLS 上界

証人の対数的上界に用いる解析的結果は、次の文献に基づく。

> Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, “Conditional bounds for the least quadratic non-residue and related problems,” *Mathematics of Computation* **84** (2015), no. 295, 2391–2412. [DOI: 10.1090/S0025-5718-2015-02925-1](https://doi.org/10.1090/S0025-5718-2015-02925-1), [arXiv:1309.3595](https://arxiv.org/abs/1309.3595).

本形式化は、この論文の関連する結果と解析的評価を、プロジェクトの算術的議論及び有限範囲の議論と組み合わせて用いる。対応する形式化済みの結果については [LLS のモジュール解説](doc/LLS.md) を参照。

### Baillie–PSW 及び Lucas–Selfridge 素数判定法

Lucas–Selfridge と Baillie–PSW の背景となる歴史的文献として、次が挙げられる。

> Robert Baillie and Samuel S. Wagstaff, Jr., “Lucas pseudoprimes,” *Mathematics of Computation* **35** (1980), no. 152, 1391–1417. [DOI: 10.1090/S0025-5718-1980-0583518-6](https://doi.org/10.1090/S0025-5718-1980-0583518-6).

> Carl Pomerance, John L. Selfridge, and Samuel S. Wagstaff, Jr., “The pseudoprimes to $25\cdot10^9$,” *Mathematics of Computation* **35** (1980), no. 151, 1003–1026. [DOI: 10.1090/S0025-5718-1980-0572872-7](https://doi.org/10.1090/S0025-5718-1980-0572872-7).

これらの論文は、Baillie–PSW テストに関連する底 2 の強 Miller–Rabin と Lucas–Selfridge の構成要素、及びこのプロジェクトにおいて `selfridgeD`、 `firstStopNegOne`、 `firstStopNeOne` が表現する Selfridge パラメータ選択の文脈に関する歴史的な参考文献である。Baillie–PSW テストの後年の強化については、Robert Baillie, Andrew Fiori, and Samuel S. Wagstaff, Jr., “[Strengthening the Baillie-PSW primality test](https://arxiv.org/abs/2006.14425v2),” arXiv:2006.14425v2 を参照。

本プロジェクトの実行用 `bailliePSW` と `strengthenedBPSW` は、Jacobi 記号が $-1$ となる判別式に限定した Selfridge 昇順探索の変種である。共通の事前判定、Selfridge 判別式の探索、探索成功後の底 2 Miller–Rabin と Lucas 系判定の順で実行する。歴史的な因子検出付き変種とは異なり、この実行用探索では Jacobi 値 $0$ を因子検出による早期停止として用いない。

### 疑似平方数に関する参考文献

背景となる用語と数値データについては、[OEIS A002189 — Pseudosquares](https://oeis.org/A002189) を参照。OEIS A002189 は、奇素数列の各初期部分に対し、 $1 \pmod 8$ に合同で、その初期部分に含まれるすべての奇素数を法として非零平方剰余となる最小の正の非平方整数を記録する。

本プロジェクトは、Selfridge/LLS 証人定理において、より広い正の奇数かつ非平方数の定義域を用いる。OEIS のエントリは参考資料として挙げるにとどめる。
