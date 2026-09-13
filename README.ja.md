# PseudoPrime

> このプロジェクトは AI の支援を受けて開発された。

[公開モジュールの構成と成果](doc/README.md) ·
[C++・PythonのBPSW参考実装](doc/BPSWImplementations.md)

## 非 1 ヤコビ目撃者と Selfridge 境界

このプロジェクトは、ヤコビ目撃者（Jacobi witness）と Selfridge 停止値に関する
境界を Lean で形式化する。

### 基本定義

以下を通じて、$\log$ は自然対数を表し、$\mathbb P_{\mathrm{odd}}$ は奇素数の
集合を表す。整数 $a$ と奇素数 $p$ に対して、Legendre 記号は次で定義される。

$$
\left(\frac{a}{p}\right)=
\begin{cases}
0 & a\equiv0\pmod p,\\
1 & a\not\equiv0\pmod p\text{ かつ } a\text{ が }p\text{ を法とする平方剰余のとき},\\
-1 & a\text{ が }p\text{ を法とする平方非剰余のとき}.
\end{cases}
$$

Euler の規準により、すべての奇素数 $p$ について

$$
\left(\frac{a}{p}\right)\equiv a^{(p-1)/2}\pmod p.
$$

正の奇分母 $n=\prod_p p^{e_p}$ に対して、Jacobi 記号は
$\left(\frac an\right)=\prod_p\left(\frac ap\right)^{e_p}$ で定義される。
分母が素数のときは Legendre 記号と一致する。

### GRH と RH の関係

GRH は一般化リーマン予想（generalized Riemann hypothesis）、RH はリーマン予想
（Riemann hypothesis）の略である。

以下の解析的境界は GRH 単独の仮定で得られる。停止値の比較自体は無条件である。

mathlib における RH の定義は次のとおりである。

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
    (_ : s ≠ 1), s.re = 1 / 2
```

本プロジェクトでは GRH を次のように定義する。

```lean
noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  by
    classical
    exact if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)} else
      if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else
        {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, χ.LFunction s = 0 →
    s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → DirichletRiemannHypothesis χ
```

`DirichletRiemannHypothesis χ` は、`dirichletTrivialZeros χ` として指定した自明零点集合に
属さないすべての $L(s,\chi)$ の零点が $\Re(s)=1/2$ 上にあると主張する。自明な零点は
整数として定義して複素数へ cast しており、法1では負の偶数、
奇指標では負の奇数、法1以外の偶指標では非正の偶数とする。

この `GeneralizedRiemannHypothesis` は、
[Formal Conjectures の指定版（6fbb54f24ccc2e64dcfaffc28c58950e377110d2）](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/Millennium/RiemannHypothesis.lean)
の `GRH.generalized_riemann_hypothesis` と同一の命題である。
どちらも、非零の法 `q` と原始 Dirichlet 指標 `χ : DirichletCharacter ℂ q` のすべてを対象に、
同じ整数値の自明零点集合を `ℂ` へ埋め込んで除外し、残るすべての `χ.LFunction` の零点に
`s.re = 1 / 2` を要求する。零点の量化範囲を開臨界帯に限定する条件も、
指標を二次指標に限定する条件もない。法1の分岐条件は `q = 1` である。

違いは命題の扱いにある。Formal Conjectures は未解決予想を `sorry` を含む theorem として
記載し、本プロジェクトは
[`GRH/Definition.lean`](PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) で
`Prop` として定義して明示的な仮定に用いる。どちらも GRH を証明したものではない。
指定版の自明零点の定義と theorem の型を本プロジェクトの Lean 環境で再現すると、
自明零点集合の等しさと GRH 全体の命題の同値性を検証できる。
必要なのは定義の展開と集合内包表記に現れる等式の向きの交換だけであり、
外部の予想を証明として使用していない。

法1の指標に対する主張は、mathlib の `RiemannHypothesis` と同値である。

```lean
theorem dirichletRiemannHypothesis_one_iff :
    DirichletRiemannHypothesis (1 : DirichletCharacter ℂ 1) ↔ RiemannHypothesis := by
  have htriv (s : ℂ) :
      s ∉ (Int.cast : ℤ → ℂ) ''
          ({z : ℤ | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)} : Set ℤ) ↔
        ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    constructor
    · intro hs h
      rcases h with ⟨n, hn⟩
      apply hs
      refine ⟨-2 * ((n : ℤ) + 1), ⟨n, rfl⟩, ?_⟩
      calc
        ((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) = -2 * ((n : ℂ) + 1) := by
          norm_num [Int.cast_neg, Int.cast_mul, Int.cast_add]
        _ = s := hn.symm
    · intro hs h
      rcases h with ⟨z, ⟨n, hn⟩, hz⟩
      apply hs
      refine ⟨n, ?_⟩
      calc
        s = (z : ℂ) := hz.symm
        _ = ((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) := by rw [← hn]
        _ = -2 * ((n : ℂ) + 1) := by
          norm_num [Int.cast_neg, Int.cast_mul, Int.cast_add]
  simp only [DirichletRiemannHypothesis, DirichletCharacter.LFunction_modOne_eq,
    dirichletTrivialZeros, RiemannHypothesis, ite_eq_left]
  simp only [htriv]
  constructor
  · intro h s hs ht _; exact h s hs ht
  · intro h s hs ht; exact h s hs ht (fun he => riemannZeta_one_ne_zero (he ▸ hs))
```

この同値を用いて GRH → RH を導く。GRH の仮定 `hGRH` から、
RH を `hGRH.riemann` で供給できる。逆向きの RH → GRH は主張していない。

```lean
theorem GeneralizedRiemannHypothesis.riemann (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  exact dirichletRiemannHypothesis_one_iff.mp
    (h 1 1 DirichletCharacter.isPrimitive_one_level_one)
```

### 奇素数目撃者の点ごとの境界

正の奇数かつ非平方数の `n` に対する二つの存在主張は、
`exists_prime_ne_one_witness_of_grh` と
`exists_prime_neg_one_witness_of_grh` に分けて与えられている。

```lean
theorem exists_prime_ne_one_witness_of_grh
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hnpos : 0 < n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1
```

```lean
theorem exists_prime_neg_one_witness_of_grh
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hnpos : 0 < n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (p : ℝ) ≤
        (Real.log (4 * (n : ℝ)) +
          (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 ∧
      jacobiSym n p = -1
```

任意の正の奇非平方数 $n$ に対して、GRH の下では、条件を満たす奇素数
$p_{\ne1}$ と $p_{-1}$ がそれぞれ存在し、

$$
p_{\ne1}\le\max\left(5,(\log n)^2\right),\quad
\left(\frac n{p_{\ne1}}\right)\ne1,
$$

かつ

$$
p_{-1}\le\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2,\quad
\left(\frac n{p_{-1}}\right)=-1
$$

が成り立つ。Lean では Jacobi 記号を `jacobiSym n p` で表す。

上の二つの目撃者定理は、LLS Theorem 1.1 の interface とは分けて扱う。
`ne_one` 定理は因子検出経路、`neg_one` 定理は古典的 Selfridge 探索で用いる
純粋な Jacobi 値 $-1$ の経路である。一般の LLS の組立ては
`LLS/Theorem11S1GRH.lean` にあり、Jacobi 値 $-1$ の評価はこの一般S1を法 $4n$ に適用する。
本プロジェクト独自の $Q\ne1$ 経路は、中間の重み付き評価と二次指標の精密評価を用いる。

### Selfridge 因子検出停止

古典的な Selfridge のパラメータ選択は Lucas–Selfridge 素数判定、特に
Baillie–PSW（BPSW）素数判定法などで用いられる。歴史的な参考文献は
[`Baillie–PSW 及び Lucas–Selfridge 素数判定法`](#bailliepsw-及び-lucasselfridge-素数判定法)
に示す。

古典的な候補述語と符号付き Selfridge 値は
[`PrimeTest/Selfridge/Candidates.lean`](PseudoPrime/PrimeTest/Selfridge/Candidates.lean)
で定義される。

```lean
def selfridgeD (i : ℕ) : ℤ :=
  if i % 4 = 1 then (i : ℤ) else -(i : ℤ)

def isClassicalCandidate (i : ℕ) : Prop :=
  5 ≤ i ∧ Odd i
```

古典的な Selfridge 数列は数学的には次のように書かれる。

$$
D(k)=(-1)^k(2k+5)\qquad(k\ge0).
$$

正の奇非平方数 $n$ に対して、純粋な $-1$ 停止と因子検出停止では
Jacobi 記号を用い、次のように表される。

$$
g_{-1}(n)=D\!\left(\min\left\lbrace k\in\mathbb N\mathrel{}\middle\vert\mathrel{}
\left(\frac{D(k)}{n}\right)=-1\right\rbrace\right),
$$

$$
g_{\ne1}(n)=D\!\left(\min\left\lbrace k\in\mathbb N\mathrel{}\middle\vert\mathrel{}
n\nmid\left\lvert D(k)\right\rvert\ \text{かつ}\ \left(\frac{D(k)}{n}\right)\ne1\right\rbrace\right).
$$

条件 $n\nmid\left\lvert D(k)\right\rvert$ は、入力の倍数を候補絶対値から
除外するものであり、
[`PrimeTest/Selfridge/FirstStop.lean`](PseudoPrime/PrimeTest/Selfridge/FirstStop.lean)
の `FirstStopNeOneSet` に対応する。
Lean では `selfridgeD` は候補絶対値を引数に取るため、$D(k)$ は
`selfridgeD (2 * k + 5)` に対応する。式
`firstStopNegOne isClassicalCandidate n ...` と
`firstStopNeOne isClassicalCandidate n ...` は、数列の添字 $k$ ではなく、
最小の停止候補絶対値そのものを返す。`selfridgeD` を適用するとそれぞれ
$g_{-1}(n)$ と $g_{\ne1}(n)$ になり、`natAbs` によりそれらの絶対値が得られる。

### Selfridge 停止に対する点ごとの初等半径境界

点ごとの Selfridge 走査については、無条件の比較

```lean
theorem firstStopNeOne_le_firstStopNegOne_same_candidates
    {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNeOne C n (firstStopNeOneSet_nonempty_of_negOne hn hneg) ≤
      firstStopNegOne C n hneg
```

が
[`PrimeTest/Selfridge/Coincidence.lean`](PseudoPrime/PrimeTest/Selfridge/Coincidence.lean)
で証明されている。

Method A と Method A* の Strong Lucas 判定結果も、例外的な $D=5$ の分岐を
含めて一致する。この証明は、
[`PrimeTest/Selfridge/MethodAStarEquivalence.lean`](PseudoPrime/PrimeTest/Selfridge/MethodAStarEquivalence.lean)
の `strongLucasMethodAStar_eq_methodA` とその逆向きの定理で与えられる。

Method A と A* が用いる共通の古典的 D 選択走査については、$B\ge751$ に対する
対応する集約境界が、
[`SelfridgeBoundGrh/LogSqMaximum.lean`](PseudoPrime/SelfridgeBoundGrh/LogSqMaximum.lean)
の `classicalNeOneMaximum_cast_le_log_sq_of_751_le` として証明されている。

点ごとの初等半径境界は GRH の下で、
[`SelfridgeBoundGrh/ElementaryRadius.lean`](PseudoPrime/SelfridgeBoundGrh/ElementaryRadius.lean)
で証明される。

```lean
theorem classicalSelfridgeD_elementary_bound_explicit
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ((selfridgeD (firstStopNeOne isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        ((selfridgeD (firstStopNegOne isClassicalCandidate n
          (classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ∧
      ((selfridgeD (firstStopNegOne isClassicalCandidate n
        (classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        (Real.log (4 * (n : ℝ)) +
          (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2
```

ここで

$$
R(n)=\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2
$$

であり、正の奇非平方数 $n$ に対して GRH の下でこれは以下を証明する。

$$
\left\lvert g_{\ne1}(n)\right\rvert\le\left\lvert g_{-1}(n)\right\rvert\le R(n)
$$

この定理は、無条件の停止値比較と GRH の解析的境界を併用する。
その公理依存は `propext`、`Classical.choice`、`Quot.sound` であり、
GRH は明示的な仮定であり、RH はそこから導かれる。

これと対になる純粋な `-1` 停止値についても、GRH の下で公開する。
すべての

$$
n\ge3,\qquad n\text{ は奇数},\qquad n\text{ は非平方数}
$$

に対して、

$$
\left\lvert g_{-1}(n)\right\rvert\le R(n)
$$

が成り立ち、さらに奇素数 $p_{-1}$ が存在して

$$
p_{-1}\le R(n),\qquad
\left(\frac n{p_{-1}}\right)=-1
$$

となる。ここで

$$
R(n)=\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2.
$$

Lean では、$g_{-1}(n)$ の絶対値を、符号付き `selfridgeD` に
`firstStopNegOne` を適用した値の `natAbs` で表す。

### Selfridge 停止に対する対数境界

因子検出停止の対数境界は
[`SelfridgeBoundGrh/LogSq.lean`](PseudoPrime/SelfridgeBoundGrh/LogSq.lean)
で証明される。

```lean
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hn13 : 13 ≤ n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ((selfridgeD (firstStopNeOne isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        Real.log (n : ℝ) ^ 2
```

正の奇非平方数 $n\ge13$ に対して、GRH の下でこれは以下を証明する。

$$
\left\lvert g_{\ne1}(n)\right\rvert\le(\log n)^2
$$

この境界は、すべての正の奇非平方数 $n$ に対して次の系へ拡張される。

```lean
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hnpos : 0 < n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ((selfridgeD (firstStopNeOne isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        max 13 (Real.log (n : ℝ) ^ 2)
```

したがって、GRH の下で、すべての正の奇非平方数 $n$ について

$$
\left\lvert g_{\ne1}(n)\right\rvert\le\max\left(13,(\log n)^2\right)
$$

が成り立つ。

同じファイルには Wheel30 移送定理
`wheel30SelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le` も含まれる。

## 参考文献

### 最小非剰余に対する LLS 境界

対数的な目撃者境界に用いられる解析的入力は、次の文献に基づく。

> Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, “Conditional bounds for the least quadratic non-residue and related problems,” *Mathematics of Computation* **84** (2015), no. 295, 2391–2412. [DOI: 10.1090/S0025-5718-2015-02925-1](https://doi.org/10.1090/S0025-5718-2015-02925-1), [arXiv:1309.3595](https://arxiv.org/abs/1309.3595).

証明計画は、対数的目撃者境界の解析的基盤として Theorem 1.1(2) を、
このプロジェクトの算術的・有限範囲的な還元とともに用いる。

### Baillie–PSW 及び Lucas–Selfridge 素数判定法

Lucas probable prime と Baillie–PSW テストの原典は次の通り。

> Robert Baillie and Samuel S. Wagstaff, Jr., “Lucas pseudoprimes,” *Mathematics of Computation* **35** (1980), no. 152, 1391–1417. [DOI: 10.1090/S0025-5718-1980-0583518-6](https://doi.org/10.1090/S0025-5718-1980-0583518-6).

> Carl Pomerance, John L. Selfridge, and Samuel S. Wagstaff, Jr., “The pseudoprimes to
> $25\cdot10^9$,” *Mathematics of Computation* **35** (1980), no. 151, 1003–1026.
> [DOI: 10.1090/S0025-5718-1980-0572872-7](https://doi.org/10.1090/S0025-5718-1980-0572872-7).

これらの論文は、強基底 2 プラス Lucas–Selfridge の Baillie–PSW テスト、および
このプロジェクトにおいて `selfridgeD`、`firstStopNegOne`、`firstStopNeOne` が
表現する Selfridge パラメータ選択の文脈に関する歴史的な参考文献である。
Baillie–PSW テストの後の強化については、Robert Baillie, Andrew Fiori, and
Samuel S. Wagstaff, Jr., “[Strengthening the Baillie-PSW primality test](https://arxiv.org/abs/2006.14425v2),”
arXiv:2006.14425v2 を参照。

本プロジェクトの実行用 `bailliePSW` と `strengthenedBPSW` は、Selfridge の
Jacobi 値 $-1$ だけを用いる昇順探索の変種である。共通の事前判定、Selfridge
判別式の探索、探索成功後の底2 Miller–Rabin と Lucas 系判定の順で実行する。
探索中に Jacobi 値 $0$ を因子検出として扱う早期停止は、歴史的アルゴリズムの
説明とは異なり、この実行用探索には実装していない。

### 疑似平方数に関する参考文献

背景となる用語と数値データについては、[OEIS A002189 —
Pseudosquares](https://oeis.org/A002189) を参照。OEIS A002189 は古典的な
定義、すなわち $1\pmod 8$ に合同で、最初のいくつかの奇素数を法として
非零平方剰余となる最小の正の非平方整数を用いている。

本プロジェクトは、Selfridge/LLS 目撃者定理において、より広い
$1\pmod 2$（奇数）非平方数の定義域を用いる。OEIS のエントリは参考情報としてのみ扱う。
