# PseudoPrime

> This project was developed with the assistance of AI.

[Module guide and results (Japanese)](doc/README.md) ·
[C++ / Python BPSW examples (Japanese)](doc/BPSWImplementations.md)

## Prime Miller–Rabin witnesses under GRH

Assuming the generalized Riemann hypothesis (GRH), every odd composite integer $n>1$
has a prime base $p\le(\log n)^2$ that the strong Miller–Rabin test rejects.
Here $\log$ is the natural logarithm. Write $n-1=2^s d$ with $s,d\in\mathbb N$ and $d$ odd;
this decomposition is unique. The witness satisfies

$$
p^d\not\equiv1\pmod n,\qquad
\forall j\in\mathbb N,\quad j < s\Longrightarrow p^{2^j d}\not\equiv-1\pmod n.
$$

The result includes composite squares and other perfect powers; the witness may be $2$
or a prime divisor of $n$. GRH is an explicit hypothesis.
The proof combines an unconditional proper-subgroup construction, a kernel-checked
finite proof for $1 < n < 3000$, and the GRH theorem for LLS Theorem 1.1(2).

The public results are in
[`MillerRabinBoundGrh/FromLLS.lean`](PseudoPrime/MillerRabinBoundGrh/FromLLS.lean):

```lean
import PseudoPrime

#check PseudoPrime.MillerRabinBoundGrh.primeMillerRabinWitnessBound_of_grh
#check PseudoPrime.MillerRabinBoundGrh.exists_prime_millerRabin_witness_le_log_sq
#check PseudoPrime.MillerRabinBoundGrh.exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq
```

The first theorem proves the property `PrimeMillerRabinWitnessBound`; the second gives
the witness for `n` and its decomposition `s,d`, and the third gives
`PseudoPrime.PrimeTest.strongMillerRabinWithBase n p = false` for the executable test.
See the [theorem and proof guide (Japanese)](doc/MillerRabinBoundGrh.md) for the assumptions,
source mapping, and finite-range argument.

## Non-1 Jacobi witnesses and Selfridge bounds

This project formalizes bounds on Jacobi witnesses and Selfridge stopping values in Lean.
### Basic definitions

Throughout, $\log$ denotes the natural logarithm and $\mathbb P_{\mathrm{odd}}$
denotes the set of odd primes. For an integer $a$ and an odd prime $p$, the Legendre symbol is

$$
\left(\frac{a}{p}\right)=
\begin{cases}
0 & a\equiv0\pmod p,\\
1 & a\not\equiv0\pmod p\text{ and }a\text{ is a quadratic residue mod }p,\\
-1 & a\text{ is a quadratic non-residue modulo }p.
\end{cases}
$$

Euler's criterion gives, for every odd prime $p$,

$$
\left(\frac{a}{p}\right)\equiv a^{(p-1)/2}\pmod p.
$$

For a positive odd denominator $n=\prod_p p^{e_p}$, the Jacobi symbol is
$\left(\frac an\right)=\prod_p\left(\frac ap\right)^{e_p}$.
It agrees with the Legendre symbol when the denominator is prime.

### GRH and its relation to RH

GRH stands for the generalized Riemann hypothesis, and RH stands for the Riemann hypothesis.

The analytic bounds follow from GRH alone. The stopping-value comparison is unconditional.

mathlib defines RH as follows:

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
    (_ : s ≠ 1), s.re = 1 / 2
```

GRH is defined in this project as follows:

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

`DirichletRiemannHypothesis χ` asserts that every zero of $L(s,\chi)$ not belonging to the
trivial-zero set specified by `dirichletTrivialZeros χ` lies on $\Re(s)=1/2$. The trivial zeros
are represented as integers and cast into $\mathbb C$; they are negative even integers at modulus one,
negative odd integers for odd characters, and nonpositive even integers for even
characters at other moduli.

This `GeneralizedRiemannHypothesis` states the same proposition as
`GRH.generalized_riemann_hypothesis` in
[Formal Conjectures at revision 6fbb54f24ccc2e64dcfaffc28c58950e377110d2](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/Millennium/RiemannHypothesis.lean).
Both quantify over every nonzero modulus `q` and every primitive Dirichlet character
`χ : DirichletCharacter ℂ q`, exclude exactly the same integer-valued trivial zeros
cast into `ℂ`, and conclude `s.re = 1 / 2` for every remaining zero of `χ.LFunction`.
Neither statement restricts its quantified zeros to the open critical strip or assumes
that the character is quadratic. The modulus-one branch is selected by `q = 1`.

The difference is how the proposition is packaged: Formal Conjectures records an open
conjecture as a theorem with a `sorry` proof; this project defines a `Prop` in
[`GRH/Definition.lean`](PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) and uses it
as an explicit hypothesis. Neither proves GRH. Reproducing the upstream trivial-zero
definition and theorem type in this project's Lean environment verifies equality of
the trivial-zero sets and equivalence of the full GRH propositions. This requires only
unfolding definitions and reversing the equality inside the set-builder notation;
it does not use the upstream conjecture as a proof.

The statement for the modulus-one character is equivalent to mathlib's `RiemannHypothesis`:

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

This equivalence gives GRH → RH: from a GRH assumption `hGRH`, RH is supplied by
`hGRH.riemann`. The reverse implication RH → GRH is not asserted.

```lean
theorem GeneralizedRiemannHypothesis.riemann (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  exact dirichletRiemannHypothesis_one_iff.mp
    (h 1 1 DirichletCharacter.isPrimitive_one_level_one)
```

### Pointwise bounds for odd-prime witnesses

For every positive odd nonsquare `n`, the two existence statements requested above are
provided separately by `exists_prime_ne_one_witness_of_grh` and
`exists_prime_neg_one_witness_of_grh`:

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

For every positive odd nonsquare $n$, GRH implies that there exist odd primes
$p_{\ne1}$ and $p_{-1}$ satisfying, respectively,

$$
p_{\ne1}\le\max\left(5,(\log n)^2\right),\quad
\left(\frac n{p_{\ne1}}\right)\ne1,
$$

and

$$
p_{-1}\le\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2,\quad
\left(\frac n{p_{-1}}\right)=-1.
$$

Here `jacobiSym n p` is the Lean representation of the Jacobi symbol.

The two witness theorems above are separate from the LLS Theorem 1.1 interfaces:
the `ne_one` theorem is the factor-detecting route, while the `neg_one` theorem is
the pure Jacobi $-1$ route used by the classical Selfridge search. The generic LLS
assembly is exposed by `LLS/Theorem11S1GRH.lean`. The Jacobi $-1$ bound applies this
general S1 theorem at modulus $4n$; the project's additional $Q\ne1$ route uses
intermediate weighted estimates with quadratic refinements.

### The Selfridge factor-detection stop

The classical Selfridge parameter choice is used in Lucas–Selfridge primality
testing, notably in the Baillie–PSW (BPSW) primality test. Historical references
are listed in [Baillie–PSW and Lucas–Selfridge primality testing](#baillie-psw-and-lucas-selfridge-primality-testing).

The classical candidate predicate and signed Selfridge value are defined in
[`PrimeTest/Selfridge/Candidates.lean`](PseudoPrime/PrimeTest/Selfridge/Candidates.lean):

```lean
def selfridgeD (i : ℕ) : ℤ :=
  if i % 4 = 1 then (i : ℤ) else -(i : ℤ)

def isClassicalCandidate (i : ℕ) : Prop :=
  5 ≤ i ∧ Odd i
```

The classical Selfridge sequence is written mathematically as

$$
D(k)=(-1)^k(2k+5)\qquad(k\ge0).
$$

For a positive odd nonsquare $n$, the pure $-1$ and factor-detecting stops use the
Jacobi symbol and are

$$
g_{-1}(n)=D\left(\min\left\lbrace k\in\mathbb N\mathrel{}\middle\vert\mathrel{}
\left(\frac{D(k)}{n}\right)=-1\right\rbrace\right),
$$

$$
g_{\ne1}(n)=D\left(\min\left\lbrace k\in\mathbb N\mathrel{}\middle\vert\mathrel{}
n\nmid\left\lvert D(k)\right\rvert\ \text{and}\ \left(\frac{D(k)}{n}\right)\ne1\right\rbrace\right).
$$

The condition $n\nmid\left\lvert D(k)\right\rvert$ excludes multiples of the input
as candidate absolute values, matching `FirstStopNeOneSet` in
[`PrimeTest/Selfridge/FirstStop.lean`](PseudoPrime/PrimeTest/Selfridge/FirstStop.lean).
In Lean, `selfridgeD` takes a candidate absolute value,
so $D(k)$ corresponds to `selfridgeD (2 * k + 5)`. The expressions
`firstStopNegOne isClassicalCandidate n ...` and
`firstStopNeOne isClassicalCandidate n ...` return the least stopping candidate
absolute values, rather than the sequence indices $k$. Applying `selfridgeD` gives
$g_{-1}(n)$ and $g_{\ne1}(n)$, respectively; `natAbs` gives their absolute values.

### Pointwise elementary-radius bounds for the Selfridge stop

For the pointwise Selfridge scan, the unconditional comparison

```lean
theorem firstStopNeOne_le_firstStopNegOne_same_candidates
    {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNeOne C n (firstStopNeOneSet_nonempty_of_negOne hn hneg) ≤
      firstStopNegOne C n hneg
```

is proved in
[`PrimeTest/Selfridge/Coincidence.lean`](PseudoPrime/PrimeTest/Selfridge/Coincidence.lean).

The Strong Lucas results of Method A and Method A* also agree, including the
exceptional $D=5$ branch.  The proof is provided by
`strongLucasMethodAStar_eq_methodA` and its converse in
[`PrimeTest/Selfridge/MethodAStarEquivalence.lean`](PseudoPrime/PrimeTest/Selfridge/MethodAStarEquivalence.lean).

For the common classical D-selection scan used by Methods A and A*, the corresponding
aggregate bound for $B\ge751$ is proved as
`classicalNeOneMaximum_cast_le_log_sq_of_751_le` in
[`SelfridgeBoundGrh/LogSqMaximum.lean`](PseudoPrime/SelfridgeBoundGrh/LogSqMaximum.lean).

The pointwise elementary-radius bound is proved under GRH in
[`SelfridgeBoundGrh/ElementaryRadius.lean`](PseudoPrime/SelfridgeBoundGrh/ElementaryRadius.lean):

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

Here

$$
R(n)=\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2.
$$

Under GRH, for every positive odd nonsquare $n$, this proves

$$
\left\lvert g_{\ne1}(n)\right\rvert\le\left\lvert g_{-1}(n)\right\rvert\le R(n)
$$

The theorem uses the unconditional stopping-value comparison together with the
GRH analytic bound. Its axiom dependencies are `propext`, `Classical.choice`,
and `Quot.sound`; GRH remains an explicit hypothesis and supplies RH.

The corresponding pure `-1` statement is also public under GRH. For every
$n\ge3$ that is odd and nonsquare,

$$
\left\lvert g_{-1}(n)\right\rvert\le R(n),
$$

and there is an odd prime $p_{-1}$ such that

$$
p_{-1}\le R(n),\qquad
\left(\frac n{p_{-1}}\right)=-1.
$$

Here

$$
R(n)=\left(\log(4n)+\frac{24}{5}\log(\log(4n))+3\right)^2.
$$

In Lean, the absolute value of $g_{-1}(n)$ is represented by the `natAbs` of
the signed `selfridgeD` at `firstStopNegOne`.

### Logarithmic bound for the Selfridge stop

The logarithmic bound for the factor-detection stop is proved in
[`SelfridgeBoundGrh/LogSq.lean`](PseudoPrime/SelfridgeBoundGrh/LogSq.lean):

```lean
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hn13 : 13 ≤ n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ((selfridgeD (firstStopNeOne isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        Real.log (n : ℝ) ^ 2
```

Under GRH, for every positive odd nonsquare $n\ge13$, this proves

$$
\left\lvert g_{\ne1}(n)\right\rvert\le(\log n)^2
$$

The bound extends to every positive odd nonsquare $n$ as

```lean
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq
    (hGRH : GeneralizedRiemannHypothesis)
    {n : ℕ} (hnpos : 0 < n) (hn : Odd n) (hns : ¬ IsSquare n) :
    ((selfridgeD (firstStopNeOne isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
        max 13 (Real.log (n : ℝ) ^ 2)
```

Thus, under GRH, every positive odd nonsquare $n$ satisfies

$$
\left\lvert g_{\ne1}(n)\right\rvert\le\max\left(13,(\log n)^2\right).
$$

The same file also contains the Wheel30 transfer theorem
`wheel30SelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le`.

## References

### LLS bounds for least non-residues

The analytic input used for the logarithmic witness bounds is based on:

> Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, “Conditional bounds for the least quadratic non-residue and related problems,” *Mathematics of Computation* **84** (2015), no. 295, 2391–2412. [DOI: 10.1090/S0025-5718-2015-02925-1](https://doi.org/10.1090/S0025-5718-2015-02925-1), [arXiv:1309.3595](https://arxiv.org/abs/1309.3595).

The proof plan uses Theorem 1.1(2) as the analytic basis for the logarithmic
witness bound, together with the project's arithmetic and finite-range reductions.

### Baillie–PSW and Lucas–Selfridge primality testing

The original references for Lucas probable primes and the Baillie–PSW test are:

> Robert Baillie and Samuel S. Wagstaff, Jr., “Lucas pseudoprimes,” *Mathematics of Computation* **35** (1980), no. 152, 1391–1417. [DOI: 10.1090/S0025-5718-1980-0583518-6](https://doi.org/10.1090/S0025-5718-1980-0583518-6).

> Carl Pomerance, John L. Selfridge, and Samuel S. Wagstaff, Jr., “The pseudoprimes to
> $25\cdot10^9$,” *Mathematics of Computation* **35** (1980), no. 151, 1003–1026.
> [DOI: 10.1090/S0025-5718-1980-0572872-7](https://doi.org/10.1090/S0025-5718-1980-0572872-7).

These papers are the historical references for the strong base-2 plus Lucas–Selfridge
Baillie–PSW test and the Selfridge parameter-selection context represented by `selfridgeD`,
`firstStopNegOne`, and `firstStopNeOne` in this project. For a later strengthening of the
Baillie–PSW test, see Robert Baillie, Andrew Fiori, and Samuel S. Wagstaff, Jr.,
“[Strengthening the Baillie-PSW primality test](https://arxiv.org/abs/2006.14425v2),”
arXiv:2006.14425v2.

The executable `bailliePSW` and `strengthenedBPSW` interfaces in this project are an
ascending, pure Jacobi $-1$ Selfridge variant. They perform the common precheck first,
then search for a Selfridge discriminant, and only after a successful search evaluate
the base-2 Miller–Rabin and Lucas tests. The search itself does not perform the
factor-detecting Jacobi $0$ early stop described in the historical algorithm.

### Pseudosquare reference

For background terminology and numerical data, see [OEIS A002189 —
Pseudosquares](https://oeis.org/A002189). OEIS A002189 uses the classical
definition: the least positive nonsquare integer congruent to $1\pmod 8$ that
is a nonzero quadratic residue modulo the first several odd primes.

The present project uses a broader $1\pmod 2$ (odd) nonsquare domain in its
Selfridge/LLS witness theorems. The OEIS entry is reference information only.
