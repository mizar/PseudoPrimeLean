# PseudoPrime

> This project was developed with the assistance of AI.

[日本語](README.ja.md) · [Module guide and results (Japanese)](doc/README.md) · [C++ / Python BPSW examples (Japanese)](doc/BPSWImplementations.md)

## Overview

This project formalizes in Lean explicit bounds for primality testing and quadratic-character witnesses under the **Generalized Riemann Hypothesis (GRH)**.

The analytic development follows the work of Lamzouri, Li, and Soundararajan, [*Conditional bounds for the least quadratic non-residue and related problems*](https://arxiv.org/abs/1309.3595). The results needed for these bounds, together with the required finite-range and algebraic arguments, are formalized in Lean.

The project has two main results:

1. Under GRH, an odd integer $n > 1$ is prime if and only if it passes the strong Miller–Rabin conditions for every prime base $p \le (\ln\mathrel{} n)^2$.
2. Under GRH, every positive odd nonsquare $n$ has odd-prime witnesses of two kinds, each with an explicit upper bound. For one kind, the Legendre symbol $\bigl(\frac{n}{p}\bigr)$ is different from $1$; for the other, it is equal to $-1$.

Here and throughout, $\ln$ denotes the natural logarithm (base $e$), represented by `Real.log` in Lean.

## Strong Miller–Rabin primality criterion under GRH

Let $n > 1$ be odd. The project proves that, assuming GRH,

$$
\boxed{
n \text{ is prime}
\iff
\text{every prime }p \le (\ln\mathrel{} n)^2
\text{ passes the strong Miller–Rabin conditions for }n
}
$$

More explicitly, write the unique decomposition

$$
n - 1 = 2^s d,\qquad s, d \in \mathbb{N},\quad d \text{ odd}.
$$

Then

$$
n \text{ is prime}
\iff
\forall p \text{ prime},\quad p \le (\ln\mathrel{} n)^2
\Longrightarrow \bigl(p^d \equiv 1 \pmod n
\lor
\exists j \in \mathbb{N},\quad j < s \land p^{2^j d} \equiv -1 \pmod n\bigr).
$$

Equivalently, since $n > 1$, the same result can be stated on the composite side:

$$
n \text{ is composite}
\iff
\exists p \text{ prime},\quad
p \le (\ln\mathrel{} n)^2
\land
p^d \not\equiv 1 \pmod n
\land
\forall j \in \mathbb{N},\quad j < s \Longrightarrow p^{2^j d} \not\equiv -1 \pmod n.
$$

Thus, $n$ is composite if and only if there is a prime base not exceeding the stated bound for which the strong Miller–Rabin test rejects $n$.

Here $\mathbb{N} = \lbrace 0, 1, 2, \ldots \rbrace$, matching Lean's `ℕ`.

The two directions play different roles:

- $\text{Prime} \to (\text{all pass})$ is unconditional: every prime base satisfying the stated bound passes when $n$ is prime.
- $(\text{all pass}) \to \text{Prime}$ uses GRH: every odd composite $n > 1$ has a rejecting prime base not exceeding the stated bound.

In Lean, the decomposition is determined canonically from $n$. The values $s$, $d$, and the decomposition equation are not additional assumptions of this public criterion.

The public theorem is in namespace `PseudoPrime.PrimeTestBounds.MillerRabin`, in [FromLLS.lean](PseudoPrime/PrimeTestBounds/MillerRabin/FromLLS.lean). The following declaration excerpt omits its proof.

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

The chained implications `Nat.Prime p → (p : ℝ) ≤ ... → ...` require the strong Miller–Rabin pass condition whenever the arbitrary base `p` is prime and satisfies the bound. This explicit power-congruence pass condition is equivalent to `PrimeTest.strongMillerRabinWithBase n p = true`, as proved by [`strongMillerRabinWithBase_eq_true_iff_pass`](PseudoPrime/PrimeTest/MillerRabin/Decomposition.lean).

## Legendre-symbol witnesses under GRH

Let $n > 0$ be odd and not a perfect square.

### A prime witness with symbol different from $1$

Assuming GRH, there exists an odd prime $p$ such that

$$
p \le \max\left\lbrace 5, (\ln\mathrel{} n)^2 \right\rbrace,\qquad
\boxed{\Bigl(\frac{n}{p}\Bigr) \ne 1}
$$

The public theorem is in namespace `PseudoPrime.PseudoSquare`, in [PointwiseWitness.lean](PseudoPrime/PseudoSquare/Bounds/PointwiseWitness.lean).

```lean
theorem exists_prime_ne_one_witness_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1
```

### A quadratic non-residue witness

Assuming GRH, there also exists an odd prime $p$ such that

$$
p \le \Bigl(\ln(4n) + \frac{24}{5}\ln(\ln(4n)) + 3\Bigr)^2,\qquad
\boxed{\Bigl(\frac{n}{p}\Bigr) = -1}
$$

The corresponding public theorem is in the same namespace and file.

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

These Lean statements use `jacobiSym n p`. Since the denominator $p$ is an odd prime, this is exactly the Legendre symbol $\bigl(\frac{n}{p}\bigr)$.

The first result allows $\bigl(\frac{n}{p}\bigr) = 0$ or $\bigl(\frac{n}{p}\bigr) = -1$. The former is equivalent to $p \mid n$; the latter means that $n$ is a quadratic non-residue modulo $p$. The second theorem guarantees the latter case.

## Status of the GRH assumption

GRH is an explicit hypothesis of the conditional results above, represented by [`AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis`](PseudoPrime/AnalyticNumberTheory/GRH/Definition.lean) within namespace `PseudoPrime`.

This project does **not** prove GRH. From GRH, it derives within Lean the results corresponding to the relevant parts of LLS Theorem 1.1, including [`LLS.llsTheorem11S1_of_grh`](PseudoPrime/LLS/Theorem11S1GRH.lean) and [`LLS.llsTheorem11S2_of_grh`](PseudoPrime/LLS/Theorem11S2.lean). These are then combined with the project's algebraic, number-theoretic, and finite-range arguments to obtain the public bounds above.

## Further documentation

- [Miller–Rabin bounds](doc/MillerRabinBoundGrh.md)
- [LLS analytic bounds](doc/LLS.md)
- [Pseudosquares and prime witnesses](doc/PseudoSquare.md)
- [Selfridge search bounds](doc/SelfridgeBoundGrh.md)

These module guides are in Japanese.

## References

### LLS bounds for least non-residues

The logarithmic witness bounds build on the following analytic work:

> Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, “Conditional bounds for the least quadratic non-residue and related problems,” *Mathematics of Computation* **84** (2015), no. 295, 2391–2412. [DOI: 10.1090/S0025-5718-2015-02925-1](https://doi.org/10.1090/S0025-5718-2015-02925-1), [arXiv:1309.3595](https://arxiv.org/abs/1309.3595).

The formalization draws on the relevant results and analytic estimates in this paper, together with the project's arithmetic and finite-range arguments. See the [LLS module guide](doc/LLS.md) for the corresponding formalized results.

### Baillie–PSW and Lucas–Selfridge primality testing

Historical sources underlying the Lucas–Selfridge and Baillie–PSW context include:

> Robert Baillie and Samuel S. Wagstaff, Jr., “Lucas pseudoprimes,” *Mathematics of Computation* **35** (1980), no. 152, 1391–1417. [DOI: 10.1090/S0025-5718-1980-0583518-6](https://doi.org/10.1090/S0025-5718-1980-0583518-6).

> Carl Pomerance, John L. Selfridge, and Samuel S. Wagstaff, Jr., “The pseudoprimes to $25\cdot10^9$,” *Mathematics of Computation* **35** (1980), no. 151, 1003–1026. [DOI: 10.1090/S0025-5718-1980-0572872-7](https://doi.org/10.1090/S0025-5718-1980-0572872-7).

These papers provide historical background for the strong base-2 and Lucas–Selfridge components associated with the Baillie–PSW test, as well as the Selfridge parameter-selection context represented by `selfridgeD`, `firstStopNegOne`, and `firstStopNeOne` in this project. For a later strengthening of the Baillie–PSW test, see Robert Baillie, Andrew Fiori, and Samuel S. Wagstaff, Jr., “[Strengthening the Baillie-PSW primality test](https://arxiv.org/abs/2006.14425v2),” arXiv:2006.14425v2.

Use `bailliePSWWheel30` and `strengthenedBPSWWheel30` for executable BPSW tests. They run base-2 Miller–Rabin first and use factor-detecting Wheel30 Selfridge selection. The strengthened entry agrees with the BFW five-stage specification. Use `BPSW.decideWheel30 n false` or `BPSW.decideWheel30 n true` for certified decisions, and `Execution.runBPSWWheel30` for staged execution. MR-before-square ordering can cost more on square inputs.

### Pseudosquare reference

For background terminology and numerical data, see [OEIS A002189 — Pseudosquares](https://oeis.org/A002189). OEIS A002189 records the classical pseudosquares: for each initial segment of the odd primes, the least positive nonsquare integer congruent to $1 \pmod 8$ that is a nonzero quadratic residue modulo every prime in that segment.

The present project uses the broader domain of positive odd nonsquares in its Selfridge/LLS witness theorems. The OEIS entry is included for reference only.
