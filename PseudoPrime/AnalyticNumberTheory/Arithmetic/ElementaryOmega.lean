/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimorialEnvelope
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# An elementary (Robin-free) bound on the number of distinct prime factors

For odd `n` with `m := n.primeFactors.card`, this file proves
`2^m * m! ≤ oddPrimorial m ≤ n`. The zero-indexed odd prime `oddPrime j` is at least
`2j + 3`, so comparison with the factors `2(j + 1)` gives the factorial bound.

`ElementaryOmegaTail` combines this bound with Stirling's logarithmic inequality to prove
`ω(4n) ≤ (7/5) * log(4n) / loglog(4n)` when `m ≥ 163`.
`ElementaryOmegaFiniteCertificates` supplies the remaining indices for odd `n ≥ 750`.
The declarations here require only oddness and elementary prime-factor arithmetic.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The `k`-th odd prime is at least the `k`-th odd number `2k + 3`
(`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is `0`-indexed starting at `3`).
Proved by induction using that consecutive odd primes are strictly increasing and every
`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is odd:
if `PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime (k+1)`
  `> PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime k ≥ 2k+3` then
`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime (k+1) ≥ 2k+4`,
and being odd it cannot equal the even number `2k+4`, so it is
`≥ 2k+5 = 2(k+1)+3`. -/
theorem oddPrime_ge (k : ℕ) :
    2 * k + 3 ≤ oddPrime k := by
  induction k with
  | zero => rw [oddPrime_zero]
  | succ k
    ih =>
    have hmono :
      oddPrime k <
        oddPrime (k + 1) :=
      oddPrime_strictMono (Nat.lt_succ_self k)
    obtain ⟨j, hj⟩ := oddPrime_odd (k + 1)
    omega

/-- The odd primorial dominates `2^m * m!`: termwise, the `j`-th odd prime (`≥ 2j+3`, in particular
`> 2(j+1)`) exceeds the `j`-th even number `2(j+1)` used to build `2^m * m!`. -/
theorem oddPrimorial_ge_pow_mul_factorial (m : ℕ) :
    2 ^ m * Nat.factorial m ≤ oddPrimorial m := by
  induction m with
  | zero =>
    norm_num only [oddPrimorial_zero, pow_zero,
      Nat.factorial_zero, one_mul]
  | succ m
    ih =>
    rw [oddPrimorial_succ, Nat.factorial_succ, pow_succ]
    have hle : 2 * (m + 1) ≤ oddPrime m := by
      have := oddPrime_ge m; omega
    have h3 :
      (2 ^ m * Nat.factorial m) * (2 * (m + 1)) ≤
        oddPrimorial m *
          oddPrime m :=
      Nat.mul_le_mul ih hle
    calc
      2 ^ m * 2 * ((m + 1) * Nat.factorial m) = (2 ^ m * Nat.factorial m) * (2 * (m + 1)) := by ring
      _ ≤
          oddPrimorial m *
            oddPrime m :=
        h3

/-- An odd number with `m` distinct prime factors is at least `2^m * m!`. -/
theorem pow_mul_factorial_le_of_card_primeFactors {n : ℕ} (hn : Odd n) :
    2 ^ n.primeFactors.card * Nat.factorial n.primeFactors.card ≤ n :=
  (oddPrimorial_ge_pow_mul_factorial
        n.primeFactors.card).trans
    (oddPrimorial_le_of_card_primeFactors hn)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
