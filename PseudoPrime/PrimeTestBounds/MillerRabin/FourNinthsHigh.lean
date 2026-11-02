/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighSquare
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighSemiprime
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSemiprimeSmall

/-! # High-range four-ninths witnesses for two-factor inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of distinct primes `p < q` with `log n ≥ 1024`
has a prime MR rejecting base within the four-ninths bound. Split at
`log q = (2 / 3) * log n`: the small branch uses the non-Korselt witness,
and the large branch uses the uniform high-range prime-product count. -/
theorem exists_prime_high_distinct_factors {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hq2 : q ≠ 2) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (1024 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log q ≤ (2 / 3 : ℝ) * Real.log n
  · exact semiprime_small_factor_log hn ho hp hq hpq hprod hGRH h
  · exact exists_prime_witness_high_semiprime hn ho hp hq hq2 hprod hGRH.riemann hL (lt_of_not_ge h)

end PseudoPrime.PrimeTestBounds.MillerRabin
