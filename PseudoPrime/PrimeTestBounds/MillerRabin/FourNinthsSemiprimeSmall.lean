/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSemiprimeBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MarkedFactorLogBounds

/-! # The small-factor-log branch for semiprime inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, for `n = p * q` with primes `p < q`, the branch
`log q ≤ (2 / 3) * log n` has a prime MR witness within the four-ninths bound.
The larger factor violates the Korselt divisibility condition, so its existing
local logarithmic witness bound applies and can be squared. -/
theorem semiprime_small_factor_log {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := by
    rw [hprod]
    exact dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_nonKorselt_factor_log_sq hn ho hq hdiv hbad hGRH
  have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg q) hsmall 2
  have hbound : (Real.log q) ^ 2 ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hsq]
  exact ⟨r, hr, hb.trans hbound, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
