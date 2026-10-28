/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeSubgroupBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaComparison

/-! # Conductor-free Gamma upper bounds for Miller-Rabin prime witnesses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- At any real scale and cutoff, if every prime divisor of q exceeds floor X,
the finite nonunit exponential sum is zero. Every retained positive noncoprime
index would have a common prime divisor below the cutoff, a contradiction.
No RH or positivity of the scale is needed. This removes finite modulus loss
under universal passage of small Miller-Rabin prime bases. -/
theorem commonFactorExponentialSum_eq_zero_of_prime_divisors_gt {q : ℕ} {X : ℝ}
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p) (x : ℝ) :
    commonFactorExponentialSum x X q = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hm := Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1
  obtain ⟨p, hp, hpk, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp (Finset.mem_filter.mp hk).2
  exact False.elim ((not_lt_of_ge ((Nat.le_of_dvd hm.1 hpk).trans hm.2)) (hdiv p hp hpq))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
