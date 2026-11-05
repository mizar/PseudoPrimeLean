/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareUniform371
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeUniform409
public import PseudoPrime.NumberTheory.PrimeFactorPairClassification

/-! # Uniform witness bound for two prime factors with multiplicity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd input with exactly two prime factors counted with multiplicity
and logarithm in `[8, 350]` has a rejecting prime at most `(409/1000) * (log n)²`.
Classify the factors as a prime square or a product of distinct primes and apply the
corresponding certified uniform bound. -/
theorem exists_prime_reject_two_factors_409 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : ArithmeticFunction.cardFactors n = 2) (hlo : (8 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 350) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (409 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hk
  have hpdiv : p ∣ n := by
    rw [hprod]
    exact dvd_mul_right p q
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
  rcases hpq.eq_or_lt with heq | hlt
  · have hsquare : n = p ^ 2 := by rw [hprod, ← heq, pow_two]
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_square_371 hn ho hp hp2 hsquare hGRH.riemann hlo hhi
    have hcoeff : (371 / 1000 : ℝ) * (Real.log n) ^ 2 ≤ (409 / 1000 : ℝ) * (Real.log n) ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
    exact ⟨r, hr, hb.trans hcoeff, hf⟩
  · exact exists_prime_reject_semiprime_409 hn ho hp hq hlt hprod hGRH hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
