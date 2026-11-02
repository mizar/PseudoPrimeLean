/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds

/-! # Four-ninths witness bound for three or more prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least three prime factors counted with
multiplicity has a prime failing base at most `(4 / 9) * log n ^ 2`.
Compare the existing total-factor coefficient with `4 / 9`; this supplies the
three-or-more-factor branch of the global witness theorem. -/
theorem exists_prime_witness_four_ninths_of_factors {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (3 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) := Nat.cast_le.mpr hk
  have hs : (9 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hp : (0 : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by linarith only [hs]
  have hcoeff : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 4 / 9 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 9)).mpr
    nlinarith only [hs]
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
