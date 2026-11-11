/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformLogSquareWitness

/-! # Endpoint transfer for log-square uniform budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a logarithmic interval starting at 2000, endpoint bounds for the reflected
terms and logarithm reduce the log-square witness budget to a rational inequality. -/
theorem uniform_log_square_scalar {a b L r R H J y : ℝ} (ha : 2000 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hr : r = (52223 / 100000 : ℝ) * L) (hlog0 : 0 ≤ Real.log (r ^ 2)) (hlog : Real.log (r ^ 2) ≤ y)
    (hR0 : 0 ≤ quarterReflectedScale r) (hR : quarterReflectedScale r ≤ R)
    (hH : quarterMomentScale r ≤ H) (hJ : quarterEulerClosedTailCap (r ^ 2) ≤ J)
    (hcert :
      (2645975208579 / 48828125000000000 : ℝ) * a +
            (27 / 25 : ℝ) ^ 5 *
              ((3117 / 400 : ℝ) - 7 / 200 - (351 / 200 : ℝ) / ((52223 / 100000 : ℝ) * a) -
                (61 / 3000 : ℝ) * y ^ 2) -
          (2 * b + 3 * (1839 / 1000 : ℝ)) * R -
          H -
          4 * J -
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 ≥
        0) :
    (2 * L) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 8 : ℝ) * L -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - 7 / 200 - (351 / 200 : ℝ) / r -
            (61 / 3000 : ℝ) * Real.log (r ^ 2) ^ 2) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have ha0 : 0 < (52223 / 100000 : ℝ) * a := by nlinarith only [ha]
  have har : (52223 / 100000 : ℝ) * a ≤ r := by
    rw [hr]; nlinarith only [haL]
  have hb0 : 0 ≤ b := by linarith only [ha, haL, hLb]
  have hc := Analysis.log_two_mul_pi_lt
  have hcoef : 2 * L + 3 * Real.log (2 * Real.pi) ≤ 2 * b + 3 * (1839 / 1000 : ℝ) := by
    linarith only [hc, hLb]
  have hcoef0 : 0 ≤ 2 * b + 3 * (1839 / 1000 : ℝ) := by linarith only [hb0]
  have htR := mul_le_mul hcoef hR hR0 hcoef0
  have hinv := one_div_le_one_div_of_le ha0 har
  have hlin :=
    mul_le_mul_of_nonneg_left haL
      (show (0 : ℝ) ≤ 2645975208579 / 48828125000000000 by norm_num only)
  have hd :=
    mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (351 / 200 : ℝ) by norm_num only)
  have hsq :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2)
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (61 / 3000 : ℝ) by norm_num only)
  simp only [hr] at htR hH hJ hd hsq ⊢
  ring_nf at hcert htR hH hJ hlin hd hsq ⊢
  nlinarith only [hcert, htR, hH, hJ, hlin, hd, hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
