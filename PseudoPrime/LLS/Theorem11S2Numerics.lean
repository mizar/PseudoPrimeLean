/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.WeightedComparison
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Numerical separation for Theorem 1.1 S2 -/

namespace PseudoPrime.LLS

/-- Above `8`, the logarithm is at least `2`, using the rational certificate for `log 2`.
This supplies the positive coefficients in the S2 zero-mass comparison. -/
theorem theorem11S2_two_le_log {y : ℝ} (hy : 8 ≤ y) : 2 ≤ Real.log y := by
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hy
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow] at hl
  norm_num only at hl
  linarith only [hl, Real.log_two_gt_d9]

/-- The rationalized reciprocal numerator is below the desired S2 zero-mass bound.
On `[8,12]` use `log y ≥ 2`; above `12` use the certified lower bound `247/100`.
The result retains the paper's saving `4/7`. -/
theorem theorem11S2_zeroMass_numerator_le {y : ℝ} (hy : 8 ≤ y) :
    1 / 2 * y - 2 * Real.log y + 17 / 20 ≤
      (1 / 2 * y - Real.log y - 4 / 7) * (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hL := theorem11S2_two_le_log hy
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hypos)
  field_simp
  by_cases hy12 : y ≤ 12
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hL)
      (show 0 ≤ y ^ 2 + 2 * y - 1 by nlinarith only [sq_nonneg y, hy]),
      mul_nonneg hypos.le (sub_nonneg.mpr hy12), hy]
  · have hl := (Analysis.log_ge_twelve_lower (le_of_not_ge hy12)).le
    nlinarith only [mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ y ^ 2 + 2 * y - 1 by nlinarith only [sq_nonneg y, hy]), sq_nonneg y, hy]

/-- The common reciprocal estimate with zero defect implies the paper's bound for `b`.
The conductor logarithm is bounded by `y-1`; only nonnegative coefficients are relaxed.
This is the scalar interface consumed at `y = log q`. -/
theorem theorem11S2_zeroMass_le {y F R b : ℝ} (hy : 8 ≤ y) (hF : F ≤ y - 1)
    (hR : 2 * Real.log y - 8 / 5 ≤ R)
    (hb : (1 - 1 / y) ^ 2 * b ≤ (1 / 2) * (1 - 1 / y ^ 2) * F - R - 1 / 4) :
    b ≤ 1 / 2 * y - Real.log y - 4 / 7 := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hsq : 1 ≤ y ^ 2 := by nlinarith only [hy]
  have hfac : 0 ≤ 1 - 1 / y ^ 2 := sub_nonneg.mpr ((div_le_one₀ (sq_pos_of_pos hypos)).mpr hsq)
  have hmul := mul_le_mul_of_nonneg_left hF
    (mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num only) hfac)
  have hdrop := mul_le_mul_of_nonneg_right
    (sub_le_self 1 (show 0 ≤ 1 / y ^ 2 by positivity))
    (show 0 ≤ y - 1 by linarith only [hy])
  have hnum := theorem11S2_zeroMass_numerator_le hy
  have hden : 0 < (1 - 1 / y) ^ 2 := sq_pos_of_pos
    (sub_pos.mpr ((div_lt_one hypos).mpr (lt_of_lt_of_le (by norm_num only) hy)))
  apply le_of_mul_le_mul_left _ hden
  nlinarith only [hb, hmul, hdrop, hR, hnum]

/-- The common logarithmic upper estimate and the S2 zero-mass bound give the
paper's upper envelope. The generic error `-11/4` is retained in the calculation. -/
theorem theorem11S2_logWeighted_le {y F S b : ℝ} (hy : 8 ≤ y) (hF : F ≤ y)
    (hb : b ≤ 1 / 2 * y - Real.log y - 4 / 7)
    (hS : S ≤ (2 * y + 2 + 2 * Real.log y) * b + F * Real.log y - 11 / 4) :
    S ≤ y ^ 2 - y / 7 - 4 * Real.log y - 8 / 7 := by
  have hL := theorem11S2_two_le_log hy
  have hC : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hL]
  have hm := mul_le_mul_of_nonneg_left hb hC
  have hf := mul_le_mul_of_nonneg_right hF (le_trans (by norm_num only) hL)
  nlinarith only [hS, hm, hf, sq_nonneg (Real.log y - 1), hL]

/-- The Riemann lower envelope strictly exceeds the S2 upper envelope for `y ≥ 8`.
Certified constants `β ≤ 1/16` and `log(2π) < 1839/1000` preserve a strict gap. -/
theorem theorem11S2_upper_lt_riemann_lower {y : ℝ} (hy : 8 ≤ y) :
    y ^ 2 - y / 7 - 4 * Real.log y - 8 / 7 < riemannLogLowerAt (y ^ 2) := by
  have hL := theorem11S2_two_le_log hy
  have hm := mul_le_mul_of_nonneg_right
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
    (show 0 ≤ y + 1 by linarith only [hy])
  have hp := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
    (show 0 ≤ Real.log y by linarith only [hL])
  rw [riemannLogLowerAt, Real.sqrt_sq (by linarith only [hy]), Real.log_pow]
  norm_num only
  nlinarith only [hm, hp, hy, hL]

end PseudoPrime.LLS
