/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrefix644
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Signed cutoff terms for the two section 132 comparisons -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii in [322,328] lying in [a,b], bound the signed Chebyshev and
logarithmic cutoff contributions using the endpoints a and b. The negative
deficit uses the upper weight and the positive contribution uses the lower weight. -/
theorem quarter_cutoff_boundary_656 {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b)
    (hr : r ∈ Set.Icc 322 328) :
    -(4 * (9319732 / 100000000) * 70.4 / a) + 4 * (9319731 / 100000000) * (1837 / 1000) / b ≤
      4 * quarterWeight656 (r ^ 2) (r ^ 2) *
        (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
  have hp := ha.trans_le har
  have hl := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) hr.1 2
  have hu := pow_le_pow_left₀ hp.le hr.2 2
  have hψ :=
    quarter_psi_signed_656 ((by norm_num only : (103684 : ℝ) ≤ 322 ^ 2).trans hl)
      (hu.trans (by norm_num only : (328 : ℝ) ^ 2 ≤ 107584))
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  let w := (quarterKernel656.transform 1).re
  change _ ≤ 4 * (w / r) * _
  rw [mul_assoc (4 : ℝ) (w / r)]
  have hw₀ : 0 ≤ w :=
    (by norm_num only : (0 : ℝ) ≤ 9319731 / 100000000).trans quarter_unit_weight_656.1.le
  have hw₁ := div_le_div_of_nonneg_left hw₀ ha har
  have hw₂ := div_le_div_of_nonneg_left hw₀ hp hrb
  have hwU : w / r ≤ (9319732 / 100000000) / a :=
    hw₁.trans (div_le_div_of_nonneg_right quarter_unit_weight_656.2.le ha.le)
  have hwL : (9319731 / 100000000) / b ≤ w / r :=
    (div_le_div_of_nonneg_right quarter_unit_weight_656.1.le (hp.trans_le hrb).le).trans hw₂
  have hneg := mul_le_mul_of_nonpos_right hwU (by norm_num only : (-70.4 : ℝ) ≤ 0)
  have hpos := mul_le_mul_of_nonneg_right hwL (by norm_num only : (0 : ℝ) ≤ (1837 / 1000))
  have hsum :=
    mul_le_mul_of_nonneg_left (add_le_add hψ Analysis.log_two_mul_pi_gt.le) (div_nonneg hw₀ hp.le)
  calc
    _ = 4 * ((9319732 / 100000000 / a) * (-70.4) + (9319731 / 100000000 / b) * (1837 / 1000)) := by
      ring
    _ ≤ 4 * (w / r * (-70.4) + w / r * (1837 / 1000)) :=
      mul_le_mul_of_nonneg_left (add_le_add hneg hpos) (by norm_num only)
    _ ≤ _ := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hsum (by norm_num only : (0 : ℝ) ≤ 4)

end PseudoPrime.PrimeTestBounds.MillerRabin
