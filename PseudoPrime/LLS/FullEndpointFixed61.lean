/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEvenPolynomial

/-! # A fixed even-endpoint gap at radius 49/6 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The logarithm of 49/6 is greater than 10499/5000.
Factor it as eight times 49/48 and use the rational lower bound for log two
and log u>=1-1/u. This needs no new transcendental certificate. -/
theorem endpoint61_log_lower : (10499 / 5000 : ℝ) < Real.log (49 / 6 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 48 / 49)
  have hi : Real.log (48 / 49 : ℝ) = -Real.log (49 / 48 : ℝ) := by
    rw [← Real.log_inv]
    congr 1
    norm_num only
  have he : Real.log (49 / 6 : ℝ) = 3 * Real.log 2 + Real.log (49 / 48 : ℝ) := by
    have hr : (49 / 6 : ℝ) = 2 ^ 3 * (49 / 48) := by norm_num only
    rw [hr, Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  linarith only [h, hi, he, Real.log_two_gt_d9]

/-- At L=286/25 and radius 49/6, the exact even gap is the displayed quadratic in z.
Expand the existing gap definition and normalize rational coefficients.
The identity permits a rational anchor followed by logarithmic monotonicity. -/
theorem endpoint61_gap_eq (z : ℝ) :
    fullEndpointEvenExactComparisonGap (286 / 25) (2096 / 1831) (49 / 6) z =
      (731 / 2 : ℝ) * z ^ 2 + (1902512433377 / 1977480000 : ℝ) * z -
        8599664769551 / 2372976000 := by
  dsimp only [fullEndpointEvenExactComparisonGap]
  ring

/-- For L<=286/25, the exact even gap at radius 49/6 is positive.
Use the logarithmic lower bound in the quadratic anchor, then antitonicity in L.
This is the analytic input for the fixed prime-base bound 61. -/
theorem endpoint61_gap_pos {L : ℝ} (hL : L ≤ 286 / 25) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) (49 / 6) (Real.log (49 / 6 : ℝ)) := by
  have hz := endpoint61_log_lower.le
  have hz0 : 0 ≤ Real.log (49 / 6 : ℝ) := by linarith only [hz]
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 10499 / 5000) hz0).mpr hz
  have hg :
    0 <
      fullEndpointEvenExactComparisonGap (286 / 25) (2096 / 1831) (49 / 6)
        (Real.log (49 / 6 : ℝ)) := by
    rw [endpoint61_gap_eq]
    nlinarith only [hz, hs]
  exact hg.trans_le (fullEndpointEvenExactComparisonGap_antitone_level (by norm_num only) hz0 hL)

end PseudoPrime.LLS.PaperStatements
