import PseudoPrime.Analysis.ElementaryBounds
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Elementary logarithmic constants and reciprocal-square identities -/

namespace PseudoPrime.Analysis

/-- Expand `log 48` into the logarithms with certified decimal lower bounds. -/
lemma zeroStar_log_forty_eight_eq : Real.log (48 : ℝ) = Real.log 3 + 4 * Real.log 2 := by
  rw [show (48 : ℝ) = 3 * 2 ^ 4 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
  norm_num only

/-- The rational bound `73/20 ≤ log 48`, obtained from lower bounds for `log 2` and `log 3`. -/
lemma zeroStar_log_forty_eight_lower : (73 / 20 : ℝ) ≤ Real.log 48 := by
  rw [zeroStar_log_forty_eight_eq]
  have h :=
    add_lt_add Real.log_three_gt_d9
      (mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num only : (0 : ℝ) < 4))
  exact (lt_of_lt_of_le (by norm_num only) h.le).le

/-- For positive `y ≥ 48`, monotonicity gives `73/20 ≤ log y`. -/
lemma zeroStar_log_lower {y : ℝ} (hy : 48 ≤ y) (hypos : 0 < y) : (73 / 20 : ℝ) ≤ Real.log y := by
  exact
    zeroStar_log_forty_eight_lower.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 48) hypos hy)

/-- The lower bound `1 ≤ log π`, using `3 < π` and the lower bound for `log 3`. -/
lemma zeroStar_log_pi_lower : (1 : ℝ) ≤ Real.log Real.pi := by
  have h3pi :=
    Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only) Real.pi_pos
      (le_of_lt Real.pi_gt_three)
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := le_trans (by norm_num only) Real.log_three_gt_d9.le
  exact hlog3.trans h3pi

/-- The rational upper bound `log 4 ≤ 139/100`, using `log 4 = 2 log 2`. -/
lemma zeroStar_log_four_upper : Real.log (4 : ℝ) ≤ (139 / 100 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
  norm_num only
  have h := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (show (0 : ℝ) ≤ 2 by norm_num only)
  exact h.trans (by norm_num only)

/-- For positive `y ≥ 48`, the reciprocal square `(1 - 1/y)²` is strictly positive. -/
lemma zeroStar_den_pos {y : ℝ} (hy : 48 ≤ y) (hypos : 0 < y) : 0 < (1 - 1 / y) ^ 2 := by
  exact sq_pos_of_pos (sub_pos.mpr ((div_lt_one hypos).2 (lt_of_lt_of_le (by norm_num only) hy)))

/-- For `y ≥ 48`, the square factor multiplying the logarithmic error is nonnegative. -/
lemma zeroStar_square_sub_one_nonneg {y : ℝ} (hy : 48 ≤ y) : 0 ≤ y ^ 2 - 1 := by
  have hy1 : 0 ≤ y - 1 := sub_nonneg.mpr ((by norm_num only : (1 : ℝ) ≤ 48).trans hy)
  rw [show y ^ 2 - 1 = (y - 1) * (y + 1) by ring]
  exact mul_nonneg hy1 (add_nonneg ((by norm_num only : (0 : ℝ) ≤ 48).trans hy) zero_le_one)

/-- Multiplying by the positive square clears the reciprocal square factor explicitly. -/
lemma zeroStar_den_mul_sq {y : ℝ} (hy : y ≠ 0) : (1 - 1 / y) ^ 2 * y ^ 2 = (y - 1) ^ 2 := by
  rw [← mul_pow, sub_mul, one_mul, one_div_mul_cancel hy]

end PseudoPrime.Analysis
