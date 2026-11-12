/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions265
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Normalized Chebyshev remainder from logarithmic height twenty-six and one half -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height at least 53/2, the shifted logarithms are nonnegative
or bounded by half the height, as needed in the polynomial remainder bound. -/
private theorem scale265_log_bounds {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    0 ≤ L / 2 - Real.log L ∧
      L / 2 - Real.log L + Real.log (2 * Real.pi) ≤ L / 2 ∧ L / 2 - Real.log L ≤ L / 2 := by
  have hl : 0 < L := by linarith only [hL]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have h2 : Real.log (2 : ℝ) < 1 := by linarith only [Real.log_two_lt_d9]
  have hloghalf := Real.log_le_sub_one_of_pos (show 0 < L / 2 by linarith only [hl])
  rw [Real.log_div hl.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hloghalf
  have hpi : (2 * Real.pi : ℝ) ≤ L := by linarith only [Real.pi_lt_four, hL]
  have hlogpi := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hpi
  constructor
  · linarith only [hloghalf, h2]
  constructor
  · linarith only [hlogpi]
  · linarith only [hlog]

private theorem scale265_remainder_numerator {L a z : ℝ} (hL : (53 / 2 : ℝ) ≤ L) (ha : 0 ≤ a)
    (hau : a ≤ L / 2) (hzu : z ≤ L / 2) :
    L * a ^ 2 * Real.pi⁻¹ ^ 2 / 4 + L * Real.pi⁻¹ / 2 + L * z * Real.pi⁻¹ ^ 2 + 3 ≤
      L ^ 3 / 48 + 3 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hi0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  have hi : Real.pi⁻¹ ≤ (1 / 3 : ℝ) := by
    have h := (inv_le_inv₀ Real.pi_pos (by norm_num only : (0 : ℝ) < 3)).2 Real.pi_gt_three.le
    simpa only [one_div] using h
  have hi2 : Real.pi⁻¹ ^ 2 ≤ (1 / 9 : ℝ) := by nlinarith only [hi, hi0]
  have ha2 : a ^ 2 ≤ L ^ 2 / 4 := by nlinarith only [ha, hau, hL]
  have hmul :=
    mul_le_mul ha2 hi2 (sq_nonneg _) (div_nonneg (sq_nonneg L) (by norm_num only) : 0 ≤ L ^ 2 / 4)
  have hmL := mul_le_mul_of_nonneg_left hmul hL0
  have hzmul := mul_le_mul_of_nonneg_right hzu (sq_nonneg Real.pi⁻¹)
  have hzL := mul_le_mul_of_nonneg_left hzmul hL0
  have hp2 :=
    mul_le_mul_of_nonneg_left hi2
      (show (0 : ℝ) ≤ L ^ 2 / 2 from div_nonneg (sq_nonneg L) (by norm_num only))
  have hp1 := mul_le_mul_of_nonneg_left hi hL0
  have hl2 : L / 6 ≤ L ^ 3 / 144 := by
    have hh := mul_nonneg hL0 (show 0 ≤ L ^ 2 - 24 by nlinarith only [hL])
    nlinarith only [hh]
  have hl3 : L ^ 2 / 18 ≤ L ^ 3 / 144 := by
    have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 8 by linarith only [hL])
    nlinarith only [hh]
  nlinarith only [hmL, hzL, hp2, hp1, hl2, hl3]

/-- For `L ≥ 53/2`, the explicit remainder in the normalized Chebyshev bound
is at most `1/100`. Bound its numerator by a cubic and compare that cubic
with the exponential lower bound. -/
theorem scale265_remainder_le {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    let a := L / 2 - Real.log L
    let c := Real.log (2 * Real.pi)
    let δ := L / (Real.pi * Real.exp (L / 2))
    δ * a ^ 2 / (4 * Real.pi) + δ / 2 + δ * (a + c) / Real.pi + 3 / Real.exp (L / 2) ≤ 1 / 100 := by
  dsimp only
  have hlog := scale265_log_bounds hL
  have hn := scale265_remainder_numerator hL hlog.1 hlog.2.2 hlog.2.1
  have he := Real.exp_pos (L / 2)
  have heq :
    (L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L) ^ 2 / (4 * Real.pi) +
        (L / (Real.pi * Real.exp (L / 2))) / 2 +
        (L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) /
          Real.pi +
        3 / Real.exp (L / 2) =
      (L * (L / 2 - Real.log L) ^ 2 * Real.pi⁻¹ ^ 2 / 4 + L * Real.pi⁻¹ / 2 +
          L * (L / 2 - Real.log L + Real.log (2 * Real.pi)) * Real.pi⁻¹ ^ 2 +
          3) /
        Real.exp (L / 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  have hdiv := div_le_div_of_nonneg_right hn he.le
  apply hdiv.trans
  apply (div_le_iff₀ he).2
  have hc := exp_half_cubic265 hL
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ (53 / 2 : ℝ) by norm_num only) hL 3
  norm_num only at hpow
  nlinarith only [hc, hpow]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
