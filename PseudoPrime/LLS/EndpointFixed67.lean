/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointFourStep
/-! # Sharper fixed endpoint anchors -/
@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y>0, log y>=3 log 2+1-8/y. Apply log u<=u-1 at u=8/y.
This reusable bound supplies the two rational logarithm anchors. -/
theorem endpoint_log_lower {y : ℝ} (hy : 0 < y) :
    3 * Real.log 2 + 1 - 8 / y ≤ Real.log y := by
  have h := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 8) hy)
  rw [Real.log_div (by norm_num only) hy.ne',
    show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- Given a positive rational gap anchor and nonnegative quadratic coefficients,
transfer positivity to log y and then every L<=the anchor level.
Square monotonicity and conductor-level antitonicity justify both transfers. -/
theorem endpoint_gap_from_quad {L L₀ y z₀ a b : ℝ} (hL : L ≤ L₀) (hy : 1 ≤ y)
    (hz0 : 0 ≤ z₀) (hz : z₀ ≤ Real.log y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoly : ∀ z : ℝ,
      fullEndpointEvenExactComparisonGap L₀ (2096 / 1831) y z -
        fullEndpointEvenExactComparisonGap L₀ (2096 / 1831) y z₀ =
          a * (z ^ 2 - z₀ ^ 2) + b * (z - z₀))
    (hanchor : 0 < fullEndpointEvenExactComparisonGap L₀ (2096 / 1831) y z₀) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) y (Real.log y) := by
  have hzpos := hz0.trans hz
  have hsq := (sq_le_sq₀ hz0 hzpos).mpr hz
  have h1 := mul_nonneg ha (sub_nonneg.mpr hsq)
  have h2 := mul_nonneg hb (sub_nonneg.mpr hz)
  have hident := hpoly (Real.log y)
  have hgap : 0 < fullEndpointEvenExactComparisonGap L₀ (2096 / 1831) y (Real.log y) := by
    linarith only [hanchor, hident, h1, h2]
  exact hgap.trans_le (fullEndpointEvenExactComparisonGap_antitone_level hy hzpos hL)

/-- The logarithm at 1637/200 is at least 1051/500.
Combine the reciprocal logarithm lower bound with the certified bound for log two. -/
theorem endpoint61Sharp_log_lower : (1051 / 500 : ℝ) ≤ Real.log (1637 / 200 : ℝ) := by
  have h := endpoint_log_lower (by norm_num only : (0 : ℝ) < 1637 / 200)
  norm_num only at h
  linarith only [h, Real.log_two_gt_d9]

/-- For L<=1147/100, the exact endpoint gap at radius 1637/200 is positive.
Its rational anchor and positive quadratic coefficients permit logarithm transfer.
This supplies the extended fixed prime-witness bound 61. -/
theorem endpoint61Sharp_gap_pos {L : ℝ} (hL : L ≤ 1147 / 100) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) (1637 / 200)
      (Real.log (1637 / 200 : ℝ)) := by
  apply endpoint_gap_from_quad (z₀ := 1051 / 500) (a := 7344507 / 20000)
    (b := 708540428363131 / 732400000000)
    hL (by norm_num only) (by norm_num only) endpoint61Sharp_log_lower
    (by norm_num only) (by norm_num only)
  · intro z
    dsimp only [fullEndpointEvenExactComparisonGap]
    ring
  · norm_num only [fullEndpointEvenExactComparisonGap]

/-- The logarithm at 337/40 is at least 10649/5000.
Combine the reciprocal logarithm lower bound with the certified bound for log two. -/
theorem endpoint67_log_lower : (10649 / 5000 : ℝ) ≤ Real.log (337 / 40 : ℝ) := by
  have h := endpoint_log_lower (by norm_num only : (0 : ℝ) < 337 / 40)
  norm_num only at h
  linarith only [h, Real.log_two_gt_d9]

/-- For L<=47/4, the exact endpoint gap at radius 337/40 is positive.
Its rational anchor and positive quadratic coefficients permit logarithm transfer.
This supplies the fixed prime-witness bound 67. -/
theorem endpoint67_gap_pos {L : ℝ} (hL : L ≤ 47 / 4) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) (337 / 40)
      (Real.log (337 / 40 : ℝ)) := by
  apply endpoint_gap_from_quad (z₀ := 10649 / 5000) (a := 312147 / 800)
    (b := 30849497726131 / 29296000000)
    hL (by norm_num only) (by norm_num only) endpoint67_log_lower
    (by norm_num only) (by norm_num only)
  · intro z
    dsimp only [fullEndpointEvenExactComparisonGap]
    ring
  · norm_num only [fullEndpointEvenExactComparisonGap]

end PseudoPrime.LLS.PaperStatements
