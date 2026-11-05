/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourCumulative

/-! # Absorption scales for the reduced-contour cumulative history -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the first entrance, the paired history is bounded by the global four-ninths scale. -/
theorem pairedCap_entry_upper : pairedCumulativeCap 80000 ≤ (4 / 9 : ℝ) * 80000 ^ 2 := by
  have hA := pairedAlpha_bounds (high_log_twice_ge_22 (by norm_num only : (70000 : ℝ) ≤ 80000))
  have ha : (pairedAlpha (2 * Real.log 80000)) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by linarith only [hA.1]) hA.2 2
  unfold pairedCumulativeCap
  apply max_le
  · norm_num only
  · nlinarith only [ha]

/-- The first quadratic has absorbed its entrance history by scale 100000. -/
theorem reducedHistory1_absorbed {L : ℝ} (hL : 100000 ≤ L) :
    reducedHistory1 L ≤ (1057 / 2500 : ℝ) * L ^ 2 := by
  apply reducedStep_absorbed (by norm_num only) (by norm_num only) hL
  exact pairedCap_entry_upper.trans (by norm_num only)

/-- The coefficient 39/100 has absorbed the preceding history by scale 210000000. -/
theorem reducedHistory2_absorbed {L : ℝ} (hL : 210000000 ≤ L) :
    reducedHistory2 L ≤ (39 / 100 : ℝ) * L ^ 2 := by
  apply reducedStep_absorbed (by norm_num only) (by norm_num only) hL
  exact (reducedHistory1_absorbed (by norm_num only)).trans (by norm_num only)

/-- The coefficient 161/500 has absorbed the preceding history by scale 551000000. -/
theorem reducedHistory3_absorbed {L : ℝ} (hL : 551000000 ≤ L) :
    reducedHistory3 L ≤ (161 / 500 : ℝ) * L ^ 2 := by
  apply reducedStep_absorbed (by norm_num only) (by norm_num only) hL
  exact (reducedHistory2_absorbed (by norm_num only)).trans (by norm_num only)

/-- The coefficient 3/10 has absorbed the preceding history by scale 1037000000. -/
theorem reducedHistory4_absorbed {L : ℝ} (hL : 1037000000 ≤ L) :
    reducedHistory4 L ≤ (3 / 10 : ℝ) * L ^ 2 := by
  apply reducedStep_absorbed (by norm_num only) (by norm_num only) hL
  exact (reducedHistory3_absorbed (by norm_num only)).trans (by norm_num only)

/-- The coefficient 71/250 has absorbed the preceding history by scale 5140000000. -/
theorem reducedHistory5_absorbed {L : ℝ} (hL : 5140000000 ≤ L) :
    reducedHistory5 L ≤ (71 / 250 : ℝ) * L ^ 2 := by
  apply reducedStep_absorbed (by norm_num only) (by norm_num only) hL
  exact (reducedHistory4_absorbed (by norm_num only)).trans (by norm_num only)

/-- The Gaussian candidate absorbs the fixed history by scale 30100000000.
A rational slope bound covers the entry and monotonicity extends it to later scales. -/
theorem reducedGaussianHistory_absorbed {L : ℝ} (hL : 30100000000 ≤ L) :
    reducedGaussianHistory L ≤ (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
  have hU : (30000000000 : ℝ) ≤ 30100000000 := by norm_num only
  have hA := earlyGaussian_slope_lower 30100000000 hU
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) hA 2
  have hentry :
    reducedHistory5 30000000000 ≤
      (21 / 10 : ℝ) * (adaptiveGaussianA 30100000000 * 30100000000) ^ 2 := by
    have hh := reducedHistory5_absorbed (by norm_num only : (5140000000 : ℝ) ≤ 30000000000)
    rw [mul_pow]
    nlinarith only [hh, hs]
  have ha : 0 ≤ adaptiveGaussianA 30100000000 := by linarith only [hA]
  have hscale := earlyGaussian_scaled_mono hU hL
  have hs' := pow_le_pow_left₀ (mul_nonneg ha (by norm_num only)) hscale 2
  have hh := mul_le_mul_of_nonneg_left hs' (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  exact (min_le_right _ _).trans (max_le (hentry.trans hh) le_rfl)

end PseudoPrime.PrimeTestBounds.MillerRabin
