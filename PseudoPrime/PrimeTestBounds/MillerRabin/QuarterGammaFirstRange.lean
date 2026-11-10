/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaFirstNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaLogLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaLogUpper

/-! # First Gamma-pole correction on the final bounded range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On radii from `180` through `200`, the first Gamma-pole correction at
cutoff `r²` is at least `19/500`. The independent logarithm certificates
place its shifted scale in the verified endpoint interval. -/
theorem quarter_first_correction_180_200 {r : ℝ} (hr : 180 ≤ r) (hR : r ≤ 200) :
    (19 / 500 : ℝ) ≤ quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hlo : (32400 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 180)]
  have hhi : r ^ 2 ≤ (40000 : ℝ) := by nlinarith only [hr, hR, sq_nonneg (r - 200)]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 32400) hlo
  have hu := Real.log_le_log (sq_pos_of_pos hr0) hhi
  apply quarter_first_correction_13_1325
  · linarith only [quarter_gamma_log_lower, hl]
  · linarith only [quarter_gamma_log_upper, hu]

end PseudoPrime.PrimeTestBounds.MillerRabin
