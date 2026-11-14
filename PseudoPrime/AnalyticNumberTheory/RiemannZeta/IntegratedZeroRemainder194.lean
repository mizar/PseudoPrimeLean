/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbelRH
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Uniform bound for the integrated zero-count remainder -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For T at least 4000, the integrated zero-count remainder is bounded
by 3/1000000. A logarithmic tangent bound reduces the comparison to a
quadratic inequality. -/
theorem integrated_zero_remainder_le {T : ℝ} (hT : 4000 ≤ T) :
    ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
          1 / 10) /
        T ^ 2 ≤
      3 / 1000000 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 400 8 64 (5991 / 1000) (5992 / 1000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have htangent := Real.log_le_sub_one_of_pos (div_pos hT0 (by norm_num only : (0 : ℝ) < 400))
  rw [Real.log_div hT0.ne' (by norm_num only : (400 : ℝ) ≠ 0)] at htangent
  have hlog : Real.log T ≤ 5 + T / 400 := by linarith only [htangent, hc.2]
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 3)
    linarith only [h]
  have hnum :
    (29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
        (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
        1 / 10 ≤
      26 + T / 250 := by
    linarith only [hlog, hlog3, hT]
  apply (div_le_iff₀ (pow_pos hT0 2)).2
  have hs := sq_nonneg (T - 4000)
  nlinarith only [hnum, hT, hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
