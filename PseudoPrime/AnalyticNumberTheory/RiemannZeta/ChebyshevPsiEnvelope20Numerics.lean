/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Endpoint margin for the height-20 ψ envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height 20, the Lee–Nosal target exceeds the main term of
the `1/25` combined-zero envelope by more than `1/100`. Rational logarithm
intervals and bounds for π certify the comparison. -/
theorem envelope20_main_gap :
    (1 / 100 : ℝ) <
      ((20 : ℝ) * (20 - Real.log 20) - Real.pi * 20 -
          4 *
            (((10 : ℝ) - Real.log (5 * Real.pi)) ^ 2 + 2 * ((10 : ℝ) - Real.log (5 * Real.pi)) +
              2) -
          (8 / 25 : ℝ) * Real.pi) /
        (8 * Real.pi) := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 20 4 64 (299572 / 100000) (299574 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ha :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (31415 / 2000) 4 64 (275413 / 100000) (275415 / 100000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ha
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hlog : (275413 / 100000 : ℝ) ≤ Real.log (5 * Real.pi) := by
    have hp : (31415 / 2000 : ℝ) ≤ 5 * Real.pi := by linarith only [hpi]
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 31415 / 2000) hp
    linarith only [h, ha.1]
  have ha0 : 0 ≤ (10 : ℝ) - Real.log (5 * Real.pi) := by
    have hp : 5 * Real.pi ≤ (20 : ℝ) := by nlinarith only [Real.pi_lt_four]
    have h := Real.log_le_log (by nlinarith only [Real.pi_pos] : (0 : ℝ) < 5 * Real.pi) hp
    linarith only [h, hl.2]
  have ha1 : (10 : ℝ) - Real.log (5 * Real.pi) ≤ 10 - 275413 / 100000 := by linarith only [hlog]
  have hm := mul_le_mul ha1 ha1 ha0 (by norm_num only : (0 : ℝ) ≤ 10 - 275413 / 100000)
  apply (lt_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 8 * Real.pi)).2
  nlinarith only [hl.2, ha1, hm, Real.pi_lt_d4]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
