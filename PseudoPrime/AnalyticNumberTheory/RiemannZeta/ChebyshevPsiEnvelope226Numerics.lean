/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Endpoint margin for the logarithmic Chebyshev envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At `L = 113/5`, the Lee–Nosal normalized target exceeds the main part
of the proposed combined-zero envelope by more than `11/2000`. Rational
logarithm intervals and a bound for π certify the endpoint comparison. -/
theorem envelope226_main_gap :
    (11 / 2000 : ℝ) <
      ((113 / 5 : ℝ) * ((113 / 5 : ℝ) - Real.log (113 / 5)) - (10 / 3 : ℝ) * (113 / 5) -
          4 *
            (((113 / 10 : ℝ) - Real.log (113 / 6)) ^ 2 + 2 * ((113 / 10 : ℝ) - Real.log (113 / 6)) +
              2) -
          (16 / 5 : ℝ) * Real.pi) /
        (8 * Real.pi) := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (113 / 5) 5 64 (311794 / 100000) (311796 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ha :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (113 / 6) 5 64 (293562 / 100000) (293564 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ha
  apply (lt_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 8 * Real.pi)).2
  have ha0 : 0 ≤ (113 / 10 : ℝ) - Real.log (113 / 6) := by linarith only [ha.2]
  have ha1 : (113 / 10 : ℝ) - Real.log (113 / 6) ≤ 113 / 10 - 293562 / 100000 := by
    linarith only [ha.1]
  have hm := mul_le_mul ha1 ha1 ha0 (by norm_num only : (0 : ℝ) ≤ 113 / 10 - 293562 / 100000)
  nlinarith only [hl.2, ha1, hm, Real.pi_lt_d4]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
