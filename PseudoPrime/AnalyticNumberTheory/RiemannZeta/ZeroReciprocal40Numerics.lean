/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Height-40 reciprocal-sum entrance constant -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The height-40 entrance constant for the reciprocal zero sum is at most
`2/5`. Certified rational logarithm intervals and a bound on π establish
the comparison without a table of zeros. -/
theorem reciprocal_40_entrance_le :
    (1 / Real.pi) * (Real.log 40 - Real.log (2 * Real.pi) - 1) + (7 / 4 : ℝ) / 40 -
          (1 / Real.pi) / 2 * (Real.log 40 - Real.log (2 * Real.pi)) ^ 2 +
        ((3 / 4 : ℝ) * (Real.log 40 + 1) + 16 / 5) / 40 +
        (2 / 5 : ℝ) / (2 * 40 ^ 2) +
        (231 / 5000 : ℝ) * (640401 / 64000) ≤
      2 / 5 := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 40 5 64 (368887 / 100000) (368888 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (18377 / 10000) (18379 / 10000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hcu : Real.log (2 * Real.pi) ≤ (18379 / 10000 : ℝ) := by
    have hp : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hl := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp
    linarith only [hl, hc.2]
  have hu : (185097 / 100000 : ℝ) ≤ Real.log 40 - Real.log (2 * Real.pi) := by
    linarith only [hL.1, hcu]
  have hf :
    Real.log 40 - Real.log (2 * Real.pi) - 1 - (Real.log 40 - Real.log (2 * Real.pi)) ^ 2 / 2 ≤
      (185097 / 100000 : ℝ) - 1 - (185097 / 100000 : ℝ) ^ 2 / 2 := by
    have hs := sq_nonneg (Real.log 40 - Real.log (2 * Real.pi) - 185097 / 100000)
    nlinarith only [hu, hs]
  have hp0 : 0 ≤ 1 / Real.pi := one_div_nonneg.mpr Real.pi_pos.le
  have hp : (10000 / 31416 : ℝ) ≤ 1 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_lt_d4]
  have hmul := mul_le_mul_of_nonneg_left hf hp0
  have hneg : (185097 / 100000 : ℝ) - 1 - (185097 / 100000 : ℝ) ^ 2 / 2 ≤ 0 := by norm_num only
  have hmul2 := mul_le_mul_of_nonpos_right hp hneg
  nlinarith only [hmul, hmul2, hL.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
