/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Numerical entrance bound for reciprocal zero sums -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The height-100 entrance constant is at most `-11446/10000`. Rational
logarithm intervals and a bound for π give the sharper comparison needed
for the `1/25` reciprocal-sum constant. -/
theorem reciprocal_100_entrance_sharp :
    (1 / Real.pi) * (Real.log 100 - Real.log (2 * Real.pi) - 1) + (7 / 4 : ℝ) / 100 - 58 / 100 -
          (1 / Real.pi) / 2 * (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 +
        ((3 / 4 : ℝ) * (Real.log 100 + 1) + 16 / 5) / 100 +
        (2 / 5 : ℝ) / (2 * 100 ^ 2) ≤
      -(11446 / 10000 : ℝ) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 100 6 64 (460517 / 100000) (460518 / 100000) = true
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
  have hu : (276727 / 100000 : ℝ) ≤ Real.log 100 - Real.log (2 * Real.pi) := by
    linarith only [hL.1, hcu]
  have hf :
    Real.log 100 - Real.log (2 * Real.pi) - 1 - (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 / 2 ≤
      (276727 / 100000 : ℝ) - 1 - (276727 / 100000 : ℝ) ^ 2 / 2 := by
    have hs := sq_nonneg (Real.log 100 - Real.log (2 * Real.pi) - 276727 / 100000)
    nlinarith only [hu, hs]
  have hp0 : 0 ≤ 1 / Real.pi := one_div_nonneg.mpr Real.pi_pos.le
  have hp : (10000 / 31416 : ℝ) ≤ 1 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_lt_d4]
  have hmul := mul_le_mul_of_nonneg_left hf hp0
  have hneg : (276727 / 100000 : ℝ) - 1 - (276727 / 100000 : ℝ) ^ 2 / 2 ≤ 0 := by norm_num only
  have hmul2 := mul_le_mul_of_nonpos_right hp hneg
  nlinarith only [hmul, hmul2, hL.2]

/-- The entrance constant in the height-100 reciprocal zero sum is at most
`-143/125`. Rational logarithm certificates and the explicit bound for pi
supply the comparison without importing a zero table. -/
theorem reciprocal_100_entrance_le :
    (1 / Real.pi) * (Real.log 100 - Real.log (2 * Real.pi) - 1) + (7 / 4 : ℝ) / 100 - 58 / 100 -
          (1 / Real.pi) / 2 * (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 +
        ((3 / 4 : ℝ) * (Real.log 100 + 1) + 16 / 5) / 100 +
        (2 / 5 : ℝ) / (2 * 100 ^ 2) ≤
      -(143 / 125 : ℝ) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 100 6 64 (46051 / 10000) (46053 / 10000) = true from
        by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (1837 / 1000) (1838 / 1000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hcu : Real.log (2 * Real.pi) ≤ (1838 / 1000 : ℝ) := by
    have hp : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hl := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp
    linarith only [hl, hc.2]
  have hu : (27671 / 10000 : ℝ) ≤ Real.log 100 - Real.log (2 * Real.pi) := by
    linarith only [hL.1, hcu]
  have hf :
    Real.log 100 - Real.log (2 * Real.pi) - 1 - (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 / 2 ≤
      (27671 / 10000 : ℝ) - 1 - (27671 / 10000 : ℝ) ^ 2 / 2 := by
    have hs := sq_nonneg (Real.log 100 - Real.log (2 * Real.pi) - 27671 / 10000)
    nlinarith only [hu, hs]
  have hp0 : 0 ≤ 1 / Real.pi := one_div_nonneg.mpr Real.pi_pos.le
  have hp : (10000 / 31416 : ℝ) ≤ 1 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_lt_d4]
  have hmul := mul_le_mul_of_nonneg_left hf hp0
  have hneg : (27671 / 10000 : ℝ) - 1 - (27671 / 10000 : ℝ) ^ 2 / 2 ≤ 0 := by norm_num only
  have hmul2 := mul_le_mul_of_nonpos_right hp hneg
  nlinarith only [hmul, hmul2, hL.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
