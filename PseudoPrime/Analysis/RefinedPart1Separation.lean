/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.NumericalLogBounds
public import PseudoPrime.Analysis.LogarithmicRatios

/-! # Separation of the refined Part 1 lower and upper bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For y≥L>8, A≥0, zero mass z≤1/40, P≥57/50, and T≤1839/1000,
the Part 1 logarithmic upper and lower bounds are incompatible when the radius correction
is at least 2log(L)+2+w−2A. Retain the negative pi term and compare log ratios.
A tangent bound for log(y) at eight proves the remaining positive margin.
This closes the real-variable comparison for the refined correction with constant two. -/
theorem refinedPart1_bounds_incompatible {L y A w z P T U : ℝ} (hL : 8 < L) (hy : L ≤ y)
    (hA : 0 ≤ A) (hz : z ≤ (1 / 40 : ℝ)) (hP : (57 / 50 : ℝ) ≤ P) (hT : T ≤ (1839 / 1000 : ℝ))
    (hB : 2 * Real.log L + 2 + w - 2 * A ≤ y - L)
    (hupper :
      U ≤
        (2 * y + 2 + Real.log (y ^ 2)) * (L / 2 + 9 / 50 - A) +
            (1 / 2 : ℝ) * (L - P) * Real.log (y ^ 2) -
          11 / 4)
    (hlower : y ^ 2 - y * (2 * z + w) - T * Real.log (y ^ 2) - 1 - 2 * z ≤ U) : False := by
  have hy8 : (8 : ℝ) ≤ y := hL.le.trans hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy8
  have hly : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy8)
  have hratio := strictAntiOn_logLinearRatio.antitoneOn hL.le hy8 hy
  change (2 * Real.log y + 1) / y ≤ (2 * Real.log L + 1) / L at hratio
  have hL0 : 0 < L := lt_trans (by norm_num only : (0 : ℝ) < 8) hL
  have hr := (div_le_div_iff₀ hy0 hL0).mp hratio
  have hb := mul_le_mul_of_nonneg_left hB hy0.le
  have ha := mul_nonneg hA (by linarith only [hly] : 0 ≤ 2 + 2 * Real.log y)
  have hp := mul_le_mul_of_nonneg_right hP hly
  have ht := mul_le_mul_of_nonneg_right hT hly
  have hzmul := mul_le_mul_of_nonneg_right hz (by linarith only [hy8] : 0 ≤ 2 * y + 2)
  have hlog := log_le_log_add_sub_div (a := (8 : ℝ)) (y := y) (by norm_num only) hy0
  have hlog8 : Real.log (8 : ℝ) < (52 / 25 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_lt_d9]
  rw [Real.log_pow] at hupper hlower
  norm_num only [Nat.cast_ofNat] at hupper hlower
  nlinarith only [hr, hb, ha, hp, ht, hzmul, hlog, hlog8, hupper, hlower, hy8]

end PseudoPrime.Analysis
