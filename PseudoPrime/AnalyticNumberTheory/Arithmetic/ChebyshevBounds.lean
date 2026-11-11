/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.NumberTheory.Chebyshev

/-! # Elementary uniform bounds for Chebyshev's psi function -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For every nonnegative real argument, Chebyshev's function satisfies `psi x ≤ 3x`.
Chebyshev's elementary estimate and a tangent bound for `log x` prove the result
above one; below one the Mangoldt sum vanishes. This common bound supplies MR
principal sums, higher-prime-power removal, and LLS theta estimates without RH. -/
theorem psi_le_three {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ 3 * x := by
  by_cases hx1 : 1 ≤ x
  · have h4 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 4 2 16 1 (7 / 5) = true from by decide +kernel)).2
    have h25 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck (5 / 2) 2 16 (9 / 10) 1 = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h4 h25
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have htangent :=
      Analysis.log_le_log_add_sub_div (a := (5 / 2 : ℝ)) (y := Real.sqrt x) (by norm_num only) hs
    have he := Real.log_sqrt hx
    have hlog : Real.log x ≤ (4 / 5 : ℝ) * Real.sqrt x := by linarith only [htangent, h25, he]
    have hroot := Real.sq_sqrt hx
    have hprod := mul_le_mul_of_nonneg_left hlog hs.le
    have hmain := mul_le_mul_of_nonneg_right h4 hx
    have hpsi := Chebyshev.psi_le hx1
    nlinarith only [hpsi, hmain, hprod, hroot]
  · rw [Chebyshev.psi_eq_zero_of_le_one (le_of_not_ge hx1)]
    exact mul_nonneg (by norm_num only) hx

end PseudoPrime.AnalyticNumberTheory.Arithmetic
