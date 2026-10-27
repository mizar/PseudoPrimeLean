/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogShiftRampPrincipalBounds

/-! # Relative-width Chebyshev lower bounds retaining the logarithmic correction -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, a relative width in (0,1/2] yields a global one-sided Chebyshev
bound with linear main loss and square-root error. Retain the logarithmic
correction before taking the two smoothed secants. -/
theorem psi_lower_relative_log_shift (hRH : RiemannHypothesis) {h t : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (ht : 0 ≤ t) :
    (1 - h) * t - (Real.sqrt t / 10 + 21 / 10) / h - 1839 / 1000 ≤ Chebyshev.psi t := by
  have hh0 : 0 ≤ 1 - h := by linarith only [hh1]
  have hE0 : 0 ≤ Real.sqrt t / 10 + 21 / 10 := by linarith only [Real.sqrt_nonneg t]
  by_cases ht2 : 2 < t
  · have hx : 1 < (1 - h) * t := by nlinarith only [hh1, ht2]
    have hxt : (1 - h) * t < t := by nlinarith only [mul_pos hh (zero_lt_two.trans ht2)]
    have hs := Real.sqrt_le_sqrt (show (1 - h) * t ≤ t from hxt.le)
    have hL := logWeightedMangoldtSum_log_shift_error_le hRH hx
    have hR := logWeightedMangoldtSum_log_shift_error_le hRH (show 1 < t by linarith only [ht2])
    have hL' :
      |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((1 - h) * t) - (1 - h) * t +
            Real.log (2 * Real.pi) * Real.log ((1 - h) * t)| ≤
        Real.sqrt t / 20 + 21 / 20 := by
      linarith only [hL, hs]
    have hc : 0 ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
    have hb :=
      (AnalyticNumberTheory.Arithmetic.psi_bounds_of_log_shift_error_without_log hc
          (zero_lt_one.trans hx) hxt hL' hR).2
    have he :
      ((Real.sqrt t / 20 + 21 / 20) + (Real.sqrt t / 20 + 21 / 20)) * ((1 - h) * t) /
          (t - (1 - h) * t) =
        (Real.sqrt t / 10 + 21 / 10) * (1 - h) / h := by
      have ht0 : t ≠ 0 := (zero_lt_two.trans ht2).ne'
      field_simp [hh.ne', ht0]
      ring
    rw [he] at hb
    have hmul := mul_nonneg hE0 hh.le
    have hcomp : (Real.sqrt t / 10 + 21 / 10) * (1 - h) / h ≤ (Real.sqrt t / 10 + 21 / 10) / h := by
      apply div_le_div_of_nonneg_right _ hh.le
      nlinarith only [hmul]
    linarith only [hb, hcomp, Analysis.log_two_mul_pi_lt]
  · have hmain : (1 - h) * t ≤ 2 := by nlinarith only [le_of_not_gt ht2, mul_nonneg hh.le ht]
    have hcost : 2 ≤ (Real.sqrt t / 10 + 21 / 10) / h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith only [hh1, Real.sqrt_nonneg t]
    linarith only [hmain, hcost, Chebyshev.psi_nonneg t]

end PseudoPrime.LLS
