/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogShiftStencilBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedExplicitBounds
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Relative Chebyshev bounds under the Riemann hypothesis -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH at t greater than one, the corrected smoothed error has absolute
value at most sqrt(t)/20+21/20. Retain log(2 pi)log t in the explicit formula and bound
only the zero mass and trivial-zero tail. This avoids a logarithmic stencil error. -/
theorem logWeightedMangoldtSum_log_shift_error_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 < t) :
    |logWeightedMangoldtSum t - t + Real.log (2 * Real.pi) * Real.log t| ≤
      Real.sqrt t / 20 + 21 / 20 := by
  have he := abs_le.mp (RiemannZeta.abs_logWeightedMangoldtSum_error_le hRH ht)
  have hm :=
    mul_le_mul_of_nonneg_right RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg t) zero_le_one)
  have hb := RiemannZeta.logTrivialSeries_le_pi_sq_div_24 ht
  have hz : 0 ≤ RiemannZeta.riemannZetaLogTrivialZeroSeries t := by
    apply tsum_nonneg
    intro k
    exact
      div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans ht).le) _)
        (mul_nonneg (by norm_num only) (sq_nonneg _))
  rw [abs_le]
  constructor
  · linarith only [he.1, hm, hb]
  · nlinarith only [he.2, hm, hz, Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]

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
      |logWeightedMangoldtSum ((1 - h) * t) - (1 - h) * t +
            Real.log (2 * Real.pi) * Real.log ((1 - h) * t)| ≤
        Real.sqrt t / 20 + 21 / 20 := by
      linarith only [hL, hs]
    have hc : 0 ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
    have hb := (psi_bounds_of_log_shift_error_without_log hc (zero_lt_one.trans hx) hxt hL' hR).2
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

/-- Under RH, for `t > 1` and `h > 0`, the displayed relative-width expression bounds
`psi t` from above. Apply the corrected smoothed-error bounds at `t` and `(1 + h) * t`
and cancel their spacing in the upper stencil. This supplies theta upper bounds after
choosing an explicit width. -/
theorem psi_upper_relative_log_shift (hRH : RiemannHypothesis) {h t : ℝ} (hh : 0 < h) (ht : 1 < t) :
    Chebyshev.psi t ≤
      (1 + h) * t +
        (Real.sqrt t / 20 + 21 / 20 + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20)) * (1 + h) / h := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hty : t < (1 + h) * t := by nlinarith only [mul_pos hh ht0]
  have hL := logWeightedMangoldtSum_log_shift_error_le hRH ht
  have hR := logWeightedMangoldtSum_log_shift_error_le hRH (ht.trans hty)
  have hc : 0 ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hb := (psi_bounds_of_log_shift_error_without_log hc ht0 hty hL hR).1
  have he :
    ((Real.sqrt t / 20 + 21 / 20) + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20)) * ((1 + h) * t) /
        ((1 + h) * t - t) =
      ((Real.sqrt t / 20 + 21 / 20) + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20)) * (1 + h) / h := by
    have hd : (1 + h) * t - t = h * t := by ring
    rw [hd, ← mul_assoc, mul_div_mul_right _ _ ht0.ne']
  rw [he] at hb
  linarith only [hb, hc]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
