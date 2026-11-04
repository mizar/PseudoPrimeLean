/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevLowerBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Relative-width Chebyshev upper and theta lower bounds

The logarithmic correction in the smoothed explicit formula gives an upper estimate for psi.
The existing prime-power error bound transfers the relative psi lower estimate to theta.
-/

@[expose] public section

namespace PseudoPrime.LLS

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
  have hb :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_log_shift_error_without_log hc ht0 hty hL hR).1
  have he :
    ((Real.sqrt t / 20 + 21 / 20) + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20)) * ((1 + h) * t) /
        ((1 + h) * t - t) =
      ((Real.sqrt t / 20 + 21 / 20) + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20)) * (1 + h) / h := by
    have hd : (1 + h) * t - t = h * t := by ring
    rw [hd, ← mul_assoc, mul_div_mul_right _ _ ht0.ne']
  rw [he] at hb
  linarith only [hb, hc]

/-- Under RH, for `t ≥ 1` and `0 < h ≤ 1 / 2`, the displayed expression bounds
`theta t` from below. Subtract the existing `18 * sqrt t` bound for `psi t - theta t`
from the relative psi lower estimate. This supplies theta lower bounds for prime counting. -/
theorem theta_lower_relative_log_shift (hRH : RiemannHypothesis) {h t : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (ht : 1 ≤ t) :
    (1 - h) * t - (Real.sqrt t / 10 + 21 / 10) / h - 1839 / 1000 - 18 * Real.sqrt t ≤
      Chebyshev.theta t := by
  have hp := psi_lower_relative_log_shift hRH hh hh1 (by linarith only [ht])
  have hd := AnalyticNumberTheory.Arithmetic.psi_sub_theta_le_eighteen_sqrt ht
  linarith only [hp, hd]

/-- Under RH, let `0 < h ≤ 1 / 2`, `r ≥ 1`, and `t ≥ r ^ 2`. If the displayed
relative-error budget is at most `1 - η`, then `η * t ≤ theta t`. Bound `sqrt t`
and the constant error by multiples of `t` using the common lower scale `r`.
This turns one rational budget into a uniform theta bound on a half-line. -/
theorem theta_lower_of_relative_budget (hRH : RiemannHypothesis) {h t r η : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hr : 1 ≤ r) (ht : r ^ 2 ≤ t)
    (hbudget : h + (1 / (10 * h) + 18) / r + (21 / (10 * h) + 1839 / 1000) / r ^ 2 ≤ 1 - η) :
    η * t ≤ Chebyshev.theta t := by
  have hr0 : 0 < r := by linarith only [hr]
  have ht1 : 1 ≤ t := by nlinarith only [ht, hr]
  have ht0 : 0 ≤ t := by linarith only [ht1]
  have hs : r ≤ Real.sqrt t := Real.le_sqrt_of_sq_le ht
  have heq := Real.sq_sqrt ht0
  have hrt : r * Real.sqrt t ≤ t := by
    have hh' := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg t)
    nlinarith only [hh', heq]
  have hsr : Real.sqrt t ≤ t / r := (le_div_iff₀ hr0).mpr (by nlinarith only [hrt])
  have htr : 1 ≤ t / r ^ 2 := (le_div_iff₀ (pow_pos hr0 2)).mpr (by simpa only [one_mul] using ht)
  have hE : 0 ≤ 1 / (10 * h) + 18 := by
    have hx : 0 ≤ (1 : ℝ) / (10 * h) :=
      div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hh.le)
    linarith only [hx]
  have hF : 0 ≤ 21 / (10 * h) + 1839 / 1000 := by
    have hx : 0 ≤ (21 : ℝ) / (10 * h) :=
      div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hh.le)
    linarith only [hx]
  have hE' := mul_le_mul_of_nonneg_left hsr hE
  have hF' := mul_le_mul_of_nonneg_left htr hF
  have hb := mul_le_mul_of_nonneg_right hbudget ht0
  have hp := psi_lower_relative_log_shift hRH hh hh1 ht0
  have hd := AnalyticNumberTheory.Arithmetic.psi_sub_theta_le_eighteen_sqrt ht1
  have hcost :
    (Real.sqrt t / 10 + 21 / 10) / h + 1839 / 1000 + 18 * Real.sqrt t ≤
      ((1 / (10 * h) + 18) / r + (21 / (10 * h) + 1839 / 1000) / r ^ 2) * t := by
    calc
      _ = (1 / (10 * h) + 18) * Real.sqrt t + (21 / (10 * h) + 1839 / 1000) := by ring
      _ ≤ (1 / (10 * h) + 18) * (t / r) + (21 / (10 * h) + 1839 / 1000) * (t / r ^ 2) := by
        exact add_le_add hE' (by simpa only [mul_one] using hF')
      _ = _ := by ring
  nlinarith only [hcost, hb, hp, hd]

/-- Under RH, let `h > 0`, `r ≥ 2`, and `t ≥ r ^ 2`. If the displayed
relative-error budget is at most `P - 1`, then `theta t ≤ P * t`. Bound the displaced
square root using `sqrt (1 + h) ≤ 1 + h / 2`, then use `r` to control the remaining
errors. This turns a rational budget into a uniform theta upper bound. -/
theorem theta_upper_of_relative_budget (hRH : RiemannHypothesis) {h t r P : ℝ} (hh : 0 < h)
    (hr : 2 ≤ r) (ht : r ^ 2 ≤ t)
    (hbudget :
      h + ((2 + h / 2) / 20 * (1 + h) / h) / r + ((21 / 10) * (1 + h) / h) / r ^ 2 ≤ P - 1) :
    Chebyshev.theta t ≤ P * t := by
  have hr0 : 0 < r := by linarith only [hr]
  have ht1 : 1 < t := by nlinarith only [ht, hr]
  have ht0 : 0 ≤ t := by linarith only [ht1]
  have hs : r ≤ Real.sqrt t := Real.le_sqrt_of_sq_le ht
  have heq := Real.sq_sqrt ht0
  have hrt : r * Real.sqrt t ≤ t := by
    have hh' := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg t)
    nlinarith only [hh', heq]
  have hsr : Real.sqrt t ≤ t / r := (le_div_iff₀ hr0).mpr (by nlinarith only [hrt])
  have htr : 1 ≤ t / r ^ 2 := (le_div_iff₀ (pow_pos hr0 2)).mpr (by simpa only [one_mul] using ht)
  have hE : 0 ≤ (2 + h / 2) / 20 * (1 + h) / h := by
    have he : 0 ≤ (2 + h / 2) / 20 := by linarith only [hh]
    exact div_nonneg (mul_nonneg he (by linarith only [hh])) hh.le
  have hF : 0 ≤ (21 / 10 : ℝ) * (1 + h) / h :=
    div_nonneg (mul_nonneg (by norm_num only) (by linarith only [hh])) hh.le
  have hsqrt : Real.sqrt ((1 + h) * t) ≤ (1 + h / 2) * Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by linarith only [hh]) (Real.sqrt_nonneg t)
    · have hsq : 0 ≤ (h / 2) ^ 2 * t := mul_nonneg (sq_nonneg _) ht0
      have heq' := congrArg (fun z : ℝ ↦ (1 + h / 2) ^ 2 * z) heq
      nlinarith only [heq', hsq]
  have herr :
    Real.sqrt t / 20 + 21 / 20 + (Real.sqrt ((1 + h) * t) / 20 + 21 / 20) ≤
      (2 + h / 2) / 20 * Real.sqrt t + 21 / 10 := by
    linarith only [hsqrt]
  have herr' :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right herr (show 0 ≤ 1 + h by linarith only [hh])) hh.le
  have hE' := mul_le_mul_of_nonneg_left hsr hE
  have hF' := mul_le_mul_of_nonneg_left htr hF
  have hb := mul_le_mul_of_nonneg_right hbudget ht0
  have hp := psi_upper_relative_log_shift hRH hh ht1
  have hθ := Chebyshev.theta_le_psi t
  have hcost :
    ((2 + h / 2) / 20 * Real.sqrt t + 21 / 10) * (1 + h) / h ≤
      (((2 + h / 2) / 20 * (1 + h) / h) / r + ((21 / 10) * (1 + h) / h) / r ^ 2) * t := by
    calc
      _ = ((2 + h / 2) / 20 * (1 + h) / h) * Real.sqrt t + ((21 / 10) * (1 + h) / h) := by ring
      _ ≤ ((2 + h / 2) / 20 * (1 + h) / h) * (t / r) + ((21 / 10) * (1 + h) / h) * (t / r ^ 2) := by
        exact add_le_add hE' (by simpa only [mul_one] using hF')
      _ = _ := by ring
  nlinarith only [hp, hθ, herr', hcost, hb]

end PseudoPrime.LLS
