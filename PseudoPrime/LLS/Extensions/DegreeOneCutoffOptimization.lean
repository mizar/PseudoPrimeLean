/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.DegreeOneValueCorrection

/-! Limits of optimizing the existing degree-one exponential cutoff majorant. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For positive half-logarithmic cutoff `z`, the exponential tangent inequality gives
`z+(r-1)/2 ≤ z exp((r-1)/(2z))`. Cancel the positive denominator.
This is the first comparison in the ideal degree-one cutoff bound. -/
private theorem cutoff_linear_exp_bound {z r : ℝ} (hz : 0 < z) :
    z + (r - 1) / 2 ≤ z * Real.exp ((r - 1) / (2 * z)) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((r - 1) / (2 * z))) hz.le
  have he : z * ((r - 1) / (2 * z) + 1) = z + (r - 1) / 2 := by
    field_simp (disch :=
      first
      | exact ne_of_gt hz
      | norm_num only)
    ring
  rw [he] at h
  exact h

/-- At the first-order optimal ratio two and positive cutoff `z`, the exponential
tangent comparison is strict. The argument `1/(2z)` is nonzero.
This handles the equality case in the comparison of cutoff ratios. -/
private theorem cutoff_two_exp_bound {z : ℝ} (hz : 0 < z) :
    z + 1 / 2 < z * Real.exp (1 / (2 * z)) := by
  have hp := one_div_pos.mpr (mul_pos (by norm_num only : (0 : ℝ) < 2) hz)
  have h := mul_lt_mul_of_pos_left (Real.add_one_lt_exp hp.ne') hz
  have he : z * (1 / (2 * z) + 1) = z + 1 / 2 := by
    field_simp (disch :=
      first
      | exact ne_of_gt hz
      | norm_num only)
    ring
  rw [he] at h
  exact h

/-- The idealized degree-one value majorant without any truncation or prime-sum error.
Here `t=log log C` and `z=log x/2`; its value is
`2z exp((2 exp(t-log 2-z)-1)/(2z))`. It retains the conductor term and the negative
Mangoldt correction. It is used to test whether choosing a different cutoff can prove
the error-free degree-one endpoint; it is not asserted to equal an actual L-value. -/
noncomputable def idealDegreeOneValueUpper (t z : ℝ) : ℝ :=
  2 * z * Real.exp ((2 * Real.exp (t - Real.log 2 - z) - 1) / (2 * z))

/-- For every real `t` and positive half-logarithmic cutoff `z`, the idealized
majorant strictly exceeds `2(t-log 2+1/2)`. Away from the optimal first-order ratio,
the inner exponential tangent inequality is strict; at that ratio the outer one is strict.
Thus even removing all analytic errors does not close the endpoint by this majorant. -/
theorem idealDegreeOneValueUpper_gt_endpoint (t : ℝ) {z : ℝ} (hz : 0 < z) :
    2 * (t - (Real.log 2 - 1 / 2)) < idealDegreeOneValueUpper t z := by
  by_cases hw : t - Real.log 2 - z = 0
  · have h := cutoff_two_exp_bound hz
    simp only [idealDegreeOneValueUpper, hw, Real.exp_zero, mul_one]
    linarith only [h, hw]
  · have he := Real.add_one_lt_exp hw
    have h := cutoff_linear_exp_bound (r := 2 * Real.exp (t - Real.log 2 - z)) hz
    dsimp only [idealDegreeOneValueUpper]
    linarith only [he, h]

/-- For conductor `C>1` and cutoff `x>1`, express the idealized majorant as
`log x * exp((log C/sqrt x-1)/log x)`. Exponential and logarithmic identities identify
the ratio and the half-logarithmic cutoff. This connects the scalar comparison
to the conductor-centered value estimate used in the LLS argument. -/
theorem idealDegreeOneValueUpper_eq_logCutoff {C x : ℝ} (hC : 1 < C) (hx : 1 < x) :
    idealDegreeOneValueUpper (Real.log (Real.log C)) (Real.log x / 2) =
      Real.log x * Real.exp ((Real.log C / Real.sqrt x - 1) / Real.log x) := by
  have he :
    2 * Real.exp (Real.log (Real.log C) - Real.log 2 - Real.log x / 2) =
      Real.log C / Real.sqrt x := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (Real.log_pos hC),
      Real.exp_log (by norm_num only : (0 : ℝ) < 2), ← Real.log_sqrt (zero_lt_one.trans hx).le,
      Real.exp_log (Real.sqrt_pos.mpr (zero_lt_one.trans hx))]
    ring
  dsimp only [idealDegreeOneValueUpper]
  rw [he, show (2 : ℝ) * (Real.log x / 2) = Real.log x by ring]

/-- For any conductor and cutoff greater than one, the idealized cutoff bound is
strictly larger than the required degree-one endpoint, before the Euler-constant prefactor.
Rewrite with the half-logarithmic cutoff and apply the scalar comparison.
This rules out repairing the current majorant solely by a different cutoff. -/
theorem idealDegreeOne_logCutoff_gt_endpoint {C x : ℝ} (hC : 1 < C) (hx : 1 < x) :
    2 * (Real.log (Real.log C) - (Real.log 2 - 1 / 2)) <
      Real.log x * Real.exp ((Real.log C / Real.sqrt x - 1) / Real.log x) := by
  rw [← idealDegreeOneValueUpper_eq_logCutoff hC hx]
  exact idealDegreeOneValueUpper_gt_endpoint _ (div_pos (Real.log_pos hx) (by norm_num only))

/-- For conductor and cutoff greater than one, adding any nonnegative logarithmic
error to the idealized majorant preserves its strict excess over the degree-one endpoint.
Use monotonicity of the exponential and the positive cutoff logarithm.
This includes the nonnegative error bounds supplied by the second-order arithmetic inputs;
it does not imply that the actual L-value violates the endpoint. -/
theorem idealDegreeOne_logCutoff_with_error_gt_endpoint {C x b : ℝ} (hC : 1 < C) (hx : 1 < x)
    (hb : 0 ≤ b) :
    2 * (Real.log (Real.log C) - (Real.log 2 - 1 / 2)) <
      Real.log x * Real.exp ((Real.log C / Real.sqrt x - 1) / Real.log x + b) := by
  apply lt_of_lt_of_le (idealDegreeOne_logCutoff_gt_endpoint hC hx)
  exact
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_add_of_nonneg_right hb)) (Real.log_pos hx).le

end PseudoPrime.LLS.Extensions.GeneralLFunction
