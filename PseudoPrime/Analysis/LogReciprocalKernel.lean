/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Derivative and local integrability of the reciprocal logarithmic weight. -/

public section

namespace PseudoPrime.Analysis

/-- For `x > 1`, the derivative of `1 / (x * log x)` is
`-(log x + 1) / (x² * (log x)²)`. Apply the product and inverse rules,
then cancel `x * x⁻¹`. This supplies the weight derivative in partial summation. -/
theorem hasDerivAt_inv_mul_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ 1 / (t * Real.log t)) (-((Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2)))
      x := by
  have hp := (hasDerivAt_id x).mul (Real.hasDerivAt_log (zero_lt_one.trans hx).ne')
  have hi := hp.fun_inv (mul_ne_zero (zero_lt_one.trans hx).ne' (Real.log_pos hx).ne')
  simp only [Pi.mul_apply, id_eq, one_mul, mul_inv_cancel₀ (zero_lt_one.trans hx).ne'] at hi
  simpa only [one_div, mul_pow, neg_div] using hi

/-- The negative derivative kernel of `1 / (x * log x)` is continuous for `x > 1`.
The logarithm and polynomial factors are continuous and neither denominator factor vanishes.
This provides local integrability of the kernel in logarithmically weighted sums. -/
theorem continuousOn_logReciprocalKernel :
    ContinuousOn (fun x : ℝ ↦ (Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2)) (Set.Ioi 1) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hx1 : 1 < x := hx
  have hx0 := zero_lt_one.trans hx1
  have hl := Real.continuousAt_log hx0.ne'
  exact
    (hl.add continuousAt_const).div ((continuousAt_id.pow 2).mul (hl.pow 2))
      (mul_ne_zero (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 (Real.log_pos hx1).ne'))

/-- On any closed interval with left endpoint greater than one, the derivative of
`1 / (x * log x)` is integrable. Restrict the continuous kernel to the compact interval
and identify it with the derivative. This discharges the analytic input to Abel summation. -/
theorem integrableOn_deriv_inv_mul_log_Icc {a b : ℝ} (ha : 1 < a) :
    MeasureTheory.IntegrableOn (deriv (fun t : ℝ ↦ 1 / (t * Real.log t))) (Set.Icc a b) := by
  have hs : Set.Icc a b ⊆ Set.Ioi 1 := fun _ hx ↦ ha.trans_le hx.1
  apply ((continuousOn_logReciprocalKernel.mono hs).neg.integrableOn_Icc).congr_fun
  · intro x hx
    exact (hasDerivAt_inv_mul_log (ha.trans_le hx.1)).deriv.symm
  · exact measurableSet_Icc

/-- Normalize the derivative coefficient of `log log x - 1 / log x` for `x > 1`.
Clear the denominator by multiplication and use the two explicit inverse cancellations.
This identifies the linear main term in the reciprocal logarithmic kernel. -/
private theorem logLog_sub_inv_log_deriv_eq {x : ℝ} (hx : 1 < x) :
    (Real.log x)⁻¹ * x⁻¹ - -x⁻¹ / (Real.log x) ^ 2 =
      x * ((Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2)) := by
  have hx0 := zero_lt_one.trans hx
  have hl := Real.log_pos hx
  rw [← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hl.ne'))).mpr
  simp only [div_eq_mul_inv, ← inv_pow, neg_mul, sub_neg_eq_add]
  calc
    ((Real.log x)⁻¹ * x⁻¹ + x⁻¹ * ((Real.log x)⁻¹) ^ 2) * (x ^ 2 * (Real.log x) ^ 2) =
        (x * x⁻¹) * x *
          ((Real.log x * (Real.log x)⁻¹) * Real.log x + (Real.log x * (Real.log x)⁻¹) ^ 2) :=
      by ring
    _ = x * (Real.log x + 1) := by
      rw [mul_inv_cancel₀ hx0.ne', mul_inv_cancel₀ hl.ne']
      ring

/-- For `x > 1`, `log log x - 1 / log x` is a primitive of
`x * (log x + 1) / (x² * (log x)²)`. Differentiate the composed logarithm and inverse,
then normalize their difference. This integrates the linear main term in partial summation. -/
theorem hasDerivAt_logLog_sub_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ Real.log (Real.log t) - 1 / Real.log t)
      (x * ((Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2))) x := by
  have hd := Real.hasDerivAt_log (zero_lt_one.trans hx).ne'
  have h :=
    ((Real.hasDerivAt_log (Real.log_pos hx).ne').comp x hd).sub (hd.fun_inv (Real.log_pos hx).ne')
  simp only [one_div] at h ⊢
  exact h.congr_deriv (logLog_sub_inv_log_deriv_eq hx)

/-- Integrating the linear part of the logarithmic kernel on `(a, b]`, with `1 < a ≤ b`,
gives the difference of `log log x - 1 / log x` at the endpoints.
The continuous kernel is integrable on the compact interval, so the fundamental theorem
applies to the explicit primitive. This extracts the main term from psi-weighted integrals. -/
theorem integral_mul_logReciprocalKernel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) =
      (Real.log (Real.log b) - 1 / Real.log b) - (Real.log (Real.log a) - 1 / Real.log a) := by
  have hs : Set.Icc a b ⊆ Set.Ioi 1 := fun _ hx ↦ ha.trans_le hx.1
  have hint :=
    (continuousOn_id.mul (continuousOn_logReciprocalKernel.mono hs)).integrableOn_Icc (μ :=
      MeasureTheory.volume)
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_logLog_sub_inv_log (ha.trans_le ht.1)
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint

/-- For `x > 1`, the derivative of `-1 / (2 * (log x)^2)` is `1 / (x * (log x)^3)`.
Differentiate the reciprocal square of the logarithm and cancel its nonzero factor.
This antiderivative gives an explicit bound for the tail of the psi error kernel. -/
theorem hasDerivAt_neg_inv_two_log_sq {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(1 / (2 * (Real.log t) ^ 2))) (1 / (x * (Real.log x) ^ 3)) x := by
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hd :=
    (((Real.hasDerivAt_log (zero_lt_one.trans hx).ne').pow 2).fun_inv (pow_ne_zero 2 hl)).const_mul
      (-(1 / 2 : ℝ))
  convert hd using 1
  · funext t
    simp only [Pi.pow_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv, mul_inv_rev]
    rw [← inv_pow, ← inv_pow, ← inv_pow]
    symm
    calc
      _ = (Real.log x * (Real.log x)⁻¹) * ((Real.log x)⁻¹) ^ 3 * x⁻¹ := by
        norm_num only
        ring
      _ = _ := by
        rw [mul_inv_cancel₀ hl]
        ring

/-- The reciprocal-square logarithmic antiderivative tends to zero at positive infinity.
Use divergence of the logarithm, take the reciprocal and square, and multiply by `-1/2`.
This determines the endpoint at infinity when integrating the cubic logarithmic kernel. -/
theorem tendsto_neg_inv_two_log_sq :
    Filter.Tendsto (fun t : ℝ => -(1 / (2 * (Real.log t) ^ 2))) Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_log_atTop.inv_tendsto_atTop.pow 2).const_mul (-(1 / 2 : ℝ))
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext t
  simp only [div_eq_mul_inv, mul_inv_rev]
  dsimp only [Pi.inv_apply]
  rw [← inv_pow]
  ring

/-- For `x > 1`, the cubic reciprocal logarithmic kernel is integrable on `(x, ∞)`.
Its nonnegative values are the derivative of an antiderivative with limit zero.
This supplies an integrable majorant for the quantitative psi remainder. -/
theorem integrableOn_inv_mul_log_cube {x : ℝ} (hx : 1 < x) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ 1 / (t * (Real.log t) ^ 3)) (Set.Ioi x) := by
  apply
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (fun t ht ↦ hasDerivAt_neg_inv_two_log_sq (hx.trans_le ht))
      (fun t ht ↦
        one_div_nonneg.mpr
          (mul_nonneg (zero_lt_one.trans (hx.trans ht)).le
            (pow_nonneg (Real.log_pos (hx.trans ht)).le 3)))
      tendsto_neg_inv_two_log_sq

/-- For `x > 1`, the tail integral of `1 / (t * (log t)^3)` equals `1 / (2 * (log x)^2)`.
Apply the fundamental theorem on the half-line to the nonnegative kernel and its
reciprocal-square antiderivative. This provides the explicit second-order tail scale. -/
theorem integral_inv_mul_log_cube {x : ℝ} (hx : 1 < x) :
    (∫ t in Set.Ioi x, 1 / (t * (Real.log t) ^ 3)) = 1 / (2 * (Real.log x) ^ 2) := by
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun t (ht : t ∈ Set.Ici x) ↦ hasDerivAt_neg_inv_two_log_sq (hx.trans_le ht))
      (fun t (ht : t ∈ Set.Ioi x) ↦
        one_div_nonneg.mpr
          (mul_nonneg (zero_lt_one.trans (hx.trans ht)).le
            (pow_nonneg (Real.log_pos (hx.trans ht)).le 3)))
      tendsto_neg_inv_two_log_sq
  simpa only [zero_sub, neg_neg] using h

/-- For positive `t` with `log t ≥ 1`, an error bounded by `B*t/(log t)^2` gives a
kernel-weighted error at most `2*B/(t*(log t)^3)`, provided `B ≥ 0`.
Multiply the error bound by the nonnegative kernel and use `log t + 1 ≤ 2*log t`.
This replaces the psi remainder by a kernel with an explicit integrable tail. -/
theorem abs_mul_logReciprocalKernel_le {B r t : ℝ} (hB : 0 ≤ B) (ht : 0 < t) (hl : 1 ≤ Real.log t)
    (hr : |r| ≤ B * t / (Real.log t) ^ 2) :
    |r * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))| ≤ 2 * B / (t * (Real.log t) ^ 3) := by
  have hp : 0 < Real.log t := zero_lt_one.trans_le hl
  rw [abs_mul,
    abs_of_nonneg
      (div_nonneg (by linarith only [hl]) (mul_nonneg (sq_nonneg t) (sq_nonneg (Real.log t))))]
  calc
    _ ≤ (B * t / (Real.log t) ^ 2) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
      mul_le_mul_of_nonneg_right hr
        (div_nonneg (by linarith only [hl]) (mul_nonneg (sq_nonneg t) (sq_nonneg (Real.log t))))
    _ = B * (Real.log t + 1) / (t * (Real.log t) ^ 4) := by
      rw [div_mul_div_comm]
      apply
        (div_eq_div_iff
            (mul_ne_zero (pow_ne_zero 2 hp.ne')
              (mul_ne_zero (pow_ne_zero 2 ht.ne') (pow_ne_zero 2 hp.ne')))
            (mul_ne_zero ht.ne' (pow_ne_zero 4 hp.ne'))).mpr
      ring
    _ ≤ 2 * B / (t * (Real.log t) ^ 3) := by
      apply (div_le_div_iff₀ (mul_pos ht (pow_pos hp 4)) (mul_pos ht (pow_pos hp 3))).mpr
      have h :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hl] : Real.log t + 1 ≤ 2 * Real.log t) hB)
          (mul_nonneg ht.le (pow_nonneg hp.le 3))
      convert h using 1
      ring

end PseudoPrime.Analysis
