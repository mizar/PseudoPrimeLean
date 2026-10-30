/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CauchyPowerIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
/-! Exact scaled Cauchy moments with absolute and linear height weights. -/

@[expose] public section

namespace PseudoPrime.Analysis
/-- The absolute first moment of the second Cauchy power is integrable.
Dominate it by the Cauchy weight using abs(t) <= 1+t² and continuity.
This supplies absolute integrability before evaluating the half-line primitive. -/
theorem integrable_cauchy_abs :
    MeasureTheory.Integrable (fun t : ℝ ↦ |t| / (1 + t ^ 2) ^ 2) := by
  have hi := integrable_inv_one_add_sq
  apply hi.mono'
  · exact (continuous_abs.div ((continuous_const.add (continuous_id.pow 2)).pow 2)
      (fun t ↦ pow_ne_zero 2
        (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      have hp : 0 < 1 + t ^ 2 := add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)
      have ha : |t| ≤ 1 + t ^ 2 := by
        nlinarith only [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg t) (sq_nonneg _))]
      have h := div_le_div_of_nonneg_right ha (sq_nonneg (1 + t ^ 2))
      have he : (1 + t ^ 2) / (1 + t ^ 2) ^ 2 = 1 / (1 + t ^ 2) := by
        rw [pow_two (1 + t ^ 2), div_mul_eq_div_div, div_self hp.ne']
      rw [he, one_div] at h
      exact h

/-- The derivative of -1/(2(1+t²)) is t/(1+t²)².
Differentiate the quotient and normalize its derivative polynomial.
This evaluates the positive-half-line absolute first Cauchy moment. -/
private theorem hasDerivAt_cauchyPrimitive (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ -(1 / 2 : ℝ) / (1 + u ^ 2))
      (t / (1 + t ^ 2) ^ 2) t := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))
  convert (hasDerivAt_const t (-(1 / 2 : ℝ))).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) hd using 1
  · rfl
  · norm_num only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, one_mul, mul_one, zero_add]
    ring

/-- The exact full-line absolute first moment of (1+t²)^(-2) is one.
Integrate its primitive on the positive half-line and reflect through the absolute value.
This is the normalized weighted moment used in contour and gamma estimates. -/
theorem integral_cauchy_abs : (∫ t : ℝ, |t| / (1 + t ^ 2) ^ 2) = 1 := by
  have ht : Filter.Tendsto (fun t : ℝ ↦ -(1 / 2 : ℝ) / (1 + t ^ 2))
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun t : ℝ ↦ t * t) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_atTop₀ Filter.tendsto_id
    have hs := Filter.tendsto_atTop_add_const_left Filter.atTop 1 hp
    simpa only [pow_two] using hs.const_div_atTop (-(1 / 2 : ℝ))
  have hi : MeasureTheory.IntegrableOn (fun t : ℝ ↦ t / (1 + t ^ 2) ^ 2) (Set.Ioi 0) := by
    apply integrable_cauchy_abs.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_of_pos (show 0 < t from ht)]
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ ↦ hasDerivAt_cauchyPrimitive t) hi ht
  have he : (fun t : ℝ ↦ |t| / (1 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ |t| / (1 + |t| ^ 2) ^ 2) := by
    funext t
    rw [sq_abs]
  rw [he, integral_comp_abs (f := fun t : ℝ ↦ t / (1 + t ^ 2) ^ 2), h]
  norm_num only [zero_pow (by norm_num only : 2 ≠ 0), add_zero, div_one]

/-- For nonzero d and arbitrary real t and W, dilate the squared Cauchy denominator.
The exact denominator identity and explicit inverse cancellation supply the scale
factor used by both the integrable weights and their integral evaluations. -/
private theorem cauchy_scale_four {d : ℝ} (hd : d ≠ 0) (t W : ℝ) :
    W / (d ^ 2 + t ^ 2) ^ 2 = (1 / d ^ 4) * (W / (1 + (d⁻¹ * t) ^ 2) ^ 2) := by
  have he : 1 + (d⁻¹ * t) ^ 2 = (d ^ 2 + t ^ 2) / d ^ 2 := by
    rw [add_div, div_self (pow_ne_zero 2 hd)]
    ring
  rw [he, div_pow, div_div_eq_mul_div]
  symm
  calc
    _ = (d ^ 4 * (d ^ 4)⁻¹) * (W / (d ^ 2 + t ^ 2) ^ 2) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 4 hd), one_mul]

/-- For positive scale d, the squared Cauchy denominator defines an integrable weight.
Dilate the normalized second Cauchy power and multiply by d^(-4).
This justifies integrating unweighted parts of explicit contour majorants. -/
theorem integrable_scaled_cauchy_two {d : ℝ} (hd : 0 < d) :
    MeasureTheory.Integrable (fun t : ℝ ↦ 1 / (d ^ 2 + t ^ 2) ^ 2) := by
  have he : (fun t : ℝ ↦ 1 / (d ^ 2 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ (1 / d ^ 4) * (1 / (1 + (d⁻¹ * t) ^ 2) ^ 2)) := by
    funext t
    exact cauchy_scale_four hd.ne' t 1
  rw [he]
  exact ((MeasureTheory.integrable_comp_mul_left_iff (fun t : ℝ ↦ 1 / (1 + t ^ 2) ^ 2)
      (inv_ne_zero hd.ne')).mpr
    (integrable_cauchy_power (by norm_num only : 1 ≤ 2))).const_mul _

/-- For positive scale d, the absolute first moment of the squared denominator is integrable.
Dilate the normalized weighted moment and multiply by d^(-3).
This justifies the linear-height part of gamma and left-contour bounds. -/
theorem integrable_scaled_cauchy_abs {d : ℝ} (hd : 0 < d) :
    MeasureTheory.Integrable (fun t : ℝ ↦ |t| / (d ^ 2 + t ^ 2) ^ 2) := by
  have he : (fun t : ℝ ↦ |t| / (d ^ 2 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ (1 / d ^ 3) * (|d⁻¹ * t| / (1 + (d⁻¹ * t) ^ 2) ^ 2)) := by
    funext t
    rw [abs_mul, abs_inv, abs_of_pos hd]
    calc
      _ = (1 / d ^ 4) * (|t| / (1 + (d⁻¹ * t) ^ 2) ^ 2) :=
        cauchy_scale_four hd.ne' t |t|
      _ = _ := by ring
  rw [he]
  exact ((MeasureTheory.integrable_comp_mul_left_iff (fun t : ℝ ↦ |t| / (1 + t ^ 2) ^ 2)
      (inv_ne_zero hd.ne')).mpr
    integrable_cauchy_abs).const_mul _

/-- For positive d, the integral of (d²+t²)^(-2) is pi/(2d³).
Use real dilation and the normalized exact second Cauchy integral.
This is the unweighted moment for a vertical line at positive distance from the pole. -/
theorem integral_scaled_cauchy_two {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ, 1 / (d ^ 2 + t ^ 2) ^ 2) = Real.pi / (2 * d ^ 3) := by
  have he : (fun t : ℝ ↦ 1 / (d ^ 2 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ (1 / d ^ 4) * (1 / (1 + (d⁻¹ * t) ^ 2) ^ 2)) := by
    funext t
    exact cauchy_scale_four hd.ne' t 1
  rw [he, MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ ↦ 1 / (1 + t ^ 2) ^ 2) d⁻¹,
    integral_cauchy_power_two, smul_eq_mul, inv_inv, abs_of_pos hd]
  calc
    _ = (d * d⁻¹) * (Real.pi / (2 * d ^ 3)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd.ne', one_mul]

/-- For positive d, the integral of abs(t)/(d²+t²)² is 1/d².
Use real dilation and the normalized absolute first moment.
This is the height-weighted moment in finite gamma and contour errors. -/
theorem integral_scaled_cauchy_abs {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ, |t| / (d ^ 2 + t ^ 2) ^ 2) = 1 / d ^ 2 := by
  have he : (fun t : ℝ ↦ |t| / (d ^ 2 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ (1 / d ^ 3) * (|d⁻¹ * t| / (1 + (d⁻¹ * t) ^ 2) ^ 2)) := by
    funext t
    rw [abs_mul, abs_inv, abs_of_pos hd]
    calc
      _ = (1 / d ^ 4) * (|t| / (1 + (d⁻¹ * t) ^ 2) ^ 2) :=
        cauchy_scale_four hd.ne' t |t|
      _ = _ := by ring
  rw [he, MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ ↦ |t| / (1 + t ^ 2) ^ 2) d⁻¹,
    integral_cauchy_abs, smul_eq_mul, inv_inv, abs_of_pos hd]
  calc
    _ = (d * d⁻¹) * (1 / d ^ 2) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd.ne', one_mul]

/-- For positive d and arbitrary real coefficients A and B, evaluate the integral
of (A+B abs(t))/(d²+t²)² exactly. Split the integrable unweighted and weighted parts.
This turns linear-height analytic bounds into explicit finite error constants. -/
theorem integral_scaled_cauchy_linear {d : ℝ} (hd : 0 < d) (A B : ℝ) :
    (∫ t : ℝ, (A + B * |t|) / (d ^ 2 + t ^ 2) ^ 2) =
      A * (Real.pi / (2 * d ^ 3)) + B / d ^ 2 := by
  have he : (fun t : ℝ ↦ (A + B * |t|) / (d ^ 2 + t ^ 2) ^ 2) =
      (fun t : ℝ ↦ A * (1 / (d ^ 2 + t ^ 2) ^ 2) +
        B * (|t| / (d ^ 2 + t ^ 2) ^ 2)) := by
    funext t
    ring
  rw [he, MeasureTheory.integral_add ((integrable_scaled_cauchy_two hd).const_mul A)
    ((integrable_scaled_cauchy_abs hd).const_mul B), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_scaled_cauchy_two hd,
    integral_scaled_cauchy_abs hd, mul_one_div]

end PseudoPrime.Analysis
