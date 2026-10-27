/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-! # Normalized Gaussian moments for logarithmic smoothing -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real density exp(−v²)/sqrt(pi), normalized to integral one.
Its exponential moment at a is exp(a²/4), corresponding to Gaussian smoothing parameter 1/4.
This density supplies the positive logarithmic mixture of Gamma kernels. -/
noncomputable def normalizedGaussianWeight (v : ℝ) : ℝ :=
  Real.exp (-(v ^ 2)) / Real.sqrt Real.pi

/-- The normalized Gaussian density is positive at every real input.
Both the exponential and sqrt(pi) are positive. This preserves positivity in smoothing averages. -/
theorem normalizedGaussianWeight_pos (v : ℝ) : 0 < normalizedGaussianWeight v := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)

/-- The complex Gaussian integral with linear coefficient z equals
sqrt(pi)exp(z²/4). Specialize the complex quadratic integral and identify the positive square root.
This is the unnormalized moment used by the smoothing density. -/
private theorem gaussian_quadratic_integral (z : ℂ) :
    (∫ v : ℝ, Complex.exp (-(v : ℂ) ^ 2 + z * v)) =
      (Real.sqrt Real.pi : ℝ) * Complex.exp (z ^ 2 / 4) := by
  have h :=
    integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num only [Complex.neg_re, Complex.one_re]) z 0
  have he : (0 : ℂ) - z ^ 2 / (4 * (-1)) = z ^ 2 / 4 := by ring
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℝ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simpa only [neg_one_mul, add_zero, neg_neg, div_one, he, hp] using h

/-- The normalized Gaussian times exp(zv) is integrable for every complex z.
Use complex quadratic integrability and divide by the fixed normalization.
This provides absolute convergence for complex logarithmic moments. -/
theorem integrable_normalizedGaussian_mul_cexp (z : ℂ) :
    MeasureTheory.Integrable
      (fun v : ℝ ↦ (normalizedGaussianWeight v : ℂ) * Complex.exp (z * v)) := by
  have hi := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num only [Complex.one_re]) z 0
  apply (hi.div_const (Real.sqrt Real.pi : ℂ)).congr
  apply Filter.Eventually.of_forall
  intro v
  simp only [normalizedGaussianWeight, Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow, neg_one_mul, add_zero, Complex.exp_add]
  ring

/-- The complex exponential moment of the normalized Gaussian is exp(z²/4).
Extract the normalization from the integral and apply the complex quadratic formula.
This is the Mellin multiplier for the smoothing kernel. -/
theorem integral_normalizedGaussian_mul_cexp (z : ℂ) :
    (∫ v : ℝ, (normalizedGaussianWeight v : ℂ) * Complex.exp (z * v)) =
      Complex.exp (z ^ 2 / 4) := by
  have he :
    (∫ v : ℝ, (normalizedGaussianWeight v : ℂ) * Complex.exp (z * v)) =
      (∫ v : ℝ, Complex.exp (-(v : ℂ) ^ 2 + z * v)) / (Real.sqrt Real.pi : ℂ) := by
    rw [← MeasureTheory.integral_div]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    simp only [normalizedGaussianWeight, Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow, Complex.exp_add]
    ring
  rw [he, gaussian_quadratic_integral]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')

/-- Every real exponential moment of the normalized Gaussian is integrable.
Take the real part of the complex integrability theorem and identify the real exponential.
This supplies dominating functions for the Gamma smoothing mixture. -/
theorem integrable_normalizedGaussian_mul_exp (a : ℝ) :
    MeasureTheory.Integrable (fun v : ℝ ↦ normalizedGaussianWeight v * Real.exp (a * v)) := by
  have hi := integrable_normalizedGaussian_mul_cexp (a : ℂ)
  have hr := hi.re
  change
    MeasureTheory.Integrable
      (fun v : ℝ ↦ ((normalizedGaussianWeight v : ℂ) * Complex.exp ((a : ℂ) * v)).re) at hr
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re] using hr

/-- The real exponential moment at a equals exp(a²/4).
Project the complex moment identity through the real embedding.
This evaluates the half and quarter moments in principal and truncation estimates. -/
theorem integral_normalizedGaussian_mul_exp (a : ℝ) :
    (∫ v : ℝ, normalizedGaussianWeight v * Real.exp (a * v)) = Real.exp (a ^ 2 / 4) := by
  have h := integral_normalizedGaussian_mul_cexp (a : ℂ)
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp h

/-- The normalized Gaussian density is integrable.
Use its zero exponential moment. This justifies averages against the smoothing density. -/
theorem integrable_normalizedGaussianWeight :
    MeasureTheory.Integrable normalizedGaussianWeight := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using integrable_normalizedGaussian_mul_exp 0

/-- The normalized Gaussian density has integral one.
Evaluate the zero exponential moment. This gives the normalization of logarithmic smoothing. -/
theorem integral_normalizedGaussianWeight_eq_one : (∫ v : ℝ, normalizedGaussianWeight v) = 1 := by
  simpa only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero, mul_one] using
    integral_normalizedGaussian_mul_exp 0

/-- The normalized Gaussian density is continuous on the real line.
Compose the square, negation and exponential, then divide by the constant sqrt(pi).
This supplies measurability of the smoothing integrands. -/
theorem continuous_normalizedGaussianWeight : Continuous normalizedGaussianWeight := by
  exact (Real.continuous_exp.comp ((continuous_id.pow 2).neg)).div_const _

end PseudoPrime.Analysis
