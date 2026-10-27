/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Weighted mean squares of finite exponential sums

Finite exponential sums and the Laplace weight used in arXiv:2607.14515v1, Section 4.
The development does not assume GRH or a pair-correlation conjecture.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The positive weight `exp (-2 * |v|)` for the real-line mean square.
The input is a real logarithmic displacement. This weight defines the energy below. -/
noncomputable def weight (v : ℝ) : ℝ :=
  Real.exp (-2 * |v|)

/-- The weighted Fourier integrand at real frequency `t` and displacement `v`.
Its integral is the positive definite kernel `4 / (4 + t^2)`. -/
noncomputable def kernelIntegrand (t v : ℝ) : ℂ :=
  Complex.exp (Complex.I * t * v) * (weight v : ℂ)

/-- For nonnegative displacement, the weighted phase is one decaying complex exponential.
Use the absolute-value branch and the exponential addition identity.
This supplies the integrand on the positive half-line. -/
theorem kernelIntegrand_of_nonneg (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    kernelIntegrand t v = Complex.exp (((-2 : ℂ) + Complex.I * t) * v) := by
  rw [kernelIntegrand, weight, abs_of_nonneg hv, Complex.ofReal_exp, ← Complex.exp_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 1
  ring

/-- For nonpositive displacement, the weighted phase is one decaying complex exponential.
Use the absolute-value branch and the exponential addition identity.
This supplies the integrand on the negative half-line. -/
theorem kernelIntegrand_of_nonpos (t : ℝ) {v : ℝ} (hv : v ≤ 0) :
    kernelIntegrand t v = Complex.exp (((2 : ℂ) + Complex.I * t) * v) := by
  rw [kernelIntegrand, weight, abs_of_nonpos hv, Complex.ofReal_exp, ← Complex.exp_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 1
  ring

/-- For every real frequency, the positive half-line integrand is integrable.
Use its decaying complex exponential expression to justify the Fourier integral. -/
theorem integrableOn_kernelIntegrand_Ioi (t : ℝ) :
    MeasureTheory.IntegrableOn (kernelIntegrand t) (Set.Ioi 0) := by
  have hr : ((-2 : ℂ) + Complex.I * t).re < 0 := by
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    change (-2 : ℝ) < 0
    norm_num only
  exact
    (integrableOn_exp_mul_complex_Ioi hr 0).congr_fun
      (fun v hv ↦ (kernelIntegrand_of_nonneg t (le_of_lt hv)).symm) measurableSet_Ioi

/-- For every real frequency, the negative half-line integrand is integrable.
Use its decaying complex exponential expression to justify the Fourier integral. -/
theorem integrableOn_kernelIntegrand_Iic (t : ℝ) :
    MeasureTheory.IntegrableOn (kernelIntegrand t) (Set.Iic 0) := by
  have hr : 0 < ((2 : ℂ) + Complex.I * t).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    change (0 : ℝ) < 2
    norm_num only
  exact
    (integrableOn_exp_mul_complex_Iic hr 0).congr_fun
      (fun v hv ↦ (kernelIntegrand_of_nonpos t hv).symm) measurableSet_Iic

/-- For every real frequency, the weighted phase is integrable on the real line.
Join the half-lines; finite sums can then be integrated term by term. -/
theorem integrable_kernelIntegrand (t : ℝ) : MeasureTheory.Integrable (kernelIntegrand t) := by
  have h := (integrableOn_kernelIntegrand_Iic t).union (integrableOn_kernelIntegrand_Ioi t)
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at h
  exact h

/-- The positive half-line Fourier integral is a negative reciprocal.
Evaluate the decaying exponential to obtain one half of the rational kernel. -/
theorem integral_kernelIntegrand_Ioi (t : ℝ) :
    (∫ v : ℝ in Set.Ioi 0, kernelIntegrand t v) = -1 / ((-2 : ℂ) + Complex.I * t) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun v hv ↦ kernelIntegrand_of_nonneg t (le_of_lt hv))]
  have hr : ((-2 : ℂ) + Complex.I * t).re < 0 := by
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    change (-2 : ℝ) < 0
    norm_num only
  rw [integral_exp_mul_complex_Ioi hr 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- The negative half-line Fourier integral is a reciprocal.
Evaluate the decaying exponential to obtain the other half of the rational kernel. -/
theorem integral_kernelIntegrand_Iic (t : ℝ) :
    (∫ v : ℝ in Set.Iic 0, kernelIntegrand t v) = 1 / ((2 : ℂ) + Complex.I * t) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (fun v hv ↦ kernelIntegrand_of_nonpos t hv)]
  have hr : 0 < ((2 : ℂ) + Complex.I * t).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    change (0 : ℝ) < 2
    norm_num only
  rw [integral_exp_mul_complex_Iic hr 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- For a nonzero real c, c + I t is nonzero for every real t.
Take the real part of a hypothetical zero to justify reciprocal denominators. -/
theorem nonzero_real_add_imaginary {c : ℝ} (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at hr
  exact hc hr

/-- For real t, the rational kernel denominator 4+t squared is nonzero in the complex numbers.
Use positivity of its real antecedent to clear the Fourier-integral denominator. -/
theorem kernel_denominator_ne_zero (t : ℝ) : (4 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
  have he : (4 : ℂ) + (t : ℂ) ^ 2 = ((4 + t ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [he]
  exact
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t)))

/-- For every real frequency, the two half-line reciprocal integrals add to the rational kernel.
Clear the three nonzero denominators and use I squared equals minus one. -/
theorem kernel_reciprocal_sum (t : ℝ) :
    1 / ((2 : ℂ) + Complex.I * t) + -1 / ((-2 : ℂ) + Complex.I * t) =
      (4 : ℂ) / (4 + (t : ℂ) ^ 2) := by
  have hp := nonzero_real_add_imaginary (by norm_num only : (2 : ℝ) ≠ 0) t
  have hn := nonzero_real_add_imaginary (by norm_num only : (-2 : ℝ) ≠ 0) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg] at hp hn
  field_simp [hp, hn, kernel_denominator_ne_zero t]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- For every real frequency, the Fourier transform of the Laplace weight is rational.
Add the half-line integrals and clear the explicitly nonzero denominators.
This identifies the positive definite kernel in the mean-square formula. -/
theorem integral_kernelIntegrand (t : ℝ) :
    (∫ v : ℝ, kernelIntegrand t v) = (4 : ℂ) / (4 + (t : ℂ) ^ 2) := by
  rw [←
    intervalIntegral.integral_Iic_add_Ioi (integrableOn_kernelIntegrand_Iic t)
      (integrableOn_kernelIntegrand_Ioi t),
    integral_kernelIntegrand_Iic, integral_kernelIntegrand_Ioi, kernel_reciprocal_sum]

end PseudoPrime.Analysis.ExponentialMeanSquare
