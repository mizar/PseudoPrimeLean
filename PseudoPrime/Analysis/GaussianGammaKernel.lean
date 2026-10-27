/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMoments
public import PseudoPrime.Analysis.GammaMellin

/-! # The fixed Gaussian multiplier for the Gamma kernel

These identities fix the normalization tau = 1/4. They identify the logarithmic
Gaussian average and the exact vertical-line norm, without assuming inversion
or a finite-conductor zero-mass certificate.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The shifted Gamma function multiplied by exp(s²/4).
The input is a complex Mellin variable; the multiplier is the complex moment
of the normalized Gaussian. This is the fixed P2 kernel function. -/
noncomputable def gaussianGammaFunction (s : ℂ) : ℂ :=
  Complex.Gamma (s + 1 / 2) * Complex.exp (s ^ 2 / 4)

/-- At every complex input, the Gaussian moment times the fixed Gamma value
is absolutely integrable. The complex moment theorem supplies integrability,
and multiplication by a constant preserves it. This justifies the average. -/
theorem integrable_gaussianGamma_average (s : ℂ) :
    MeasureTheory.Integrable
      (fun v : ℝ ↦
        (normalizedGaussianWeight v : ℂ) * Complex.exp (s * v) * Complex.Gamma (s + 1 / 2)) :=
  (integrable_normalizedGaussian_mul_cexp s).mul_const _

/-- The Gaussian Gamma function is the logarithmic Gaussian average of the
Gamma function times exp(sv). Evaluate the complex Gaussian moment and extract
the constant Gamma factor. This fixes the smoothing normalization. -/
theorem gaussianGammaFunction_eq_average (s : ℂ) :
    gaussianGammaFunction s =
      ∫ v : ℝ,
        (normalizedGaussianWeight v : ℂ) * Complex.exp (s * v) * Complex.Gamma (s + 1 / 2) := by
  rw [MeasureTheory.integral_mul_const, integral_normalizedGaussian_mul_cexp]
  exact mul_comm _ _

/-- At every complex input, the multiplier has norm exp((re(s)²-im(s)²)/4).
Use the norm of the complex exponential and compute the real part of s².
This gives the Gaussian damping on every vertical line. -/
theorem norm_gaussianGammaFunction (s : ℂ) :
    ‖gaussianGammaFunction s‖ =
      ‖Complex.Gamma (s + 1 / 2)‖ * Real.exp ((s.re ^ 2 - s.im ^ 2) / 4) := by
  rw [gaussianGammaFunction, norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.div_ofNat_re, Complex.mul_re]

/-- On the vertical line with real part c, the fixed function has exact
Gaussian damping exp((c²-t²)/4). Compute the real and imaginary parts of the
line in the general norm identity. This supplies vertical integrability. -/
theorem norm_gaussianGammaFunction_vertical (c t : ℝ) :
    ‖gaussianGammaFunction ((c : ℂ) + Complex.I * (t : ℂ))‖ =
      ‖Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2)‖ * Real.exp ((c ^ 2 - t ^ 2) / 4) := by
  rw [norm_gaussianGammaFunction]
  congr 2
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_self, mul_zero,
    zero_add, add_zero]

/-- The Gaussian multiplier is bounded by exp(re(s)²/4) at every complex input.
The square of the imaginary part is nonnegative. This supplies a constant
majorant on each vertical line without discarding its exact damping identity. -/
theorem norm_gaussian_multiplier_le (s : ℂ) :
    ‖Complex.exp (s ^ 2 / 4)‖ ≤ Real.exp (s.re ^ 2 / 4) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [pow_two, Complex.div_ofNat_re, Complex.mul_re]
  nlinarith only [sq_nonneg s.im]

/-- The endpoint multiplier exp(1/16) is at most 2129/2000.
A four-term Taylor bound leaves positive rational slack. This is the endpoint
contract used in the Gaussian coefficient comparison. -/
theorem gaussian_endpoint_exp_le : Real.exp (1 / 16 : ℝ) ≤ 2129 / 2000 := by
  have h :=
    Real.exp_bound' (x := (1 / 16 : ℝ)) (n := 4) (by norm_num only) (by norm_num only) (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_ofNat] at h
  linarith only [h]

/-- The kernel endpoint at s=1/2 is exp(1/16).
Gamma(1)=1 and the multiplier argument is 1/16. This identifies the principal
main term before applying the rational endpoint certificate. -/
theorem gaussianGammaFunction_endpoint :
    (gaussianGammaFunction (1 / 2)).re = Real.exp (1 / 16 : ℝ) := by
  have harg : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num only
  have hsquare : (1 / 2 : ℂ) ^ 2 / 4 = (1 / 16 : ℝ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [gaussianGammaFunction, harg, Complex.Gamma_one, one_mul, hsquare, ← Complex.ofReal_exp,
    Complex.ofReal_re]

/-- The Gaussian Gamma endpoint obeys the P2 rational contract.
Combine the exact endpoint identity with its Taylor certificate. This bounds
the principal main term by 2129/2000. -/
theorem gaussianGammaFunction_endpoint_le : (gaussianGammaFunction (1 / 2)).re ≤ 2129 / 2000 :=
  gaussianGammaFunction_endpoint.trans_le gaussian_endpoint_exp_le

/-- The exponential multiplier is continuous as a function of height on each
vertical line. Polynomial operations and the complex exponential preserve
continuity. This supplies measurability for vertical integral bounds. -/
theorem continuous_gaussian_multiplier_vertical (c : ℝ) :
    Continuous (fun t : ℝ ↦ Complex.exp ((((c : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4)) :=
  Complex.continuous_exp.comp
    (((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow 2).div_const _)

/-- At every height, the multiplier on the line with real part c is bounded
by exp(c²/4). Apply the general multiplier norm bound and compute the real
part. This is the majorant needed to preserve Gamma integrability. -/
theorem norm_gaussian_multiplier_vertical_le (c t : ℝ) :
    ‖Complex.exp ((((c : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4)‖ ≤ Real.exp (c ^ 2 / 4) := by
  have h := norm_gaussian_multiplier_le ((c : ℂ) + Complex.I * (t : ℂ))
  simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using h

/-- Shifted Gamma is absolutely integrable on every vertical line c>-1/2.
Transport the established Gamma vertical integral along the half-unit shift.
This is the unsmoothed dominating function for Gaussian inversion. -/
theorem integrable_shiftedGamma_vertical {c : ℝ} (hc : -(1 : ℝ) / 2 < c) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2)) := by
  have hi := integrable_Gamma_vertical (by linarith only [hc] : 0 < c + 1 / 2)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact congrArg Complex.Gamma (add_right_comm _ _ _)

/-- The Gaussian Gamma function is absolutely integrable on each line c>-1/2.
Multiply the shifted Gamma integrand by the bounded measurable multiplier.
This provides the vertical integral used in Gaussian inverse Mellin formulas. -/
theorem integrable_gaussianGamma_vertical {c : ℝ} (hc : -(1 : ℝ) / 2 < c) :
    MeasureTheory.Integrable (fun t : ℝ ↦ gaussianGammaFunction ((c : ℂ) + Complex.I * (t : ℂ))) :=
  (integrable_shiftedGamma_vertical hc).mul_bdd
    (continuous_gaussian_multiplier_vertical c).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_gaussian_multiplier_vertical_le c))

end PseudoPrime.Analysis
