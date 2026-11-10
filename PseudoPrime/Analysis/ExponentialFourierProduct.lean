/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquare
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral

/-! # Fourier weights with an exponential product kernel -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A continuous integrable complex weight times the exponential Fourier
kernel is integrable on the product space for every real frequency scale.
The absolute value is dominated by the product of the weight's norm and the
integrable exponential envelope. This justifies exchanging the two integrals. -/
theorem exponential_fourier_product_integrable (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) (s : ℝ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ F p.1 * ExponentialMeanSquare.kernelIntegrand (s * p.1) p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hw : MeasureTheory.Integrable ExponentialMeanSquare.weight := by
    exact integrable_exp_neg_mul_abs (by norm_num only : (0 : ℝ) < 2)
  have hm := hi.norm.mul_prod hw
  have hf : Continuous (fun p : ℝ × ℝ ↦ F p.1) := hF.comp continuous_fst
  have hwc : Continuous (fun p : ℝ × ℝ ↦ (ExponentialMeanSquare.weight p.2 : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp continuous_snd))
  have he : Continuous (fun p : ℝ × ℝ ↦ Complex.exp (Complex.I * (s * (p.1 : ℂ)) * p.2)) := by
    apply Complex.continuous_exp.comp
    exact
      (continuous_const.mul
            (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  have hmeas :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ F p.1 * ExponentialMeanSquare.kernelIntegrand (s * p.1) p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hc :=
      (hf.mul (he.mul hwc)).aestronglyMeasurable (μ :=
        MeasureTheory.volume.prod MeasureTheory.volume)
    convert hc using 1
    funext p
    simp only [ExponentialMeanSquare.kernelIntegrand, Pi.mul_apply, Complex.ofReal_mul]
  apply hm.mono' hmeas
  apply MeasureTheory.ae_of_all
  intro p
  dsimp only [ExponentialMeanSquare.kernelIntegrand, Pi.mul_apply, Function.comp_apply]
  have hwpos : 0 ≤ ExponentialMeanSquare.weight p.2 := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hwpos]
  have hre : (Complex.I * (↑(s * p.1) : ℂ) * (p.2 : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
  rw [hre, Real.exp_zero, one_mul]

/-- The resolvent with an arbitrary real frequency scale is the integral of
the exponential Fourier kernel. Product integrability permits exchanging the
frequency and kernel integrals. -/
theorem exponential_fourier_resolvent_eq (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) (s : ℝ) :
    (∫ t : ℝ, F t * ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ, ∫ t : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v := by
  have hprod := exponential_fourier_product_integrable F hF hi s
  calc
    _ = ∫ t : ℝ, ∫ v : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [MeasureTheory.integral_const_mul, ExponentialMeanSquare.integral_kernelIntegrand]
    _ = _ := MeasureTheory.integral_integral_swap hprod

/-- If every Fourier transform of an integrable continuous weight has
nonnegative real part, then its exponential resolvent integral has
nonnegative real part at every real frequency scale. -/
theorem exponential_fourier_resolvent_nonneg (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) (s : ℝ)
    (hpos : ∀ v : ℝ, 0 ≤ (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)).re) :
    0 ≤ (∫ t : ℝ, F t * ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))).re := by
  rw [exponential_fourier_resolvent_eq F hF hi s]
  have hprod := exponential_fourier_product_integrable F hF hi s
  have hout := hprod.integral_prod_right
  have hre := Complex.reCLM.integral_comp_comm hout
  change
    (∫ v : ℝ, (∫ t : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v).re) =
      (∫ v : ℝ, ∫ t : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v).re at hre
  rw [← hre]
  apply MeasureTheory.integral_nonneg
  intro v
  have he :
    (∫ t : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v) =
      (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) *
        (ExponentialMeanSquare.weight v : ℂ) := by
    rw [← MeasureTheory.integral_mul_const]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [ExponentialMeanSquare.kernelIntegrand, Complex.ofReal_mul]
    ring
  change 0 ≤ (∫ t : ℝ, F t * ExponentialMeanSquare.kernelIntegrand (s * t) v).re
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hpos v) (Real.exp_pos _).le

/-- The resolvent integral is an exponentially weighted integral of Fourier
transforms at the scaled frequencies. The product-integrability theorem
justifies this representation for every real scale. -/
theorem exponential_fourier_resolvent_convolution (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) (s : ℝ) :
    (∫ t : ℝ, F t * ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ,
        (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) *
          (ExponentialMeanSquare.weight v : ℂ) := by
  rw [exponential_fourier_resolvent_eq F hF hi s]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [← MeasureTheory.integral_mul_const]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [ExponentialMeanSquare.kernelIntegrand, Complex.ofReal_mul]
  ring

/-- Rescale the exponential Fourier convolution by a positive frequency
scale. The Jacobian is `s⁻¹` and the exponential decay rate becomes `2 / s`.
This form is useful when the scale represents a resolvent pole. -/
theorem exponential_convolution_rescale (g : ℝ → ℂ) {s : ℝ} (hs : 0 < s) :
    (∫ v : ℝ, g (s * v) * (ExponentialMeanSquare.weight v : ℂ)) =
      (s⁻¹ : ℂ) * ∫ w : ℝ, g w * (Real.exp (-(2 / s) * |w|) : ℂ) := by
  let h : ℝ → ℂ := fun w ↦ g w * (Real.exp (-(2 / s) * |w|) : ℂ)
  have hh := MeasureTheory.Measure.integral_comp_mul_left h s
  simp only [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, Complex.ofReal_inv] at hh
  have he (v : ℝ) : h (s * v) = g (s * v) * (ExponentialMeanSquare.weight v : ℂ) := by
    dsimp only [h, ExponentialMeanSquare.weight]
    rw [abs_mul, abs_of_pos hs]
    have hcancel : (2 / s) * s = (2 : ℝ) := div_mul_cancel₀ 2 hs.ne'
    have hex : -(2 / s) * (s * |v|) = -2 * |v| := by rw [← mul_assoc, neg_mul, hcancel]
    rw [hex]
  simpa only [he, h] using hh

end PseudoPrime.Analysis
