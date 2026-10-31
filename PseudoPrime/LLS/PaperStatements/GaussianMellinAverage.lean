/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMoments
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian averaging of vertical Mellin integrals

An absolutely integrable vertical-line integrand can be averaged against the
normalized logarithmic Gaussian. Fubini then transfers the average to the
complex Gaussian multiplier on the Mellin line.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The logarithmic Gaussian average of an integrable vertical-line integrand
is itself integrable. The Gaussian exponential moment times `‖F‖` gives an
integrable product majorant; the left product marginal is the required average. -/
theorem integrable_logGaussianAverage_integrand {c : ℝ} {F : ℝ → ℂ}
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable
      (fun v : ℝ =>
        (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
          (∫ t : ℝ, Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t)) := by
  let J : ℝ → ℝ → ℂ := fun v t =>
    (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
      Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
      F t
  have hcont :
    Continuous
      (fun z : ℝ × ℝ =>
        (PseudoPrime.Analysis.normalizedGaussianWeight z.1 : ℂ) *
          Complex.exp (((c : ℂ) + Complex.I * (z.2 : ℂ)) * (z.1 : ℂ))) := by
    exact
      (Complex.continuous_ofReal.comp
            (PseudoPrime.Analysis.continuous_normalizedGaussianWeight.comp continuous_fst)).mul
        (Complex.continuous_exp.comp
          ((continuous_const.add
                (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
            (Complex.continuous_ofReal.comp continuous_fst)))
  have hmeas :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry J)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    dsimp only [J, Function.uncurry]
    exact hcont.aestronglyMeasurable.mul (hF.aestronglyMeasurable.comp_snd)
  have hnorm (v t : ℝ) :
    ‖(PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
          Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
          F t‖ =
      PseudoPrime.Analysis.normalizedGaussianWeight v * Real.exp (c * v) * ‖F t‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (PseudoPrime.Analysis.normalizedGaussianWeight_pos v), Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  have hprod :
    MeasureTheory.Integrable
      (fun z : ℝ × ℝ =>
        (PseudoPrime.Analysis.normalizedGaussianWeight z.1 * Real.exp (c * z.1)) * ‖F z.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (PseudoPrime.Analysis.integrable_normalizedGaussian_mul_exp c).mul_prod hF.norm
  have hJ :
    MeasureTheory.Integrable (Function.uncurry J)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    apply hprod.mono' hmeas
    filter_upwards with z
    rw [show
        Function.uncurry J z =
          (PseudoPrime.Analysis.normalizedGaussianWeight z.1 : ℂ) *
            Complex.exp (((c : ℂ) + Complex.I * (z.2 : ℂ)) * (z.1 : ℂ)) *
            F z.2
        by rfl,
      hnorm]
  have hi := hJ.integral_prod_left
  apply hi.congr
  exact
    Filter.Eventually.of_forall fun v => by
      calc
        (∫ t : ℝ, J v t) =
            ∫ t : ℝ,
              (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                (Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) :=
          by
          congr 1
          funext t
          dsimp only [J]
          ring
        _ =
            (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
              (∫ t : ℝ, Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) :=
          MeasureTheory.integral_const_mul _ _

/-- If `F` is integrable on a vertical line with real part `c`, multiplication
by the Gaussian Mellin factor equals averaging the vertically integrated
shifted integrand against the normalized Gaussian. The product majorant is the
Gaussian exponential moment times `‖F‖`; Fubini and the complex Gaussian moment
give the identity. This is the transfer interface for signed contour estimates. -/
theorem integral_gaussianMultiplier_eq_logGaussianAverage {c : ℝ} {F : ℝ → ℂ}
    (hF : MeasureTheory.Integrable F) :
    (∫ t : ℝ, Complex.exp ((((c : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4) * F t) =
      ∫ v : ℝ,
        (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
          (∫ t : ℝ, Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) := by
  let J : ℝ → ℝ → ℂ := fun v t =>
    (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
      Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
      F t
  have hcont :
    Continuous
      (fun z : ℝ × ℝ =>
        (PseudoPrime.Analysis.normalizedGaussianWeight z.1 : ℂ) *
          Complex.exp (((c : ℂ) + Complex.I * (z.2 : ℂ)) * (z.1 : ℂ))) := by
    exact
      (Complex.continuous_ofReal.comp
            (PseudoPrime.Analysis.continuous_normalizedGaussianWeight.comp continuous_fst)).mul
        (Complex.continuous_exp.comp
          ((continuous_const.add
                (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
            (Complex.continuous_ofReal.comp continuous_fst)))
  have hmeas :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry J)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    dsimp only [J, Function.uncurry]
    exact hcont.aestronglyMeasurable.mul (hF.aestronglyMeasurable.comp_snd)
  have hnorm (v t : ℝ) :
    ‖(PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
          Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
          F t‖ =
      PseudoPrime.Analysis.normalizedGaussianWeight v * Real.exp (c * v) * ‖F t‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (PseudoPrime.Analysis.normalizedGaussianWeight_pos v), Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  have hprod :
    MeasureTheory.Integrable
      (fun z : ℝ × ℝ =>
        (PseudoPrime.Analysis.normalizedGaussianWeight z.1 * Real.exp (c * z.1)) * ‖F z.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (PseudoPrime.Analysis.integrable_normalizedGaussian_mul_exp c).mul_prod hF.norm
  have hJ :
    MeasureTheory.Integrable (Function.uncurry J)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    apply hprod.mono' hmeas
    filter_upwards with z
    rw [show
        Function.uncurry J z =
          (PseudoPrime.Analysis.normalizedGaussianWeight z.1 : ℂ) *
            Complex.exp (((c : ℂ) + Complex.I * (z.2 : ℂ)) * (z.1 : ℂ)) *
            F z.2
        by rfl,
      hnorm]
  calc
    _ =
        ∫ t : ℝ,
          ∫ v : ℝ,
            (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
              Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
              F t :=
      by
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall fun t => by
          calc
            Complex.exp ((((c : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4) * F t =
                (∫ v : ℝ,
                    (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                      Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ))) *
                  F t :=
              by rw [PseudoPrime.Analysis.integral_normalizedGaussian_mul_cexp]
            _ =
                ∫ v : ℝ,
                  (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                    Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
                    F t :=
              by rw [← MeasureTheory.integral_mul_const]
    _ = ∫ v : ℝ, ∫ t : ℝ, J v t := by rw [MeasureTheory.integral_integral_swap hJ]
    _ =
        ∫ v : ℝ,
          (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
            (∫ t : ℝ, Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) :=
      by
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall fun v => by
          calc
            (∫ t : ℝ, J v t) =
                ∫ t : ℝ,
                  (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                    (Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) :=
              by
              congr 1
              funext t
              dsimp only [J]
              ring
            _ =
                (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                  (∫ t : ℝ, Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) :=
              MeasureTheory.integral_const_mul _ _

end PseudoPrime.LLS.PaperStatements
